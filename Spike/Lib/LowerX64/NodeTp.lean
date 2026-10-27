/-
**Nodes with the thread pointer** (x86-64, H7a calls), the twin of
`Spike/Lib/LowerA64/NodeTp.lean`: a node whose invariant also pins the
`%fs` base to the thread's pointer `tp` (`ND.withTp`), for the call
bracket's depth word at `%fs:depth`. No covered instruction writes the `%fs`
base (`arun_fsBase`; it is not a `Reg64`, and `movfs` only reads it), so
every block's edge is one with the thread pointer at both ends
(`BlkEdge.tp`), and the per-construct edges of
`Spike/Lib/LowerX64/Node.lean`/`Node1.lean` (`add_edge`, `store_edge`,
`ret_edge`, `sub_edge`, `br_edge`, `jmp_edge`) hold between nodes with the
thread pointer.

- `BlkW.mono`, `BlkW.withTp`, `BlkW.nodeW`: a block's states inside `W` at
  a node with a stronger invariant; the node's own states (the block's
  first).
-/
import Spike.Lib.LowerX64.Node1

namespace Spike.Lib.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64

/-- **A node with the thread pointer**: `n`, the `%fs` base holding `tp`. -/
def ND.withTp (n : ND) (tp : UInt64) : ND := ⟨n.pc, n.o, fun σ c => n.J σ c ∧ σ.regs.fsBase = tp⟩

theorem Reg64s.set64_fsBase (s : Reg64s) (r : Reg64) (v : BitVec 64) : (s.set64 r v).fsBase = s.fsBase := by
  cases r <;> rfl

theorem Reg64s.set_fsBase (s : Reg64s) {w : Width} (r : Reg w) (v : w.type) : (s.set r v).fsBase = s.fsBase := by
  unfold Reg64s.set
  split <;> exact Reg64s.set64_fsBase _ _ _

/-- **A register operation keeps the `%fs` base.** -/
theorem regRes_fsBase {w : Width} {op : Operation w} (h : RegOnly op = true) (m : MachineData) :
    (regRes op m).regs.fsBase = m.regs.fsBase := by
  unfold RegOnly at h
  split at h <;> first
    | exact absurd h (by decide)
    | rfl
    | exact Reg64s.set_fsBase _ _ _
    | (show (Reg64s.set _ _ _).fsBase = _; exact Reg64s.set_fsBase _ _ _)

/-- **No covered instruction writes the `%fs` base.** -/
theorem dstep_fsBase (lab : String → Int64) (am : AM) (d : Directive × Nat) :
    (dstep lab am d).σ.regs.fsBase = am.σ.regs.fsBase := by
  obtain ⟨d, z⟩ := d
  simp only [dstep]
  split
  · rename_i a ha
    obtain ⟨-, hr⟩ := classify_sound ha
    cases a with
    | ld r b n => exact Reg64s.set64_fsBase _ _ _
    | st b n r => rfl
    | push r => exact Reg64s.set64_fsBase _ _ _
    | pop r => exact (Reg64s.set64_fsBase _ _ _).trans (Reg64s.set64_fsBase _ _ _)
    | reg w op => exact regRes_fsBase (hr w op rfl) _
    | jmp L => rfl
    | jcc cc L => rfl
    | call L => exact Reg64s.set64_fsBase _ _ _
    | ret => exact Reg64s.set64_fsBase _ _ _
  · rfl

/-- **A block's abstract run keeps the `%fs` base.** -/
theorem arun_fsBase (lab : String → Int64) (blk : List (Directive × Nat)) (am : AM) :
    (arun lab blk am).σ.regs.fsBase = am.σ.regs.fsBase := by
  induction blk generalizing am with
  | nil => rfl
  | cons d ds ih =>
    show (arun lab ds (dstep lab am d)).σ.regs.fsBase = _
    rw [ih, dstep_fsBase]

end Spike.Lib.X64

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64

variable {p : Prog}

/-- **A block's edge with the thread pointer** at both ends. -/
theorem BlkEdge.tp {lab : String → Int64} {lo hi : Int} {n : ND} {blk : List (Directive × Nat)} {ι κ : Sort _}
    {N : ι → ND} {E : κ → ND} (h : BlkEdge p lab lo hi n blk N E) (tp : UInt64) :
    BlkEdge p lab lo hi (n.withTp tp) blk (fun j => (N j).withTp tp) (fun x => (E x).withTp tp) := by
  refine ⟨h.1, h.2.1, fun σ c ⟨hJ, ht⟩ => ?_⟩
  obtain ⟨c', hr, hL⟩ := h.2.2 σ c hJ
  have ht' := arun_fsBase lab blk ⟨n.pc, n.o, σ⟩
  refine ⟨c', hr, ?_⟩
  rcases hL with ⟨j, h1, h2, h3⟩ | ⟨x, h1, h2, h3⟩
  · exact .inl ⟨j, h1, h2, h3, ht'.trans ht⟩
  · exact .inr ⟨x, h1, h2, h3, ht'.trans ht⟩

section W

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isa} {K : State → State → Prop}

/-- **A block's states inside `W` at a node with a stronger invariant.** -/
theorem BlkW.mono {n n' : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk)
    (hpc : n'.pc = n.pc) (ho : n'.o = n.o) (hJ : ∀ σ c, n'.J σ c → n.J σ c) : BlkW W K exe endPc R F n' blk := by
  intro s σ c he hn hd hp hA hF hJ' k hk m hA' hD
  rw [hpc] at hp hA' ⊢
  rw [ho] at hA hA'
  exact h s σ c he hn hd hp hA hF (hJ σ c hJ') k hk m hA' hD

/-- A block's states inside `W` at the node with the thread pointer. -/
theorem BlkW.withTp {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk) (tp : UInt64) :
    BlkW W K exe endPc R F (n.withTp tp) blk :=
  BlkW.mono h rfl rfl fun _ _ h => h.1

/-- A state at the node with the thread pointer is one at the node. -/
theorem At.of_withTp {n : ND} {tp : UInt64} {s : State} {c : Ctl} (h : At exe endPc R F (n.withTp tp) s c) :
    At exe endPc R F n s c :=
  let ⟨he, hn, hd, hp, σ, hA, hF, hJ, _⟩ := h
  ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}

/-- An `At` exit from a one-node `Next` with no exits. -/
theorem SegW.of_next1E {P : Frag isa} {n : ND} {E : Empty → ND}
    (h : SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) E)) :
    SegW W K p lbl ms P (At exe endPc R F n) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

/-- The two `At` exits of a compare-and-branch's `Next` with the thread
pointer (`br_edge`'s nodes, `BlkEdge.tp`). -/
theorem SegW.of_nextBTp {P : Frag isa} {A B : ND} {tp : UInt64} {E : Empty → ND}
    (h : SegW W K p lbl ms P (Next exe endPc R F (fun bb : Bool => (if bb then A else B).withTp tp) E)) :
    SegW W K p lbl ms P (fun st c => At exe endPc R F (A.withTp tp) st c ∨ At exe endPc R F (B.withTp tp) st c) :=
  h.mono_post fun _ _ h => by
    rcases h with ⟨bb, h⟩ | ⟨e, _⟩
    · cases bb
      · exact .inr h
      · exact .inl h
    · exact e.elim

/-- **A node's states inside `W`**: the first of a block's. -/
theorem BlkW.nodeW {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk) (hne : blk ≠ []) :
    NodeW W K exe endPc R F n := by
  rintro s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩
  have hk : 0 < blk.length := List.length_pos_iff.mpr hne
  have := h s σ c he hn hd hp hA hF hJ 0 hk s.st.1 (by simpa [arun] using hA) (DFrame.refl _ _)
  have hs : { s with st := (s.st.1, n.pc + Int64.ofNat (cellOff blk 0)) } = s := by
    rw [← hp]; simp [cellOff]
    rfl
  rw [hs] at this
  exact this

end W

end Spike.Lib.LowerX64
