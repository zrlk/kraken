/-
**Nodes with the thread pointer** (AArch64, H7a calls): a node whose
invariant also pins `tpidr_el0` to the thread's pointer `tp` (`ND.withTp`),
for the thread's words read from `tp` (the stack limit's at `limA tp`).
No covered instruction writes `tpidr_el0` (`arun_tpidr`), so every block's
edge is one with the thread pointer at both ends (`BlkEdge.tp`), and the
per-construct segments of `Spike/Lib/LowerA64/Node.lean`/`Node1.lean` hold
between nodes with the thread pointer (`add_segT`, `store_segT`, `sub_segT`,
`br_segT`, `jmp_segT`, `ret_segT`).

- `BlkW.mono`, `BlkW.nodeW`: a block's states inside `W` at a node with a
  stronger invariant; the node's own states (the block's first).
-/
import Spike.Lib.LowerA64.Node1

namespace Spike.Lib.A64.Flow

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

/-- **A node with the thread pointer**: `n`, `tpidr_el0` holding `tp`. -/
def ND.withTp (n : ND) (tp : UInt64) : ND := ⟨n.pc, n.o, fun σ c => n.J σ c ∧ σ.regs.TPIDR_EL0 = tp⟩

theorem setRegOrZr_TPIDR (r : Reg64s) {w : RegWidth} (d : RegOrZr w) (v : w.type) :
    (r.setRegOrZr d v).TPIDR_EL0 = r.TPIDR_EL0 := by
  rcases d with ⟨x | _, w⟩ <;> cases w <;> first | rfl | (cases x <;> rfl)

theorem setRegOrSp_TPIDR (r : Reg64s) {w : RegWidth} (d : RegOrSp w) (v : w.type) :
    (r.setRegOrSp d v).TPIDR_EL0 = r.TPIDR_EL0 := by
  rcases d with ⟨x | _, w⟩ <;> cases w <;> first | rfl | (cases x <;> rfl)

/-- **A register operation keeps `tpidr_el0`** (`mrs` reads it). -/
theorem regRes_TPIDR {w : RegWidth} {op : Operation w} (h : RegOnly op = true) (m : MachineData) :
    (regRes op m).regs.TPIDR_EL0 = m.regs.TPIDR_EL0 := by
  unfold RegOnly at h
  split at h <;> first
    | exact absurd h (by decide)
    | (simp only [regRes, Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp]
       first
       | exact setRegOrZr_TPIDR _ _ _
       | exact setRegOrSp_TPIDR _ _ _
       | rfl)

/-- **No covered instruction writes `tpidr_el0`.** -/
theorem dstep_tpidr (lab : Label → Int64) (am : AM) (d : Directive) :
    (dstep lab am d).σ.regs.TPIDR_EL0 = am.σ.regs.TPIDR_EL0 := by
  unfold dstep
  split
  · rename_i a ha
    obtain ⟨-, hr⟩ := classify_sound ha
    cases a with
    | ldr t n => exact setRegOrZr_TPIDR _ _ _
    | str t n => rfl
    | reg w op =>
      show (regRes op _).regs.TPIDR_EL0 = _
      exact regRes_TPIDR (hr w op rfl) _
    | bl L => exact setRegOrZr_TPIDR _ _ _
    | _ => rfl
  · rfl

/-- **A block's abstract run keeps `tpidr_el0`.** -/
theorem arun_tpidr (lab : Label → Int64) (blk : List Directive) (am : AM) :
    (arun lab blk am).σ.regs.TPIDR_EL0 = am.σ.regs.TPIDR_EL0 := by
  induction blk generalizing am with
  | nil => rfl
  | cons d ds ih =>
    show (arun lab ds (dstep lab am d)).σ.regs.TPIDR_EL0 = _
    rw [ih, dstep_tpidr]

end Spike.Lib.A64.Flow

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode

set_option linter.unusedSimpArgs false

variable {p : Prog}

/-- **A block's edge with the thread pointer** at both ends. -/
theorem BlkEdge.tp {lab : Label → Int64} {lo hi : Int} {n : ND} {blk : List Directive} {ι κ : Sort _}
    {N : ι → ND} {E : κ → ND} (h : BlkEdge p lab lo hi n blk N E) (tp : UInt64) :
    BlkEdge p lab lo hi (n.withTp tp) blk (fun j => (N j).withTp tp) (fun x => (E x).withTp tp) := by
  refine ⟨h.1, h.2.1, fun σ c ⟨hJ, ht⟩ => ?_⟩
  obtain ⟨c', hr, hL⟩ := h.2.2 σ c hJ
  have ht' := arun_tpidr lab blk ⟨n.pc, n.o, σ⟩
  refine ⟨c', hr, ?_⟩
  rcases hL with ⟨j, h1, h2, h3⟩ | ⟨x, h1, h2, h3⟩
  · exact .inl ⟨j, h1, h2, h3, ht'.trans ht⟩
  · exact .inr ⟨x, h1, h2, h3, ht'.trans ht⟩

section W

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isaLSE2} {K : State → State → Prop}

/-- **A block's states inside `W` at a node with a stronger invariant.** -/
theorem BlkW.mono {n n' : ND} {blk : List Directive} (h : BlkW W K exe endPc R F n blk) (hpc : n'.pc = n.pc)
    (ho : n'.o = n.o) (hJ : ∀ σ c, n'.J σ c → n.J σ c) : BlkW W K exe endPc R F n' blk := by
  intro s σ c he hn hd hp hA hF hJ' k hk m hA' hD
  rw [hpc] at hp hA' ⊢
  rw [ho] at hA hA'
  exact h s σ c he hn hd hp hA hF (hJ σ c hJ') k hk m hA' hD

/-- A block's states inside `W` at the node with the thread pointer. -/
theorem BlkW.withTp {n : ND} {blk : List Directive} (h : BlkW W K exe endPc R F n blk) (tp : UInt64) :
    BlkW W K exe endPc R F (n.withTp tp) blk :=
  BlkW.mono h rfl rfl fun _ _ h => h.1

/-- **A node's states inside `W`**: the first of a block's. -/
theorem BlkW.nodeW {n : ND} {blk : List Directive} (h : BlkW W K exe endPc R F n blk) (hne : blk ≠ []) :
    NodeW W K exe endPc R F n := by
  rintro s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩
  have hk : 0 < blk.length := List.length_pos_iff.mpr hne
  have := h s σ c he hn hd hp hA hF hJ 0 hk s.st.1 (by simpa [arun] using hA) (DFrame.refl _ _)
  have hs : { s with st := (s.st.1, n.pc + Int64.ofNat (4 * 0)) } = s := by
    rw [← hp]; simp
    rfl
  rw [hs] at this
  exact this

end W

end Spike.Lib.LowerA64
