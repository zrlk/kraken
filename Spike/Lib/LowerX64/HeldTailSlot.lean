/-
**The held return tail's `Ret0` from a frame slot** (x86-64; the twin of
`Spike/Lib/LowerA64/HeldTailSlot.lean`): along `main`'s `ret b` block at the
held frames, the callee's result is not yet in `%rax` but in `main`'s cell
of the frame's result `f.x` (the result's store wrote it); the block stores
nothing, so the cell keeps the word at every state, and `Ret0` places the
callee's `ret a` at that slot.

- `wordRep_slot`: a region cell's word at its slot place;
- `RetSlot`, `nodeW_ret0_slot`, `blkW_ret0_slot`: `Ret0` along the tail's
  nodes and blocks that keep the cell;
- `frameStep_of_heldRun`: a held pair's frame run to depth 0 is one step;
- `lookup_of_nodeJE_slot`, `retSlot_of_heldRun`: `RetSlot` from a node whose
  symbolic environment places `f.x` as a register operand at a cell;
- `blkW_heldS`: `HeldS` on a block from its four parts (the A64 one is in
  `Spike/Lib/LowerA64/Body2SegHF.lean`).
-/
import Spike.Lib.LowerX64.HeldTailRet

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Scc.Sem (ValRep)
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA

/-- **A region cell's word at its slot place**: the cell `k` of the region
holds the abstract slot `σ.slot k`. -/
theorem wordRep_slot {R : Spike.Lib.Region} {o : Spike.Lib.X64.SO} {s : State} {σ : Spike.Lib.X64.AS}
    (hA : Spike.Lib.X64.Abs R o s.st.1 σ) {k : Int} (hk : R.Off k) {lbl : Lbl} {w : WeakMem.Val}
    (hv : ValRep lbl w (σ.slot k).toNat) :
    WordPlaceRep (machine (kernel 1)) lbl s (.one (.slot (R.addr k).toNat)) w := by
  obtain ⟨j, hj, he⟩ := hA.slot k hk
  refine ⟨_, ?_, hv⟩
  show (privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [privLoad, hj, Option.map_some, he]

/-- **A node's state holds a held callee's result in a region cell**: the
control a callee's `ret a`, its return landing with the frame's result bound
to one word the cell `k` of the region represents. -/
def RetSlot (p : Prog) (lbl : Lbl) (R : Spike.Lib.Region) (σ : Spike.Lib.X64.AS) (c : Ctl) : Prop :=
  ∃ a f fs cR ty w k, c.term = .ret a ∧ FrameStep p (c, f :: fs) (cR, fs) ∧
    TermRun.lookupE cR.env f.x = some (ty, [w]) ∧ R.Off k ∧ ValRep lbl w.val (σ.slot k).toNat

/-- **`Ret0` from a region cell** at a state the abstract state describes. -/
theorem ret0_of_retSlot {p : Prog} {lbl : Lbl} {R : Spike.Lib.Region} {o : Spike.Lib.X64.SO} {s : State}
    {σ : Spike.Lib.X64.AS} {c : Ctl} (hA : Spike.Lib.X64.Abs R o s.st.1 σ) (h : RetSlot p lbl R σ c) :
    Ret0 lbl s c := by
  obtain ⟨a, f, fs, cR, ty, w, k, hc, hst, hl, hk, hv⟩ := h
  exact ret0_of_frameStep hc hst hl (wordRep_slot hA hk hv)

/-- **A node's states are `Ret0`** where its invariant holds the result in
a region cell (`RetSlot`). -/
theorem nodeW_ret0_slot {p : Prog} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop} {n : Spike.Lib.X64.ND}
    (hJ : ∀ σ c, n.J σ c → RetSlot p lbl R σ c) :
    Spike.Lib.X64.NodeW (Ret0 lbl) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, hA, -, hJn⟩
  exact ⟨ret0_of_retSlot hA (hJ σ c hJn), fun _ h => h⟩

/-- **A block's states are `Ret0`** where the node's invariant holds the
result in a region cell (`RetSlot`) and the block's instructions before
each state leave the cells as they were (`hsl`). -/
theorem blkW_ret0_slot {p : Prog} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop} {n : Spike.Lib.X64.ND} {blk : List (Directive × Nat)}
    (hJ : ∀ σ c, n.J σ c → RetSlot p lbl R σ c)
    (hsl : ∀ σ k, k < blk.length →
      (Spike.Lib.X64.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot = σ.slot) :
    Spike.Lib.X64.BlkW (Ret0 lbl) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hJn k hk m hA' _
  refine ⟨ret0_of_retSlot (p := p) hA' ?_, fun _ h => h⟩
  obtain ⟨a, f, fs, cR, ty, w, j, hc, hst, hl, hj, hv⟩ := hJ σ c hJn
  exact ⟨a, f, fs, cR, ty, w, j, hc, hst, hl, hj, by rw [hsl σ k hk]; exact hv⟩

/-- **A held pair's frame run to depth 0 is one step**: the callee's return
into the frame's `ret b`, which takes no further step. -/
theorem frameStep_of_heldRun {p : Prog} {c cR : Ctl} {fs : List TermRun.Frame} (hH : HeldTail c fs)
    (hr : FrameRun p (c, fs) (cR, [])) : ∃ f, fs = [f] ∧ FrameStep p (c, [f]) (cR, []) := by
  obtain ⟨a, f, b, hc, rfl, -, hb, -⟩ := hH
  refine ⟨f, rfl, ?_⟩
  cases hr with
  | step h1 h2 =>
    cases h1 with
    | loc hl => exact absurd hc (hl.not_ret a)
    | call hc' => rw [hc] at hc'; cases hc'
    | ret hc' hσ he =>
      cases h2 with
      | refl => exact .ret hc' hσ he
      | step h3 _ =>
        cases h3 with
        | loc hl => exact absurd hb (hl.not_ret b)
        | call hc' => rw [hb] at hc'; cases hc'

/-- **A variable placed in one register operand reads its cell**: at a node
whose cells are `sl`, a variable placed as a register operand at offset `k`
(`hx`, `hrs`) is bound to one word `sl k` represents. -/
theorem lookup_of_nodeJE_slot {lbl : Lbl} {rs : Scc.IR.Reg → Option Int} {e : Expr} {s : Spike.Lib.Form.SEnv}
    {sl : Int → BitVec 64} {c : Ctl} (hJ : Spike.Lib.Form.NodeJE lbl rs e s sl c) {x : String} {t : Ty}
    {r : Scc.IR.Reg} {k : Int} (hx : Spike.Lib.Form.lookupS s x = some (t, [.one (.reg r)]))
    (hrs : rs r = some k) :
    ∃ ty w, TermRun.lookupE c.env x = some (ty, [w]) ∧ ValRep lbl w.val (sl k).toNat := by
  obtain ⟨-, -, hs⟩ := hJ
  obtain ⟨ty, ws, hl, -, hw⟩ := hs.lookup hx
  match ws, hw with
  | [w], ⟨⟨vv, hvv, hrep⟩, _⟩ =>
    simp only [Spike.Lib.Form.opdVal, hrs, Option.map_some, Option.some.injEq] at hvv
    exact ⟨ty, w, hl, hvv ▸ hrep⟩

/-- **`RetSlot` at a held pair** from the frame's node past the return:
the held pair's run to depth 0 lands at `cR`, which runs locally to the
node's control (`hloc`), whose symbolic environment places the frame's
result `f.x` as a register operand at a region cell (`hx`, `hrs`, `hk`). -/
theorem retSlot_of_heldRun {p : Prog} {lbl : Lbl} {R : Spike.Lib.Region} {σ : Spike.Lib.X64.AS}
    {c cR c' : Ctl} {fs : List TermRun.Frame} (hH : HeldTail c fs) (hr : FrameRun p (c, fs) (cR, []))
    (hloc : LocalRun p cR c') {rs : Scc.IR.Reg → Option Int} {e : Expr} {s : Spike.Lib.Form.SEnv}
    (hJ : Spike.Lib.Form.NodeJE lbl rs e s σ.slot c')
    (hx : ∀ f, fs = [f] → ∃ t r, Spike.Lib.Form.lookupS s f.x = some (t, [.one (.reg r)]) ∧
      ∃ k, rs r = some k ∧ R.Off k) :
    RetSlot p lbl R σ c := by
  obtain ⟨f, rfl, hst⟩ := frameStep_of_heldRun hH hr
  obtain ⟨a, f', b, hc, hf, -, hb, -⟩ := hH
  cases hf
  have hcR : cR.term = .ret b := by
    cases hst with
    | ret _ _ _ => exact hb
  have heq : c' = cR := by
    cases hloc with
    | refl => rfl
    | step h1 _ => exact absurd hcR (Spike.Lib.localStep_not_ret h1 b)
  subst heq
  obtain ⟨t, r, hxs, k, hrs, hk⟩ := hx f rfl
  obtain ⟨ty, w, hl, hv⟩ := lookup_of_nodeJE_slot hJ hxs hrs
  exact ⟨a, f, [], c', ty, w, k, hc, hst, hl, hk, hv⟩

/-- **`HeldS` on a block from its parts**: the abort phase's facts, `Ret0`,
no write, and no system call (so no output `write`). -/
theorem blkW_heldS {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {μ : Scc.Sem.Marks} {Ab : State → Prop} {lbl : Lbl} {n : Spike.Lib.X64.ND} {blk : List (Directive × Nat)}
    (hab : Spike.Lib.X64.BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hr : Spike.Lib.X64.BlkW (Ret0 lbl) (fun _ _ => False) exe endPc R F n blk)
    (hw : Spike.Lib.X64.BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk)
    (hs : Spike.Lib.X64.BlkW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk) :
    Spike.Lib.X64.BlkW (HeldS μ Ab lbl) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn hd hpc hA hF hJ k hk m hA' hD
  have hs' := (hs s σ c he hn hd hpc hA hF hJ k hk m hA' hD).1
  exact ⟨⟨(hab s σ c he hn hd hpc hA hF hJ k hk m hA' hD).1, (hr s σ c he hn hd hpc hA hF hJ k hk m hA' hD).1,
    (hw s σ c he hn hd hpc hA hF hJ k hk m hA' hD).1, fun h => absurd (hs'.symm.trans h) (by decide)⟩,
    fun _ h => h⟩

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.blkW_ret0_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.blkW_ret0_slot

/-- info: 'Spike.Lib.LowerX64.retSlot_of_heldRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.retSlot_of_heldRun

/-- info: 'Spike.Lib.LowerX64.blkW_heldS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.blkW_heldS
