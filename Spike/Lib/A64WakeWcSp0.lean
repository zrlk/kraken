/-
**wake.w's `wc_main` at `.sp0`: the box's store** (AArch64, the pre-spawn
consumer), inside `W`, in any valid layout of `wakeProg`, from checks
decided once on the program (`decide +kernel`):

    .L21_wc_main.sp0:                   -- x0 = the box's cell (Alloc.EB)
      str x0, [sp, #8]; movz x9, #0; ldr x10, [sp, #8]          (wcS0)
      str x9, [x10]                     -- row: the box's store (Out.newStore)
      dmb ishst                         -- `.sp0 + 16`, the next segment's

The allocator's return at a box allocation keeps the source at wake.w's
`let o = new z` with the hold recording the counter's old value
(`Alloc.EB`, `wake_wc_pre_segW`'s `.sp0` exit `wX .sp0`); the box's store
is where the source takes its `new` (`Alloc.newStore_ndW`). The segment
ends there: for every fresh label `l` the pair lands at `bX l A` (`x`
bound to `l`'s owned pointer, the cell `A` at `[sp, #8]`), which one
`ms.xa` continues in (`hxa`, the instance's choice).

- `wcS0`, `boxSt`, `wcS0In`, `wake_wcS0In`: the block and the row at
  `.sp0`;
- `sN`, `bX`: the nodes (`.sp0`, the store) and the landing past the store;
- `BoxW`: the source's box facts at the allocator's ghost (one word, its
  representation `0`);
- `WcSp0W`: the nodes' states inside `W`;
- `wake_wc_sp0_segW`: the segment from `wX .sp0` to the landing.
-/
import Spike.Lib.A64WakeWcPre

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Alloc (Call)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

/-! ## The block and the row -/

/-- `.sp0`'s block: the cell to `[sp, #8]`, the box's word `0`, the cell back. -/
def wcS0 : List Directive := parseAArch64("str x0, [sp, #8]
movz x9, #0
ldr x10, [sp, #8]")

block_spec wcS0 (-80) 0 (⟨-80, []⟩ : SO) wcS0

/-- The box's store (a row). -/
def boxSt : List Directive := parseAArch64("str x9, [x10]")

theorem boxSt_eq : boxSt = [strDir .X9 .X10 0] := by decide

/-- **`.sp0`'s block and row in `prog`**: the block at `0`, the store at `3`. -/
def wcS0In (prog : List Directive) : Bool :=
  blockAt prog ".L21_wc_main.sp0" 0 wcS0 && blockAt prog ".L21_wc_main.sp0" 3 boxSt

theorem wake_wcS0In : wcS0In SccCode.wakeProg = true := by decide +kernel

/-! ## Nodes -/

/-- `.sp0`'s nodes. -/
inductive SN where
  | b | st

section Sp0

variable (ms : MemSide isaLSE2) (lab : Label → Int64) (J0 : AS → Ctl → Prop)

/-- **The nodes**: `.sp0` (the allocator's return, `wX .sp0`) and the box's
store (`x9` the word `0`, `x10` and `[sp, #8]` the cell, the hold kept). -/
def sN : SN → ND
  | .b => wX ms lab J0 .sp0
  | .st => ⟨lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 3), ⟨-80, []⟩, fun σ c => ∃ q : AGB ms lab, ∃ o : BitVec 64,
      wcJ J0 σ q.1.c0 ∧ c = holdCtr ms q.1.c0 o ∧ σ.regs.X9.toBitVec = 0#64 ∧
      σ.regs.X10.toBitVec = σ.slot (-72) ∧ (σ.slot (-72)).toNat = ms.heap + 16 * o.toNat + ms.off 1 q.1.τ ∧
      o.toNat + ms.units 1 q.1.τ ≤ ms.cells ∧ ms.lo o.toNat⟩

/-- **The landing past the box's store** for the fresh label `l` at the
cell `A`: the source past its `new` (`x` bound to `l`'s owned pointer, no
hold), the cell at `[sp, #8]`, the frame kept; the cell the allocator's,
`ms.heap + 16·o + ms.off 1 τ` for a counter value `o` within the cells
(the landing's `AllocLand` at a concrete memory side). -/
def bX (l : WeakMem.AllocLabel) (A : Nat) : ND :=
  ⟨lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 4), ⟨-80, []⟩, fun σ c => ∃ q : AGB ms lab,
    wcJ J0 σ q.1.c0 ∧ (σ.slot (-72)).toNat = A ∧
    c = ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ ∧
    ∃ o : Nat, A = ms.heap + 16 * o + ms.off 1 q.1.τ ∧ o + ms.units 1 q.1.τ ≤ ms.cells⟩

end Sp0

/-- **The source's box facts** at the allocator's ghost `q`: the value
`new` boxes is one word `w` of a one-word type, represented by `0` (wake.w's
`let z = zero[Int]`). -/
def BoxW (lbl : WeakMem.AllocLabel → Option Nat) (q : Call) : Prop :=
  ∃ w : TermRun.Word, q.ws = [w] ∧ TermRun.accs q.τ = some [.one] ∧ Scc.Sem.ValRep lbl w.val 0

/-- **`.sp0`'s states inside `W`**, none moved by `K`: the block's and the
store's. -/
structure WcSp0W (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J0 : AS → Ctl → Prop) : Prop where
  b : BlkW W K exe endPc R F (sN ms (_root_.Executable.labels exe).label J0 .b) wcS0
  st : NodeW W K exe endPc R F (sN ms (_root_.Executable.labels exe).label J0 .st)

/-- `.sp0` is inside the trivial predicate, with no outside moves. -/
theorem WcSp0W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop} :
    WcSp0W (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 :=
  ⟨BlkW.triv, fun _ _ _ => ⟨trivial, fun _ h => h⟩⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` at `.sp0` is one segment inside `W`** in any valid layout of
`wakeProg`: from the allocator's return at a box allocation (`wX .sp0`) to
the box's store, where the source takes its `new` and every fresh label's
landing `bX l A` is one `ms.xa` continues in (`hxa`); the segment has no
other exit (`Q` any). The value boxed is one word represented by `0`
(`hbox`); every cell the allocator may return is mapped for writing and
unmapped in private memory under `F` (`hcell`). Its states lie in `W`,
none moved by `K` (`hW`). -/
theorem wake_wc_sp0_segW {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop} (hW : WcSp0W W K exe endPc R F ms J0)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J0 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J0 σ q.1.c0) →
      ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c →
      ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc R F (wX ms (_root_.Executable.labels exe).label J0 .sp0)) Q := by
  have hin := wake_wcS0In
  simp only [wcS0In, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  refine (fn_segW (N := sN ms lab J0) (E := fun x : Empty => x.elim) (fun i => ?_) SN.b).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case b =>
    refine seg_ndW (by simp [wcS0]) wcS0_ok hF hR hal hlo hhi (code_of hp hend h0 (ofNat4_zero _)) hW.b
      fun σ c hJ => ⟨c, .refl c, .inl ⟨SN.st, ?_, ?_, ?_⟩⟩
    · simp only [sN, wX]; rw [wcS0_run]
      rw [show Int64.ofNat (4 * 3) = 4 + 4 + 4 from rfl]; simp only [Int64.add_assoc]
    · simp only [sN, wX]; rw [wcS0_run]; rfl
    · simp only [sN, wX] at hJ ⊢
      rw [wcS0_run]
      obtain ⟨q, ⟨σe, hJe, h16, h8, h80⟩, o, hc, hx0, hle, hlo', -, -⟩ := hJ
      have h1 := q.2.one
      rw [h1] at hx0 hle
      refine ⟨q, o, ⟨σe, hJe, ?_, ?_, ?_⟩, hc, rfl, ?_, ?_, hle, hlo'⟩
      · simp [Spike.Lib.upd, h16]
      · simp [Spike.Lib.upd, h8]
      · simp [Spike.Lib.upd, h80]
      · simp [Spike.Lib.upd]
      · simpa [Spike.Lib.upd] using hx0
  case st =>
    refine Alloc.newStore_ndW (t := .X9) (b := .X10) (i := 0) (bX ms lab J0)
      (code_of hp hend (boxSt_eq ▸ h3) rfl) hxa hW.st fun m σ c hA hD hJ => ?_
    obtain ⟨q, o, hwc, rfl, h9, h10, hA72, hle, hlo'⟩ := hJ
    have hj : ∃ σ, J0 σ q.1.c0 := let ⟨σe, hJe, _⟩ := hwc; ⟨σe, hJe⟩
    obtain ⟨w, hws, hacc, hrep⟩ := hbox q hj
    have ha : rAddr σ.regs .X10 0 = σ.slot (-72) := by
      rw [Ret0.rAddr_x10 h10]; simp
    have ha' : rAddr σ.regs .X10 0 = BitVec.ofNat 64 (ms.heap + 16 * o.toNat + ms.off 1 q.1.τ) := by
      rw [ha, ← hA72, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    obtain ⟨hmp, hun⟩ := hcell q hj o.toNat hlo' hle
    refine ⟨q.2.newOk, ha' ▸ hmp, ha' ▸ hun m hD, q.1.x, q.1.a, q.1.τ, q.1.e, w, TermRun.cst (.num o.toNat),
      o.toNat, q.2.term, hws ▸ q.2.ev, hacc, ?_, rfl, rfl, by rw [ha, hA72], hle, fun l _ => ⟨?_, rfl, q, hwc,
      by rw [ha], rfl, o.toNat, by rw [ha, hA72], hle⟩⟩
    · rw [Ret0.getRegOrZr_x9, h9]; exact hrep
    · show lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 4) = lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 3) + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl

end Seg

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wcS0In' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wcS0In

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_sp0_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_sp0_segW
