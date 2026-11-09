/-
**The allocator's exits with the heap abort's return address** (AArch64, the read-only
data abort): `Alloc.E`'s exits with the heap abort's `x30` the return address past `.4_full`'s
`bl scc_rt_abort` (as `Alloc.EB .abort`), at a buffer allocation.

`Alloc.seg_allocW_at` reaches `Alloc.E .abort`, which drops `x30`; `seg_allocW_genR` hands it over at the abort's
hit (`hab`), so the strengthened exits cost no allocator proof: the `ret` node's step is `seg_allocW_at`'s.

- `Alloc.EX30`: `E`'s return, `EB`'s abort (`x30` kept).
- `Alloc.seg_allocW_atA`: `seg_allocW_at` to `EX30` (`seg_allocW_genR`).
- `Flow.seg_alloc_ofW_atA`: `seg_alloc_ofW_at` to `EX30` (its code from the checks, `allocIn`).
-/
import Spike.Lib.A64Hello1Rodata
import Spike.Lib.A64AllocBox

namespace Spike.Lib.A64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

section Spec

variable (lab : Label → Int64) (ms : MemSide isaLSE2) (q : Call)

/-- **The exits with the heap abort's return address**: `E`'s return, and the heap abort as `E`'s with `x30` past
`.4_full`'s `bl scc_rt_abort` (`EB .abort`'s facts). -/
def EX30 (lbl : WeakMem.AllocLabel → Option Nat) : AX → ND
  | .ret => E lab ms q lbl .ret
  | .abort => ⟨lab "scc_rt_abort", oI, fun σ c => σ.regs.X0 = 2 ∧
      σ.regs.X30.toBitVec = (lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec ∧ Jfull ms q c⟩

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {q : Call}

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0`** to its return or its heap abort with
the abort's return address (`EX30`): `seg_allocW_genR` with `seg_allocW_at`'s `ret` step. -/
theorem seg_allocW_atA {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OK ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_alloc" + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (EX30 (_root_.Executable.labels exe).label ms q lbl x) s c) := by
  refine seg_allocW_genR hF hR hal hlo hhi hq.toS hcode hentry hmem hW (lbl := lbl)
    (Ex := EX30 _ ms q lbl) (fun _ _ ⟨h1, h2, h0, hf⟩ h30 => ⟨h1, h2, h0, h30, hf⟩) ?_ i0
  refine alloc_ndW (Ea ms q) (a := iRet) (lo := -160) (hi := 0) rfl (by rintro w op ⟨⟩) hF
    hR hal hlo hhi (fun s he hn => hcode.ret s he hn) hxa hW.ret fun σ c hJ => ?_
  obtain ⟨o, rfl, hle, hn28, h0, h29, h30, hlo'⟩ := hJ
  have hk := Call.k_toNat hq.n_lt
  have hcl := hq.cells
  have hA : σ.regs.X0.toBitVec.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ := by
    rw [h0, base8_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk, hq.off]
  obtain ⟨us, hus⟩ := hq.accs
  refine ⟨σ.regs.X0.toBitVec, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, TermRun.cst (.num o.toNat), o.toNat, us, hq.term,
    hq.ev, hq.num, rfl, rfl, hA, hle, hus, fun l ini _ =>
    ⟨?_, rfl, ini, o.toNat, rfl, rfl, hA, hle, hlo', h29, h30, us, hus, rfl⟩⟩
  simp [Ea, iRet, AI.tgt, Reg64s.getXReg, h30]

end Proof

end Spike.Lib.A64.Alloc

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Spike.Lib.A64.Alloc

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {q : Call}

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0`** to `EX30` (the heap abort with its
return address) in any valid layout `exe` of a program `prog` with `allocIn prog = true`: `seg_alloc_ofW_at`'s
twin by `seg_allocW_atA`. -/
theorem seg_alloc_ofW_atA {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (EX30 (_root_.Executable.labels exe).label ms q lbl x) s c) := by
  have hcode := alloc_code (ms := ms) (q := q) hp hend hprog
  simp only [allocIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap⟩ := hprog
  exact seg_allocW_atA hF hR hal hlo hhi hq hcode (by rw [label_labelGap hp hgap]; simp only [add4, add0]) hmem hxa
    hW i0

end Spike.Lib.A64.Flow

/-- info: 'Spike.Lib.A64.Alloc.seg_allocW_atA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Alloc.seg_allocW_atA

/-- info: 'Spike.Lib.A64.Flow.seg_alloc_ofW_atA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.seg_alloc_ofW_atA
