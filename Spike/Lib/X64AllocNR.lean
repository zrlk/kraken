/-
**The allocator with no return exit** (x86-64, hello): `scc_rt_alloc` from any of its nodes as one segment whose
only exit is the heap abort (`EX30 .abort`, with the abort's pushed return address). The x86-64 twin of
`Spike/Lib/A64AllocNR.lean` (same names).

The allocator's `ret` row is the allocation itself (`alloc_ndW`): the source's `new` takes a fresh label (`lbl l =
none`) and the state after the `ret` is in `ms.xa`. That row lands nowhere in `Next` (`Out.alloc`), so no state of
the segment ever reaches `E .ret`. At a level-ending allocation (hello's `wc_rodata` call: level 0 ends at rodata's
landing) the return's continuation is phantom, so here the return exit is `⊥` (`ENR .ret`) and no freshness premise
is needed: the allocation step's own row excludes it.

- `ENR`: `EX30`'s exits with the return node `⊥`.
- `Alloc.seg_allocW_atNR`: `seg_allocW_genR` at `ENR`, with `seg_allocW_at`'s `ret` step (`alloc_ndW`).
- `Flow.seg_alloc_ofW_atNR`: the same under AArch64's `Flow` name. On x86-64 the allocator's code already comes from
  the checks (`allocIn cells`, `Lays`), so it is `seg_allocW_atNR` itself.

Deviations from AArch64: no `hal` (stack alignment) or `hentry` premise (x86-64's `seg_allocW_genR` derives the entry
from `allocIn`), `8 ≤ R.hi` (the return address slot) for AArch64's `0 ≤ R.hi`; `seg_allocW_atA_of_NR` is not twinned
(it is dead in hello).
-/
import Spike.Lib.X64HelloAllocEA

namespace Spike.Lib.X64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf code_field label_labelGapB)

section Spec

variable (lab : Label → Int64) (ms : MemSide isa) (q : Call)

/-- **The exits with no return**: no state at the return (the `ret` row is the allocation, landing in `xa`), and
the heap abort as `EX30`'s (the return address past `.full`'s `call scc_rt_abort` at `-160`). -/
def ENR (lbl : WeakMem.AllocLabel → Option Nat) : AX → ND
  | .ret => ⟨Int64.ofBitVec q.ra, oR, fun _ _ => False⟩
  | .abort => EX30 lab ms q lbl .abort

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {q : Call} {cells : List (Directive × Nat)}

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0` to its heap abort alone** (`EX30 .abort`,
the abort's pushed return address kept): `seg_allocW_genR` at `ENR`, the `ret` row `alloc_ndW` (as
`seg_allocW_at`'s), which lands only in `ms.xa` (`hxa`), so the return exit `ENR .ret` is never reached. -/
theorem seg_allocW_atNR {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (At exe endPc R F (EX30 (_root_.Executable.labels exe).label ms q lbl .abort)) := by
  have hin' := hin
  simp only [allocIn, fiAt, iCtr, iHeap, iRmw, iHdr, iRet, Bool.and_eq_true] at hin'
  have hk := Call.k_toNat hq.n_lt
  have hcl := hq.cells
  refine (seg_allocW_genR hp hend hin hF hR hlo hhi hq.toS hmem hW (lbl := lbl) (Ex := ENR _ ms q lbl)
    (fun _ _ ⟨hpc, ho, h2, hf⟩ hs => ⟨hpc, ho, h2, hf, hs⟩) ?_ i0).mono_post ?_
  rotate_left
  · rintro s c ⟨x, h⟩
    cases x
    · obtain ⟨-, -, -, -, -, -, -, ⟨⟩⟩ := h
    · exact h
  refine alloc_ndW (Ea ms q) (a := .ret) (z := 1) (lo := -160) (hi := 8) rfl (by rintro w op ⟨⟩) hF
    hR hlo hhi (code_field hp hend (by simp only [hin']) (l := retL) (off := 0)
      (by rw [label_labelGapB (a := okL) (b := retL) (off := 226) hp (by simp only [hin'])]
          exact Spike.Lib.X64.Flow.ofNat_zero' _)) hxa hW.ret
    fun σ c hJ => ?_
  obtain ⟨o, rfl, hle, hn28, h0, h29, h30, hlo⟩ := hJ
  have hA : σ.regs.rax.toBitVec.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ := by
    rw [h0, base8_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk, hq.off]
  obtain ⟨us, hus⟩ := hq.accs
  refine ⟨σ.regs.rax.toBitVec, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, TermRun.cst (.num o.toNat), o.toNat, us,
    hq.term, hq.ev, hq.num, rfl, rfl, hA, hle, hus, fun l ini _ =>
      ⟨?_, rfl, ini, o.toNat, rfl, ?_, hA, hle, hlo, ?_, us, hus, rfl⟩⟩
  · simp [N, Ea, AI.tgt, h30]
  · simp [iRet, AI.step, Reg64s.set64, Reg64s.get64]
  · simp [iRet, AI.step, Reg64s.set64, Reg64s.get64, h29]

end Proof

end Spike.Lib.X64.Alloc

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.Alloc

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {q : Call} {cells : List (Directive × Nat)}

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0` to its heap abort alone** in any valid
layout `exe` of cells holding its code (`allocIn cells = true`): `seg_allocW_atNR` (AArch64's `Flow` name). -/
theorem seg_alloc_ofW_atNR {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (At exe endPc R F (EX30 (_root_.Executable.labels exe).label ms q lbl .abort)) :=
  seg_allocW_atNR hp hend hin hF hR hlo hhi hq hmem hxa hW i0

end Spike.Lib.X64.Flow

/-- info: 'Spike.Lib.X64.Alloc.seg_allocW_atNR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Alloc.seg_allocW_atNR

/-- info: 'Spike.Lib.X64.Flow.seg_alloc_ofW_atNR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.seg_alloc_ofW_atNR
