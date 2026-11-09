/-
**The allocator with no return exit** (AArch64, option (a) piece 1):
`scc_rt_alloc` from any of its nodes as one segment whose only exit is the heap abort (`EX30 .abort`, with the
abort's return address).

The allocator's `ret` row is the allocation itself (`alloc_ndW`): the source's `new` takes a fresh label (`lbl l =
none`) and the state after the `ret` is in `ms.xa`. That row lands nowhere in `Next` (`Out.alloc`), so no state of
the segment ever reaches `E .ret`. `seg_allocW_atA` lists `E .ret` as an exit all the same, and a caller that
composes past it covers the return's continuation at the caller's level. At a level-ending allocation (hello's
`wc_rodata` call: level 0 ends at rodata's landing) that continuation is phantom, and anything it asks for at the
old level would be phantom too. Here the return exit is `⊥` (`ENR .ret`), so no freshness premise is needed: the
allocation step's own row excludes it.

- `ENR`: `EX30`'s exits with the return node `⊥`.
- `Alloc.seg_allocW_atNR`: `seg_allocW_atA`'s twin to the heap abort alone (`seg_allocW_genR` at `ENR`, with
  `seg_allocW_atA`'s `ret` step).
- `Alloc.seg_allocW_atA_of_NR`: `seg_allocW_atA`'s conclusion from `seg_allocW_atNR`'s (it is a strengthening).
- `Flow.seg_alloc_ofW_atNR`: the same with the code from the checks (`allocIn`), as `seg_alloc_ofW_atA`.
-/
import Spike.Lib.A64HelloAllocEA

namespace Spike.Lib.A64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

section Spec

variable (lab : Label → Int64) (ms : MemSide isaLSE2) (q : Call)

/-- **The exits with no return**: no state at the return (the `ret` row is the allocation, landing in `xa`), and
the heap abort as `EX30`'s (`x30` past `.4_full`'s `bl scc_rt_abort`). -/
def ENR (lbl : WeakMem.AllocLabel → Option Nat) : AX → ND
  | .ret => ⟨Int64.ofBitVec q.ra, oE, fun _ _ => False⟩
  | .abort => EX30 lab ms q lbl .abort

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {q : Call}

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0` to its heap abort alone** (`EX30 .abort`,
the abort's return address kept): `seg_allocW_genR` at `ENR`, the `ret` row `alloc_ndW` (as `seg_allocW_atA`'s),
which lands only in `ms.xa` (`hxa`), so the return exit `ENR .ret` is never reached. -/
theorem seg_allocW_atNR {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
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
      (At exe endPc R F (EX30 (_root_.Executable.labels exe).label ms q lbl .abort)) := by
  refine (seg_allocW_genR hF hR hal hlo hhi hq.toS hcode hentry hmem hW (lbl := lbl)
    (Ex := ENR _ ms q lbl) (fun _ _ ⟨h1, h2, h0, hf⟩ h30 => ⟨h1, h2, h0, h30, hf⟩) ?_ i0).mono_post ?_
  rotate_left
  · rintro s c ⟨x, h⟩
    cases x
    · obtain ⟨-, -, -, -, -, -, -, ⟨⟩⟩ := h
    · exact h
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

/-- **`seg_allocW_atNR` strengthens `seg_allocW_atA`**: from the same premises, `seg_allocW_atA`'s conclusion
(the exits `EX30 x`) follows from `seg_allocW_atNR`'s by widening the abort exit (non-vacuity: atNR is no weaker a
statement about the same, used, premises). -/
theorem seg_allocW_atA_of_NR {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop}
    {i0 : AN}
    (h : SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (At exe endPc R F (EX30 (_root_.Executable.labels exe).label ms q lbl .abort))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (EX30 (_root_.Executable.labels exe).label ms q lbl x) s c) :=
  h.mono_post fun _ _ hA => ⟨.abort, hA⟩

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

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0` to its heap abort alone** in any valid
layout `exe` of a program `prog` with `allocIn prog = true`: `seg_alloc_ofW_atA`'s twin by `seg_allocW_atNR`. -/
theorem seg_alloc_ofW_atNR {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive}
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
      (At exe endPc R F (EX30 (_root_.Executable.labels exe).label ms q lbl .abort)) := by
  have hcode := alloc_code (ms := ms) (q := q) hp hend hprog
  simp only [allocIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap⟩ := hprog
  exact seg_allocW_atNR hF hR hal hlo hhi hq hcode (by rw [label_labelGap hp hgap]; simp only [add4, add0]) hmem
    hxa hW i0

end Spike.Lib.A64.Flow

/-- info: 'Spike.Lib.A64.Alloc.seg_allocW_atNR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Alloc.seg_allocW_atNR

/-- info: 'Spike.Lib.A64.Alloc.seg_allocW_atA_of_NR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Alloc.seg_allocW_atA_of_NR

/-- info: 'Spike.Lib.A64.Flow.seg_alloc_ofW_atNR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.seg_alloc_ofW_atNR
