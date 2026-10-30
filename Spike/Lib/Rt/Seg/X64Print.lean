import Scc.Cert.Rt.X64Print

/-!
# The segment theorems of `Scc.Cert.Rt.X64Print`

The theorems of `Scc/Cert/Rt/X64Print.lean` whose statements are stated over the
untrusted segment predicate (`Spike.Lib.Seg`, `MemSide`), moved out of the
trusted tree unchanged (same namespace, names and statements; FENCE1
follow-up 2): `seg_print_of`. The definitions, code
data and decided checks they use stay in `Scc.Cert.Rt.X64Print`.
-/

namespace Scc.Cert.Rt.X64.Print

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Print

set_option linter.unusedSimpArgs false in
/-- **`scc_rt_print` is one segment** in any valid layout `exe` of code
cells `cells` with `printIn cells = true`, given its write system call. -/
theorem seg_print_of {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl} {rbp0 ra : BitVec 64}
    {cells : List (Directive × Nat)} [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hprog : printIn cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 rbp0 ra .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 rbp0 ra .n5))) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 rbp0 ra .e))
      (fun s c => ∃ x, At exe endPc R (DFrame R m0) (E (_root_.Executable.labels exe).label c0 rbp0 ra x) s c) := by
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, hgap⟩ := hprog
  refine seg_print hR hlo hhi ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [label_labelGapB hp hgap]; rfl) hsys
  · exact code_field hp hend h0 (off0 _)
  · exact code_field hp hend h1 (off0 _)
  · exact code_field hp hend h2 (off0 _)
  · exact code_field hp hend h3 rfl
  · exact code_field hp hend h4 (off0 _)
  · exact code_field hp hend h5 rfl
  · exact code_field hp hend h6 rfl
  · exact code_field hp hend h7 (off0 _)
  · exact code_field hp hend h8 rfl
  · exact code_field hp hend h9 (off0 _)
  · exact code_field hp hend h10 rfl
  · exact code_field hp hend h11 (off0 _)
  · exact code_field hp hend h12 (off0 _)
  · exact code_field hp hend h13 (off0 _)
  · exact code_field hp hend hs rfl

end Scc.Cert.Rt.X64.Print
