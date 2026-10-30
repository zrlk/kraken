import Scc.Cert.Rt.X64Abort

/-!
# The segment theorems of `Scc.Cert.Rt.X64Abort`

The theorems of `Scc/Cert/Rt/X64Abort.lean` whose statements are stated over the
untrusted segment predicate (`Spike.Lib.Seg`, `MemSide`), moved out of the
trusted tree unchanged (same namespace, names and statements; FENCE1
follow-up 2): `seg_stub_of`, `seg_abort_of`, `seg_main_tail_of`. The definitions, code
data and decided checks they use stay in `Scc.Cert.Rt.X64Abort`.
-/

namespace Scc.Cert.Rt.X64.Abort

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Spike.Lib Spike.Lib.X64
  Spike.Lib.X64.Abort
  Scc.Cert.Rt.X64.Print

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {m0 : MachineData} {c0 : Ctl} {Q : Frag isa}

/-- **An abort stub does not return** in any valid layout of code cells
with `abortIn cells = true`, given its `write` call. -/
theorem seg_stub_of {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : abortIn cells = true) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (x : Disp.DX)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .e)) Q := by
  have hc := code_stubs (c0 := c0) hp hend hprog x
  cases x
  · exact seg_overflow hR hlo hhi hc hK hsys hab
  · exact seg_heap hR hlo hhi hc hK hsys hab
  · exact seg_stack hR hlo hhi hc hK hsys hab
  · exact seg_write hR hlo hhi hc hK hsys hab
  · exact seg_threads hR hlo hhi hc hK hsys hab

/-- **`scc_rt_abort` does not return** in any valid layout of code cells
with `abortIn cells = true`: from its entry with a code in `[1, 5]`, given
the stubs' `write` calls. -/
theorem seg_abort_of {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : abortIn cells = true) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hsys : ∀ x : Disp.DX,
      Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .sys))
        (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .n5)))
    (hab : ∀ (x : Disp.DX) s c,
      At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .ex) s c → ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (Disp.DN.nd (_root_.Executable.labels exe).label c0 .e)) Q := by
  have hd : dispIn cells = true := by
    simp only [abortIn, Bool.and_eq_true, and_assoc] at hprog; exact hprog.2.2.2.2.2
  exact Disp.seg_abort hR hlo hhi (code_disp hp hend hd) hK (code_stubs hp hend hprog) hsys hab

/-- **The tail of `scc_rt_main` does not return** in any valid layout of
code cells with `mainIn cells = true`: from `.x3` with `ret` in `%rax`,
through `exit_group(ret)`. Given that the exit is `main`'s (`hmain`). -/
theorem seg_main_tail_of {ret : BitVec 64} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hprog : mainIn cells = true) (hR : R.OK)
    (hlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi) (hK : ms.K = some Scc.Sem.X64.abi)
    (hmain : ∀ s c,
      At exe endPc R (DFrame R m0) (MainTail.MN.nd (_root_.Executable.labels exe).label c0 ret .ex) s c →
      ¬ ms.abortAt s → MainExit p ms s c ret.toNat) :
    Seg p lbl ms
      (At exe endPc R (DFrame R m0) (MainTail.MN.nd (_root_.Executable.labels exe).label c0 ret .x3)) Q := by
  exact MainTail.seg_main_tail hR hlo hhi (code_main hp hend hprog) hK hmain

end Seg

end Scc.Cert.Rt.X64.Abort
