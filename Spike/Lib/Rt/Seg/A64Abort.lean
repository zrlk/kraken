import Scc.Cert.Rt.A64Abort

/-!
# The segment theorems of `Scc.Cert.Rt.A64Abort`

The theorems of `Scc/Cert/Rt/A64Abort.lean` whose statements are stated over the
untrusted segment predicate (`Spike.Lib.Seg`, `MemSide`), moved out of the
trusted tree unchanged (same namespace, names and statements; FENCE1
follow-up 2): `seg_stub_of`, `seg_abort_of`, `seg_main_tail_of`, `seg_main_tail0_of`. The definitions, code
data and decided checks they use stay in `Scc.Cert.Rt.A64Abort`.
-/

namespace Scc.Cert.Rt.A64.Abort

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow
  Spike.Lib.A64.Abort Scc.Cert.Rt.A64.Print

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Region} {m0 : MachineData} {c0 : Ctl} {Q : Frag isaLSE2}

/-- **An abort stub does not return** in any valid layout of a program with
`abortIn prog = true`, given its `write` call. -/
theorem seg_stub_of {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : abortIn prog = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) (x : Disp.DX)
    (hsvc : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .svc))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .e)) Q := by
  have hc := code_stubs (c0 := c0) hp hend hprog x
  cases x
  · exact seg_overflow hR hal hlo hhi hc hK hsvc hab
  · exact seg_heap hR hal hlo hhi hc hK hsvc hab
  · exact seg_stack hR hal hlo hhi hc hK hsvc hab
  · exact seg_write hR hal hlo hhi hc hK hsvc hab
  · exact seg_threads hR hal hlo hhi hc hK hsvc hab

/-- **`scc_rt_abort` does not return** in any valid layout of a program with
`abortIn prog = true`: from its entry with a code in `[1, 5]`, given the
stubs' `write` calls. -/
theorem seg_abort_of {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : abortIn prog = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hsvc : ∀ x : Disp.DX,
      Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .svc))
        (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .n5)))
    (hab : ∀ (x : Disp.DX) s c,
      At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .ex) s c → ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (Disp.DN.nd (_root_.Executable.labels exe).label c0 .e)) Q := by
  have hd : dispIn prog = true := by
    simp only [abortIn, Bool.and_eq_true, and_assoc] at hprog; exact hprog.2.2.2.2.2
  exact Disp.seg_abort hR hal hlo hhi (code_disp hp hend hd) hK (code_stubs hp hend hprog) hsvc hab

/-- **The tail of `scc_rt_main` does not return** in any valid layout of a
program with `mainIn prog = true` (after a setup block): from the return of
`wc_main` with `ret` in `x0`, through `exit_group(ret)`. Given that the exit
is `main`'s (`hmain`). -/
theorem seg_main_tail_of {ret : BitVec 64} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hm : mainIn prog = true) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hmain : ∀ s c,
      At exe endPc R (DFrame R m0) (MainTail.MN.nd (_root_.Executable.labels exe).label c0 ret .ex) s c →
      ¬ ms.abortAt s → MainExit p ms s c ret.toNat) :
    Seg p lbl ms
      (At exe endPc R (DFrame R m0) (MainTail.MN.nd (_root_.Executable.labels exe).label c0 ret .sp1)) Q :=
  MainTail.seg_main_tail hR hal hlo hhi (code_main hp hend hm) hK hmain

/-- **The tail of `scc_rt_main` does not return** in any valid layout of a
program with `mainIn0 prog = true` (without a setup block): from the return
of `wc_main` with `ret` in `x0`, through `exit_group(ret)`. Given that the
exit is `main`'s (`hmain`). -/
theorem seg_main_tail0_of {ret : BitVec 64} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hm : mainIn0 prog = true) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hmain : ∀ s c,
      At exe endPc R (DFrame R m0) (MainTail0.MN.nd (_root_.Executable.labels exe).label c0 ret .ex) s c →
      ¬ ms.abortAt s → MainExit p ms s c ret.toNat) :
    Seg p lbl ms
      (At exe endPc R (DFrame R m0) (MainTail0.MN.nd (_root_.Executable.labels exe).label c0 ret .sp0)) Q :=
  MainTail0.seg_main_tail hR hal hlo hhi (code_main0 hp hend hm) hK hmain

end Seg

end Scc.Cert.Rt.A64.Abort
