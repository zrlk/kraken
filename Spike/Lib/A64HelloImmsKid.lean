/-
**The root's table has no immediate at the child's terms** (AArch64; row 5i-hab1, the worker segment's table
premises): at `ImmsMe.iRdM Λ0` (`immsH Λ0 (i0M Λ0)`: hello's certificate immediates, rodata's, `me` at both setup
terms), neither the child's control at `tail worker` (`XH.kidC`) nor `print`'s call `workerCallH` has an
immediate, as at `ImmsH.iH` (`XH.iH_kid`, `XHNode.iH_wcall`). These are `HelloWorkerRRXF`'s `hkid`, `hwc`.

- `kid_iRdM`, `wcall_iRdM`: the two facts at `iRdM Λ0`.
- `kid_root`, `wcall_root`: the same at the root's layout `ofPlaceW hp (iRdM Λ0)` (its `imms` is the table).
- `immsKid_root`: `XHFSeg.ImmsKid` at that layout (`hello_root_inv`'s `hI` at `i0 := i0M Λ0`).
-/
import Spike.Lib.A64HelloImmsMe
import Spike.Lib.A64HelloXHNode
import Spike.Lib.A64HelloXHFSeg

namespace Spike.Lib.A64.HelloPh.ImmsMe

open CoreLang CoreTerm
open Spike.Lib.A64.HelloPh.XH (kidC)
open Spike.Lib.HelloSplit (workerCallH workerRestH)
open Spike.Lib.HelloRodataSrc (eB eW0 eO0 eW1 eO1 eS eN eRet)

/-- **No immediate at the child's control** at `iRdM`. -/
theorem kid_iRdM (Λ0 : Scc.Sem.Layout) (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (y : String) (k : Nat) :
    iRdM Λ0 (kidC T w0 w1 w2 w3 w4).term y k = none := by
  simp [iRdM, Spike.Lib.A64.HelloPh.C0S.immsH, i0M, Spike.Lib.A64.HelloPh.ImmsRd.i0Rd, SccCode.helloImms, kidC,
    Scc.Sem.SrcSem.setupTerm, Spike.Lib.SrcCalls.setupCont, SccCode.helloImm_t0, SccCode.helloImm_t1,
    SccCode.helloImm_t2, eW0, eO0, eW1, eO1, eS, eN, eRet]

/-- **No immediate at `print`'s call** at `iRdM`. -/
theorem wcall_iRdM (Λ0 : Scc.Sem.Layout) (y : String) (k : Nat) : iRdM Λ0 workerCallH y k = none := by
  simp [iRdM, Spike.Lib.A64.HelloPh.C0S.immsH, i0M, Spike.Lib.A64.HelloPh.ImmsRd.i0Rd, SccCode.helloImms,
    workerCallH, workerRestH, Scc.Sem.SrcSem.setupTerm, Spike.Lib.SrcCalls.setupCont, SccCode.helloImm_t0,
    SccCode.helloImm_t1, SccCode.helloImm_t2, eW0, eO0, eW1, eO1, eS, eN, eRet]

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o)

/-- **`hkid` at the root's layout.** -/
theorem kid_root : ∀ (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (y : String) (k : Nat),
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ.imms (kidC T w0 w1 w2 w3 w4).term y k = none :=
  kid_iRdM Λ0

/-- **`hwc` at the root's layout.** -/
theorem wcall_root : ∀ (y : String) (k : Nat),
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ.imms workerCallH y k = none :=
  wcall_iRdM Λ0

/-- **`XHFSeg.ImmsKid` at the root's layout** (`HelloWorkerDHF`'s `hI`; the root's `hI` at `i0 := i0M Λ0`). -/
theorem immsKid_root :
    Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ :=
  ⟨kid_root hp, wcall_root hp⟩

end Root

/-- At a concrete layout (`Layout`'s default fields) the two facts hold, and the table still has rodata's `m` at
`eB` (so `iRdM` is not `iH`: the premises are met at a table `hi` would reject). -/
example (Λ0 : Scc.Sem.Layout) :
    iRdM Λ0 (kidC .unit (TermRun.cst (.num 0)) (TermRun.cst (.num 0)) (TermRun.cst (.num 0))
      (TermRun.cst (.num 0)) (TermRun.cst (.num 0))).term "a" 0 = none ∧
    iRdM Λ0 workerCallH "sl" 0 = none ∧ iRdM Λ0 eW0 "m" 0 = some 2 :=
  ⟨kid_iRdM _ _ _ _ _ _ _ _ _, wcall_iRdM _ _ _, by
    simp [iRdM, Spike.Lib.A64.HelloPh.C0S.immsH, i0M, Spike.Lib.A64.HelloPh.ImmsRd.i0Rd, eW0,
      Scc.Sem.SrcSem.setupTerm, Spike.Lib.SrcCalls.setupCont]⟩

end Spike.Lib.A64.HelloPh.ImmsMe

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.kid_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.kid_iRdM

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.wcall_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.wcall_iRdM

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.kid_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.kid_root

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.wcall_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.wcall_root

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.immsKid_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.immsKid_root
