/-
**The root's table has no immediate at the child's terms** (x86-64; the twin of
`Spike/Lib/A64HelloImmsKid.lean`, the worker segment's table premises): at `X64.HelloImms.iRdM Λ0`
(`immsH Λ0 (i0M Λ0)`: hello's certificate immediates, rodata's, `me` at both setup terms), neither the
child's control at `tail worker` (`X64.HelloPh.XH.kidC`) nor `print`'s call `X64HelloSplit.workerCallH` has
an immediate.

- `kid_iRdM`, `wcall_iRdM`: the two facts at `iRdM Λ0`.
- `kid_root`, `wcall_root`: the same at the root's layout `ofPlaceWX hp (iRdM Λ0)` (its `imms` is the table).

## Differences from the AArch64 version

- The namespace is `Spike.Lib.X64.HelloImms` (the x86-64 `immsH`/`i0Rd`/`i0M`/`iRdM` live in one module,
  `X64HelloImms`, rather than A64's `C0S`/`ImmsRd`/`ImmsMe`); the runtime layout is
  `X64.Rt.RuntimeLayout.ofPlaceWX` at `PlaceWX`.
- A64's `immsKid_root` (`XHFSeg.ImmsKid` at the root's layout, the pair `⟨kid_root hp, wcall_root hp⟩`) is
  not twinned here: the x86-64 `XHFSeg` does not exist yet. It is one line once it does.
-/
import Spike.Lib.X64HelloImms
import Spike.Lib.X64HelloXH
import Spike.Lib.X64HelloSplit

namespace Spike.Lib.X64.HelloImms

open CoreLang CoreTerm
open Spike.Lib.X64.HelloPh.XH (kidC)
open Spike.Lib.X64HelloSplit (workerCallH workerRestH)
open Spike.Lib.X64HelloRodataSrc (eB eW0 eO0 eW1 eO1 eS eN eRet)

/-- **No immediate at the child's control** at `iRdM`. -/
theorem kid_iRdM (Λ0 : Scc.Sem.Layout) (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (y : String) (k : Nat) :
    iRdM Λ0 (kidC T w0 w1 w2 w3 w4).term y k = none := by
  simp [iRdM, immsH, i0M, i0Rd, SccCode.helloImms, kidC, Scc.Sem.SrcSem.setupTerm,
    Spike.Lib.SrcCalls.setupCont, SccCode.helloImm_t0, SccCode.helloImm_t1, SccCode.helloImm_t2, eW0, eO0, eW1,
    eO1, eS, eN, eRet]

/-- **No immediate at `print`'s call** at `iRdM`. -/
theorem wcall_iRdM (Λ0 : Scc.Sem.Layout) (y : String) (k : Nat) : iRdM Λ0 workerCallH y k = none := by
  simp [iRdM, immsH, i0M, i0Rd, SccCode.helloImms, workerCallH, workerRestH, Scc.Sem.SrcSem.setupTerm,
    Spike.Lib.SrcCalls.setupCont, SccCode.helloImm_t0, SccCode.helloImm_t1, SccCode.helloImm_t2, eW0, eO0, eW1,
    eO1, eS, eN, eRet]

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o)

/-- **`hkid` at the root's layout.** -/
theorem kid_root : ∀ (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (y : String) (k : Nat),
    (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ.imms (kidC T w0 w1 w2 w3 w4).term y k = none :=
  kid_iRdM Λ0

/-- **`hwc` at the root's layout.** -/
theorem wcall_root : ∀ (y : String) (k : Nat),
    (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ.imms workerCallH y k = none :=
  wcall_iRdM Λ0

end Root

/-- The two facts hold, and the table still has rodata's `m` at `eW0` (so `iRdM` is not `iH`: the premises
are met at a table `iH` would reject). -/
example (Λ0 : Scc.Sem.Layout) :
    iRdM Λ0 (kidC .unit (TermRun.cst (.num 0)) (TermRun.cst (.num 0)) (TermRun.cst (.num 0))
      (TermRun.cst (.num 0)) (TermRun.cst (.num 0))).term "a" 0 = none ∧
    iRdM Λ0 workerCallH "sl" 0 = none ∧ iRdM Λ0 eW0 "m" 0 = some 2 :=
  ⟨kid_iRdM _ _ _ _ _ _ _ _ _, wcall_iRdM _ _ _, by
    simp [iRdM, immsH, i0M, i0Rd, eW0, Scc.Sem.SrcSem.setupTerm, Spike.Lib.SrcCalls.setupCont]⟩

end Spike.Lib.X64.HelloImms

/-- info: 'Spike.Lib.X64.HelloImms.kid_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.kid_iRdM

/-- info: 'Spike.Lib.X64.HelloImms.wcall_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.wcall_iRdM

/-- info: 'Spike.Lib.X64.HelloImms.kid_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.kid_root

/-- info: 'Spike.Lib.X64.HelloImms.wcall_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.wcall_root
