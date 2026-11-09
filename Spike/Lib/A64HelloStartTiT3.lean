/-
**hello.w's `scc_rt_stack_take` call inside `W0`** (AArch64,
the `hti` chain; the twin of wake's at helloProg): every node of the call from
`scc_rt_thread_init` (returning to its `.sp0`) inside the start's level
`HelloPh.StartWf.WSH` (`takeA_WSH`, `takeB_WSH`), and the facts `startTi_WSH`
reads.

- `takeW_WSH`: the take's node obligations inside `WSH`.
- `ti_labsH`: `scc_rt_thread_init`'s labels at the canonical base (wake's
  plus 36).

Wake's `bandI_mono` is program independent and reused as is.
-/
import Spike.Lib.A64HelloStartTiT1
import Spike.Lib.A64HelloStartTiT2
import Spike.Lib.A64WakeStartTiT3

namespace Spike.Lib.A64.HelloPh.StartTi

open Spike.Lib.A64.WakePh Spike.Lib.A64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.Flow.Ret0 (TakeG TakeW StackM stacksA)
open Spike.Lib (Arena FragS)

variable {P : MachineData → Prop}
variable {L : RuntimeLayout}

/-- `scc_rt_thread_init`'s labels at the canonical base. -/
theorem ti_labsH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label Spike.Lib.A64.Flow.Ret0.ThreadInit.fnL = Int64.ofNat 2165284 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.A64.Flow.Ret0.ThreadInit.entryL = Int64.ofNat 2165304 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

set_option maxHeartbeats 400000 in
/-- **`scc_rt_stack_take`'s node obligations inside `WSH`**, called from
`scc_rt_thread_init` returning to its `.sp0` (`hra`): `takeA_WSH` and
`takeB_WSH`. -/
theorem takeW_WSH {a : BitVec 64} {rS : Range} {lbl' : Lbl} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
    (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
    (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
    (hbd : BandI L R (-208))
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS))
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 → X0 s) :
    ∀ i, TakeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q i P := by
  intro i
  cases h : takeA i
  · exact takeB_WSH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd hΛ hs hro hC0 hR hal hRlo hhi hFr q hq hra hrS hsub hSM
      hoffL hoffX hXs i h
  · exact takeA_WSH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd hΛ hs hro hC0 hR hal hRlo hhi hFr q hq hra hrS hsub hSM
      hoffL i h

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.ti_labsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.ti_labsH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.takeW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.takeW_WSH

end Spike.Lib.A64.HelloPh.StartTi
