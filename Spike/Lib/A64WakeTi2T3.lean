/-
**wake.w's second `scc_rt_stack_take` call inside `W0`** (AArch64; the
`hatA` ti discharger): every node of the call from the second
`scc_rt_thread_init` (returning to its `.sp0`, on a pool stack) inside the
level `StartWf.WS` (`take2A_WS`, `take2B_WS`), as `StartTi.takeW_WS`.

- `take2W_WS`: the take's node obligations inside `WS`.
-/
import Spike.Lib.A64WakeTi2T1
import Spike.Lib.A64WakeTi2T2

namespace Spike.Lib.A64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.Flow.Ret0 (TakeG TakeW StackM stacksA)
open Spike.Lib (Arena FragS)
open Spike.Lib.A64.WakePh.Ti2 (BandP)

variable {P : MachineData → Prop}
variable {L : RuntimeLayout}

set_option maxHeartbeats 400000 in
/-- **`scc_rt_stack_take`'s node obligations inside `WS`**, called from
`scc_rt_thread_init` returning to its `.sp0` (`hra`): `take2A_WS` and
`take2B_WS`. -/
theorem take2W_WS {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl} {Pl : MachineData → Prop}
    (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s : State, Pl s.st.1 → Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
    (hPl : ∀ m m', F m → Spike.Lib.A64.Flow.DFrame R m m' → Pl m')
    (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
    (hbd : BandP L R (-208))
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
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
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 →
      (∀ k, R.Off k → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome) → X0 s) :
    ∀ i, TakeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q i P := by
  intro i
  cases h : takeA i
  · exact take2B_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd hΛ hs hro hR hal hRlo hhi hFr q hq hra hrS hsub hSM
      hoffL hoffX hXs i h
  · exact take2A_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd hΛ hs hro hR hal hRlo hhi hFr q hq hra hrS hsub hSM
      hoffL i h

/-- info: 'Spike.Lib.A64.WakePh.StartTi.take2W_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms take2W_WS

end Spike.Lib.A64.WakePh.StartTi
