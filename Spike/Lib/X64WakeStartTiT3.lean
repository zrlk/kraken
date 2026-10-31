/-
**wake.w's `scc_rt_stack_take` call inside `W0`** (x86-64; twin of
`Spike/Lib/A64WakeStartTiT3.lean`): every node of the call from
`scc_rt_thread_init` (returning to its `.x7`) inside the start's level
`StartWf.WS` (`takeA_WS`, `takeB_WS`), and the facts `startTi_WS` reads.

- `takeW_WS`: the take's node obligations inside `WS`.
- `bandI_mono`: a frame off the pool, its low end raised.
- `ti_labs`: `scc_rt_thread_init`'s labels at the canonical base.

**Unlike AArch64**: no `P` (`hXs` takes the frame condition alone), no
`hal`; `hRlo : R.lo ≤ -200`, `hhi : 8 ≤ R.hi`, `hbd : BandI L R (-200)`
(A64's `-208`, `0`); the return is to `Code.Ti.x7L` (A64's `.sp0`);
`ti_labs`' literals are x86-64's (`4199545`, `4199557`).
-/
import Spike.Lib.X64WakeStartTiT1
import Spike.Lib.X64WakeStartTiT2

namespace Spike.Lib.X64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.Flow.Ret0 (TakeG TakeW StackM stacksA)
open Spike.Lib (Arena FragS)

variable {L : RuntimeLayout}

/-- **A frame off the pool, its low end raised.** -/
theorem bandI_mono {R : Spike.Lib.Region} {lo lo' : Int} (hb : BandI L R lo) (h : lo ≤ lo') : BandI L R lo' :=
  fun k h1 h2 => hb k (by omega) h2

/-- `scc_rt_thread_init`'s labels at the canonical base. -/
theorem ti_labs (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.ThreadInit.fnL = Int64.ofNat 4199545 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.ThreadInit.entryL = Int64.ofNat 4199557 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

set_option maxHeartbeats 400000 in
/-- **`scc_rt_stack_take`'s node obligations inside `WS`**, called from
`scc_rt_thread_init` returning to its `.x7` (`hra`): `takeA_WS` and
`takeB_WS`.

VACUOUS at root (`hXs` unsatisfiable): superseded by `takeW_WSP`
(`Spike/Lib/X64WakeStartTiP.lean`). -/
theorem takeW_WS {a : BitVec 64} {rS : Range} {lbl' : Lbl} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
    (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
    (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
    (hbd : BandI L R (-200))
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.Code.Ti.x7L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → X0 s) :
    ∀ i, TakeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q i := by
  intro i
  cases h : takeA i
  · exact takeB_WS hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd hΛ hs hro hC0 hR hRlo hhi hFr q hq hra hrS hsub hSM
      hoffL hoffX hXs i h
  · exact takeA_WS hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd hΛ hs hro hC0 hR hRlo hhi hFr q hq hra hrS hsub hSM
      hoffL i h

end Spike.Lib.X64.WakePh.StartTi

/-- info: 'Spike.Lib.X64.WakePh.StartTi.bandI_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.bandI_mono

/-- info: 'Spike.Lib.X64.WakePh.StartTi.ti_labs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.ti_labs

/-- info: 'Spike.Lib.X64.WakePh.StartTi.takeW_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.takeW_WS
