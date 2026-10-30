/-
**The threads abort path's components give `W1X`** (AArch64, wake.w):
`WakeRefStub.RefMap`. At a state of the path, `SFactsAC` at `own2b` (`ACW`)
with `ownG`'s agreement (`AgW`) gives `SFactsSt2` at `ownG`
(`SFactsSt2.congr`); with the write abort's phase kept (`AbSt`) and no write
to the arena or the counter (`NoWrW`) it gives `W1W`; the state in
`scc_rt_abort`'s code (`AbW`) is off the clone's and the take's pcs, so
`X1W` holds and no `K1W` move leaves it.

- `sfactsSt2_of_ac`: `SFactsSt2` at the frames `[]` from `SFactsAC`.
- `refMap`: `RefMap`, given `DtW ⊆ Dt`.
-/
import Spike.Lib.A64WakeRefStub
import Spike.Lib.WakeAWSite

namespace Spike.Lib.WakeRefStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (SFactsAC)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.ThreadsAb (raT)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Cert.Link.A64 (codeOf)

/-- **`SFactsSt2` from `SFactsAC`** at the frames `[]`, its map `own` at no
frame. -/
theorem sfactsSt2_of_ac {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : State → List (Loc × Val)} {rS : Range} {Tk : State → Prop} {ar : Arena}
    {J : Spike.Lib.A64ConsumerS.InvS} {lbl : Spike.Lib.A64Consumer.Lbl} {lsize : Lsize} {s : State} {c : Ctl}
    {Dt Ab Cl Ac : State → Prop}
    (h : SFactsAC Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c [] Dt Ab Cl Ac) :
    Spike.Lib.A64ConsumerA.SFactsSt2 Λ μ own s Dt :=
  ⟨h.noSite, h.mapped, h.svc, fun hs t he => h.ownInstr _ _ (.refl _) hs t he,
    fun hs call hd s' hs' => h.ownSys _ _ (.refl _) hs call hd s' hs', h.ownTake,
    fun a ha hp => let ⟨_, h2, h3, _⟩ := h.site a ha hp; ⟨h2, h3⟩, h.wrTail⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`RefMap`**: `W1W` from the components (`Wf.intro`, the marks the
record's by `marks_target`, the write tail widened by `hDt`), `X1W` and no
`K1W` move off the clone's and the take's pcs (`scc_rt_abort`'s code lies
between them). -/
theorem refMap (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hDt : ∀ s, Spike.Lib.A64.WakeWf.DtW s → Dt s) (l : WeakMem.AllocLabel) (b n : Nat) :
    RefMap hp i E Dt Ctx ls0 l b n := by
  intro R' s c hac hag habs hnw habw
  have hpW := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hpW]; exact hwp
  have hlab := Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo
  obtain ⟨e1, e2, -⟩ := Spike.Lib.A64.WakePh.ab_labs hlab
  have hst : (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165940 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have h6 : (Ly).lab (pfxM ++ ".sp6") = Int64.ofNat 2169292 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have haW := Spike.Lib.WakeOSide.aW_site hp i hpa hwp hpL (Spike.Lib.PlaceW.site_ofPlaceW hp i) E
  -- `scc_rt_abort`'s code is between the take's and the clone's pcs.
  obtain ⟨⟨hin1, hin2⟩, -, -⟩ := habw.1
  rw [e1] at hin1
  rw [e2] at hin2
  have hn1 : (Int64.ofNat 2167996).toBitVec.toNat = 2167996 := rfl
  have hn2 : (Int64.ofNat 2168560).toBitVec.toNat = 2168560 := rfl
  rw [hn1] at hin1
  rw [hn2] at hin2
  have hcl : pcOf s ≠ Spike.Lib.A64.Flow.WakeWc.clonePc (Ly) := by
    have : Spike.Lib.A64.Flow.WakeWc.clonePc (Ly) = 2169344 := by
      unfold Spike.Lib.A64.Flow.WakeWc.clonePc Spike.Lib.WakePreA.cloneAt
      show ((Ly).lab (pfxM ++ ".sp6") + Int64.ofNat (4 * 13)).toBitVec.toNat = _
      rw [h6]; rfl
    omega
  have hta : s.st.2 ≠ Spike.Lib.WakeOSide.aW hp i E := by
    intro he
    have := congrArg (fun x : Int64 => x.toBitVec.toNat) he
    simp only [haW, hst] at this
    unfold pcOf at hin1
    rw [this] at hin1
    exact absurd hin1 (by decide)
  refine ⟨⟨?_, Spike.Lib.WakeH1Inv.x1W_off hcl (Spike.Lib.A64.Flow.WakeWc.pcOf_ne hta)⟩,
    Spike.Lib.A64.Flow.WakeWc.takeCKS_none (fun s h => h.1) hta hcl⟩
  have hst2 := (sfactsSt2_of_ac hac).congr hag.1 hag.2
  show Spike.Lib.A64.WakeWf.Wf _ _ _ _ _ _ _ _ _ _ _ _ s c []
  rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
  exact Spike.Lib.A64.WakeWf.Wf.intro (Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt hst2 (hDt s)) habs hac.acSt
    (fun s h => h.2) hac.noRet hac.place hnw.1 hnw.2 ⟨hac.cell, hac.zero⟩
    (fun k a ha hpc => by
      obtain ⟨h1, h2⟩ := hac.abortOk k a ha hpc
      refine ⟨?_, h2⟩
      rcases h1 with ⟨-, h⟩ | h | h | h
      · exact h.elim
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h)))

end Inst

end Spike.Lib.WakeRefStub

/-- info: 'Spike.Lib.WakeRefStub.refMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefStub.refMap
