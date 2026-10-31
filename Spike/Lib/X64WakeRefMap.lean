/-
**The threads abort path's components give `W1X`** (x86-64, wake.w; the
twin of `Spike/Lib/A64WakeRefMap.lean`): `X64WakeRefStub.RefMap`. At a state
of the path, `SFactsAC` at `own2b` (`ACW`) with `ownG`'s agreement (`AgW`)
gives `SFactsSt2` at `ownG` (`sfactsSt2_congr`), which `Lft2` moves to
`ownGXW`; with the write abort's phase kept (`AbSt`) and no write to the
arena or the counter (`NoWrW`) it gives `W1W`; the state in `scc_rt_abort`'s
code (`AbW`) is off the clone's and the take's pcs, so `X1W` holds and no
`K1W` move leaves it.

- `sfactsSt2_of_ac`: `SFactsSt2` at the frames `[]` from `SFactsAC`.
- `sfactsSt2_congr`: `SFactsSt2` at a map agreeing at the state and its
  successors.
- `refMap`: `RefMap`, given `DtW ⊆ Dt`.

**Where this differs from AArch64**: the level owns `ownGXW` (main's and
the worker's TCB words appended to `ownG`), so the state facts at `ownG`
are lifted by the path's `Lft2` (`RefMap`'s last hypothesis, from
`RefLft`); `SFactsSt2.congr` is stated here (x86-64 has `SFactsSt.congr`
only); the pcs are compared at the resolved addresses (`scc_rt_abort` at
`4202449`, `scc_rt_thr_worker` at `4202935`, the clone's `syscall` at
`.Lwc_main.x21 + 46 = 4203443`, the take site at `4200277`); the parses are
on `cellsOf asm`.
-/
import Spike.Lib.X64WakeRefLay
import Spike.Lib.X64WakeAWSite
import Spike.Lib.X64WakeAbOffW
import Spike.Lib.X64OwnCongr

namespace Spike.Lib.X64.WakeRefStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsAC SFactsSt2 StSucc)
open Spike.Lib.X64Consumer (Lsize)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (wakeCells)

/-- **`SFactsSt2` from `SFactsAC`** at the frames `[]`, its map `own` at no
frame. -/
theorem sfactsSt2_of_ac {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : State → List (Loc × Val)} {rS : Range} {Tk : State → Prop} {ar : Arena}
    {J : Spike.Lib.X64ConsumerS.InvS} {lbl : Spike.Lib.X64Consumer.Lbl} {lsize : Lsize} {s : State} {c : Ctl}
    {Dt Ab Cl Ac : State → Prop}
    (h : SFactsAC Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c [] Dt Ab Cl Ac) :
    SFactsSt2 Λ μ own s Dt :=
  ⟨h.noSite, h.mapped, h.svc, fun hs t he => h.ownInstr _ _ (.refl _) hs t he,
    fun hs call hd s' hs' => h.ownSys _ _ (.refl _) hs call hd s' hs', h.ownTake,
    fun a ha hp => let ⟨_, h2, h3, _⟩ := h.site a ha hp; ⟨h2, h3⟩, h.wrTail⟩

/-- **`SFactsSt2` at agreeing maps**: `own'` equal to `own` at `s` and at
every successor of `s`. -/
theorem sfactsSt2_congr {Λ : Scc.Sem.Layout} {μ : Marks} {own own' : Spike.Lib.X64Consumer.Own} {s : State}
    {Dt : State → Prop} (h : SFactsSt2 Λ μ own s Dt) (hs : own' s = own s)
    (hsucc : ∀ s', StSucc μ s s' → own' s' = own s') : SFactsSt2 Λ μ own' s Dt where
  noSite := h.noSite
  mapped := h.mapped
  svc := h.svc
  ownInstr := fun hns tree he => by
    rw [hs]
    exact Spike.Lib.X64ConsumerA.ownTree_congr (fun s' hl => hsucc s' (.inl ⟨hns, tree, he, hl⟩))
      (h.ownInstr hns tree he)
  ownSys := fun hsy call hd s' hs' => by
    rw [hs, hsucc s' (.inr (.inl ⟨hsy, call, hd, hs'⟩))]
    exact h.ownSys hsy call hd s' hs'
  ownTake := fun a ha hpc m => by
    rw [hs, hsucc _ (.inr (.inr ⟨a, ha, hpc, m, rfl⟩))]
    exact h.ownTake a ha hpc m
  site := h.site
  wrTail := h.wrTail

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`RefMap`**: `W1W` from the components (`Wf.intro`, `SFactsSt2` at
`ownG` by `sfactsSt2_congr` lifted to `ownGXW` by `Lft2`, the marks the
record's by `marks_target`, the write tail widened by `hDt`), `X1W` and no
`K1W` move off the clone's and the take's pcs (`scc_rt_abort`'s code lies
between them). -/
theorem refMap (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hDt : ∀ s, Spike.Lib.X64.WakeWf.DtW s → Dt s)
    (l : WeakMem.AllocLabel) (b n : Nat) : RefMap asm hp i E Dt Ctx ls0 l b n := by
  intro R' s c hac hag habs hnw habw hlft
  have hpW := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hpL : cellsOf asm = some (Ly).prog := by rw [hpW]; exact hwp
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo
  obtain ⟨e1, e2, -⟩ := Spike.Lib.X64.WakePh.ab_labs hlab
  have hst : (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have h21 : (Ly).lab Spike.Lib.X64.WakePh.WcClone.x21L = Int64.ofNat 4203397 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have haW := Spike.Lib.X64WakeOSide.aW_site hp i hpa E
  -- `scc_rt_abort`'s code is between the take's and the clone's pcs.
  obtain ⟨⟨hin1, hin2⟩, -, -⟩ := habw.1
  rw [e1] at hin1
  rw [e2] at hin2
  have hn1 : (Int64.ofNat 4202449).toBitVec.toNat = 4202449 := rfl
  have hn2 : (Int64.ofNat 4202935).toBitVec.toNat = 4202935 := rfl
  rw [hn1] at hin1
  rw [hn2] at hin2
  have hcl : pcOf s ≠ Spike.Lib.X64.Flow.WakeWc.clonePc (Ly) := by
    have : Spike.Lib.X64.Flow.WakeWc.clonePc (Ly) = 4203443 := by
      unfold Spike.Lib.X64.Flow.WakeWc.clonePc Spike.Lib.X64WakePreA.cloneAt
      show ((Ly).lab Spike.Lib.X64.WakePh.WcClone.x21L + 46).toBitVec.toNat = _
      rw [h21]; rfl
    omega
  have hta : s.st.2 ≠ Spike.Lib.X64WakeOSide.aW hp i E := by
    intro he
    have := congrArg (fun x : Int64 => x.toBitVec.toNat) he
    simp only [haW, hst] at this
    unfold pcOf at hin1
    rw [this] at hin1
    exact absurd hin1 (by decide)
  refine ⟨⟨?_, Spike.Lib.X64.WakeH1Inv.x1W_off hcl (Spike.Lib.X64.Flow.WakeWc.pcOf_ne hta)⟩,
    Spike.Lib.X64.Flow.WakeWc.takeCKS_none (fun s h => h.1) hta hcl⟩
  have hst2 := hlft (sfactsSt2_congr (sfactsSt2_of_ac hac) hag.1 hag.2)
  show Spike.Lib.X64.WakeWf.Wf _ _ _ _ _ _ _ _ _ _ _ _ s c []
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
  exact Spike.Lib.X64.WakeWf.Wf.intro (Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt hst2 (hDt s)) habs hac.acSt
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

end Spike.Lib.X64.WakeRefStub

/-- info: 'Spike.Lib.X64.WakeRefStub.sfactsSt2_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.sfactsSt2_congr

/-- info: 'Spike.Lib.X64.WakeRefStub.refMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refMap
