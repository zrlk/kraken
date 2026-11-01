/-
**The threads abort path's components give the third level, and the exit call is an abort site** (AArch64;
piece R5; the hello twins of wake's `A64WakeRefMap` and `A64WakeRefEx`):
`RefO.MapH` at the level `RootWX.W2H ∧ HelloH2Inv.X2H` under `TakeCKS`, and `RefO.ExH` at any `msOfA` side whose
marks are the canonical target's of a text parsing to hello's program.

At a state of the path, `SFactsAC` at `own2bH` (`ACWH`) with `ownGH`'s agreement (`AgWH`) gives `SFactsSt2` at
`ownGH` (`SFactsSt2.congr`); with the write abort's phase kept (`AbSt`) and no write to the arena or the counter
(`NoWrC`) it gives `W2H` (`Wf.intro`, the write tail widened by `hDt`). The state is in `scc_rt_abort`'s code
(`AbW`), off hello's clone and the take site (`HAbStub.abort_offH`), so `X2H` holds vacuously and no `TakeCKS`
move leaves it (`WakeWcK1.takeCKS_none`).

- `refMapH`: `MapH` at `W2H … ∧ X2H …`, given `DtW ⊆ Dt` (row B8-h2-refObl-hDt discharges it at the root).
- `threads_exit_pcH`: the threads abort label is the stub's exit label in hello's code.
- `refExH`: `ExH` at `msOfA` at the target's marks of any text `asm` parsing to `L.prog`.

No absolute address appears in a statement here.
-/
import Spike.Lib.A64HelloRefAC
import Spike.Lib.A64HelloRootWX
import Spike.Lib.A64HelloHAbStub
import Spike.Lib.A64WakeRefMap

namespace Spike.Lib.A64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region FragS Arena)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.A64.HelloPh (ClH lo)
open Scc.Cert.Link.A64 (codeOf)

variable {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)

include hlab in
/-- **`MapH`** at the third level `W2H` (at `ntA`, `helloSrc`, `ClH`, the placement `lbl`) and the fence fact `X2H`
at the take site (any `endX`, placement `lbl'` and sizes `lsize'`) under `TakeCKS` at the take site and `ClH`
(wake's `refMap`): `W2H` from the components (`Wf.intro`, the write tail widened by `hDt`), `X2H` and no move
off the clone's and the take's pcs (`abort_offH`). -/
theorem refMapH {Dt : State → Prop} (hDt : ∀ s, Spike.Lib.A64.WakeWf.DtW s → Dt s) (lbl : Lbl) (ar : Arena)
    (lsize : Lsize) (Ctx : FragS isaLSE2) (endX : Int64) (lbl' : Lbl) (lsize' : Lsize) :
    MapH L lbl ar lsize Ctx
      (fun s c => Spike.Lib.A64.HelloPh.RootWX.W2H L (Spike.Lib.A64.Rt.Reserve.ntA L.lab) ar helloSrc Dt (ClH L)
          Ctx lbl lsize s c [] ∧ Spike.Lib.HelloH2Inv.X2H L (L.lab siteL) endX lbl' lsize' s c [])
      (TakeCKS (L.lab siteL) (ClH L)) := by
  intro R' s c hac hag habs hnw habw
  obtain ⟨hcl, hta⟩ := Spike.Lib.A64.HelloPh.HAbStub.abort_offH hlab s habw.1.1
  have hta' : s.st.2 ≠ L.lab siteL := fun he => hta (by unfold pcOf; rw [he])
  refine ⟨⟨⟨rfl, ?_⟩, fun h => absurd h hcl, fun h => absurd h hta⟩,
    Spike.Lib.A64.Flow.WakeWc.takeCKS_none (fun s h => h.1) hta' hcl⟩
  have hst2 := (Spike.Lib.WakeRefStub.sfactsSt2_of_ac hac).congr hag.1 hag.2
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

/-- The threads abort label is the stub's exit label, in hello's code (wake's `threads_exit_pc`). -/
theorem threads_exit_pcH : Scc.Cert.Rt.A64.pcAt (codeOf lo SccCode.helloProg) Spike.Lib.A64.Abort.threads.exit 0 =
    codeOf lo SccCode.helloProg (Scc.Cert.Link.abortName .threads) := by
  rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

include hp hlo hlab hΛ in
/-- **`ExH`** (wake's `refEx`): at `msOfA` at the canonical target's marks of any text `asm` parsing to `L.prog`
(`hpa`), the exit call's pc is the `.threads` abort of `PhRec.μ` (`marks_target`). -/
theorem refExH {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {asm : String} (hpa : textProgram asm = .ok L.prog)
    (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : Spike.Lib.A64ConsumerS.OwnS) (ar : Arena)
    (I : Spike.Lib.A64ConsumerS.InvS) (lbl : Lbl) (lsize : Lsize) :
    ExH L (Spike.Lib.A64ConsumerA.msOfA L.Λ ((target H E).marks asm L.Λ) rd G own ar I lbl lsize []) := by
  intro s hs
  cases hx : Scc.Cert.Rt.A64.pcAt (codeOf lo SccCode.helloProg) Spike.Lib.A64.Abort.threads.exit 0 with
  | none => rw [threads_exit_pcH, ← Scc.Cert.Rt.A64.codeT_eq] at hx; exact absurd hx (by decide +kernel)
  | some x =>
    refine ⟨.threads, x, ?_, ?_⟩
    · rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target L hpa]
      show codeOf L.Λ.code.lo L.prog (L.Λ.abortLbl .threads) = some x
      rw [hΛ, hlo, hp, ← threads_exit_pcH, hx]
    · unfold pcOf; rw [hs]; exact Spike.Lib.A64.Rt.PhOfTab.pcAt0_eq hlab hx

end Spike.Lib.A64.HelloPh.RefO

/-- info: 'Spike.Lib.A64.HelloPh.RefO.refMapH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.refMapH

/-- info: 'Spike.Lib.A64.HelloPh.RefO.refExH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.refExH
