/-
**Smoke test of the fence-aware guard: the fence-released MP writer on `EnvG`**.
The writer `FenceW.fwriterMp` (`mov w2,#1; mov w3,#1; str w2,[x1];
dmb ish; str w3,[x0]`, both stores plain) by one `vcgen` call in each of
the two environments a per-program proof needs:

- `fwriter_envG : TripleEnv (E P tid) …` (`EnvG` under MP's plan
  `mpPlan`, unchanged): the flag store is plain, so it is a planned release
  only through the fence bits (`effRel`, set by the `dmb ish` access,
  `FenceOut`). Its VC is `vc_wf`: the same uniform obligation as `stlr`'s
  `vc_w2`, with the timestamp bound `ts_data ≤ vwOld ≤ vwNew < tw` from the
  fence (`W2F`: `vwOld ≤ vwNew` after `dmb ish`) instead of `stlr`'s
  `WriteBound.rel`.
- `fwriter_relPureF : TripleEnv (relPureF Arch.armv8 rel) …`: the data store
  is pure, the flag store is fence-released (flag set by `dmb ish`).

These are exactly the per-thread inputs of `ThreadRuleRXG.ofSafelyEnvGHyb`
(`EnvG/FenceEnvA64.lean`) and `final_of_relPureFSafely`
(`EnvG/FenceEnvPureA64.lean`).
-/
import Kraken.Promising.SLR.EnvG.MpSmokeVCGen
import Kraken.Promising.SLR.EnvG.FenceEnvPureA64
import Kraken.Promising.SLR.FenceWTrees

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.FenceW

namespace Kraken.Promising.SLR.EnvG.FenceEnvMp

open Kraken.Promising.SLR.EnvG.MpSmoke

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The fence-released flag store -/

/-- Before the flag store (position 4): `W2`, both fence bits (set by
`dmb ish`), and `vwOld ≤ vwNew` (the fence's view effect). -/
def W2F (P : Params) (σ : State isa) : Prop :=
  W2 P σ ∧ σ.fencedR = true ∧ σ.fencedW = true ∧ σ.vs.vwOld ≤ σ.vs.vwNew

theorem W2F.fence {P : Params} {σ σ' : State isa} (h : W2F P σ) (hf : FenceLe σ σ') : W2F P σ' :=
  ⟨W2.fence h.1 hf, hf.fencedR h.2.1, hf.fencedW h.2.2.1, by rw [hf.vwOld]; exact Nat.le_trans h.2.2.2 hf.vwNew⟩

/-- **VC dmb** (`dmb ish`): the full fence sets both bits and puts `vwNew`
above `vwOld`. -/
theorem vc_dmb {P : Params} (tid : Nat) (σ : State isa) (h : W2 P σ) :
    ∀ σ' : State isa, (E P tid).step (.fence .sy) σ () σ' → W2F P σ' := by
  intro σ' hs
  have hs' : FenceOut σ σ' .sy := hs
  subst hs'
  obtain ⟨hw, hq, ⟨ts, hX, hmax, hts⟩, hW, hF⟩ := h
  refine ⟨⟨hw, hq, ⟨ts, hX, hmax, ?_⟩, hW, hF⟩, rfl, rfl, ?_⟩
  · simpa [fenceViews, fenceStep] using hts
  · simp only [fenceViews, fenceStep]; simp only [Time, View] at *; omega

/-- **VC W2F** (`str w3, [x0]`, plain, `w3 = 1`, after `dmb ish`): the
planned release is permitted by the fence bits (`effRel`), with the same
uniform obligation as `stlr`'s (`vc_w2`): the data timestamp is at most
`vwOld ≤ vwNew < tw`. Every outcome keeps the token `W`. -/
theorem vc_wf {P : Params} (hL : MpLocs P) (tid : Nat) (σ : State isa) (h : W2F P σ) :
    (E P tid).ok (.store .plain false P.f 4 1#128) σ ∧
      ∀ b (σ' : State isa), (E P tid).step (.store .plain false P.f 4 1#128) σ b σ' → W3 P σ' := by
  obtain ⟨⟨⟨hrel, hpure⟩, hq, ⟨ts, hX, hmax, hts⟩, hW, hF⟩, hfR, hfW, hvw⟩ := h
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  have hWd : P.W ≠ P.Dt := hL.wd
  refine ⟨⟨rfl, hF, fun hr => by simp [mpPlan] at hr, fun _ => ⟨.inr ⟨hfR, hfW⟩, ?_, ?_, ?_⟩⟩, ?_⟩
  · rw [hrel]; exact flagPred_impure (by decide)
  · simp [mpPlan, hne]
  · intro c g _ hwb
    have hlt := hwb.vwNew
    rw [hrel]
    refine fun _ => ⟨by simp [mpPlan, hq], ts, by simpa [mpPlan] using hX, fun p hp => hmax p (by simpa [mpPlan] using hp), ?_⟩
    simp only [Time, View] at *; omega
  · intro b σ' hs
    obtain ⟨c, tw, hanc, -, -, -, -, hr, -⟩ := step_storeFacts hs
    obtain ⟨_, -, hr⟩ := hr
    refine ⟨WorldW.anchor ⟨hrel, hpure⟩ hanc, ?_⟩
    rw [hr]
    simp [mpPlan, hWd, hW]

variable [layout : _root_.Layout]

local instance fwriterMp.env : CodeEnv := ⟨layout fwriterMp⟩

/-- **The fence-released MP writer on `EnvG`**: from `W1` the writer ends in
`W3`, its fence-released flag store accounted as a planned release. -/
theorem fwriter_envG (P : Params) (hL : MpLocs P) (tid : Nat) :
    TripleEnv (E P tid)
      (fun s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
        Mem.loadInt s.dmem P.d 4 = none ∧ W1 P σ)
      fwriterMp (fun _ σ => W3 P σ) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold fwriterMp
  vcgen
  all_goals simp only [fenceMono_le_envG] at *
  case vc1 => simp
  case vc3 => simp
  case vc4 => simp
  case vc2 s σ0 hpre σ1 hf1 σ2 hf2 rng _ =>
    obtain ⟨-, hx1, -, -, hW⟩ := hpre
    simpa [hx1] using (vc_w1 hL tid σ2 (W1.fence (W1.fence hW hf1) hf2)).1
  case vc5 s σ0 hpre σ1 hf1 σ2 hf2 rng dm σ3 hd σ4 hfe rng2 _ =>
    obtain ⟨hx0, hx1, -, hdd, hW⟩ := hpre
    simp [hx0, hx1, hdd] at hd ⊢
    have hW2 : W2 P σ3 := by
      rcases hd.2 with hst | hst <;> exact (vc_w1 hL tid σ2 (W1.fence (W1.fence hW hf1) hf2)).2 _ σ3 hst
    exact (vc_wf hL tid σ4 (vc_dmb tid σ3 hW2 σ4 hfe)).1
  case vc6 s σ0 hpre σ1 hf1 σ2 hf2 rng dm σ3 hd σ4 hfe rng2 dm2 σ5 hst5 σ6 hf6 =>
    obtain ⟨hx0, hx1, hdf, hdd, hW⟩ := hpre
    simp [hx0, hx1, hdd] at hd hst5
    obtain ⟨rfl, hd2⟩ := hd
    have hW2 : W2 P σ3 := by
      rcases hd2 with hst | hst <;> exact (vc_w1 hL tid σ2 (W1.fence (W1.fence hW hf1) hf2)).2 _ σ3 hst
    simp [hdf] at hst5
    have hWF := vc_dmb tid σ3 hW2 σ4 hfe
    rcases hst5.2 with hst | hst <;> exact W3.fence ((vc_wf hL tid σ4 hWF).2 _ σ5 hst) hf6

/-- **The fence-released MP writer is fence-aware pure**: its data store
writes `⟨d, 4⟩`, whose release predicate is pure (`hd`); its flag store is
fence-released (the `dmb ish` sets the flag), unconstrained. -/
theorem fwriter_relPureF (rel : Loc → Pred) (f d : BitVec 64) (hd : ∀ v, Pred.Pure (rel ⟨d, 4⟩) v) :
    TripleEnv (SharedEnv.relPureF Arch.armv8 rel)
      (fun s _ => s.regs.X0.toBitVec = f ∧ s.regs.X1.toBitVec = d ∧ Mem.loadInt s.dmem f 4 = none ∧
        Mem.loadInt s.dmem d 4 = none)
      fwriterMp (fun _ _ => True) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold fwriterMp
  vcgen
  all_goals simp_all [SharedEnv.relPureFQ, Arch.storeKind, show Arch.armv8.plainStore = .plain from rfl]

end Kraken.Promising.SLR.EnvG.FenceEnvMp
