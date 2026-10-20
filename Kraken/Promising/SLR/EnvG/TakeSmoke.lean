/-
**Part 7: smoke test — a reader that writes
after its acquire** (one slot, the MP shape of `EnvG/MpSmoke.lean`).

The writer is MP's (`str w2, [x1]; stlr w3, [x0]` releasing all of `Dt` to
the flag's slot for the reader's acquire id `ι`, `flagPred`). The reader runs
on `EnvGT` (`EnvG/TakeEnv.lean`) with the empty plan:

- `vc_t1` (`ldar w3, [x0]`): an outcome with a non-zero low word **takes**
  the flag message's slot: afterwards the reader holds a positive share of
  `Dt` (`TakeCond`: acquire, no forwarding item for `Fl`; the slot from
  `slot_of_seen` under the validity-free erasure `ErOwn` the step records,
  so no clean flag is needed; `loadFactsT_wr_pos_of_slot`).
- `vc_t2` (`str w5, [x1]`): the plain store to `Dt` is then permitted
  (`StoreOk`: a positive share, a pure value, not a planned release) and
  keeps the reader's state.

This is the per-instruction content of a reader proof (as `MpSmoke` was for
MP before `MpSmokeVCGen`); a whole-thread `vcgen` run over `EnvGT` needs the
`EnvGT` step lemmas in the `EnvG` simp set (not done here).
-/
import Kraken.Promising.SLR.EnvG.TakeA64Link
import Kraken.Promising.SLR.EnvG.MpSmoke

namespace Kraken.Promising.SLR.EnvG.TakeSmoke

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp

/-- The reader's plan: it releases nothing. -/
def rdPlan : Plan := ⟨[]⟩

/-- The reader's environment, with taking loads. -/
abbrev ET (tid : Nat) : SharedEnv := EnvGT isa Arch.armv8 tid rdPlan

/-- Before `ldar w3, [x0]`: MP's reader world (acquire id `ι` of `Fl` with
`flagPred`), `Dt` pure, and no forwarding item for `Fl`. -/
def T1 (P : Params) (σ : State isa) : Prop :=
  WorldR P σ.r σ.g ∧ (∀ v, Pred.Pure (σ.g.rel P.Dt) v) ∧ σ.vs.getFwd P.Fl = none

/-- Before `str w5, [x1]`: `Dt` pure and a positive share of `Dt`. -/
def T2 (P : Params) (σ : State isa) : Prop := (∀ v, Pred.Pure (σ.g.rel P.Dt) v) ∧ 0 < (σ.r.wr P.Dt).q

/-- **VC T1** (`ldar w3, [x0]` on `EnvGT`): a non-zero flag takes `Dt`. -/
theorem vc_t1 {P : Params} (tid : Nat) (σ : State isa) (h : T1 P σ) :
    ∀ v (σ' : State isa), (ET tid).step (.load .acq false P.f 4) σ v σ' → BitVec.setWidth 32 v ≠ 0 → T2 P σ' := by
  intro v σ' hs hv
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, -, a, ha, hr, hg, -⟩ := step_loadFactsT hs
  obtain ⟨⟨hrel, ι, hlt, hι, hacq⟩, hpure, hfw⟩ := h
  have hrel' : σ'.g.rel = σ.g.rel := by rw [hg, (ha.ghost_le).rel, hanc.rel]
  refine ⟨fun w => by rw [hrel']; exact hpure w, ?_⟩
  have hc : TakeCond Arch.armv8 .acq σ.vs P.Fl tr := ⟨by decide, not_fwded_of_none hfw⟩
  obtain ⟨s, hs, hkey, hid, hP⟩ := slot_of_seen (k := (P.Fl, tr)) E hanc.lt hacq hrd.val
    (by rw [hanc.rel, hrel]; exact flagPred_impure hv)
  rw [hanc.acqPred hlt, hι] at hP
  have hq : (s.res.wr P.Dt).q = 1 := (hP hv).1
  exact loadFactsT_wr_pos_of_slot ha hr hc E.slotsNodup hs hkey (by rw [hid]; exact hacq)
    (by rw [hid]; exact hanc.acqLen hlt) (by rw [hq]; decide)

/-- **VC T2** (`str w5, [x1]`, any value `w`): the reader's plain store to
`Dt` is permitted, and its state is kept. -/
theorem vc_t2 {P : Params} (tid : Nat) (σ : State isa) (w : Val) (h : T2 P σ) :
    (ET tid).ok (.store .plain false P.d 4 w) σ ∧
      ∀ b (σ' : State isa), (ET tid).step (.store .plain false P.d 4 w) σ b σ' → T2 P σ' := by
  obtain ⟨hpure, hq⟩ := h
  refine ⟨⟨rfl, hq, fun _ => hpure w, fun hr => by simp [rdPlan, Plan.rel, Plan.find?] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, -, -, -, ⟨Q, -, hr⟩, -⟩ := step_storeFactsT hs
  have hr' : σ'.r = σ.r.addW P.Dt (w, tw) := by simpa [Plan.after, rdPlan, Plan.rel, Plan.find?] using hr
  refine ⟨fun v => ?_, by rw [hr', Res.addW_q]; exact hq⟩
  rw [hanc.rel]; exact hpure v

#print axioms vc_t1
#print axioms vc_t2

end Kraken.Promising.SLR.EnvG.TakeSmoke
