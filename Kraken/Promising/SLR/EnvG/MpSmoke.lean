/-
**The MP smoke test on `EnvG`**: the per-access verification
conditions a program author discharges for message passing
(`SLR/MpTrees.lean`), each **in isolation**, against `EnvG`'s `ok`/`step`
through the Out/Facts interface (`step_storeFacts`, `step_loadFacts`) and the
simp set of `EnvG/Simp.lean`. No event trees, no `NodeRel`, no prepay: this
measures what one VC costs.

MP's parameters and predicates are reused (`SLR/MpInv.lean`: `Params`,
`MpLocs`, `Good`, `flagPred`, `WorldW`, `WorldR`, `Own0`, `Own1`); the
architecture is `Arch.armv8`, the ISA AArch64's.

**The plan** (`mpPlan`): one entry, `Fl := 1` gives `[Dt]`. Valid by `decide`
on concrete addresses (`mpPlan₀_valid`) and by `simp` on symbolic ones
(`mpPlan_valid`).

**The VCs** (each the `ok ∧ ∀ outcome, post` shape of the access's `vcgen`
spec, `str_env_spec`/`stlr_shared_spec`/`ldar_shared_spec`/`ldr_env_spec`):
- `vc_w1` (`str w2, [x1]`, plain, pure value): `W1 → ok ∧ (step → W2)`.
- `vc_w2` (`stlr w3, [x0]`, planned release): `W2 → ok ∧ (step → W3)`; the
  `ok` includes `effRel` and the uniform `RelOb` (every anchor, fresh `tw`).
- `vc_r1` (`ldar w3, [x0]`): `R1 → step → R1 ∧ (low word ≠ 0 → R3)`.
- `vc_r3` (`ldr w4, [x1]`): `R3 → step → (cl → value = 1)`, through
  `slot_of_seen` and `read_owned` (`EnvG/Seen.lean`).

Phase-1 limits apply (single-access trees, read-side acquire only, releases
are stores).
-/
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.MpInv

namespace Kraken.Promising.SLR.EnvG.MpSmoke

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp

/-! ## The plan -/

/-- MP's plan: the release `Fl := 1` gives all of `Dt`. -/
def mpPlan (P : Params) : Plan := ⟨[{ loc := P.Fl, val := some 1#128, gives := [P.Dt] }]⟩

/-- Concrete parameters. -/
def P₀ : Params := ⟨0x1000, 0x2000, ⟨0x3000, 4⟩⟩

theorem mpPlan₀_valid : (mpPlan P₀).Valid := by decide

theorem mpPlan_valid {P : Params} (hL : MpLocs P) : (mpPlan P).Valid := by
  simp [Plan.Valid, mpPlan, hL.fl_dt]

/-- The environment of the MP thread `tid`. -/
abbrev E (P : Params) (tid : Nat) : SharedEnv := EnvG isa Arch.armv8 tid (mpPlan P)

/-! ## The writer -/

/-- Before `str w2, [x1]` (position 1). -/
def W1 (P : Params) (σ : State isa) : Prop := WorldW P σ.g ∧ Own0 P σ.r

/-- Before `stlr w3, [x0]` (positions 2, 3). -/
def W2 (P : Params) (σ : State isa) : Prop := WorldW P σ.g ∧ Own1 P σ.vs σ.r

/-- After the release (position 4). -/
def W3 (P : Params) (σ : State isa) : Prop := WorldW P σ.g ∧ 1 ≤ (σ.r.wr P.W).q

/-- The writer's world facts carry over a re-anchor. -/
theorem WorldW.anchor {P : Params} {tid : Nat} {σ : State isa} {c : Config isa} {g : Ghost} (h : WorldW P σ.g)
    (hanc : AnchorOk tid σ c g) : WorldW P g := by
  unfold WorldW; rw [hanc.rel]; exact h

/-- **VC W1** (`str w2, [x1]`, `w2 = 1`): the plain store is permitted (a
positive share of `Dt`, a pure value) and every outcome adds `(1, tw)` to
`Dt`'s write set with `tw ≤ vwOld`. -/
theorem vc_w1 {P : Params} (hL : MpLocs P) (tid : Nat) (σ : State isa) (h : W1 P σ) :
    (E P tid).ok (.store .plain false P.d 4 1#128) σ ∧
      ∀ b (σ' : State isa), (E P tid).step (.store .plain false P.d 4 1#128) σ b σ' → W2 P σ' := by
  obtain ⟨⟨hrel, hpure⟩, hq, hX, hW, hF⟩ := h
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  refine ⟨⟨rfl, by rw [hq]; decide, fun _ => hpure _, fun hr => by simp [mpPlan, hne] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, -, hwv, -, hr, -⟩ := step_storeFacts hs
  have hr' : σ'.r = σ.r.addW P.Dt (1#128, tw) := by simpa [mpPlan, hne] using hr
  refine ⟨WorldW.anchor ⟨hrel, hpure⟩ hanc, by rw [hr', Res.addW_q]; exact hq,
    ⟨tw, ?_, fun p hp => ?_, hwv.vwOld (by simp)⟩, by rw [hr', Res.addW_q]; exact hW,
    by rw [hr', Res.addW_q]; exact hF⟩
  · rw [hr', Res.addW_X_self, hq]; exact .inr ⟨by decide, rfl⟩
  · rw [hr', Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · rw [hX p hp]; exact Nat.zero_le _
    · exact Nat.le_refl _

/-- **VC W2** (`stlr w3, [x0]`, `w3 = 1`): the planned release is permitted
(`effRel`, impure value, `Fl` kept, and the uniform obligation: at every
anchor and fresh `tw`, `flagPred` holds of the `Dt` permission given away),
and every outcome keeps the token `W`. -/
theorem vc_w2 {P : Params} (hL : MpLocs P) (tid : Nat) (σ : State isa) (h : W2 P σ) :
    (E P tid).ok (.store .rel false P.f 4 1#128) σ ∧
      ∀ b (σ' : State isa), (E P tid).step (.store .rel false P.f 4 1#128) σ b σ' → W3 P σ' := by
  obtain ⟨⟨hrel, hpure⟩, hq, ⟨ts, hX, hmax, hts⟩, hW, hF⟩ := h
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  have hWd : P.W ≠ P.Dt := hL.wd
  refine ⟨⟨rfl, hF, fun hr => by simp [mpPlan] at hr, fun _ => ⟨effRel_rel _ _, ?_, ?_, ?_⟩⟩, ?_⟩
  · rw [hrel]; exact flagPred_impure (by decide)
  · simp [mpPlan, hne]
  · intro c g _ hwb
    have hlt := hwb.rel rfl
    rw [hrel]
    refine fun _ => ⟨by simp [mpPlan, hq], ts, by simpa [mpPlan] using hX, fun p hp => hmax p (by simpa [mpPlan] using hp), ?_⟩
    simp only [Time, View] at *; omega
  · intro b σ' hs
    obtain ⟨c, tw, hanc, -, -, -, -, hr, -⟩ := step_storeFacts hs
    obtain ⟨_, -, hr⟩ := hr
    refine ⟨WorldW.anchor ⟨hrel, hpure⟩ hanc, ?_⟩
    rw [hr]
    simp [mpPlan, hWd, hW]

/-! ## The reader -/

/-- Before `ldar w3, [x0]` (position 1): the world, and no forwarding item
for `Fl` (the reader never writes). -/
def R1 (P : Params) (σ : State isa) : Prop := WorldR P σ.r σ.g ∧ σ.vs.getFwd P.Fl = none

/-- Before `ldr w4, [x1]` (position 3): the world, and a flag message with a
non-zero low word at the snapshot, at or below `vrNew`. -/
def R3 (P : Params) (σ : State isa) : Prop :=
  WorldR P σ.r σ.g ∧ ∃ tsF vF, σ.snap.mem.read? P.Fl tsF = some vF ∧ BitVec.setWidth 32 vF ≠ 0 ∧ tsF ≤ σ.vs.vrNew

/-- The world facts carry over a re-anchor that keeps the resource. -/
theorem WorldR.anchor {P : Params} {tid : Nat} {σ σ' : State isa} {c : Config isa} (h : WorldR P σ.r σ.g)
    (hanc : AnchorOk tid σ c σ'.g) (hr : σ'.r = σ.r) : WorldR P σ'.r σ'.g := by
  obtain ⟨hrel, ι, hlt, hι, hacq⟩ := h
  exact ⟨by rw [hanc.rel]; exact hrel, ι, hanc.acqLen hlt, by rw [hanc.acqPred hlt]; exact hι, by rw [hr]; exact hacq⟩

/-- **VC R1** (`ldar w3, [x0]`): every outcome keeps `R1`, and one with a
non-zero low word establishes `R3` (the acquire raises `vrNew` to the
message read). -/
theorem vc_r1 {P : Params} (tid : Nat) (σ : State isa) (h : R1 P σ) :
    ∀ v (σ' : State isa), (E P tid).step (.load .acq false P.f 4) σ v σ' → R1 P σ' ∧ (BitVec.setWidth 32 v ≠ 0 → R3 P σ') := by
  intro v σ' hs
  obtain ⟨hanc, hr, -, tr, hrd, hlv, -⟩ := step_loadFacts hs
  have hw := WorldR.anchor h.1 hanc hr
  refine ⟨⟨hw, by rw [hlv.getFwd]; exact h.2⟩, fun hv => ⟨hw, tr, v, hrd.val, hv, ?_⟩⟩
  exact (hlv.acq (by simp) (not_fwded_of_none h.2)).1

/-- **VC R3** (`ldr w4, [x1]`): under the clean erasure of the load's anchor
(`cl`), the data load returns `1`. The seen flag message carries a slot for
the reader's acquire id (`slot_of_seen`), whose `flagPred` gives all of `Dt`
with maximal write `(1, ts)`, `ts ≤ tsF ≤ vrNew`; `read_owned` concludes. -/
theorem vc_r3 {P : Params} (tid : Nat) (σ : State isa) (h : R3 P σ) :
    ∀ v (σ' : State isa), (E P tid).step (.load .plain false P.d 4) σ v σ' → σ'.cl → v = 1#128 := by
  intro v σ' hs hcl
  obtain ⟨hanc, -, hcl', tr, hrd, -⟩ := step_loadFacts hs
  obtain ⟨⟨hrel, ι, hlt, hι, hacq⟩, tsF, vF, hrdF, hvF, htsF⟩ := h
  rw [hcl'] at hcl
  obtain ⟨-, rF, E'⟩ := hcl
  obtain ⟨s, hs, hkey, hid, hP⟩ := slot_of_seen (k := (P.Fl, tsF)) E' hanc.lt hacq (hanc.read? hrdF)
    (by rw [hanc.rel, hrel]; exact flagPred_impure hvF)
  rw [hanc.acqPred hlt, hι] at hP
  obtain ⟨hq, ts, hX, hmax, hts⟩ := hP hvF
  exact (read_owned E' hanc.lt hs hq (by rw [hkey, hid]; exact hacq) hX hmax hrd
    (Nat.le_trans hts (Nat.le_trans htsF (le_readBound_vrNew _ _ _ _)))).2

/-- At the end (position 4): the world and a seen flag message with a
non-zero low word at the snapshot (the reader's `MpPost` disjunct). -/
def R4 (P : Params) (σ : State isa) : Prop :=
  WorldR P σ.r σ.g ∧ ∃ tsF vF, σ.snap.mem.read? P.Fl tsF = some vF ∧ BitVec.setWidth 32 vF ≠ 0

/-- **VC R3, the world part**: every outcome of the data load keeps the world
and the seen flag message. -/
theorem vc_r3_world {P : Params} (tid : Nat) (σ : State isa) (h : R3 P σ) :
    ∀ v (σ' : State isa), (E P tid).step (.load .plain false P.d 4) σ v σ' → R4 P σ' := by
  intro v σ' hs
  obtain ⟨hanc, hr, -⟩ := step_loadFacts hs
  obtain ⟨hw, tsF, vF, hrdF, hvF, -⟩ := h
  exact ⟨WorldR.anchor hw hanc hr, tsF, vF, hanc.read? hrdF, hvF⟩

end Kraken.Promising.SLR.EnvG.MpSmoke
