/-
**The x64 MP smoke test on `EnvG`, the verification conditions**
(`EnvG/MpSmoke.lean` for x64 under `Arch.tso`): the
per-access VCs of the x64 message-passing threads against `EnvGX`
(`EnvG` restricted to the shared layout `[(f, 4), (d, 4)]`), through the
Out/Facts interface (`step_storeFacts`, `step_loadFacts`) and `EnvG/Simp.lean`.

Under `Arch.tso` the x64 plain `mov` store is a release (`plainStore := .rel`)
and the plain `mov` load an acquire (`plainLoad := .acqPc`), so the AArch64
`stlr`/`ldar` VCs are here plain stores/loads:
- `vc_w1` (`movl %eax, (%rsi)`, `eax = 42`): unplanned, pure value.
- `vc_w2` (`movl %ecx, (%rdi)`, `ecx = 1`): the planned release (`effRel`
  from the store kind), the uniform `RelOb`.
- `vc_r1` (`movl (%rdi), %eax`): the acquire raises `vrNew` to the flag
  message read.
- `vc_r3` (`movl (%rsi), %ebx`): under `cl`, the data load returns `42`
  (`slot_of_seen`, `read_owned`).
-/
import Kraken.Promising.SLR.EnvG.X64MpSpec
import Kraken.Promising.SLR.EnvG.X64Link

namespace Kraken.Promising.X64.EnvG.MpSmoke

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG.Mp

/-! ## The plan and the layout -/

/-- MP's plan: the release `Fl := 1` gives all of `Dt`. -/
def mpPlan (P : Params) : Plan := ⟨[{ loc := P.Fl, val := some 1#128, gives := [P.Dt] }]⟩

theorem mpPlan_valid {P : Params} (hL : MpLocs P) : (mpPlan P).Valid := by
  simp [Plan.Valid, mpPlan, hL.fl_dt]

/-- The shared layout: the flag and the data word. -/
abbrev mpS (P : Params) : SharedEnv.Layout := [(P.f, 4), (P.d, 4)]

theorem mpS_le16 (P : Params) : Le16 (mpS P) := fun x hx => by
  simp only [mpS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact (by decide : 4 ≤ 16)

/-- The environment of the MP thread `tid` (x64, `Arch.tso`). -/
abbrev E (P : Params) (tid : Nat) : SharedEnv := EnvGX Arch.tso tid (mpPlan P) (mpS P)

/-! ## The writer -/

/-- Before the data store. -/
def W1 (P : Params) (σ : EStateX) : Prop := WorldW P σ.g ∧ Own0 P σ.r

/-- Before the flag store. -/
def W2 (P : Params) (σ : EStateX) : Prop := WorldW P σ.g ∧ Own1 P σ.vs σ.r

/-- After the release. -/
def W3 (P : Params) (σ : EStateX) : Prop := WorldW P σ.g ∧ 1 ≤ (σ.r.wr P.W).q

/-- The writer's world facts for the flag predicate `φ` carry over a
re-anchor. -/
theorem WorldWG.anchor {P : Params} {φ : Pred} {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost}
    (h : WorldWG P φ σ.g) (hanc : AnchorOk tid σ c g) : WorldWG P φ g := by
  unfold WorldWG; rw [hanc.rel]; exact h

/-- The writer's world facts carry over a re-anchor. -/
theorem WorldW.anchor {P : Params} {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost} (h : WorldW P σ.g)
    (hanc : AnchorOk tid σ c g) : WorldW P g :=
  WorldWG.anchor (φ := P.φ) h hanc

/-- **VC W1** (`movl %eax, (%rsi)`, `eax = 42`): the store to `Dt` is not
planned, so permitted by a positive share and a pure value; every outcome
adds `(42, tw)` to `Dt`'s write set with `tw ≤ vwOld`. -/
theorem vc_w1 {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W1 P σ) :
    (E P tid).ok (.store .plain false P.d 4 dataVal) σ ∧
      ∀ b (σ' : EStateX), (E P tid).step (.store .plain false P.d 4 dataVal) σ b σ' → W2 P σ' := by
  obtain ⟨⟨hrel, hpure⟩, hq, hX, hW, hF⟩ := h
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  refine ⟨⟨⟨rfl, by rw [hq]; decide, fun _ => hpure _, fun hr => by simp [mpPlan, hne] at hr⟩, by simp [SharedEnv.AccessIn]⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, -, hwv, -, hr, -⟩ := step_storeFacts hs
  have hr' : σ'.r = σ.r.addW P.Dt (dataVal, tw) := by simpa [mpPlan, hne] using hr
  refine ⟨WorldW.anchor ⟨hrel, hpure⟩ hanc, by rw [hr', Res.addW_q]; exact hq,
    ⟨tw, ?_, fun p hp => ?_, hwv.vwOld (by decide)⟩, by rw [hr', Res.addW_q]; exact hW,
    by rw [hr', Res.addW_q]; exact hF⟩
  · rw [hr', Res.addW_X_self, hq]; exact .inr ⟨by decide, rfl⟩
  · rw [hr', Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · rw [hX p hp]; exact Nat.zero_le _
    · exact Nat.le_refl _

/-- **VC W2** (`movl %ecx, (%rdi)`, `ecx = 1`): the planned release is
permitted (`effRel`: a plain store is a release under `Arch.tso`; impure
value; `Fl` kept; the uniform obligation), and every outcome keeps `W`. -/
theorem vc_w2 {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W2 P σ) :
    (E P tid).ok (.store .plain false P.f 4 1#128) σ ∧
      ∀ b (σ' : EStateX), (E P tid).step (.store .plain false P.f 4 1#128) σ b σ' → W3 P σ' := by
  obtain ⟨⟨hrel, hpure⟩, hq, ⟨ts, hX, hmax, hts⟩, hW, hF⟩ := h
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  have hWd : P.W ≠ P.Dt := hL.wd
  refine ⟨⟨⟨rfl, hF, fun hr => by simp [mpPlan] at hr, fun _ => ⟨.inl rfl, ?_, ?_, ?_⟩⟩, by simp [SharedEnv.AccessIn]⟩, ?_⟩
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

/-! ### Generic over the flag predicate

The reader's table predicates and VCs for any flag predicate `φ`
(`X64MpSpec.FlagLaw`); `R1`/`R3`/`R4` and `vc_r1`/`vc_r3`/`vc_r3_world`
below are the instance at `P.φ`, `MpInc`'s `…I` copies the one at `φI`. -/

/-- Before the flag load, for `φ`. -/
def R1G (P : Params) (φ : Pred) (σ : EStateX) : Prop := WorldRG P φ σ.r σ.g ∧ σ.vs.getFwd P.Fl = none

/-- Before the data load, for `φ`. -/
def R3G (P : Params) (φ : Pred) (σ : EStateX) : Prop :=
  WorldRG P φ σ.r σ.g ∧ ∃ tsF vF, σ.snap.mem.read? P.Fl tsF = some vF ∧ BitVec.setWidth 32 vF ≠ 0 ∧ tsF ≤ σ.vs.vrNew

/-- At the end, for `φ`. -/
def R4G (P : Params) (φ : Pred) (σ : EStateX) : Prop :=
  WorldRG P φ σ.r σ.g ∧ ∃ tsF vF, σ.snap.mem.read? P.Fl tsF = some vF ∧ BitVec.setWidth 32 vF ≠ 0

/-- The reader's world facts for `φ` carry over a re-anchor that keeps the
resource. -/
theorem WorldRG.anchor {P : Params} {φ : Pred} {tid : Nat} {σ σ' : EStateX} {c : Config isa}
    (h : WorldRG P φ σ.r σ.g) (hanc : AnchorOk tid σ c σ'.g) (hr : σ'.r = σ.r) : WorldRG P φ σ'.r σ'.g := by
  obtain ⟨hrel, ι, hlt, hι, hacq⟩ := h
  exact ⟨by rw [hanc.rel]; exact hrel, ι, hanc.acqLen hlt, by rw [hanc.acqPred hlt]; exact hι, by rw [hr]; exact hacq⟩

/-- **VC R1**, for `φ`. -/
theorem vc_r1G {P : Params} {φ : Pred} (tid : Nat) (σ : EStateX) (h : R1G P φ σ) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false P.f 4) σ v σ' →
      R1G P φ σ' ∧ (BitVec.setWidth 32 v ≠ 0 → R3G P φ σ') := by
  intro v σ' hs
  obtain ⟨hanc, hr, -, tr, hrd, hlv, -⟩ := step_loadFacts (pl := mpPlan P) hs
  have hw := WorldRG.anchor h.1 hanc hr
  refine ⟨⟨hw, by rw [hlv.getFwd]; exact h.2⟩, fun hv => ⟨hw, tr, v, hrd.val, hv, ?_⟩⟩
  exact (hlv.acq (by decide) (not_fwded_of_none h.2)).1

/-- **VC R3**, for `φ` with `FlagLaw`. -/
theorem vc_r3G {P : Params} {φ : Pred} (hφ : FlagLaw P.Dt φ) (tid : Nat) (σ : EStateX) (h : R3G P φ σ) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false P.d 4) σ v σ' → σ'.cl → v = dataVal := by
  intro v σ' hs hcl
  obtain ⟨hanc, -, hcl', tr, hrd, -⟩ := step_loadFacts (pl := mpPlan P) hs
  obtain ⟨⟨hrel, ι, hlt, hι, hacq⟩, tsF, vF, hrdF, hvF, htsF⟩ := h
  rw [hcl'] at hcl
  obtain ⟨-, rF, E'⟩ := hcl
  obtain ⟨s, hs, hkey, hid, hP⟩ := SLR.EnvG.slot_of_seen (k := (P.Fl, tsF)) E' hanc.lt hacq (hanc.read? hrdF)
    (by rw [hanc.rel, hrel]; exact hφ.impure hvF)
  rw [hanc.acqPred hlt, hι] at hP
  obtain ⟨hq, ts, hX, hmax, hts⟩ := hφ.good hvF hP
  exact (read_owned E' hanc.lt hs hq (by rw [hkey, hid]; exact hacq) hX hmax hrd
    (Nat.le_trans hts (Nat.le_trans htsF (le_readBound_vrNew _ _ _ _)))).2

/-- **VC R3, the world part**, for `φ`. -/
theorem vc_r3_worldG {P : Params} {φ : Pred} (tid : Nat) (σ : EStateX) (h : R3G P φ σ) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false P.d 4) σ v σ' → R4G P φ σ' := by
  intro v σ' hs
  obtain ⟨hanc, hr, -⟩ := step_loadFacts (pl := mpPlan P) hs
  obtain ⟨hw, tsF, vF, hrdF, hvF, -⟩ := h
  exact ⟨WorldRG.anchor hw hanc hr, tsF, vF, hanc.read? hrdF, hvF⟩

/-! ### The instance at `flagPred` -/

/-- Before the flag load: the world, and no forwarding item for `Fl`. -/
def R1 (P : Params) (σ : EStateX) : Prop := WorldR P σ.r σ.g ∧ σ.vs.getFwd P.Fl = none

/-- Before the data load: the world, and a flag message with a non-zero low
word at the snapshot, at or below `vrNew`. -/
def R3 (P : Params) (σ : EStateX) : Prop :=
  WorldR P σ.r σ.g ∧ ∃ tsF vF, σ.snap.mem.read? P.Fl tsF = some vF ∧ BitVec.setWidth 32 vF ≠ 0 ∧ tsF ≤ σ.vs.vrNew

/-- At the end: the world and a seen flag message with a non-zero low word. -/
def R4 (P : Params) (σ : EStateX) : Prop :=
  WorldR P σ.r σ.g ∧ ∃ tsF vF, σ.snap.mem.read? P.Fl tsF = some vF ∧ BitVec.setWidth 32 vF ≠ 0

/-- The world facts carry over a re-anchor that keeps the resource. -/
theorem WorldR.anchor {P : Params} {tid : Nat} {σ σ' : EStateX} {c : Config isa} (h : WorldR P σ.r σ.g)
    (hanc : AnchorOk tid σ c σ'.g) (hr : σ'.r = σ.r) : WorldR P σ'.r σ'.g :=
  WorldRG.anchor (φ := P.φ) h hanc hr

/-- **VC R1** (`movl (%rdi), %eax`, an acquire under `Arch.tso`): every
outcome keeps `R1`, and one with a non-zero low word establishes `R3`. -/
theorem vc_r1 {P : Params} (tid : Nat) (σ : EStateX) (h : R1 P σ) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false P.f 4) σ v σ' →
      R1 P σ' ∧ (BitVec.setWidth 32 v ≠ 0 → R3 P σ') :=
  vc_r1G (φ := P.φ) tid σ h

/-- **VC R3** (`movl (%rsi), %ebx`): under the clean erasure of the load's
anchor, the data load returns `42`. -/
theorem vc_r3 {P : Params} (tid : Nat) (σ : EStateX) (h : R3 P σ) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false P.d 4) σ v σ' → σ'.cl → v = dataVal :=
  vc_r3G (flagPred_law _) tid σ h

/-- **VC R3, the world part**: every outcome of the data load keeps the world
and the seen flag message. -/
theorem vc_r3_world {P : Params} (tid : Nat) (σ : EStateX) (h : R3 P σ) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false P.d 4) σ v σ' → R4 P σ' :=
  vc_r3_worldG (φ := P.φ) tid σ h

end Kraken.Promising.X64.EnvG.MpSmoke
