/-
**x64 message passing with an unlocked `incl` release, the verification
conditions**: the per-access VCs of `mp_incl.kl`'s
threads under `Arch.tso`, through the Out/Facts interface.

- **The writer** (`mpIncWriterX`: `movl $42, (%rsi); incl (%rdi)`) runs in
  `EnvGLRX` (`EnvGLR` restricted to `mpS`, `LRX64.lean`): `incl` is a load,
  then a release-kind store to the same location, which only the
  load-then-release link accepts. Its plan `mpIncPlan` makes **every** store
  to `Fl` a release giving all of `Dt` (`val := none`): the stored value is
  the loaded one plus one, and the `EnvGLR` load says nothing about it.
  - `vc_w1I` (`movl $42, (%rsi)`): unplanned, pure value (as `vc_w1`).
  - `vc_incLoad` / `vc_incStore` (`incl (%rdi)`): every load outcome keeps
    `W2I`; at any such outcome the store of **any** value is permitted
    (planned release; `flagPredI` is impure everywhere; `Good` from `Own1`)
    and ends in `W3I`.
- **The reader** (`X64MpVCGen.mpReaderX`, unchanged) runs in
  `X64MpSmoke.E` (`EnvGX`): the VCs of `X64MpSmoke` restated with the world
  facts `WorldRI` (flag predicate `φI`): `vc_r1I`, `vc_r3I`, `vc_r3_worldI`.
-/
import Kraken.Promising.SLR.EnvG.X64MpIncSpec
import Kraken.Promising.SLR.EnvG.X64MpSmoke
import Kraken.Promising.SLR.EnvG.LRX64VCGen
import Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.MpInc

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.X64.Parser

/-! ## The writer program, plan and environment -/

/-- **The x64 MP writer with an unlocked `incl` release**: data `42` to
`(%rsi)`, then `incl (%rdi)` (no `lock`). -/
def mpIncWriterX : Program := parse("
  movl $42, (%rsi)
  incl (%rdi)
")

/-- The writer's plan: **every** store to `Fl` is a release giving all of
`Dt` (`val := none`). -/
def mpIncPlan (P : Params) : Plan := ⟨[{ loc := P.Fl, gives := [P.Dt] }]⟩

theorem mpIncPlan_valid {P : Params} (hL : MpLocs P) : (mpIncPlan P).Valid := by
  simp [Plan.Valid, mpIncPlan, hL.fl_dt]

theorem mpIncPlan_rel_Fl (P : Params) (v : Val) : (mpIncPlan P).rel P.Fl v = true := by
  simp [mpIncPlan, Plan.rel, Plan.find?]

theorem mpIncPlan_rel_ne {P : Params} {x : Loc} (h : P.Fl ≠ x) (v : Val) : (mpIncPlan P).rel x v = false := by
  simp [mpIncPlan, Plan.rel, Plan.find?, h]

/-- The writer's environment: `EnvGLR` on `mpS` (`Arch.tso`). -/
abbrev EW (P : Params) (tid : Nat) : SharedEnv := EnvGLRX Arch.tso tid (mpIncPlan P) (mpS P)

/-! ## The writer's VCs -/

/-- Before the data store. -/
def W1I (P : Params) (σ : EStateX) : Prop := WorldWI P σ.g ∧ Own0 P σ.r

/-- Before `incl`. -/
def W2I (P : Params) (σ : EStateX) : Prop := WorldWI P σ.g ∧ Own1 P σ.vs σ.r

/-- After the release. -/
def W3I (P : Params) (σ : EStateX) : Prop := WorldWI P σ.g ∧ 1 ≤ (σ.r.wr P.W).q

theorem WorldWI.anchor {P : Params} {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost} (h : WorldWI P σ.g)
    (hanc : AnchorOk tid σ c g) : WorldWI P g :=
  WorldWG.anchor (φ := φI P) h hanc

/-- **VC W1** (`movl $42, (%rsi)`): the store to `Dt` is not planned, so
permitted by a positive share and a pure value; every outcome adds
`(42, tw)` to `Dt`'s write set with `tw ≤ vwOld`. -/
theorem vc_w1I {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W1I P σ) :
    (EW P tid).ok (.store .plain false P.d 4 dataVal) σ ∧
      ∀ b (σ' : EStateX), (EW P tid).step (.store .plain false P.d 4 dataVal) σ b σ' → W2I P σ' := by
  obtain ⟨⟨hrel, hpure⟩, hq, hX, hW, hF⟩ := h
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  refine ⟨⟨⟨rfl, by rw [hq]; decide, fun _ => hpure _, fun hr => by rw [mpIncPlan_rel_ne hne] at hr; exact absurd hr (by decide)⟩,
    by simp [SharedEnv.AccessIn]⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, -, hwv, -, hr, -⟩ := stepLR_storeFacts (I := isa) hs
  have hr' : σ'.r = σ.r.addW P.Dt (dataVal, tw) := by
    obtain ⟨_, -, hr⟩ := hr
    rw [hr, Plan.after, mpIncPlan_rel_ne hne]
    rfl
  refine ⟨WorldWI.anchor ⟨hrel, hpure⟩ hanc, by rw [hr', Res.addW_q]; exact hq,
    ⟨tw, ?_, fun p hp => ?_, hwv.vwOld (by decide)⟩, by rw [hr', Res.addW_q]; exact hW,
    by rw [hr', Res.addW_q]; exact hF⟩
  · rw [hr', Res.addW_X_self, hq]; exact .inr ⟨by decide, rfl⟩
  · rw [hr', Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · rw [hX p hp]; exact Nat.zero_le _
    · exact Nat.le_refl _

/-- **VC `incl`, the load**: every load outcome of `Fl` keeps `W2I` (the
`EnvGLR` load keeps the resource and `vwOld`, and re-anchors the ghost). -/
theorem vc_incLoad {P : Params} (tid : Nat) (σ : EStateX) (h : W2I P σ) :
    ∀ v (σ' : EStateX), (EW P tid).step (.load .plain false P.f 4) σ v σ' → W2I P σ' := by
  intro v σ' hs
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := step_loadFactsLR (I := isa) (pl := mpIncPlan P) hs
  obtain ⟨hw, hown⟩ := h
  refine ⟨WorldWI.anchor hw hanc, ?_⟩
  unfold Own1 at hown ⊢
  rw [hr, hlv.vwOld]
  exact hown

/-- **VC `incl`, the store**: from `W2I`, the store of **any** value to `Fl`
is permitted (a planned release under `Arch.tso`; `φI` is impure at every
value; `Fl` kept; the uniform obligation from `Own1`), and every outcome
keeps `W`. -/
theorem vc_incStore {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W2I P σ) (v : Val) :
    (EW P tid).ok (.store .plain false P.f 4 v) σ ∧
      ∀ b (σ' : EStateX), (EW P tid).step (.store .plain false P.f 4 v) σ b σ' → W3I P σ' := by
  obtain ⟨⟨hrel, hpure⟩, hq, ⟨ts, hX, hmax, hts⟩, hW, hF⟩ := h
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  have hWd : P.W ≠ P.Dt := hL.wd
  refine ⟨⟨⟨rfl, hF, fun hr => absurd hr (by rw [mpIncPlan_rel_Fl]; decide), fun _ => ⟨.inl rfl, ?_, ?_, ?_⟩⟩,
    by simp [SharedEnv.AccessIn]⟩, ?_⟩
  · rw [hrel]; exact flagPredI_impure v
  · simp [mpIncPlan, Plan.gives, Plan.find?, hne]
  · intro c g _ hwb
    have hlt := hwb.rel rfl
    rw [hrel]
    refine fun _ => ⟨by simp [mpIncPlan, Plan.give, Plan.find?, Plan.Entry.give, Res.only, hq], ts,
      by simpa [mpIncPlan, Plan.give, Plan.find?, Plan.Entry.give, Res.only] using hX,
      fun p hp => hmax p (by simpa [mpIncPlan, Plan.give, Plan.find?, Plan.Entry.give, Res.only] using hp), ?_⟩
    simp only [Time, View] at *; omega
  · intro b σ' hs
    obtain ⟨c, tw, hanc, -, -, -, -, hr, -⟩ := stepLR_storeFacts (I := isa) hs
    obtain ⟨_, -, hr⟩ := hr
    refine ⟨WorldWI.anchor ⟨hrel, hpure⟩ hanc, ?_⟩
    rw [hr]
    simp [Plan.after, Plan.keep, mpIncPlan, Plan.find?, Plan.Entry.keep, Res.drop, hWd, hW]

/-! ## The reader's VCs (`X64MpSmoke`'s, with `WorldRI`) -/

/-- Before the flag load: the world, and no forwarding item for `Fl`. -/
def R1I (P : Params) (σ : EStateX) : Prop := WorldRI P σ.r σ.g ∧ σ.vs.getFwd P.Fl = none

/-- Before the data load: the world, and a flag message with a non-zero low
word at the snapshot, at or below `vrNew`. -/
def R3I (P : Params) (σ : EStateX) : Prop :=
  WorldRI P σ.r σ.g ∧ ∃ tsF vF, σ.snap.mem.read? P.Fl tsF = some vF ∧ BitVec.setWidth 32 vF ≠ 0 ∧ tsF ≤ σ.vs.vrNew

/-- At the end: the world and a seen flag message with a non-zero low word. -/
def R4I (P : Params) (σ : EStateX) : Prop :=
  WorldRI P σ.r σ.g ∧ ∃ tsF vF, σ.snap.mem.read? P.Fl tsF = some vF ∧ BitVec.setWidth 32 vF ≠ 0

theorem WorldRI.anchor {P : Params} {tid : Nat} {σ σ' : EStateX} {c : Config isa} (h : WorldRI P σ.r σ.g)
    (hanc : AnchorOk tid σ c σ'.g) (hr : σ'.r = σ.r) : WorldRI P σ'.r σ'.g :=
  WorldRG.anchor (φ := φI P) h hanc hr

/-- **VC R1** (`movl (%rdi), %eax`, an acquire under `Arch.tso`). -/
theorem vc_r1I {P : Params} (tid : Nat) (σ : EStateX) (h : R1I P σ) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false P.f 4) σ v σ' →
      R1I P σ' ∧ (BitVec.setWidth 32 v ≠ 0 → R3I P σ') :=
  vc_r1G (φ := φI P) tid σ h

/-- **VC R3** (`movl (%rsi), %ebx`): under the clean erasure of the load's
anchor, the data load returns `42`. -/
theorem vc_r3I {P : Params} (tid : Nat) (σ : EStateX) (h : R3I P σ) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false P.d 4) σ v σ' → σ'.cl → v = dataVal :=
  vc_r3G (flagPredI_law _) tid σ h

/-- **VC R3, the world part.** -/
theorem vc_r3_worldI {P : Params} (tid : Nat) (σ : EStateX) (h : R3I P σ) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false P.d 4) σ v σ' → R4I P σ' :=
  vc_r3_worldG (φ := φI P) tid σ h

end Kraken.Promising.X64.EnvG.MpInc
