/-
**Smoke test of `EnvGLRV`: the `mp_incl.kl` writer with its flag value
tracked**. The writer `movl $42, (%rsi); incl
(%rdi)` of `X64MpInc.lean` on `EnvGLRVX` instead of `EnvGLRX`: the same
plan (`mpIncPlan`, every store to `Fl` a release giving `Dt`), the same
flag predicate (`φI`), and additionally the writer's permission for `Fl`.

The writer holds all of `Fl` with the initial write set `{(0, 0)}`
(`FlInit`, from `writerRes` and `initVal Fl = 0`). Its `incl` load runs in
`EnvGLRV`, whose `cl` gains `ClAtV`, so under `cl` the value read is in that
write set (`X_of_read_clAtV`): `0`. So under `cl` the `incl` store writes
`1`, and at the end the writer holds all of `Fl` with maximal write
`(1, tw)` (`FlFin`): exactly what the final argument needs for `[f]=1`
(`Erase.finalVal_of_max`), and what `X64MpInc.lean` could not state.

- `FlInit`, `FlFin`, `W1V`, `W2V`, `W3V`; `EWV` (`EnvGLRVX` on `mpS`);
- `vc_w1V`, `vc_incLoadV` (the value read is `0` under `cl`),
  `vc_incStoreV` (`FlFin` under `cl`);
- `mpIncWriterXV_envG`: the writer by one `vcgen [inc32_shared_spec]` call;
- `mpIncRuleWV`: its rule through `ThreadRuleRX.ofSafelyEnvGLRVX`, with the
  writer's postcondition `MpPostWV` (the writer half of `MpPostI` plus
  `FlFin`), and `mpIncRuleWV_noFault`.

Not done: the two-thread theorem with
`[f]=1`, which also needs the reader's postcondition to pin its acquire id
(so that the final argument can tell the writer's resource from the
reader's).
-/
import Kraken.Promising.SLR.EnvG.LRValX64VCGen
import Kraken.Promising.SLR.EnvG.LRValRead
import Kraken.Promising.SLR.EnvG.X64MpIncLink

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp
open Kraken.Promising.X64.EnvG.MpSmoke Kraken.Promising.X64.EnvG.MpLink

namespace Kraken.Promising.X64.EnvG.MpIncV

open Kraken.Promising.X64.EnvG.MpInc

/-! ## The flag permission -/

/-- All of `Fl`, with the initial write set `{(0, 0)}`. -/
def FlInit (P : Params) (r : Res) : Prop := (r.wr P.Fl).q = 1 ∧ ∀ p, (r.wr P.Fl).X p → p = (0, 0)

/-- All of `Fl`, with maximal write `(1, tw)`. -/
def FlFin (P : Params) (r : Res) : Prop :=
  (r.wr P.Fl).q = 1 ∧ ∃ tw, (r.wr P.Fl).X (1#128, tw) ∧ ∀ p, (r.wr P.Fl).X p → p.2 ≤ tw

/-- The writer's environment: `EnvGLRV` on `mpS` (`Arch.tso`). -/
abbrev EWV (P : Params) (tid : Nat) : SharedEnv := EnvGLRVX Arch.tso tid (mpIncPlan P) (mpS P)

/-- Before the data store. -/
def W1V (P : Params) (σ : EStateX) : Prop := W1I P σ ∧ FlInit P σ.r

/-- Before `incl`. -/
def W2V (P : Params) (σ : EStateX) : Prop := W2I P σ ∧ FlInit P σ.r

/-- After the release: `W3I`, and under `cl` the flag's final write. -/
def W3V (P : Params) (σ : EStateX) : Prop := W3I P σ ∧ (σ.cl → FlFin P σ.r)

theorem mpIncPlan_whole (P : Params) : ∀ e ∈ (mpIncPlan P).entries, e.split = none := by
  simp [mpIncPlan]

theorem mpIncPlan_not_gives {P : Params} (hL : MpLocs P) : ∀ l' v', P.Fl ∉ (mpIncPlan P).gives l' v' := by
  intro l' v'
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  by_cases h : P.Fl = l'
  · subst h; simp [mpIncPlan, Plan.gives, Plan.find?, hne]
  · simp [mpIncPlan, Plan.gives, Plan.find?, List.find?, h]

/-- A store to `Fl` adds the message to `Fl`'s write set. -/
theorem after_wr_Fl {P : Params} (hL : MpLocs P) (w : Val) (tw : Time) (Q : Prop) (r : Res) :
    ((mpIncPlan P).after P.Fl w tw Q r).wr P.Fl = (r.wr P.Fl).addW (w, tw) := by
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  simp [Plan.after, Plan.keep, mpIncPlan, Plan.find?, Plan.Entry.keep, Res.drop, Res.addW, hne, Plan.rel]

/-! ## The writer's VCs -/

/-- **VC W1** (`movl $42, (%rsi)`): `vc_w1I`, and `Fl`'s permission is
untouched. -/
theorem vc_w1V {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W1V P σ) {a : BitVec 64}
    {v : Val} (ha : a = P.d) (hv : v = dataVal) :
    (EWV P tid).ok (.store .plain false a 4 v) σ ∧
      ∀ b (σ' : EStateX), (EWV P tid).step (.store .plain false a 4 v) σ b σ' → W2V P σ' := by
  subst ha hv
  obtain ⟨hok, hst⟩ := vc_w1I hL tid σ h.1
  refine ⟨hok, fun b σ' hs => ⟨hst b σ' hs, ?_⟩⟩
  obtain ⟨c, tw, -, -, -, -, -, hr, -⟩ := stepLRV_storeFacts (I := isa) hs
  obtain ⟨_, -, hr⟩ := hr
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  have e : σ'.r.wr P.Fl = σ.r.wr P.Fl := by
    rw [hr, Plan.after, mpIncPlan_rel_ne hne]
    exact Res.addW_wr_ne _ _ hne
  unfold FlInit; rw [e]; exact h.2

/-- **VC `incl`, the load**: `W2V` is kept, and **under `cl` the value read
is `0`** (`X_of_read_clAtV`: the writer holds all of `Fl`, whose write set
is `{(0, 0)}`). -/
theorem vc_incLoadV {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W2V P σ) {a : BitVec 64}
    (ha : a = P.f) :
    ∀ v (σ' : EStateX), (EWV P tid).step (.load .plain false a 4) σ v σ' →
      W2V P σ' ∧ (σ'.cl → v = 0) := by
  subst ha
  intro v σ' hs
  obtain ⟨hanc, hr, hcl, tr, hrd, hlv, -⟩ := step_loadFactsLRV (I := isa) (pl := mpIncPlan P) hs
  obtain ⟨⟨hw, hown⟩, hfl⟩ := h
  refine ⟨⟨⟨WorldWI.anchor hw hanc, ?_⟩, by rw [hr]; exact hfl⟩, fun hc => ?_⟩
  · unfold Own1 at hown ⊢
    rw [hr, hlv.vwOld]
    exact hown
  · rw [hcl] at hc
    have hno : tr ∉ ownProm tid σ'.snap := fun hm => by
      have := hrd.notOwn
      simp [hm] at this
    have hX := X_of_read_clAtV hc.2 hanc.lt hfl.1 (mpIncPlan_not_gives hL) (mpIncPlan_whole P) hrd.val hno
    have := hfl.2 _ hX
    simp only [Prod.mk.injEq] at this
    exact this.1

/-- **VC `incl`, the store**: `vc_incStore`, and under `cl` (where the value
read was `0`) the writer ends with `FlFin`. -/
theorem vc_incStoreV {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (v : Val)
    (h : W2V P σ ∧ (σ.cl → v = 0)) {a : BitVec 64} (ha : a = P.f) :
    (EWV P tid).ok (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) σ ∧
      ∀ b (σ' : EStateX), (EWV P tid).step (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) σ b σ' →
        W3V P σ' := by
  subst ha
  obtain ⟨⟨hW2, hfl⟩, hv⟩ := h
  obtain ⟨hok, hst⟩ := vc_incStore hL tid σ hW2 ((v.setWidth 32 + 1).setWidth 128)
  refine ⟨hok, fun b σ' hs => ⟨hst b σ' hs, fun hc => ?_⟩⟩
  obtain ⟨c, tw, -, -, -, -, -, hr, hcl, -⟩ := stepLRV_storeFacts (I := isa) hs
  obtain ⟨_, -, hr⟩ := hr
  rw [hcl] at hc
  have hv0 : (v.setWidth 32 + 1).setWidth 128 = (1#128 : Val) := by rw [hv hc]; decide
  have e : σ'.r.wr P.Fl = (σ.r.wr P.Fl).addW (1#128, tw) := by rw [hr, after_wr_Fl hL, hv0]
  refine ⟨by rw [e]; exact hfl.1, tw, ?_, fun p hp => ?_⟩
  · rw [e]; exact .inr ⟨by rw [hfl.1]; decide, rfl⟩
  · rw [e] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · rw [hfl.2 p hp]; exact Nat.zero_le _
    · exact Nat.le_refl _

/-! ## The writer by `vcgen` -/

theorem W1V.fence {P : Params} {σ σ' : EStateX} (h : W1V P σ) (hf : FenceLe σ σ') : W1V P σ' :=
  ⟨W1I.fence h.1 hf, by unfold FlInit; rw [hf.r]; exact h.2⟩

variable [layout : _root_.Layout]

section Writer

local instance mpIncWriterXV.env : CodeEnv := ⟨layout mpIncWriterX⟩

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- **The x64 MP `incl` writer on `EnvGLRVX`**: from `W1V` the writer ends
in `W3V` (`FlFin` under `cl`). -/
theorem mpIncWriterXV_envG (P : Params) (hL : MpLocs P) (tid : Nat) :
    TripleEnv (EWV P tid)
      (fun s σ => s.regs.get64 .rdi = P.f ∧ s.regs.get64 .rsi = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
        Mem.loadInt s.dmem P.d 4 = none ∧ W1V P σ)
      mpIncWriterX (fun _ σ => W3V P σ) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold mpIncWriterX
  vcgen [inc32_shared_spec]
  case vc1 s σ hpre =>
    obtain ⟨-, hx1, -, hdd, -⟩ := hpre
    simp [hx1, hdd]
  case vc2 s σ hpre =>
    obtain ⟨-, hx1, -, -, hW⟩ := hpre
    exact (vc_w1V hL tid σ hW (by simp [hx1]) (by decide)).1
  case vc3 s σ hpre _ _ _ =>
    obtain ⟨hx0, -, hdf, -, -⟩ := hpre
    simp [hx0, hdf]
  case vc4 s σ hpre _ _ _ =>
    obtain ⟨hx0, -, -, -, -⟩ := hpre
    exact ⟨trivial, by simp [SharedEnv.AccessIn, hx0]⟩
  case vc5 s σ hpre b σ1 hst v σ2 hld =>
    obtain ⟨hx0, hx1, -, -, hW⟩ := hpre
    have hW2 := (vc_w1V hL tid σ hW (by simp [hx1]) (by decide)).2 b σ1 hst
    have hW2' := vc_incLoadV hL tid σ1 hW2 (by simp [hx0]) v σ2 hld
    have hS := vc_incStoreV hL tid σ2 v hW2' (a := s.regs.get64 .rdi + Int64.toBitVec 0) (by simp [hx0])
    exact ⟨hS.1, fun _ g'' hs' _ _ _ => Eventually.done _ (Or.inl ⟨rfl, hS.2 _ g'' hs'⟩)⟩

end Writer

/-! ## The writer's rule -/

section Rule

variable [Executable.ValidLayout (layout mpIncWriterX)]

/-- **The writer's postcondition with the flag tracked**: the writer half of
`MpPostI` and `FlFin`. -/
def MpPostWV (P : Params) (rd : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  MpPostI P rd c r g ∧ FlFin P r

/-- The writer's postcondition: the end of its text and `W3V`. -/
abbrev postWV (P : Params) : MachineState × EStateX → Prop := postOfX mpIncWriterX fun _ σ => W3V P σ

omit [Executable.ValidLayout (layout mpIncWriterX)] in
/-- **`hB` for the writer**: the token `W` and, under `cl`, `FlFin`. -/
theorem hB_WV (P : Params) (tid rd : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postWV P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpIncPlan P) σ c t r g cl → cl → MpPostWV P rd c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, hW, hF⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨.inl hW.2, hF (hrel.cl hcl)⟩
  · rw [hp] at hts; cases hts

/-- **The x64 `incl` writer's rule on `EnvGLRV`** (`Arch.tso`). -/
def mpIncRuleWV (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPostWV P rd) tid :=
  ThreadRuleRX.ofSafelyEnvGLRVX (S := mpS P) (post := postWV P) (mpIncPlan_valid hL) (mpIncPlan_whole P)
    (mpS_le16 P) mpIncWriterX_lr postOfX_end (not_instrStepEnv_of_end_labels _ 0) (hB_WV P tid rd)

/-- **The writer's rule excludes faults.** -/
theorem mpIncRuleWV_noFault (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    NoFaultRule (mpIncRuleWV P hL tid rd) :=
  noFaultRule_ofSafelyEnvGLRVX_struct _ _ _ _ _ _ _ mpIncWriterX_noFault

end Rule

end Kraken.Promising.X64.EnvG.MpIncV
