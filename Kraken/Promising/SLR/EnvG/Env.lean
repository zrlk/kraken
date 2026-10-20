/-
**The `EnvG` environment**: the whole-thread SLR environment of thread `tid`
under the plan `pl`, as a `SharedEnv`. ISA-neutral.

- `step` is the outcome predicates of `EnvG/Facts.lean` (`LoadOut`,
  `StoreOut`, `RmwOut`, `FenceOut`): every access re-anchors (§1a) and runs
  the machine's own rule on `envCtx` with `iv0`.
- `ok`: loads and fences are always permitted. A store (`StoreOk`) needs a
  positive permission for its location, and either purity of the location's
  release predicate at the value (not a planned release) or, for a planned
  release, the effective release kind (`effRel`, §3), impurity, a kept
  location, and the **uniform release obligation** (`RelOb`, §1d): the
  location's release predicate holds of what the plan gives away, at every
  admissible re-anchor and the fresh timestamp above it. An RMW (`RmwOk`)
  likewise for its write at every read the environment offers, plus the claim
  condition (`ClaimOk`: an RMW that claims update slots is acquire-release, or
  an acquire whose read is not forwarded).
- `step_loadFacts`, `step_storeFacts`, `step_rmwFacts`, `step_fenceFacts`:
  every outcome satisfies its facts.
- `PrepayGeneric`: the statement of the generic prepay theorem (§1d) at a
  store node, which the rule link proves (`Prop` definition, open-statement convention).
- F1: what a planned release gives away is
  `pl.give l v σ.cl …`, split by the thread's current knowledge; a prepay's
  resource is `pl.after … σ.cl σ.r` (the knowledge is fixed at the prepay).
  A release RMW's entry must be whole (`Plan.Whole` in `RmwOk`, phase-1
  limit: no splits on RMW releases).

Phase 1: single-access trees only (§1b).
-/
import Kraken.SharedEnv
import Kraken.Promising.SLR.EnvG.Facts
import Kraken.Promising.SLR.EnvG.Plan

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Permissions -/

/-- **The uniform release obligation** (§1d) of a planned release of `v` to
`l` with store kind `k`, giving away `R`: at every admissible re-anchor
`(c, g)`, for the fresh timestamp `|M| + 1` above the env's write bound, the
location's release predicate holds of `R` at the message. A prepayment uses
it at the promise's configuration, a fresh store at its anchor. -/
def RelOb (A : Arch) (tid : Nat) (σ : State I) (k : StoreKind) (l : Loc) (v : Val) (R : Res) : Prop :=
  ∀ (c : Config I) (g : Ghost), AnchorOk tid σ c g → WriteBound A σ.vs k l (c.mem.last + 1) →
    (σ.g.rel l).P v (c.mem.append ⟨l, v, tid⟩).1 (c.mem.last + 1) R

/-- **A store's permission**: non-exclusive, a positive permission for `l`,
and a pure message (not a planned release) or a planned release of effective
kind `.rel`, with an impure value (so it cannot fulfil an old, non-pending
promise: `Erase.pure`), a kept location, and the uniform obligation. -/
def StoreOk (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) :
    Prop :=
  xcl = false ∧ 0 < (σ.r.wr l).q ∧
    (pl.rel l v = false → Pred.Pure (σ.g.rel l) v) ∧
    (pl.rel l v = true → effRel A σ k ∧ ¬ Pred.Pure (σ.g.rel l) v ∧ l ∉ pl.gives l v ∧
      RelOb A tid σ k l v (pl.give l v σ.cl σ.r))

/-- **The claim condition** of an RMW of kind `k` reading `(l, tr)` from views
`vs`: it is acquire-release (`rmw_tr_le_wfloor_acqRel`), or an acquire whose
read is not forwarded (`rmw_tr_le_wfloor_acq`). Either bounds the floor after
the RMW by `tr` (K1). -/
def ClaimOk (A : Arch) (k : RmwKind) (vs : Views) (l : Loc) (tr : Time) : Prop :=
  A.rmwKind k = .acqRel ∨ ((A.loadKind (A.rmwKind k).loadKind).isAcquire = true ∧ ¬ Fwded vs l tr)

/-- **An RMW's permission** (live: `noRet = false`): a positive permission for
`l`, and at every admissible re-anchor `(c, g)` and every read `(tr, old)` the
environment offers with a successful operation: the claim condition when the
read message has update slots, and a pure written value (not a planned
release) or a planned release of effective kind `.rel`, with an impure value,
a kept location, a whole-location plan entry (`Plan.Whole`: no split, see
below), and the release obligation for what the plan gives away of the
resource with the claimed slots.

**Phase-1 limit (F1):** a release RMW's plan entry has no split. The link of
an in-flight release RMW (`Plan.after_op_claim`, `EnvG/LinkR.lean`) and its
prepay (`Plan.give_op_of_unit`, `EnvG/PrepayRmw.lean`) reconcile the prepay's
split of `σ.r` with the env's split of `σ.r ⋅ C` (`C` the claimed update
slots) by the homomorphism laws of `Res.only`/`Res.drop`, which a general
`(cl, r)`-dependent split does not satisfy. Store releases may split. -/
def RmwOk (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : RmwKind) (l : Loc) (op : Val → Option Val) :
    Prop :=
  0 < (σ.r.wr l).q ∧
    ∀ (c : Config I) (g : Ghost) (tr : Time) (old new : Val), AnchorOk tid σ c g →
      ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old → op old = some new →
      (claimedSlots g l tr ≠ [] → ClaimOk A k σ.vs l tr) ∧
      (pl.rel l new = false → Pred.Pure (σ.g.rel l) new) ∧
      (pl.rel l new = true → effRelRmw A k ∧ ¬ Pred.Pure (σ.g.rel l) new ∧ l ∉ pl.gives l new ∧ pl.Whole l new ∧
        (tr < c.mem.last + 1 → WriteBound A σ.vs (A.rmwKind k).storeKind l (c.mem.last + 1) →
          (σ.g.rel l).P new (c.mem.append ⟨l, new, tid⟩).1 (c.mem.last + 1)
            (pl.give l new σ.cl (σ.r.op (Res.prod ((claimedSlots g l tr).map (·.res)))))))

/-! ## The environment -/

/-- **The whole-thread SLR environment** of thread `tid` under the plan `pl`
(§4.1). -/
def _root_.Kraken.Promising.SLR.EnvG (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv where
  State := State I
  ok a σ := match a with
    | .load .. => True
    | .fence _ => True
    | .store k xcl addr n v => StoreOk A tid pl σ k xcl ⟨addr, n⟩ v
    | .rmw k addr n op => RmwOk A tid pl σ k ⟨addr, n⟩ op
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOut A tid σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

@[simp] theorem envG_ok_load (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : LoadKind) (xcl : Bool)
    (addr : BitVec 64) (n : Nat) : (EnvG I A tid pl).ok (.load k xcl addr n) σ := trivial

@[simp] theorem envG_ok_fence (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : FenceKind) :
    (EnvG I A tid pl).ok (.fence k) σ := trivial

/-! ## View lemmas -/

theorem readPre_iv0 (A : Arch) (c : Ctx) (k : LoadKind) :
    readPre A iv0 c k = max c.views.vrNew (if (A.loadKind k == .acq) = true then c.views.vRel else 0) := by
  simp [readPre, iv0]

theorem readBound_eq (A : Arch) (c : Ctx) (k : LoadKind) (l : Loc) :
    max (readPre A iv0 c k) (c.views.getCoh l) = readBound A c.views k l := by
  rw [readPre_iv0]; rfl

theorem readView_of_not_fwded (A : Arch) (k : LoadKind) {vs : Views} {l : Loc} {t : Time} (h : ¬ Fwded vs l t) :
    readView A k (vs.getFwd l) t = t := by
  unfold readView
  cases hf : vs.getFwd l with
  | none => rfl
  | some f =>
    have : f.time ≠ t := fun e => h ⟨f, hf, e⟩
    simp [this]

theorem VLe.of_setCoh (vs : Views) (l : Loc) (t : View) : ∀ l', vs.getCoh l' ≤ (vs.setCoh l t).getCoh l' := by
  intro l'
  rw [Views.getCoh_setCoh]
  split
  · next h => subst h; omega_t
  · exact Nat.le_refl _

theorem vle_readNext (A : Arch) (iv : InstrViews) (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool)
    (t : Time) (v : Val) : VLe c.views (readNext A iv c k xcl l noRet t v).views := by
  refine ⟨fun l' => VLe.of_setCoh _ _ _ l', ?_, ?_, ?_, ?_, Nat.le_refl _, Nat.le_refl _, ?_, Nat.le_refl _⟩
  all_goals simp only [readNext]
  all_goals (try split)
  all_goals omega_t

theorem vle_afterWrite (A : Arch) (iv : InstrViews) (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val)
    (t : Time) (νfwd : View) (ful : Bool) : VLe c.views (afterWrite A iv c k xcl l v t νfwd ful).views := by
  refine ⟨fun l' => VLe.of_setCoh _ _ _ l', Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
  all_goals simp only [afterWrite]
  all_goals (try split)
  all_goals omega_t

theorem vle_fenceViews (vs : Views) (k : FenceKind) : VLe vs (fenceViews vs k) := by
  cases k <;>
  exact ⟨fun _ => Nat.le_refl _, by simp [fenceViews, fenceStep] <;> omega_t, Nat.le_refl _, Nat.le_refl _,
    by simp [fenceViews, fenceStep] <;> omega_t, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem fenceViews_fwdb (vs : Views) (k : FenceKind) : (fenceViews vs k).fwdb = vs.fwdb := by
  cases k <;> rfl

theorem fenceViews_getCoh (vs : Views) (k : FenceKind) (l : Loc) : (fenceViews vs k).getCoh l = vs.getCoh l := by
  cases k <;> rfl

theorem fenceViews_getFwd (vs : Views) (k : FenceKind) (l : Loc) : (fenceViews vs k).getFwd l = vs.getFwd l := by
  cases k <;> rfl

theorem vle_fenceStep (cx : Ctx) (k : FenceKind) : VLe cx.views (fenceStep cx k).views := by
  rw [fenceStep_views]; exact vle_fenceViews _ _

theorem vle_fenceOpt (A : Arch) (cx : Ctx) : VLe cx.views (fenceOptCtx A cx).views := by
  unfold fenceOptCtx; split
  · exact vle_fenceStep _ _
  · exact VLe.refl _

theorem fenceOptCtx_views (A : Arch) (cx : Ctx) : (fenceOptCtx A cx).views = rmwReadViews A cx.views := by
  unfold fenceOptCtx rmwReadViews; split
  · exact fenceStep_views _ _
  · rfl

theorem rmwReadViews_getFwd (A : Arch) (vs : Views) (l : Loc) : (rmwReadViews A vs).getFwd l = vs.getFwd l := by
  unfold rmwReadViews; split
  · exact fenceViews_getFwd _ _ _
  · rfl

theorem vle_rmwPost (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (cx : Ctx) :
    VLe cx.views (rmwPost A k noRet l cx).views := by
  unfold rmwPost; split
  · exact ⟨fun _ => Nat.le_refl _, by simp; omega_t, Nat.le_refl _, Nat.le_refl _, by simp; omega_t,
      Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  · exact VLe.refl _

theorem vle_rmwAfter (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (cx : Ctx) :
    VLe cx.views (rmwAfter A k noRet l cx).views := by
  unfold rmwAfter; split
  · exact (vle_rmwPost A k noRet l cx).trans (vle_fenceStep _ _)
  · exact vle_rmwPost A k noRet l cx

/-! ## Write events -/

theorem count_erase_eq {l : List Time} {a b : Time} (ha : a ∈ l) (h : l.erase a = l.erase b) :
    a = b := by
  refine Classical.byContradiction fun hne => ?_
  have h1 := congrArg (List.count a) h
  rw [List.count_erase_self, List.count_erase_of_ne hne] at h1
  have := List.count_pos_iff.mpr ha
  omega

theorem last_append_ne {m : Memory} {w : Msg} (h : (m.append w).1 = m) : False := by
  have h1 := congrArg (fun m : Memory => m.msgs.size) h
  simp only [Memory.append, Array.size_push] at h1
  omega

/-- The views after an `afterWrite` from views `vs` at `tw` (the store kind
already converted by `A.storeKind`, as `writeSuccs` passes it). -/
theorem writeViews_afterWrite (A : Arch) (iv : InstrViews) (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc)
    (v : Val) (t : Time) (νfwd : View) (ful : Bool) :
    WriteViews A c.views (afterWrite A iv c (A.storeKind k) xcl l v t νfwd ful).views k l t := by
  refine ⟨vle_afterWrite _ _ _ _ _ _ _ _ _ _, ?_, ?_, ⟨{ time := t, view := νfwd, xcl }, ?_, rfl⟩, fun l' hl' => ?_⟩
  · simp only [afterWrite_getCoh, ↓reduceIte]; omega_t
  · intro hk
    simp only [afterWrite]
    split
    · next h => exact absurd (by revert h; cases A.storeKind k <;> decide) hk
    · omega_t
  · simp only [afterWrite_getFwd, ↓reduceIte]
  · simp only [afterWrite_getFwd, hl', ↓reduceIte]

/-- A `writeSuccs` outcome passes `WriteOk` at the timestamp of any
`WriteEv` for it, and its views are those of a write at that timestamp. -/
theorem writeSuccs_at (A : Arch) (tid : Nat) {iv : InstrViews} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc}
    {v : Val} {trOpt : Option Time} {extra : View} {c2 : Ctx} {tw : Time}
    (hc : c2 ∈ writeSuccs A tid iv c k xcl l v trOpt extra) (hev : WriteEv tid c c2 l v trOpt tw) :
    WriteOk A tid iv c k l trOpt extra tw ∧ WriteViews A c.views c2.views k l tw := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, ht, w, hw, -, -, -, hok, rfl⟩ | ⟨hok, rfl⟩
  · -- fulfil
    rcases hev.cases with ⟨-, htw, -⟩ | ⟨hm, -⟩
    · have e : t = tw := count_erase_eq ht hev.prom
      subst e
      exact ⟨hok, writeViews_afterWrite A iv c k xcl l v t _ true⟩
    · exact absurd hm.symm (fun h => last_append_ne h)
  · rcases hev.cases with ⟨hm, -, -⟩ | ⟨-, rfl⟩
    · exact absurd hm (fun h => last_append_ne h)
    · exact ⟨hok, writeViews_afterWrite A iv
        { c with mem := (c.mem.append { loc := l, val := v, tid }).1, prom := c.prom ++ [c.mem.last + 1], promisedNow := c.promisedNow ++ [({ loc := l, val := v, tid }, max (writePre A iv c k extra) (c.views.getCoh l))] }
        k xcl l v (c.mem.last + 1) _ false⟩

/-- `WriteOk` with no instruction views gives the env's write bound, for any
views below the context's. -/
theorem writeBound_of_writeOk (A : Arch) (tid : Nat) {c : Ctx} {k : StoreKind} {l : Loc} {trOpt : Option Time}
    {extra : View} {tw : Time} (h : WriteOk A tid iv0 c k l trOpt extra tw) {vs : Views} (hle : VLe vs c.views) :
    WriteBound A vs k l tw := by
  obtain ⟨h, -⟩ := h
  simp only [writePre] at h
  have := hle.vwNew; have := hle.vCAP; have := hle.coh l; have := hle.vrOld; have := hle.vrOldNR
  have := hle.vwOld
  refine ⟨by omega_t, by omega_t, by omega_t, fun hk => ?_⟩
  have e : (A.storeKind k == .rel) = true := by rw [hk]; rfl
  simp only [e, ↓reduceIte] at h
  omega_t

/-! ## Facts of the outcomes -/

theorem loadViews_readNext (A : Arch) (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (t : Time) (v : Val) :
    LoadViews A c.views (readNext A iv0 c k xcl l false t v).views k l t := by
  refine ⟨vle_readNext .., rfl, rfl, rfl, fun hf => ?_, fun hf => ?_, fun ha hf => ?_⟩
  · have e : (readNext A iv0 c k xcl l false t v).views.getCoh l =
        (c.views.setCoh l (max (readPre A iv0 c k) (readView A (A.loadKind k) (c.views.getFwd l) t))).getCoh l :=
      rfl
    rw [e, Views.getCoh_setCoh, readView_of_not_fwded A _ hf]
    simp only [↓reduceIte]
    omega_t
  · simp only [readNext, Bool.false_eq_true, ↓reduceIte, readView_of_not_fwded A _ hf]
    omega_t
  · simp only [readNext, ha, ↓reduceIte, readView_of_not_fwded A _ hf]
    constructor <;> omega_t

/-- Where a write from a context on the anchor `c` lands. -/
theorem writeSnap_of {tid : Nat} {c : Config I} {cx0 cx' : Ctx} {l : Loc} {v : Val} {trOpt : Option Time}
    {tw : Time} {c' : Config I} (hm : cx0.mem = c.mem) (hp : cx0.prom = ownProm tid c)
    (hsnap : c' = snapAfter tid c cx') (hev : WriteEv tid cx0 cx' l v trOpt tw) : WriteSnap tid c c' l v tw := by
  subst hsnap
  refine ⟨?_, ?_⟩
  · rcases hev.cases with ⟨hm', htw, hg⟩ | ⟨hm', htw⟩
    · exact .inl ⟨hm'.trans hm, hm ▸ hg, hp ▸ htw⟩
    · exact .inr ⟨by simp only [snapAfter]; rw [hm', hm], hm ▸ htw⟩
  · simp only [snapAfter]
    rw [hev.prom, hp]

/-- A planned release outcome that does not fulfil an own outstanding promise
appends. -/
theorem fresh_of_not_own {tid : Nat} {c : Config I} {cx0 cx' : Ctx} {l : Loc} {v : Val} {trOpt : Option Time}
    {tw : Time} (hm : cx0.mem = c.mem) (hp : cx0.prom = ownProm tid c) (hev : WriteEv tid cx0 cx' l v trOpt tw)
    {P : Prop} (h : tw ∉ ownProm tid c ∨ P) : tw = c.mem.last + 1 ∨ P := by
  rcases h with hn | h
  · rcases hev.cases with ⟨-, htw, -⟩ | ⟨-, htw⟩
    · exact absurd (hp ▸ htw) hn
    · exact .inl (hm ▸ htw)
  · exact .inr h

theorem loadOut_facts {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc} {v : Val}
    (h : LoadOut A tid σ σ' k xcl l v) : LoadFacts A tid σ σ' k l v := by
  obtain ⟨hanc, hr, hcl, tr, cx', hx, hvs, hseen, hfR, hfW⟩ := h
  obtain ⟨t, v', he, -, hrd, hwi, hp⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rw [readBound_eq] at hwi
  exact ⟨hanc, hr, hcl, tr, ⟨hrd, hp, hwi⟩, by rw [hvs]; exact loadViews_readNext A (envCtx tid σ.vs σ'.snap) k xcl l tr v, hseen, hfR, hfW⟩

theorem storeOut_facts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {b : Bool} (h : StoreOut A tid pl σ σ' k xcl l v b) : StoreFacts A tid pl σ σ' k l v := by
  obtain ⟨-, -, c, cx', tw, hanc, hc, hev, -, hrelp, hsnap, hvs, hr, hcl, hseen, hfR, hfW⟩ := h
  obtain ⟨hok, hwv⟩ := writeSuccs_at A tid hc hev
  refine ⟨c, tw, hanc, writeSnap_of rfl rfl hsnap hev, writeBound_of_writeOk A tid hok (VLe.refl _),
    by rw [hvs]; exact hwv, fun hrel => fresh_of_not_own rfl rfl hev (hrelp hrel), hr, hcl, hseen, hfR, hfW⟩

theorem rmwOut_facts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {old : Val} (h : RmwOut A tid pl σ σ' k l op old) : RmwFacts A tid pl σ σ' k l op old := by
  obtain ⟨c, x, hanc, hx, hold, hcl, hseen, hfR, hfW, hbr⟩ := h
  obtain ⟨t, v', rfl, -, hrd, hwi, hp⟩ := (mem_readSuccs A).mp hx
  simp only at hold hseen hbr
  subst hold
  have hc0v := fenceOptCtx_views A (envCtx tid σ.vs c)
  obtain ⟨hc0m, hc0p⟩ := fenceOptCtx_memProm A (envCtx tid σ.vs c)
  have hlv := loadViews_readNext A (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l t v'
  have hle2 : VLe σ.vs (readNext A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l false t
      v').views := (vle_fenceOpt A _).trans hlv.mono
  rw [readBound_eq, hc0v, hc0m] at hwi
  rw [hc0m] at hrd
  rw [hc0p] at hp
  have hfw : ∀ {vs : Views}, vs.getFwd l = σ.vs.getFwd l → ¬ Fwded σ.vs l t → ¬ Fwded vs l t :=
    fun e hn ⟨f, hf, ht⟩ => hn ⟨f, e ▸ hf, ht⟩
  have hfw0 : (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd l = σ.vs.getFwd l := by
    rw [hc0v]; exact rmwReadViews_getFwd A σ.vs l
  -- the views after the RMW are above the read's
  have hpost : VLe (readNext A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l false t
      v').views σ'.vs := by
    rcases hbr with ⟨-, -, hvs, -⟩ | ⟨new, cx', tw, -, hc, hev, -, -, -, hvs, -⟩
    · rw [hvs]; exact vle_fenceOpt A _
    · rw [hvs]; exact (writeSuccs_at A tid hc hev).2.mono.trans (vle_rmwAfter A k false l cx')
  refine ⟨c, t, hanc, ⟨hrd, hp, hwi⟩, hle2.trans hpost, hcl, hseen, hfR, hfW, fun hk hn => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hlv.acq hk (hfw hfw0 hn)
    exact ⟨Nat.le_trans h1 hpost.vrNew, Nat.le_trans h2 hpost.vwNew⟩
  · rcases hbr with ⟨hop, hsnap, -, hr⟩ | ⟨new, cx', tw, hop, hc, hev, -, hrelp, hsnap, hvs, hr, hun⟩
    · exact .inl ⟨hop, hsnap, hr⟩
    · obtain ⟨hok, hwv⟩ := writeSuccs_at A tid hc hev
      have hm2 : (readNext A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l false t
          v').mem = c.mem := hc0m
      have hp2 : (readNext A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l false t
          v').prom = ownProm tid c := hc0p
      obtain ⟨htw, hat⟩ := hok.2 t rfl
      have hle3 := vle_rmwAfter A k false l cx'
      refine .inr ⟨new, tw, hop, htw, hm2 ▸ hat, writeSnap_of hm2 hp2 hsnap hev,
        writeBound_of_writeOk A tid hok hle2, ?_, fun hnt => ?_, fun hrel => fresh_of_not_own hm2 hp2 hev (hrelp hrel),
        hr, hun⟩
      · rw [hvs]; exact Nat.le_trans hwv.coh (hle3.coh l)
      · rw [hvs]; exact Nat.le_trans (hwv.vwOld hnt) hle3.vwOld

/-- **What a load exposes.** -/
theorem step_loadFacts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} (h : (EnvG I A tid pl).step (.load k xcl addr n) σ v σ') :
    LoadFacts A tid σ σ' k ⟨addr, n⟩ v :=
  loadOut_facts h

/-- **What a store exposes.** -/
theorem step_storeFacts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool} (h : (EnvG I A tid pl).step (.store k xcl addr n v) σ b σ') :
    StoreFacts A tid pl σ σ' k ⟨addr, n⟩ v :=
  storeOut_facts h

/-- A store's outcome reports success. -/
theorem step_store_true {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool} (h : (EnvG I A tid pl).step (.store k xcl addr n v) σ b σ') :
    b = true :=
  h.2.1

/-- **What an RMW exposes.** -/
theorem step_rmwFacts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val} (h : (EnvG I A tid pl).step (.rmw k addr n op) σ old σ') :
    RmwFacts A tid pl σ σ' k ⟨addr, n⟩ op old :=
  rmwOut_facts h

/-- **What a fence exposes.** -/
theorem step_fenceFacts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : FenceKind} {u : Unit}
    (h : (EnvG I A tid pl).step (.fence k) σ u σ') : FenceFacts σ σ' k :=
  h

/-! ## The generic prepay theorem (statement) -/

/-- **The generic prepay theorem at a store node** (§1d), stated for the rule link:
thread `tid` (state `t₁` in `c`, holding the virtual resource `σ.r` with no
in-flight release) is at a store of `v` to `l` that `σ` permits
(`StoreOk`); `(c, g)` is an admissible anchor and the fresh timestamp clears
the env's write bound. Then the thread may promise the message with the
release (or, for a pure value, the relaxed write) accounted: erasure holds
after the promise with the message pending, the ghost grows, the thread
keeps `Plan.after` (the release's slots carry `Plan.give`), and K1/K2 hold
(`NPSafe`'s prepay conjunct, `ThreadRuleRX.prepay`'s conclusion without
`Inv`). An RMW variant (`prepayRmw_*`, the claim floor before the promise)
is left to the rule link. -/
def PrepayGeneric (I : ISA) (A : Arch) : Prop :=
  ∀ (tid : Nat) (pl : Plan) (σ : State I) (k : StoreKind) (l : Loc) (v : Val) (c : Config I) (g : Ghost)
    (rF : Nat → Res) (t₁ : Thread I),
    pl.Valid → StoreOk A tid pl σ k false l v → AnchorOk tid σ c g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid σ.r) g (fun _ => True) c → WriteBound A σ.vs k l (c.mem.last + 1) →
    ∃ (r' : Res) (g' : Ghost),
      Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ ⟨l, v, tid⟩) ∧ g.Le g' ∧
      (c.mem.append ⟨l, v, tid⟩).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, v, tid⟩).2) ∧
      r' = pl.after l v (c.mem.last + 1) σ.cl σ.r ∧
      (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB σ.r g x b)

end Kraken.Promising.SLR.EnvG
