/-
Whole-thread environment (`EnvG`), **Claim-conditional RMWs**: release-only RMWs
and RMW releases that give something
away, **without** ghost-knowledge side conditions. Additive beside
`EnvG/Env.lean`/`EnvG/LinkR.lean`; nothing imports this file.
ISA-neutral.

## The two gaps of the existing release-RMW link

1. `RmwOk` (`Env.lean`) asks `claimedSlots g l tr ≠ [] → ClaimOk A k σ.vs l
   tr` at every admissible anchor ghost. For a release-only RMW (armv8 `.rel`:
   `swpl`, `ldaddl`) `ClaimOk` is false, and `claimedSlots g l tr = []` cannot
   be shown at arbitrary anchor ghosts (any thread may add update ids).
2. `RelRmwGiveOk` (`PrepayRmw.lean`) with a non-empty give quantifies over all
   erasure ghosts, so it is unprovable as stated.

## Root cause: two choices of the existing environment, not of the model

- **The env always claims.** `RmwOut` sets `σ'.r = pl.afterRmw …`, i.e. every
  successful RMW claims the update slots of the message it reads, which
  forces `ClaimOk` (K1: the claimed resources are acquired, so the floor must
  reach `tr`). But claiming is a *ghost* choice. An RMW that does not claim is,
  for erasure and reach, just a store at its write timestamp: `ErAt.store`
  and `RStep.store` take any `WriteEv`, including an RMW's (`trOpt = some
  tr`). The read message's update slots stay in `u` (`Erase.slotsDom`: an
  unclaimed release message keeps them); nobody can claim them later except
  the RMW's own thread (`Erase.claimsAt`), so they are simply dead.
- **The env gives from `σ.r ⋅ C`.** `RmwOk`'s release obligation is for
  `pl.give l new (σ.r ⋅ C)` (`C` the claimed slots), while a prepay can only
  give from `σ.r` (the slots are claimed at fulfilment, never at promise
  time: `Erase.claimFulf`). `RelRmwGiveOk` and `Plan.Whole` only reconcile the
  two. Giving from `σ.r` and keeping `C` (`(pl.after … σ.r) ⋅ C`) agrees with
  the prepay by construction, and also lifts F1's "no split on RMW releases".

## The claim-conditional environment `EnvGC`

- `claimSlotsC A k vs g l tr`: the claimed update slots **if** `ClaimOk A k
  vs l tr` (acquire-release, or an acquire whose read is not forwarded), else
  `[]`;
- `RmwOkC`: `RmwOk` without the claim condition and without `Plan.Whole`; the
  release obligation is for `pl.give l new σ.cl σ.r`;
- `RmwOutC`/`RmwFactsC`: `RmwOut`/`RmwFacts` with `σ'.r = (pl.after l new tw
  P σ.r) ⋅ prod (claimSlotsC …)`;
- `EnvGC I A tid pl`: `EnvG` with these RMW clauses; loads, stores, fences are
  `EnvG`'s definitionally.

Proved here (std axioms):
- `rmwOutC_facts`, `step_rmwFactsC`: the RMW facts.
- `prepayGenericRmwC`: the generic prepay theorem at an RMW node for `RmwOkC`
  (`PrepayGenericRmw'` without its give-away side condition).
- `NodeRel.rmwC'` (no release in flight, any kind) and `NodeRel.rmwRelC` (the
  RMW's write is the in-flight prepaid promise): the transports; the
  non-claiming branch is `ErAt.store`/`RStep.store` (resp.
  `ErAt.fulfilPend`/`RStep.unpend`), the claiming branch is `LinkR`'s.
- `nodeSimS2_envGC`, `treeJ_envGC_eraseWPRDSR(_start)`: the per-tree link
  (no `RelRmwGiveOk`).
- `claimOk_rel_false`: on armv8 the release-only kind never claims.
- `RmwOk.toC`, `RmwOutC.toOut`, `envG_ok_toC`, `envGC_step_toG`: on the
  existing coverage (`RelRmwGiveOk`) `EnvG` refines `EnvGC`.

Not done here: the rule-level
link (`LinkHypsR`/`InvGR`/`ofEnvGR` over `EnvGC`, a copy of the `R` route with
`prepayGenericRmwC` for `prepayGenericRmw'_of_giveOk`), the AArch64 wrapper
(`ofSafelyEnvGRC`), vcgen simp lemmas for `RmwFactsC`, and the relay.

Phase 1 otherwise unchanged: single-access trees, read-side acquire only, an
in-flight release RMW must not fail (`RokR`).
-/
import Kraken.Promising.SLR.EnvG.LinkR

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The claim-conditional environment -/

open Classical in
/-- **The update slots a claim-conditional RMW claims**: those of the message
read when the claim condition holds (`ClaimOk`), none otherwise (the RMW's
write is then erased as a store). -/
noncomputable def claimSlotsC (A : Arch) (k : RmwKind) (vs : Views) (g : Ghost) (l : Loc) (tr : Time) : List Slot :=
  if ClaimOk A k vs l tr then claimedSlots g l tr else []

theorem claimSlotsC_of_ok {A : Arch} {k : RmwKind} {vs : Views} {g : Ghost} {l : Loc} {tr : Time}
    (h : ClaimOk A k vs l tr) : claimSlotsC A k vs g l tr = claimedSlots g l tr := by
  simp only [claimSlotsC, h, ↓reduceIte]

theorem claimSlotsC_of_not {A : Arch} {k : RmwKind} {vs : Views} {g : Ghost} {l : Loc} {tr : Time}
    (h : ¬ ClaimOk A k vs l tr) : claimSlotsC A k vs g l tr = [] := by
  simp only [claimSlotsC, h, ↓reduceIte]

/-- **An RMW's permission in `EnvGC`**: `RmwOk` without the claim condition
(a non-claiming RMW needs none) and without `Plan.Whole`; a planned release's
obligation is for what the plan gives away of the thread's own resource
`σ.r` (the claimed slots stay with the thread). -/
def RmwOkC (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : RmwKind) (l : Loc) (op : Val → Option Val) :
    Prop :=
  0 < (σ.r.wr l).q ∧
    ∀ (c : Config I) (g : Ghost) (tr : Time) (old new : Val), AnchorOk tid σ c g →
      ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old → op old = some new →
      (pl.rel l new = false → Pred.Pure (σ.g.rel l) new) ∧
      (pl.rel l new = true → effRelRmw A k ∧ ¬ Pred.Pure (σ.g.rel l) new ∧ l ∉ pl.gives l new ∧
        (tr < c.mem.last + 1 → WriteBound A σ.vs (A.rmwKind k).storeKind l (c.mem.last + 1) →
          (σ.g.rel l).P new (c.mem.append ⟨l, new, tid⟩).1 (c.mem.last + 1) (pl.give l new σ.cl σ.r)))

/-- **An RMW's outcomes in `EnvGC`**: `RmwOut` with the resource
`(pl.after l new tw P σ.r) ⋅ prod (claimSlotsC …)` (`(l, tr)` is unclaimed
at the anchor ghost, as in `RmwOut`, whether or not the RMW claims). -/
def RmwOutC (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) (old : Val) : Prop :=
  ∃ (c : Config I) (x : Time × Val × Ctx), AnchorOk tid σ c σ'.g ∧
    x ∈ readSuccs A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l false ∧ x.2.1 = old ∧
    σ'.cl = σ.cl ∧ σ'.seen = seenAfter A (A.rmwKind k).loadKind σ σ'.g l x.1 ∧
    σ'.fencedR = false ∧ σ'.fencedW = false ∧
    ((op old = none ∧ σ'.snap = c ∧ σ'.vs = (fenceOptCtx A x.2.2).views ∧ σ'.r = σ.r) ∨
     (∃ (new : Val) (cx' : Ctx) (tw : Time), op old = some new ∧
       cx' ∈ writeSuccs A tid iv0 x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) ∧
       WriteEv tid x.2.2 cx' l new (some x.1) tw ∧ ¬ cx'.Overtaken ∧
       (pl.rel l new = true → tw ∉ ownProm tid c ∨ tw ∈ σ'.g.pend) ∧
       σ'.snap = snapAfter tid c cx' ∧ σ'.vs = (rmwAfter A k false l cx').views ∧
       (∃ P : Prop, (σ.cl → P) ∧
         σ'.r = (pl.after l new tw P σ.r).op (Res.prod ((claimSlotsC A k σ.vs σ'.g l x.1).map (·.res)))) ∧
       ¬ σ'.g.Claimed (l, x.1)))

/-- **What an RMW of `EnvGC` exposes**: `RmwFacts` with `RmwOutC`'s
resource. -/
def RmwFactsC (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) (old : Val) : Prop :=
  ∃ (c : Config I) (tr : Time), AnchorOk tid σ c σ'.g ∧
    ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old ∧
    VLe σ.vs σ'.vs ∧ σ'.cl = σ.cl ∧ σ'.seen = seenAfter A (A.rmwKind k).loadKind σ σ'.g l tr ∧
    σ'.fencedR = false ∧ σ'.fencedW = false ∧
    ((A.loadKind (A.rmwKind k).loadKind).isAcquire = true → ¬ Fwded σ.vs l tr →
      tr ≤ σ'.vs.vrNew ∧ tr ≤ σ'.vs.vwNew) ∧
    ((op old = none ∧ σ'.snap = c ∧ σ'.r = σ.r) ∨
     (∃ (new : Val) (tw : Time), op old = some new ∧ tr < tw ∧ c.mem.atomic l tid tr tw = true ∧
       WriteSnap tid c σ'.snap l new tw ∧ WriteBound A σ.vs (A.rmwKind k).storeKind l tw ∧
       tw ≤ σ'.vs.getCoh l ∧ (A.storeKind (A.rmwKind k).storeKind ≠ .nt → tw ≤ σ'.vs.vwOld) ∧
       (pl.rel l new = true → tw = c.mem.last + 1 ∨ tw ∈ σ'.g.pend) ∧
       (∃ P : Prop, (σ.cl → P) ∧
         σ'.r = (pl.after l new tw P σ.r).op (Res.prod ((claimSlotsC A k σ.vs σ'.g l tr).map (·.res)))) ∧
       ¬ σ'.g.Claimed (l, tr)))

/-- **The claim-conditional whole-thread environment**: `EnvG` with
`RmwOkC`/`RmwOutC` at RMWs (loads, stores and fences are `EnvG`'s). -/
def _root_.Kraken.Promising.SLR.EnvGC (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv where
  State := State I
  ok a σ := match a with
    | .load .. => True
    | .fence _ => True
    | .store k xcl addr n v => StoreOk A tid pl σ k xcl ⟨addr, n⟩ v
    | .rmw k addr n op => RmwOkC A tid pl σ k ⟨addr, n⟩ op
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOut A tid σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOutC A tid pl σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

/-! ## Facts -/

theorem rmwOutC_facts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {old : Val} (h : RmwOutC A tid pl σ σ' k l op old) :
    RmwFactsC A tid pl σ σ' k l op old := by
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

/-- **What an RMW of `EnvGC` exposes.** -/
theorem step_rmwFactsC {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val} (h : (EnvGC I A tid pl).step (.rmw k addr n op) σ old σ') :
    RmwFactsC A tid pl σ σ' k ⟨addr, n⟩ op old :=
  rmwOutC_facts h

/-- On armv8 a release-only RMW (`.rel`: `swpl`, `ldaddl`) never claims: it is
neither acquire-release nor an acquire. -/
theorem claimOk_rel_false {vs : Views} {l : Loc} {tr : Time} : ¬ ClaimOk Arch.armv8 .rel vs l tr := by
  rintro (h | ⟨h, -⟩) <;> revert h <;> decide

/-! ## The resource lemmas -/

/-- **Give from the own resource, keep the claim**: the resource after a
claim-conditional RMW, composed with what its message carries (`R`: the
plan's give of `r` for a planned release, nothing otherwise), is `r ⋅ C` with
the write. -/
theorem Plan.afterC_op_give (pl : Plan) {l : Loc} {v : Val} {tw : Time} {cl : Prop} {r C R : Res}
    (hq : 0 < (r.wr l).q) (hR : pl.rel l v = true → l ∉ pl.gives l v ∧ R = pl.give l v cl r)
    (hR' : pl.rel l v = false → R = Res.unit) :
    ((pl.after l v tw cl r).op C).op R = (r.op C).addW l (v, tw) := by
  unfold Plan.after
  cases hrl : pl.rel l v with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hR' hrl, Res.op_unit, Res.addW_op _ _ hq]
  | true =>
    simp only [↓reduceIte]
    obtain ⟨hgl, rfl⟩ := hR hrl
    have hk := pl.keep_q_pos hgl cl r hq
    rw [Res.op_assoc, Res.op_comm C, ← Res.op_assoc, pl.keep_op_give hgl cl r, Res.addW_op _ _ hq]

/-- The resource after the fulfilment of an in-flight RMW: the actual
resource after the prepay (which already counts the write) with the claimed
slots joining. -/
theorem Res.addW_op_claim {a C : Res} {l : Loc} {p : Val × Time} (hq : 0 < (a.wr l).q) (ha : a.addW l p = a) :
    (a.op C).addW l p = a.op C := by
  rw [← Res.addW_op _ _ hq, ha]

/-- `Plan.after` already counts its write. -/
theorem Plan.after_addW (pl : Plan) {l : Loc} {v : Val} {tw : Time} {cl : Prop} {r : Res}
    (hq : 0 < ((pl.after l v tw cl r).wr l).q) :
    (pl.after l v tw cl r).addW l (v, tw) = pl.after l v tw cl r := by
  unfold Plan.after at hq ⊢
  split
  · next h =>
    simp only [h, ↓reduceIte, Res.addW_q] at hq
    exact Res.addW_addW_self hq
  · next h =>
    simp only [h, Bool.false_eq_true, ↓reduceIte, Res.addW_q] at hq
    exact Res.addW_addW_self hq

/-! ## The existing environment refines `EnvGC` on its coverage

Under the existing give-away side condition (`RelRmwGiveOk`, at the env's
release predicates), every `EnvG` permission is an `EnvGC` permission and
every `EnvGC` outcome of a permitted access is an `EnvG` outcome: a claiming
RMW's resources agree by `Plan.after_op_claim`, and a non-claiming one reads a
message without update slots (`RmwOk`'s claim condition). So a program proved
on `EnvG` is, access by access, proved on `EnvGC` (old as corollary, at the
level of the environment). -/

/-- `RmwOk` with the give-away side condition gives `RmwOkC`. -/
theorem RmwOk.toC {A : Arch} {tid : Nat} {pl : Plan} {σ : State I} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} (hG : RelRmwGiveOk I pl σ.g.rel) (h : RmwOk A tid pl σ k l op) :
    RmwOkC A tid pl σ k l op := by
  refine ⟨h.1, fun c g tr old new hanc hrd hop => ?_⟩
  obtain ⟨-, hpure, hrel⟩ := h.2 c g tr old new hanc hrd hop
  refine ⟨hpure, fun hrl => ?_⟩
  obtain ⟨heff, himp, hgl, hwh, hob⟩ := hrel hrl
  obtain ⟨rF, E⟩ := hanc.erase
  have hC := hG rF g c l tr new hanc.ghost.rel E hrl
  refine ⟨heff, himp, hgl, fun htr hwb => ?_⟩
  have := hob htr hwb
  rwa [pl.give_op_of_unit hwh σ.cl hC] at this

/-- An `EnvGC` outcome of an access `RmwOk` permits is an `EnvG` outcome,
under the give-away side condition. -/
theorem RmwOutC.toOut {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {old : Val} (hG : RelRmwGiveOk I pl σ.g.rel) (hok : RmwOk A tid pl σ k l op)
    (h : RmwOutC A tid pl σ σ' k l op old) : RmwOut A tid pl σ σ' k l op old := by
  obtain ⟨c, ⟨tr, old', cx₁⟩, hanc, hx, hold, hcl, hseen, hfR, hfW, hbr⟩ := h
  refine ⟨c, (tr, old', cx₁), hanc, hx, hold, hcl, hseen, hfR, hfW, ?_⟩
  rcases hbr with hb | ⟨new, cx', tw, hop, hc, hev, hov, hpl, hsnap, hvs, ⟨P, hP, hr⟩, hun⟩
  · exact .inl hb
  refine .inr ⟨new, cx', tw, hop, hc, hev, hov, hpl, hsnap, hvs, ⟨P, hP, ?_⟩, hun⟩
  simp only at hold hr hop
  subst hold
  obtain ⟨hrdAt, -⟩ := readAt_rmw hx
  obtain ⟨hcond, -, hrel⟩ := hok.2 c σ'.g tr old' new hanc hrdAt hop
  rw [hr, Plan.afterRmw]
  by_cases hk : ClaimOk A k σ.vs l tr
  · rw [claimSlotsC_of_ok hk]
    have hl : pl.rel l new = true → l ∉ pl.gives l new := fun hrl => (hrel hrl).2.2.1
    have hs : pl.rel l new = true → pl.Whole l new := fun hrl => (hrel hrl).2.2.2.1
    have hCu : pl.rel l new = true →
        Res.only (pl.gives l new) (Res.prod ((claimedSlots σ'.g l tr).map (·.res))) = Res.unit := fun hrl => by
      obtain ⟨rF, E⟩ := hanc.erase
      exact hG rF σ'.g c l tr new hanc.ghost.rel E hrl
    have hq : 0 < ((pl.after l new tw P σ.r).wr l).q := by
      unfold Plan.after
      cases hrl : pl.rel l new with
      | false => simp only [Bool.false_eq_true, ↓reduceIte, Res.addW_q]; exact hok.1
      | true =>
        simp only [↓reduceIte, Res.addW_q]
        exact pl.keep_q_pos (hl hrl) _ _ hok.1
    rw [← pl.after_op_claim hok.1 hl hs hCu, Res.addW_op_claim hq (pl.after_addW hq)]
  · have hnil : claimedSlots σ'.g l tr = [] := Classical.byContradiction fun hne => hk (hcond hne)
    rw [claimSlotsC_of_not hk, hnil]
    simp only [List.map_nil, Res.prod_nil, Res.op_unit]

/-- **Every `EnvG` permission is an `EnvGC` permission** (give-away side
condition at the env's release predicates). -/
theorem envG_ok_toC {A : Arch} {tid : Nat} {pl : Plan} {σ : State I} (hG : RelRmwGiveOk I pl σ.g.rel)
    {a : SharedAccess} (h : (EnvG I A tid pl).ok a σ) : (EnvGC I A tid pl).ok a σ := by
  cases a with
  | rmw k addr n op => exact RmwOk.toC hG h
  | load => exact h
  | store => exact h
  | fence => exact h

/-- **Every `EnvGC` outcome of an `EnvG`-permitted access is an `EnvG`
outcome** (give-away side condition at the env's release predicates). -/
theorem envGC_step_toG {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} (hG : RelRmwGiveOk I pl σ.g.rel)
    {a : SharedAccess} {ret : a.Ret} (hok : (EnvG I A tid pl).ok a σ) (h : (EnvGC I A tid pl).step a σ ret σ') :
    (EnvG I A tid pl).step a σ ret σ' := by
  cases a with
  | rmw k addr n op => exact RmwOutC.toOut hG hok h
  | load => exact h
  | store => exact h
  | fence => exact h

/-! ## The generic prepay theorem for `RmwOkC` -/

/-- **The generic prepay theorem at a claim-conditional RMW node**:
`PrepayGenericRmw'` for `RmwOkC`, with **no** give-away side condition (the
obligation is already for `pl.give l new σ.cl σ.r`, what the prepay pays). -/
def PrepayGenericRmwC (I : ISA) (A : Arch) : Prop :=
  ∀ (tid : Nat) (pl : Plan) (σ : State I) (k : RmwKind) (l : Loc) (op : Val → Option Val) (c : Config I)
    (g : Ghost) (rF : Nat → Res) (t₁ : Thread I) (tr : Time) (old new : Val),
    pl.Valid → RmwOkC A tid pl σ k l op → AnchorOk tid σ c g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid σ.r) g (fun _ => True) c →
    ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old → op old = some new →
    WriteBound A σ.vs (A.rmwKind k).storeKind l (c.mem.last + 1) →
    ∃ (r' : Res) (g' : Ghost),
      Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ ⟨l, new, tid⟩) ∧ g.Le g' ∧
      (c.mem.append ⟨l, new, tid⟩).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, new, tid⟩).2) ∧
      r' = pl.after l new (c.mem.last + 1) σ.cl σ.r ∧
      (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB σ.r g x b)

/-- **The generic prepay at an RMW node, from the obligation at the anchor**:
the common core of `prepayGenericRmwC` and the adjacency link's
`prepayGenericRmwCAdj`, which differ only in how the release obligation at
`(c, g, tr)` is obtained (`RmwOkC`, resp. `RmwOkCAdj` with `AdjAt`). -/
theorem prepayGenericRmw_of_ob {tid : Nat} {pl : Plan} {σ : State I} {l : Loc} {c : Config I}
    {g : Ghost} {rF : Nat → Res} {t₁ : Thread I} {new : Val} (hpos : 0 < (σ.r.wr l).q)
    (hanc : AnchorOk tid σ c g) (ht : c.threads[tid]? = some t₁)
    (E : Erase (setRes rF tid σ.r) g (fun _ => True) c)
    (hpure : pl.rel l new = false → Pred.Pure (σ.g.rel l) new)
    (hrel : pl.rel l new = true → l ∉ pl.gives l new ∧
      (σ.g.rel l).P new (c.mem.append ⟨l, new, tid⟩).1 (c.mem.last + 1) (pl.give l new σ.cl σ.r)) :
    ∃ (r' : Res) (g' : Ghost),
      Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ ⟨l, new, tid⟩) ∧ g.Le g' ∧
      (c.mem.append ⟨l, new, tid⟩).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, new, tid⟩).2) ∧
      r' = pl.after l new (c.mem.last + 1) σ.cl σ.r ∧
      (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB σ.r g x b) := by
  have hgr : g.rel = σ.g.rel := hanc.ghost.rel
  obtain ⟨R, hP, hkeep⟩ : ∃ R, (g.rel l).P new (c.mem.append ⟨l, new, tid⟩).1 (c.mem.last + 1) R ∧
      (pl.after l new (c.mem.last + 1) σ.cl σ.r).op R = σ.r.addW l (new, c.mem.last + 1) := by
    cases hrl : pl.rel l new with
    | false =>
      refine ⟨Res.unit, hgr ▸ hpure hrl _ _, ?_⟩
      simp [Plan.after, hrl, Res.op_unit]
    | true =>
      obtain ⟨hgl, hob⟩ := hrel hrl
      refine ⟨pl.give l new σ.cl σ.r, hgr ▸ hob, ?_⟩
      simp only [Plan.after, hrl, ↓reduceIte]
      exact pl.keep_op_give hgl σ.cl σ.r _
  obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hP
  have hres : (pl.after l new (c.mem.last + 1) σ.cl σ.r).op (Res.prod (ss.map (·.res))) =
      (setRes rF tid σ.r tid).addW l (new, c.mem.last + 1) := by
    rw [hprod, setRes_self]; exact hkeep
  have hpos' : 0 < ((setRes rF tid σ.r tid).wr l).q := by rw [setRes_self]; exact hpos
  have E' := Erase.prepay_exempt (w := ⟨l, new, tid⟩) E ht trivial hpos' hss hres
  rw [setRes_setRes] at E'
  have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he => by
    have h1 := E.slot_key_le hs
    rw [he, hss.key s' hs'] at h1
    simp only at h1
    omega_t
  have hres0 : (pl.after l new (c.mem.last + 1) σ.cl σ.r).op (Res.prod (ss.map (·.res))) =
      σ.r.addW l (new, c.mem.last + 1) := by rw [hprod]; exact hkeep
  refine ⟨_, prepayGhost g l (c.mem.last + 1) ss, E', ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩,
    List.mem_cons_self, fun ts h => List.mem_cons_of_mem _ h, fun ts h => ?_, rfl,
    fun x hx => mayWrite_store_le (tw := c.mem.last + 1) (rel := true) hres0 rfl hdisj hx, prepay_K2 hss,
    prepay_K1 hss hres0⟩
  rcases List.mem_cons.mp h with h | h
  · exact .inr h
  · exact .inl h

theorem prepayGenericRmwC {A : Arch} : PrepayGenericRmwC I A := by
  intro tid pl σ k l op c g rF t₁ tr old new hv hok hanc ht E hrd hop hwb
  obtain ⟨hpure, hrel⟩ := hok.2 c g tr old new hanc hrd hop
  have htr : tr < c.mem.last + 1 := Nat.lt_succ_of_le (read?_le_last' hrd.val)
  exact prepayGenericRmw_of_ob hok.1 hanc ht E hpure fun hrl =>
    let ⟨_, _, hgl, hob⟩ := hrel hrl; ⟨hgl, hob htr hwb⟩

end Kraken.Promising.SLR.EnvG
