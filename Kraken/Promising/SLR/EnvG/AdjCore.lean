/-
**Own-message adjacency and the sibling environment `EnvGCAdj`**, the
ISA-neutral core, moved here
from `EnvG/AdjSpike.lean` (same names and statements) so that the
claim-conditional link (`EnvG/RmwGhostLink.lean`) and the `F × C` rule
(`EnvG/RmwFailGhostRule.lean`) can be re-proved as instances of the
adjacency versions (`RmwOkC.toCAdj`: every `EnvGC` permission is an
`EnvGCAdj` permission). The design is described in `EnvG/AdjSpike.lean`'s module docstring.

Contents:
- `AdjAt tid c g l tr tw`: every message to `l` strictly between `tr` and
  `tw` is an own outstanding non-pending promise; `adj_of_readSuccs`,
  `adjAt_of_ctx` (the fresh release RMW), `adjAt_of_promised` (the prepay);
  `AdjAt.loc_ne_of_impure`, `AdjAt.lastAt` (the program-side use).
- `RmwOkCAdj`, `EnvGCAdj`, `RmwOkC.toCAdj`, `envGC_ok_toCAdj`,
  `envGCAdj_step_iff` (moved).
- `TreeJLive.ofCAdj`, `NodeSimS2.ofCAdj` (new): an `EnvGCAdj`
  judgment or per-node transport is an `EnvGC` one (same `W`/`Post`, same
  relations), since `EnvGCAdj` permits more and steps alike.
-/
import Kraken.Promising.SLR.EnvG.RmwGhost

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Adjacency -/

/-- **Own-message adjacency** of a read `tr` and a write `tw` to `l` at
anchor `(c, g)`: every message to `l` strictly between them is an own
outstanding promise of thread `tid` that is not pending (so, by
`Erase.pure_of_own`, its value is pure at `l`). -/
def AdjAt (tid : Nat) (c : Config I) (g : Ghost) (l : Loc) (tr tw : Time) : Prop :=
  ∀ p w, tr < p → p < tw → c.mem.get? p = some w → w.loc = l →
    w.tid = tid ∧ p ∈ ownProm tid c ∧ p ∉ g.pend

/-- **The context form**: a read of an instruction context with `OwnCoh`,
whose RMW write at `tw` is atomic, has only own outstanding promises to `l`
strictly between. -/
theorem adj_of_readSuccs {A : Arch} {iv : InstrViews} {tid : Nat} {cx : Ctx} {k : LoadKind} {xcl : Bool}
    {l : Loc} {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l noRet)
    (hoc : cx.OwnCoh tid) {tw : Time} (hat : cx.mem.atomic l tid x.1 tw = true) :
    ∀ p w, x.1 < p → p < tw → cx.mem.get? p = some w → w.loc = l → w.tid = tid ∧ p ∈ cx.prom := by
  intro p w h1 h2 hw hl
  have hown := ownSeen_of_readSuccs A iv hx hoc
  obtain ⟨t, v, rfl, -, hrd, -, -⟩ := (mem_readSuccs A).mp hx
  have htid := atomic_between hat hrd h1 h2 hw hl
  refine ⟨htid, Classical.byContradiction fun hp => ?_⟩
  have := hown p w hw hl htid hp
  simp only at this h1
  omega_t

/-- **Adjacency at the fresh site** (`NodeRel.rmwC'`: no release in
flight): the RMW's read on a context over the anchor `c` (memory `c.mem`,
promises the thread's), with `OwnCoh`, an atomic write at `tw`, and no own
pending promise. -/
theorem adjAt_of_ctx {A : Arch} {iv : InstrViews} {tid : Nat} {c : Config I} {t : Thread I} {g : Ghost}
    (ht : c.threads[tid]? = some t) {cx : Ctx} (hm : cx.mem = c.mem) (hp : cx.prom = t.prom)
    (hoc : cx.OwnCoh tid) {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv cx k xcl l noRet) {tw : Time} (hat : c.mem.atomic l tid x.1 tw = true)
    (hnp : ∀ p ∈ t.prom, p ∉ g.pend) : AdjAt tid c g l x.1 tw := by
  intro p w h1 h2 hw hl
  obtain ⟨htid, hpp⟩ := adj_of_readSuccs hx hoc (by rw [hm]; exact hat) p w h1 h2 (by rw [hm]; exact hw) hl
  rw [hp] at hpp
  exact ⟨htid, by rw [ownProm_eq ht]; exact hpp, hnp p hpp⟩

/-- **Adjacency at the prepay site** (`InvGF.prepay_of_okAtFC`): the
certification's read on the promised context (memory `c.mem` with the new
message appended, promises the thread's and `|M| + 1`), whose fulfilling
write at `|M| + 1` is atomic, with the unpromised thread's `OwnCoh` against
the context's coherence views and no own pending promise. The anchor is the
unpromised `c`, as `RmwOkC`'s obligation takes it. -/
theorem adjAt_of_promised {A : Arch} {iv : InstrViews} {tid : Nat} {c : Config I} {t : Thread I} {g : Ghost}
    (ht : c.threads[tid]? = some t) {w₀ : Msg} {cx : Ctx} (hm : cx.mem = (c.mem.append w₀).1)
    (hp : cx.prom = t.prom ++ [c.mem.last + 1])
    (hoc : ∀ ts w, c.mem.get? ts = some w → w.tid = tid → ts ∉ t.prom → ts ≤ cx.views.getCoh w.loc)
    {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv cx k xcl l noRet) (hat : cx.mem.atomic l tid x.1 (c.mem.last + 1) = true)
    (hnp : ∀ p ∈ t.prom, p ∉ g.pend) : AdjAt tid c g l x.1 (c.mem.last + 1) := by
  have hoc' : cx.OwnCoh tid := by
    intro ts w hw htid hts
    have hle : ts ≤ c.mem.last := by
      refine Nat.le_of_not_lt fun hlt => hts ?_
      have h1 := cx.mem.last_le_of_get?_eq_some hw
      rw [hm, Memory.last_append] at h1
      rw [hp, show ts = c.mem.last + 1 by omega_t]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    rw [hm, Memory.get?_append_of_le _ _ _ hle] at hw
    exact hoc ts w hw htid fun h => hts (by rw [hp]; exact List.mem_append_left _ h)
  intro p w h1 h2 hw hl
  have hle : p ≤ c.mem.last := by omega_t
  obtain ⟨htid, hpp⟩ := adj_of_readSuccs hx hoc' hat p w h1 h2
    (by rw [hm, Memory.get?_append_of_le _ _ _ hle]; exact hw) hl
  rw [hp] at hpp
  have hpp' : p ∈ t.prom := by
    rcases List.mem_append.mp hpp with h | h
    · exact h
    · rw [List.mem_singleton] at h; omega_t
  exact ⟨htid, by rw [ownProm_eq ht]; exact hpp', hnp p hpp'⟩

/-! ## The program-side use -/

/-- **At an all-impure location nothing lies between**: with adjacency at
an anchor whose erasure holds, no message to `l` lies strictly between `tr`
and `tw` when the release predicate of `l` is impure at every value (an own
outstanding non-pending promise is pure, `Erase.pure_of_own`). -/
theorem AdjAt.loc_ne_of_impure {tid : Nat} {c : Config I} {g : Ghost} {l : Loc} {tr tw : Time}
    (h : AdjAt tid c g l tr tw) {rF : Nat → Res} {T : Nat → Prop} (E : Erase rF g T c)
    (himp : ∀ v, ¬ Pred.Pure (g.rel l) v) :
    ∀ p w, tr < p → p < tw → c.mem.get? p = some w → w.loc ≠ l := by
  intro p w h1 h2 hw hl
  obtain ⟨htid, hpp, hnpd⟩ := h p w h1 h2 hw hl
  cases ht : c.threads[tid]? with
  | none => simp only [ownProm, ht, Option.map_none, Option.getD_none, List.not_mem_nil] at hpp
  | some t =>
    rw [ownProm_eq ht] at hpp
    have hget : c.mem.get? p = some ⟨l, w.val, tid⟩ := by
      rw [hw, ← hl, ← htid]
    exact himp _ (Erase.pure_of_own E ht hpp hnpd hget)

/-- **`tr` is the latest message to `l` below `tw`** (as `writeIn`): the
form a history invariant consumes. -/
theorem AdjAt.lastAt {tid : Nat} {c : Config I} {g : Ghost} {l : Loc} {tr tw : Time}
    (h : AdjAt tid c g l tr tw) {rF : Nat → Res} {T : Nat → Prop} (E : Erase rF g T c)
    (himp : ∀ v, ¬ Pred.Pure (g.rel l) v) : c.mem.writeIn l tr (tw - 1) = false := by
  rw [Bool.eq_false_iff, Ne, Memory.writeIn_iff]
  rintro ⟨p, w, h1, h2, hw, hl⟩
  exact h.loc_ne_of_impure E himp p w h1 (by omega_t) hw hl

/-! ## The sibling environment -/

/-- **An RMW's permission with adjacency** (`RmwOkC` whose release
obligation may assume `AdjAt` of the read and the fresh timestamp at the
anchor). Weaker than `RmwOkC` (`RmwOkC.toCAdj`). -/
def RmwOkCAdj (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : RmwKind) (l : Loc) (op : Val → Option Val) :
    Prop :=
  0 < (σ.r.wr l).q ∧
    ∀ (c : Config I) (g : Ghost) (tr : Time) (old new : Val), AnchorOk tid σ c g →
      ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old → op old = some new →
      (pl.rel l new = false → Pred.Pure (σ.g.rel l) new) ∧
      (pl.rel l new = true → effRelRmw A k ∧ ¬ Pred.Pure (σ.g.rel l) new ∧ l ∉ pl.gives l new ∧
        (tr < c.mem.last + 1 → WriteBound A σ.vs (A.rmwKind k).storeKind l (c.mem.last + 1) →
          AdjAt tid c g l tr (c.mem.last + 1) →
          (σ.g.rel l).P new (c.mem.append ⟨l, new, tid⟩).1 (c.mem.last + 1) (pl.give l new σ.cl σ.r)))

theorem RmwOkC.toCAdj {A : Arch} {tid : Nat} {pl : Plan} {σ : State I} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} (h : RmwOkC A tid pl σ k l op) : RmwOkCAdj A tid pl σ k l op := by
  refine ⟨h.1, fun c g tr old new hanc hrd hop => ?_⟩
  obtain ⟨hp, hr⟩ := h.2 c g tr old new hanc hrd hop
  exact ⟨hp, fun hrl => by
    obtain ⟨h1, h2, h3, h4⟩ := hr hrl
    exact ⟨h1, h2, h3, fun a b _ => h4 a b⟩⟩

/-- **The claim-conditional environment with adjacency**: `EnvGC` with
`RmwOkCAdj` at RMWs; the steps are `EnvGC`'s. -/
def _root_.Kraken.Promising.SLR.EnvGCAdj (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv where
  State := State I
  ok a σ := match a with
    | .load .. => True
    | .fence _ => True
    | .store k xcl addr n v => StoreOk A tid pl σ k xcl ⟨addr, n⟩ v
    | .rmw k addr n op => RmwOkCAdj A tid pl σ k ⟨addr, n⟩ op
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOut A tid σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOutC A tid pl σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

/-- Every `EnvGC` permission is an `EnvGCAdj` permission. -/
theorem envGC_ok_toCAdj {A : Arch} {tid : Nat} {pl : Plan} {σ : State I} {a : SharedAccess}
    (h : (EnvGC I A tid pl).ok a σ) : (EnvGCAdj I A tid pl).ok a σ := by
  cases a with
  | rmw k addr n op => exact RmwOkC.toCAdj h
  | load => exact h
  | store => exact h
  | fence => exact h

/-- `EnvGCAdj`'s outcomes are `EnvGC`'s. -/
theorem envGCAdj_step_iff {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {a : SharedAccess} {ret : a.Ret} :
    (EnvGCAdj I A tid pl).step a σ ret σ' ↔ (EnvGC I A tid pl).step a σ ret σ' := by
  cases a <;> exact Iff.rfl

/-- **An `EnvGCAdj` live judgment is an `EnvGC` one** (same `W` and `Post`):
`EnvGC`'s permissions are `EnvGCAdj`'s (`envGC_ok_toCAdj`) and the steps
agree. -/
def TreeJLive.ofCAdj {A : Arch} {tid : Nat} {pl : Plan} {σ : Type} (J : TreeJLive (EnvGCAdj I A tid pl) σ) :
    TreeJLive (EnvGC I A tid pl) σ where
  W := J.W
  Post := J.Post
  done := J.done
  fault := J.fault
  choose := J.choose
  load h₁ h₂ := J.load h₁ h₂
  store h₁ h₂ := J.store h₁ h₂
  rmw h₁ h₂ := J.rmw (RmwOkC.toCAdj h₁) h₂
  fence h₁ h₂ := J.fence h₁ h₂

/-- **An `EnvGCAdj` per-node transport is an `EnvGC` one** (same side
conditions and relations). -/
theorem NodeSimS2.ofCAdj {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop}
    {c : Config I} {t : Thread I} {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} {Pre Post : State I → Res → Ghost → Ctx → Prop}
    (hs : NodeSimS2 A tid iv rF T c t (EnvGCAdj I A tid pl) Lok Sok Rok D Pre Post) :
    NodeSimS2 A tid iv rF T c t (EnvGC I A tid pl) Lok Sok Rok D Pre Post where
  pre_post := hs.pre_post
  fence_pre := hs.fence_pre
  fence_post := hs.fence_post
  load := hs.load
  store := hs.store
  rmw hR hp hok := hs.rmw hR hp (RmwOkC.toCAdj hok)

end Kraken.Promising.SLR.EnvG
