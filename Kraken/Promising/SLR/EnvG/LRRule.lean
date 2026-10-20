/-
Whole-thread environment: **the rule link of `EnvGLR`**
(`ThreadRuleRX` from a thread-local invariant of `EnvGLR`, for code whose
trees may load and then release-write). ISA-neutral; the x64 instance is
`EnvG/LRX64.lean`.

**Shapes.** `LRShape A tree` is a phase-1 tree (`Phase1Shape`), a phase-2
tree (`Phase2Shape`: a load prefix and no release-kind write), or a
**load-then-store tree** `LRStoreShape`: on every path, loads (and fences),
then exactly one store, always to the same location `l`; no RMW. The last
covers x64 `incl (m)`, `addl $1,(m)`, `movl (m),%eax`-free read-modify-write
forms without `lock`, whose store is a release under `Arch.tso`.

**Invariant.** `CoreAtLR` is `CoreAt` (`Phase1.lean`) with the in-flight
tree condition of `EnvGLR`'s link: with a release of `⟨l, v⟩` in flight the
thread's next tree is a load prefix and then a store to `l`
(`InflFactLR`, the side conditions of `nodeSimLR_envGLR` at
`pf = some (l, v)`). `CoreAtLR.transport`/`.start` are `CoreAt`'s proofs
(additive duplication, as `CoreAtR`).

- `InvGLR.wp`: `treeJ_envGLR_eraseWPRDM_start` (`LRLink.lean`) into
  `WpPostR`; the new clean flag as in `InvG.wp`.
- `InvGLR.prepay`: the live fulfilment of a promise is the store of the
  tree's path (`relFulfilsLive_sokM`); the store is permitted at the
  `EnvGLR` state reached by the *env's* loads along that path
  (`storeOkLR_walk`: each load of the promised context is a load of the
  unpromised one, `readSuccs_unpromise`, which `NodeRel.loadLR` answers), so
  `prepayGeneric` applies; the env's `cl` at the store is the start's
  (`EnvGLR`'s loads keep it), which is what the in-flight relation records.
- `ThreadRuleRX.ofEnvGLR`, `npSafe_of_envGLR`, `noFaultRule_ofEnvGLR_struct`.

Phase-1 limits: one release in flight; releases are stores (no release-kind
RMW on this route); read-side acquire only.
-/
import Kraken.Promising.SLR.EnvG.LRLink
import Kraken.Promising.SLR.EnvG.MultiRule
import Kraken.Promising.SLR.EnvG.Answers

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Shapes -/

/-- An access-free tree has a load prefix (with `D` at its leaves). -/
theorem AccessFree.toM {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop} (hD : D)
    {σ : Type} : ∀ {tree : EvTree σ}, AccessFree tree → MultiAccessS Lok Sok Rok D tree
  | .done _, _ => hD
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => AccessFree.toM hD (tree := k i) (h i)
  | .fence _ ret, h => AccessFree.toM hD (tree := ret ()) h
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .rmw .., h => h.elim

/-- A single-access tree has a load prefix, when a load's side condition
gives the leaf condition. -/
theorem SingleAccessS.toM {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop}
    (hLD : Lok → D) {σ : Type} : ∀ {tree : EvTree σ}, SingleAccessS Lok Sok Rok D tree → MultiAccessS Lok Sok Rok D tree
  | .done _, h => h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => SingleAccessS.toM hLD (tree := k i) (h i)
  | .fence _ ret, h => SingleAccessS.toM hLD (tree := ret ()) h
  | .load .., h => ⟨h.1, fun _ => AccessFree.toM (hLD h.1) (h.2 _)⟩
  | .store .., h => h
  | .rmw .., h => h

/-- **A load-then-store tree**: on every path, loads (and fences), then one
store, always to the same location; no RMW, no write-free leaf. -/
def LRStoreShape {σ : Type} (tree : EvTree σ) : Prop :=
  ∃ l, MultiAccessS True (fun l' _ => l' = l) (fun _ => False) False tree

/-- **The tree shapes of the `EnvGLR` link**: phase 1, phase 2, or a
load-then-store tree. -/
def LRShape (A : Arch) {σ : Type} (tree : EvTree σ) : Prop :=
  Phase1Shape A tree ∨ Phase2Shape A tree ∨ LRStoreShape tree

/-- Every `LRShape` tree has a load prefix with no release-kind RMW. -/
theorem LRShape.multi {A : Arch} {σ : Type} {tree : EvTree σ} (h : LRShape A tree) :
    MultiAccessS True (fun _ _ => True) (fun k => ¬ effRelRmw A k) True tree := by
  rcases h with h | h | ⟨l, h⟩
  · exact SingleAccessS.toM id h.2
  · exact h.1
  · exact h.mono id (fun _ _ _ => trivial) (fun _ h => h.elim) (fun h => h.elim)

/-- `LRShape` trees satisfy the `EnvGLR` link's side conditions without a
release in flight. -/
theorem LRShape.none {A : Arch} {σ : Type} {tree : EvTree σ} (h : LRShape A tree) :
    MultiAccessS True (SokLR none) (RokS A none) (LokS none) tree :=
  h.multi.mono id (fun _ _ _ => .inl rfl) (fun _ hk => ⟨rfl, hk⟩) (fun _ => rfl)

/-- **A load-then-store tree at the location of its first load** (the form
the x64 shape tactic uses: the location is the first load's, found by
unification). -/
theorem LRShape.of_load {A : Arch} {σ : Type} {k : LoadKind} {xcl : Bool} {l : Loc} {ret : Val → EvTree σ}
    (h : ∀ v, MultiAccessS True (fun l' _ => l' = l) (fun _ => False) False (ret v)) :
    LRShape A (.load k xcl l ret) :=
  .inr (.inr ⟨l, trivial, h⟩)

/-- Phase-1 trees are `LRShape`. -/
theorem Phase1Shape.toLR {A : Arch} {σ : Type} {tree : EvTree σ} (h : Phase1Shape A tree) : LRShape A tree :=
  .inl h

/-! ## The fulfilment of a promise by a load-prefix tree -/

/-- **The live fulfilment of a promise by a load-prefix tree is a store of
the promised message** satisfying the store side condition, leaving every
other own promise to its location above the fulfilled one. -/
theorem relFulfilsLive_sokM {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {prom : List Time}
    {mem : Memory} {w : Msg} (hts : ts ∈ prom) (hget : mem.get? ts = some w) {Lok : Prop}
    {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop} (hR : ∀ k, Rok k → ¬ effRelRmw A k) {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), cx.prom = prom → cx.mem = mem → MultiAccessS Lok Sok Rok D tree →
      tree.RelFulfilsLive A tid iv ts cx → Sok w.loc w.val ∧ AboveAt prom mem ts w.loc
  | .done _, _, _, _, _, h => h.elim
  | .fault _, _, _, _, _, h => h.elim
  | .choose _ k, cx, hp, hm, hs, ⟨i, h⟩ => relFulfilsLive_sokM hts hget hR (k i) cx hp hm (hs i) h
  | .fence k ret, cx, hp, hm, hs, h =>
    relFulfilsLive_sokM hts hget hR (ret ()) (fenceStep cx k) (by rw [fenceStep_prom]; exact hp)
      (by rw [fenceStep_mem]; exact hm) hs h
  | .load _ _ _ ret, _, hp, hm, hs, ⟨x, hx, h⟩ => by
    obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
    exact relFulfilsLive_sokM hts hget hR (ret x.2.1) x.2.2 (hp1.trans hp) (hm1.trans hm) (hs.2 _) h
  | .rmw k _ _ _ ret, _, _, _, hs, ⟨x, _, h⟩ => by
    rcases h with h | ⟨_, _, _, _, h⟩
    · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2 _) h).elim
    · rcases h with ⟨⟨hk, _⟩, _⟩ | h
      · exact absurd hk (hR _ hs.1)
      · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2 _) h).elim
  | .store k xcl l v ret, cx, hp, hm, hs, h => by
    rcases h with ⟨c', hc', ⟨⟨-, htc, htc'⟩, hnd⟩ | h⟩ | h
    · obtain ⟨hl, hv, hab⟩ := fulfil_write_facts hts hget hp hm hc' htc htc' hnd
      subst hl hv
      exact ⟨hs.1, hab⟩
    · exact (AccessFree.not_relFulfilsLive (ret true) _ (hs.2 true) h).elim
    · exact (AccessFree.not_relFulfilsLive (ret false) _ (hs.2 false) h).elim

/-! ## The store's permission after the env's loads -/

/-- `StoreOk` at the store of a load-prefix tree, after every `EnvGLR` load
outcome and fence on the way (choices: every branch). -/
def StoreOkAtLR (A : Arch) (tid : Nat) (pl : Plan) {σ : Type} : EvTree σ → State I → Prop
  | .fence k ret, s => StoreOkAtLR A tid pl (ret ()) (fenceState s k)
  | .choose _ k, s => ∀ i, StoreOkAtLR A tid pl (k i) s
  | .load k xcl l ret, s => ∀ v s', LoadOutLR A tid s s' k xcl l v → StoreOkAtLR A tid pl (ret v) s'
  | .store k xcl l v _, s => StoreOk A tid pl s k xcl l v
  | _, _ => True

/-- **`StoreOkAtLR` is a live tree judgment of `EnvGLR`.** -/
def TreeJLive.storeOkLR (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvGLR I A tid pl) σ where
  W := StoreOkAtLR A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose h := h
  load _ h := fun v s' hs => h v s' hs
  store hok _ := hok
  rmw _ _ := trivial
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- **The env's walk to the fulfilling store**: along a live fulfilment in
the promised context `P` (the thread's promises with `ts`, the memory with
the promised message `w` appended at `ts`), `EnvGLR`'s loads answered at the
unpromised context `Qc` (`NodeRel`, same views) reach a state at which the
fulfilling store, of `w`'s location and value, is permitted; the env's `cl`
is unchanged on the way. -/
theorem storeOkLR_walk {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I}
    {t : Thread I} {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {r : Res} {g : Ghost} {ts : Time} {w : Msg} {σ : Type} :
    ∀ (tree : EvTree σ) (s : State I) (P Qc : Ctx),
      NodeRel tid pl iv rF c t rv₀ g₀ cl₀ s r g Qc → P.views = Qc.views → P.prom = Qc.prom ++ [ts] →
      P.mem = (Qc.mem.append w).1 → ts = Qc.mem.last + 1 →
      MultiAccessS True (fun _ _ => True) (fun k => ¬ effRelRmw A k) True tree →
      StoreOkAtLR A tid pl tree s → tree.RelFulfilsLive A tid iv ts P →
      ∃ (s' : State I) (Qc' : Ctx) (k : StoreKind), s'.cl = s.cl ∧ NodeRel tid pl iv rF c t rv₀ g₀ cl₀ s' r g Qc' ∧
        StoreOk A tid pl s' k false w.loc w.val
  | .done _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | .fault _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | .choose _ k, s, P, Qc, hN, hv, hp, hm, hts, hs, hok, ⟨i, h⟩ =>
    storeOkLR_walk (k i) s P Qc hN hv hp hm hts (hs i) (hok i) h
  | .fence k ret, s, P, Qc, hN, hv, hp, hm, hts, hs, hok, h => by
    obtain ⟨s', Qc', k', hcl, hN', hok'⟩ := storeOkLR_walk (ret ()) (fenceState s k) (fenceStep P k)
      (fenceStep Qc k) (hN.fence k) (by rw [fenceStep_views, fenceStep_views, hv])
      (by rw [fenceStep_prom, fenceStep_prom, hp]) (by rw [fenceStep_mem, fenceStep_mem, hm])
      (by rw [fenceStep_mem]; exact hts) hs hok h
    exact ⟨s', Qc', k', hcl, hN', hok'⟩
  | .load k xcl l ret, s, P, Qc, hN, hv, hp, hm, hts, hs, hok, ⟨x, hx, h⟩ => by
    obtain ⟨y, hy, e1, e2⟩ := readSuccs_unpromise hv hp hm hts hx
    obtain ⟨s', ho, hN'⟩ := hN.loadLR hy
    have hvx : x.2.2.views = y.2.2.reset.views := by
      obtain ⟨t1, v1, rfl, -⟩ := (mem_readSuccs A).mp hx
      obtain ⟨t2, v2, rfl, -⟩ := (mem_readSuccs A).mp hy
      simp only at e1 e2
      subst e1 e2
      simp only [Ctx.reset_views, readNext, readPre, hv]
    obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
    obtain ⟨hm2, hp2⟩ := readSuccs_memProm A iv hy
    obtain ⟨s'', Qc', k', hcl, hN'', hok'⟩ := storeOkLR_walk (ret x.2.1) s' x.2.2 y.2.2.reset hN' hvx
      (by rw [hp1, hp, Ctx.reset_prom, hp2]) (by rw [hm1, hm, Ctx.reset_mem, hm2])
      (by rw [Ctx.reset_mem, hm2]; exact hts) (hs.2 _) (hok x.2.1 s' (e2 ▸ ho)) h
    exact ⟨s'', Qc', k', hcl.trans ho.2.2.1, hN'', hok'⟩
  | .rmw k _ _ _ ret, _, _, _, _, _, _, _, _, hs, _, ⟨x, _, h⟩ => by
    rcases h with h | ⟨_, _, _, _, h⟩
    · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2 _) h).elim
    · rcases h with ⟨⟨hk, _⟩, _⟩ | h
      · exact absurd hk hs.1
      · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2 _) h).elim
  | .store k xcl l v ret, s, P, Qc, hN, _, hp, hm, hts, hs, hok, h => by
    rcases h with ⟨c', hc', ⟨⟨-, htc, htc'⟩, hnd⟩ | h⟩ | h
    · have hget : P.mem.get? ts = some w := by rw [hm, hts]; exact Memory.get?_append_last _ _
      obtain ⟨rfl, rfl, -⟩ := fulfil_write_facts (by rw [hp]; exact List.mem_append_right _ (List.mem_singleton_self _))
        hget rfl rfl hc' htc htc' hnd
      obtain rfl : xcl = false := hok.1
      exact ⟨s, Qc, k, rfl, hN, hok⟩
    · exact (AccessFree.not_relFulfilsLive (ret true) _ (hs.2 true) h).elim
    · exact (AccessFree.not_relFulfilsLive (ret false) _ (hs.2 false) h).elim

/-! ## The invariant core -/

/-- **The in-flight facts of `EnvGLR`** of the pending own promise `ts` of
`⟨l, v⟩`: the thread's next tree satisfies the `EnvGLR` link's side
conditions at `pf = some (l, v)` (loads, then a store to `l`), every other own
promise to `l` lies above `ts`, and the thread holds a permission for `l`. -/
def InflFactLR (A : Arch) (c : Config I) (t : Thread I) (r : Res) (l : Loc) (v : Val) (ts : Time) : Prop :=
  (∀ tree, I.exec t.st = some tree →
      MultiAccessS True (SokLR (some (l, v))) (RokS A (some (l, v))) (LokS (some (l, v))) tree) ∧
    (∀ p ∈ t.prom, p ≠ ts → ∀ w, c.mem.get? p = some w → w.loc = l → ts < p) ∧ 0 < (r.wr l).q

/-- **The invariant core of `EnvGLR`** (`CoreAt` with `InflFactLR`). -/
structure CoreAtLR (A : Arch) (tid : Nat) (pl : Plan) (cl : Prop) (c : Config I) (r : Res) (g : Ghost)
    (σ : State I) (t : Thread I) : Prop where
  rel : EnvRel tid pl σ c t r g cl
  pendLe : ∀ ts ∈ g.pend, ts ≤ c.mem.last
  infl : ∀ ts l v, ts ∈ t.prom → ts ∈ g.pend → c.mem.get? ts = some ⟨l, v, tid⟩ → InflFactLR A c t r l v ts

section Core

variable {A : Arch} {tid : Nat} {pl : Plan} {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} {σ : State I}
  {t₀ t : Thread I}

/-- **The core along environment extension and world growth**
(`CoreAt.transport`, verbatim). -/
theorem CoreAtLR.transport (h : CoreAtLR A tid pl cl c₀ r g₀ σ t₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g)
    (ht : c.threads[tid]? = some t) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) {rF : Nat → Res}
    {T : Nat → Prop} (E : Erase (setRes rF tid r) g T c) :
    t.st = t₀.st ∧ CoreAtLR A tid pl cl c r g σ t := by
  obtain ⟨hinit, hmsgs, hth⟩ := he
  obtain ⟨ps, ht', hps⟩ := hth t₀ h.rel.ht
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  have hle : c₀.mem.last ≤ c.mem.last := by
    have := hmsgs.length_le
    simp only [Array.length_toList] at this
    unfold Memory.last; omega_t
  have hpre : c₀.mem.Prefix c.mem := ⟨hinit, hmsgs⟩
  have hnp₀ : ∀ ts ∈ t₀.prom ++ ps, ts ∈ g₀.pend → ts ∈ t₀.prom := fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · exact h'
    · have := hps ts h'; have := h.pendLe ts hpd; omega_t
  have h1 := h.rel.ext ⟨hinit, hmsgs, hth⟩ ht hnp₀
  have hinfl : ∀ ts l v, ts ∈ t₀.prom ++ ps → ts ∈ g₀.pend → c.mem.get? ts = some ⟨l, v, tid⟩ →
      InflFactLR A c { t₀ with prom := t₀.prom ++ ps } r l v ts := by
    intro ts l v hts hpd hget
    have hts₀ := hnp₀ ts hts hpd
    have hle₀ := h.pendLe ts hpd
    obtain ⟨htree, habove, hq⟩ := h.infl ts l v hts₀ hpd (by rw [← hpre.get? hle₀]; exact hget)
    refine ⟨htree, fun p hp hne w hw hwl => ?_, hq⟩
    by_cases hpl : p ≤ c₀.mem.last
    · rcases List.mem_append.mp hp with hp | hp
      · exact habove p hp hne w (by rw [← hpre.get? hpl]; exact hw) hwl
      · have := hps p hp; omega_t
    · omega_t
  have hiff : ∀ ts ∈ t₀.prom ++ ps, (ts ∈ g.pend ↔ ts ∈ g₀.pend) := by
    intro ts hts
    refine ⟨hnp ts hts, fun hpd₀ => ?_⟩
    rcases h1.res with ⟨-, hn⟩ | ⟨ts₁, l, v, h1', -, h3, h5, h6⟩
    · exact absurd hpd₀ (hn ts hts)
    · obtain rfl := h6 ts hts hpd₀
      obtain ⟨-, -, hq⟩ := hinfl ts l v hts hpd₀ h3
      obtain ⟨P, -, h5⟩ := h5
      have hX : (r.wr l).X (v, ts) := by rw [h5] at hq ⊢; exact pl.after_X_self l v ts P σ.r hq
      exact pend_of_written E ht h1' h3 hX hq
  refine ⟨rfl, h1.ghostLe hg hiff, fun ts hts => E.pend_le hts, fun ts l v hts hpd hget => ?_⟩
  exact hinfl ts l v hts ((hiff ts hts).mp hpd) hget

/-- **The `EnvGLR` link's start from the core**: the in-flight message `pf`,
the start facts, the side conditions of the thread's (`LRShape`) tree, and,
without a release in flight, the actual resource is the env's. -/
theorem CoreAtLR.start (h : CoreAtLR A tid pl cl c r g σ t) :
    ∃ pf, StartS tid c t g pf ∧
      (∀ tree, I.exec t.st = some tree → LRShape A tree →
        MultiAccessS True (SokLR pf) (RokS A pf) (LokS pf) tree) ∧ (pf = none → r = σ.r) := by
  rcases h.rel.res with ⟨hr, hn⟩ | ⟨ts, l, v, h1, h2, h3, -, h6⟩
  · exact ⟨none, ⟨fun _ => hn, fun _ _ e => absurd e (by simp)⟩, fun _ _ hs => hs.none, fun _ => hr⟩
  · obtain ⟨htree, habove, -⟩ := h.infl ts l v h1 h2 h3
    refine ⟨some (l, v), ⟨fun e => absurd e (by simp), fun l' v' e => ?_⟩, fun tree hex _ => htree tree hex,
      fun e => absurd e (by simp)⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨ts, h1, h2, h3, habove⟩

end Core

/-! ## The rule -/

/-- **The hypotheses of the `EnvGLR` rule link** for a thread-local
invariant `Q` of `EnvGLR`: a valid plan, `LRShape` trees, and the link of
every live tree judgment of `EnvGLR`. -/
structure LinkHypsLR (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → LRShape A tree
  link : ∀ (J : TreeJLive (EnvGLR I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- **The `EnvGLR` rule's invariant**: the core `CoreAtLR` and `Q` at some
env state. -/
def InvGLR (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) (cl : Prop) (c : Config I) (r : Res)
    (g : Ghost) : Prop :=
  ∃ σ t, CoreAtLR A tid pl cl c r g σ t ∧ Q t.st σ

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`done`** (`InvG.done`). -/
theorem InvGLR.done {B : Config I → Res → Ghost → Prop}
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (h : InvGLR A tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (hcl : cl) (hd : c.Done tid) : B c r g := by
  obtain ⟨σ, t₀, hC, hQ⟩ := h
  obtain ⟨t, ht, hhalt, hprom⟩ := hd
  obtain ⟨hinit, hmsgs, hth⟩ := he
  obtain ⟨ps, ht', -⟩ := hth t₀ hC.rel.ht
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  have h1 := hC.rel.ext ⟨hinit, hmsgs, hth⟩ ht (fun ts hts _ => absurd (hprom ▸ hts) List.not_mem_nil)
  exact hB c { t₀ with prom := t₀.prom ++ ps } r g cl σ hQ hhalt hprom
    (h1.ghostLe hg fun ts hts => absurd (hprom ▸ hts) List.not_mem_nil) hcl

/-- `Q` at the current configuration (`InvG.q_at`). -/
theorem InvGLR.q_at {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (h : InvGLR A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    ∃ σ, Q t.st σ := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
  exact ⟨σ, hst ▸ hQ₀⟩

/-- **`wp`**: link theorem 1 of `EnvGLR` into `WpPostR` (`InvG.wp`). -/
theorem InvGLR.wp (H : LinkHypsLR A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGLR A tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvGLR A tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hW := H.link (TreeJLive.eraseWPRDM (nodeSimLR_envGLR (A := A) (pl := pl)
    (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS) Q)
    t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envGLR_eraseWPRDM_start hC.rel (I.deps t.st) hS E hm hW ha
  refine EvTree.EraseWPRD.mono ?_ tree _ _ _ hwp
  rintro st r' g' cx' ⟨σ', hQ', hP, ⟨hg', hkeep, hnew, hacq, hown⟩, hlast, hpd, hcl⟩
  refine ⟨hg', hkeep, hnew, hacq, hown, fun t' ht' _ => ?_⟩
  obtain ⟨cxe, hcx, -⟩ := hP.ctx
  have hE := hP.finish (pl := pl) ht hcx.sim.bnd hcx.sim.ivb (hC.rel.bnd.regs.mono hlast) ht'
  have hcl' : (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) → σ'.cl := by
    cases pf with
    | none => exact fun ⟨h1, h2⟩ => hP.cl ⟨h1, rF, (hr rfl) ▸ h2⟩
    | some _ => exact fun ⟨h1, _⟩ => hcl (by simp) h1
  have hprom' : t'.prom = cx'.prom := (finishInstr_relKey ht').1
  refine ⟨σ', t', ⟨{ hE with cl := hcl' }, fun ts hts => ?_, fun ts _ _ hts hpd' _ => ?_⟩, ?_⟩
  · have := E.pend_le (hnew ts hts)
    show ts ≤ cx'.mem.last
    omega_t
  · exact absurd hpd' (hpd ts (hprom' ▸ hts))
  · rw [finishInstr_st ht']; exact hQ'

/-- **`prepay`**: the generic prepay theorem at the fulfilling store of the
in-flight instruction's tree, at the `EnvGLR` state after the env's loads
along the fulfilling path. -/
theorem InvGLR.prepay (H : LinkHypsLR A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGLR A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGLR A tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨tree, hex, hrfl⟩ := hrel
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t₁.st σ := hst ▸ hQ₀
  have hsh : LRShape A tree := H.shape _ _ hQ tree hex
  have hn := lt_size_of_get? ht
  have hts_eq : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  have hget : (c.mem.append { w with tid }).1.get? (c.mem.append { w with tid }).2 = some { w with tid } :=
    Memory.get?_append_last _ _
  have hmem : (c.mem.append { w with tid }).2 ∈ t₁.prom ++ [(c.mem.append { w with tid }).2] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  -- the fulfilling store writes the promised message, above every other own promise to its location
  obtain ⟨-, habove⟩ := relFulfilsLive_sokM (Sok := fun _ _ => True) hmem hget (fun _ hk => hk) tree _ rfl rfl
    hsh.multi hrfl
  -- no release is in flight
  obtain ⟨hr, hn0⟩ : r = σ.r ∧ ∀ ts ∈ t₁.prom, ts ∉ g.pend := by
    rcases hC.rel.res with h' | ⟨ts₁, l₁, v₁, h1, h2, h3, -, -⟩
    · exact h'
    · exfalso
      obtain ⟨htree, -, -⟩ := hC.infl ts₁ l₁ v₁ h1 h2 h3
      obtain ⟨hsok, -⟩ := relFulfilsLive_sokM hmem hget (fun _ hk => absurd hk.1 (by simp)) tree _ rfl rfl
        (htree tree hex) hrfl
      have hl₁ : l₁ = w.loc := by
        rcases hsok with e | ⟨v₀, e⟩
        · cases e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e; exact e.1
      have hle := hC.pendLe ts₁ h2
      have hne : ts₁ ≠ (c.mem.append { w with tid }).2 := by rw [hts_eq]; omega_t
      have := habove ts₁ (List.mem_append_left _ h1) hne _
        (by rw [Memory.get?_append_of_le _ _ _ hle]; exact h3) hl₁
      rw [hts_eq] at this
      omega_t
  -- the env's walk to the store, and its permission
  have hN0 := hC.rel.toNodeRel rF (I.deps t₁.st) E hm
  obtain ⟨s', Qc', k, hscl, hN', hok⟩ := storeOkLR_walk (w := { w with tid }) tree σ
    { views := t₁.views, prom := t₁.prom ++ [(c.mem.append { w with tid }).2], mem := (c.mem.append { w with tid }).1,
      log := [.instr tid (I.showInstr t₁.st)] } _ hN0 rfl rfl rfl rfl
    hsh.multi (H.link (TreeJLive.storeOkLR A tid pl I.State) t₁.st σ tree hQ hex (fun _ _ _ => trivial)) hrfl
  have hanc : AnchorOk tid s' c g := hN'.anchorOk
  have hσr : s'.r = σ.r := hN'.rv
  have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hσr, ← hr]; exact E
  have hwb : WBnd s'.vs c.mem.last := by
    have hv := hN'.ctx.sim.rel.views
    rw [hN'.mem] at hv
    exact WBnd.of_viewsLe hv
  obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
    prepayGeneric tid pl s' k _ _ c g rF t₁ H.valid hok hanc ht E0 (hwb.writeBound A k _)
  rw [hσr, ← hr] at hacq hK1
  refine ⟨r', g', E', hgle, hpend, hkeep, hnew, ?_, hacq, hK2, hK1⟩
  -- the in-flight tree condition
  have hinfl : MultiAccessS True (SokLR (some (w.loc, w.val))) (RokS A (some (w.loc, w.val)))
      (LokS (some (w.loc, w.val))) tree := by
    rcases hsh with hs1 | hs2 | ⟨l₀, hs3⟩
    · have hFS := relFulfilsLive_firstStore hmem hget tree _ rfl rfl hs1 hrfl
      have h1 : SingleAccessS False (SokLR (some (w.loc, w.val))) (RokS A (some (w.loc, w.val)))
          (LokS (some (w.loc, w.val))) tree :=
        hFS.singleAccessS (fun _ _ _ _ ⟨e1, _, _⟩ => .inr ⟨w.val, by rw [e1]⟩) hs1.2.singleAccess
      exact (SingleAccessS.toM False.elim h1).mono (fun _ => trivial) (fun _ _ h => h) (fun _ h => h) id
    · exact absurd hrfl (NoRelWrite.not_relFulfilsLive tree _ hs2.2)
    · have hl₀ := (relFulfilsLive_sokM hmem hget (fun _ h => h.elim) tree _ rfl rfl hs3 hrfl).1
      exact hs3.mono id (fun l' _ hl' => .inr ⟨w.val, by rw [hl', ← hl₀]⟩) (fun _ h => h.elim) (fun h => h.elim)
  -- the invariant after the promise: the release is in flight
  have hExt := EnvExt.promise (tid := tid) (w := w) ht
  have ht' : (PromisedBy c tid t₁ w).threads[tid]? =
      some { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] } := by
    rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl]
  have h1 := hC.rel.ext hExt ht' (fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · exact h'
    · rw [List.mem_singleton] at h'
      have := E.pend_le hpd
      rw [h', hts_eq] at this
      omega_t)
  have huniq : ∀ ts ∈ t₁.prom ++ [(c.mem.append { w with tid }).2], ts ∈ g'.pend →
      ts = (c.mem.append { w with tid }).2 := fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · rcases hnew ts hpd with h'' | h''
      · exact absurd h'' (hn0 ts h')
      · exact h''
    · exact List.mem_singleton.mp h'
  have hr'' : r' = pl.after w.loc w.val (c.mem.last + 1) s'.cl σ.r := by rw [hr', hσr]
  refine ⟨σ, { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] },
    ⟨{ h1 with ghost := h1.ghost.trans hgle,
               res := .inr ⟨_, w.loc, w.val, hmem, hpend, hget,
                 ⟨s'.cl, fun h => by rw [hscl]; exact h, hr''⟩, huniq⟩,
               cl := fun hc => hC.rel.cl hc.1 }, fun ts hpd => ?_, fun ts l' v' hts hpd hget' => ?_⟩, hQ⟩
  · show ts ≤ (c.mem.append { w with tid }).1.last
    rw [Memory.last_append]
    rcases hnew ts hpd with h' | h'
    · have := E.pend_le h'; omega_t
    · rw [h', hts_eq]; exact Nat.le_refl _
  · obtain rfl := huniq ts hts hpd
    have e : (⟨l', v', tid⟩ : Msg) = { w with tid } := Option.some.inj (hget'.symm.trans hget)
    simp only [Msg.mk.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    refine ⟨fun tree' hex' => ?_, habove, ?_⟩
    · rw [show tree' = tree from Option.some.inj (hex'.symm.trans hex)]
      exact hinfl
    · rw [hr'']; exact pl.after_q_pos H.valid _ _ _ _ _ (hσr ▸ hok.2.1)

end Rule

/-- **The rule link of `EnvGLR`**: a `ThreadRuleRX` from a thread-local
invariant `Q` of `EnvGLR` (`LinkHypsLR`) and the postcondition at halted
threads (`hB`). -/
def ThreadRuleRX.ofEnvGLR {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsLR A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid where
  Inv := InvGLR A tid pl Q
  done h he hg hcl hd := InvGLR.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvGLR.wp H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvGLR.prepay H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafe` from the `EnvGLR` rule link** (`NPSafe.of_ruleRX`). -/
theorem npSafe_of_envGLR {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsLR A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGLR A tid pl Q cl c r g) :
    NPSafe (model I) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofEnvGLR H hB) n m cl c r g h

/-- **The `EnvGLR` no-fault rule from fault-free trees**
(`noFaultRule_ofEnvG_struct`): unconditional in the thread's promises. -/
theorem noFaultRule_ofEnvGLR_struct {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsLR A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HS : ∀ st σ tree, Q st σ → I.exec st = some tree → tree.NoFault) :
    NoFaultRule (ThreadRuleRX.ofEnvGLR H hB) :=
  NoFaultRule.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGLR.q_at rF t h he hg ht E hnp
    exact HS t.st σ tree hQ hex

end Kraken.Promising.SLR.EnvG
