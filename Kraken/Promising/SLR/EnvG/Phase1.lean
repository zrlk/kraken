/-
Whole-thread environment (`EnvG`): the **phase-1 tree shape and
the invariant core** of the rule link.
ISA-neutral.

Phase 1 restricts instruction trees (`Phase1Tree`, a stated hypothesis of
the link; `KNOWN_GAPS.md`):

- `SingleAccess` (§1(b)) with no release-kind RMW (`¬ effRelRmw`, **phase 1:
  releases are stores**);
- `DetAccess`: a `choose` node only above access-free subtrees, so the
  single access is reached by fences alone and an in-flight release's
  instruction (`RelFulfilsLive`) is exactly the release store
  (`relFulfilsLive_firstStore`).

The invariant core `CoreAt` (between instructions, at the `NPSafe` instance)
is `EnvRel` plus what the in-flight case needs across environment steps:
pending marks below `|M|`, and for the pending own promise `ts` of `⟨l, v⟩`
(`InflFact`) the instruction's tree is the store of `v` to `l`
(`SingleAccessS` at `pf = some (l, v)`), every other own promise to `l` lies
above `ts`, and the thread has a permission for `l`. `CoreAt.transport`
moves it along `EnvExt` and world growth: the own pending mark survives
(`pend_of_written`: the thread's resource has the message in its write set,
so erasure's `writes` makes it settled, and it is outstanding).
`CoreAt.start` produces the link's start (`StartS`).
-/
import Kraken.Promising.SLR.EnvG.Prepay
import Kraken.Promising.SLR.EnvG.LinkR
import Kraken.Promising.SLR.Theorem1

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Tree shapes -/

/-- **Deterministic access**: a `choose` node only above access-free
subtrees (the access, if any, is reached by fences alone). -/
def DetAccess {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, AccessFree (k i)
  | .fence _ ret => DetAccess (ret ())
  | .load .. => True
  | .store .. => True
  | .rmw .. => True

/-- **The phase-1 tree shape** of an instruction tree: deterministic access,
at most one access, and no release-kind RMW. -/
def Phase1Shape (A : Arch) {σ : Type} (tree : EvTree σ) : Prop :=
  DetAccess tree ∧ SingleAccessS True (fun _ _ => True) (fun k => ¬ effRelRmw A k) True tree

/-- The first access of a tree reached by fences alone is a store satisfying
`P` (of its kind, exclusivity, location and value). -/
def FirstStore (P : StoreKind → Bool → Loc → Val → Prop) {σ : Type} : EvTree σ → Prop
  | .fence _ ret => FirstStore P (ret ())
  | .store k xcl l v _ => P k xcl l v
  | _ => False

theorem FirstStore.exists {P : StoreKind → Bool → Loc → Val → Prop} {σ : Type} :
    ∀ {tree : EvTree σ}, FirstStore P tree → ∃ k xcl l v, P k xcl l v
  | .fence _ ret, h => FirstStore.exists (tree := ret ()) h
  | .store k xcl l v _, h => ⟨k, xcl, l, v, h⟩
  | .done _, h => h.elim
  | .fault _, h => h.elim
  | .choose _ _, h => h.elim
  | .load .., h => h.elim
  | .rmw .., h => h.elim

/-- A first store of a `SingleAccessS` tree satisfies the store side
condition. -/
theorem FirstStore.and_sok {P : StoreKind → Bool → Loc → Val → Prop} {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Prop} {D : Prop} {σ : Type} :
    ∀ {tree : EvTree σ}, FirstStore P tree → SingleAccessS Lok Sok Rok D tree →
      FirstStore (fun k xcl l v => P k xcl l v ∧ Sok l v) tree
  | .fence _ ret, h, hs => FirstStore.and_sok (tree := ret ()) h hs
  | .store .., h, hs => ⟨h, hs.1⟩
  | .done _, h, _ => h.elim
  | .fault _, h, _ => h.elim
  | .choose _ _, h, _ => h.elim
  | .load .., h, _ => h.elim
  | .rmw .., h, _ => h.elim

/-- A single-access tree whose first store satisfies `Sok` satisfies any
`SingleAccessS` with that store condition. -/
theorem FirstStore.singleAccessS {P : StoreKind → Bool → Loc → Val → Prop} {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Prop} {D : Prop} (hP : ∀ k xcl l v, P k xcl l v → Sok l v) {σ : Type} :
    ∀ {tree : EvTree σ}, FirstStore P tree → SingleAccess tree → SingleAccessS Lok Sok Rok D tree
  | .fence _ ret, h, hs => FirstStore.singleAccessS hP (tree := ret ()) h hs
  | .store .., h, hs => ⟨hP _ _ _ _ h, hs⟩
  | .done _, h, _ => h.elim
  | .fault _, h, _ => h.elim
  | .choose _ _, h, _ => h.elim
  | .load .., h, _ => h.elim
  | .rmw .., h, _ => h.elim

/-- `SingleAccessS` is monotone in its side conditions. -/
theorem SingleAccessS.mono {Lok Lok' : Prop} {Sok Sok' : Loc → Val → Prop} {Rok Rok' : RmwKind → Prop}
    {D D' : Prop} (hL : Lok → Lok') (hS : ∀ l v, Sok l v → Sok' l v) (hR : ∀ k, Rok k → Rok' k) (hD : D → D')
    {σ : Type} : ∀ {tree : EvTree σ}, SingleAccessS Lok Sok Rok D tree → SingleAccessS Lok' Sok' Rok' D' tree
  | .done _, h => hD h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => SingleAccessS.mono hL hS hR hD (tree := k i) (h i)
  | .fence _ ret, h => SingleAccessS.mono hL hS hR hD (tree := ret ()) h
  | .load .., h => ⟨hL h.1, h.2⟩
  | .store .., h => ⟨hS _ _ h.1, h.2⟩
  | .rmw .., h => ⟨hR _ h.1, h.2⟩

/-- Phase-1 trees satisfy the link's side conditions without a release in
flight. -/
theorem Phase1Shape.none {A : Arch} {σ : Type} {tree : EvTree σ} (h : Phase1Shape A tree) :
    SingleAccessS (LokS none) (SokS none) (RokS A none) (LokS none) tree :=
  SingleAccessS.mono (fun _ => rfl) (fun _ _ _ => .inl rfl) (fun _ hk => ⟨rfl, hk⟩) (fun _ => rfl) h.2

/-! ## The in-flight instruction is the release store -/

/-- An access-free tree fulfils no promise. -/
theorem AccessFree.not_relFulfilsLive {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), AccessFree tree → ¬ tree.RelFulfilsLive A tid iv ts cx
  | .done _, _, _, h => h
  | .fault _, _, _, h => h
  | .choose _ k, cx, ha, ⟨i, h⟩ => AccessFree.not_relFulfilsLive (k i) cx (ha i) h
  | .fence k ret, cx, ha, h => AccessFree.not_relFulfilsLive (ret ()) (fenceStep cx k) ha h
  | .load .., _, ha, _ => ha
  | .store .., _, ha, _ => ha
  | .rmw .., _, ha, _ => ha

/-- **The live fulfilment of a promise by a phase-1 tree is its first
store**, of the promised message, and leaves every other own promise to its
location above the fulfilled one (`NoDead` after the write). -/
theorem relFulfilsLive_firstStore {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {prom : List Time}
    {mem : Memory} {w : Msg} (hts : ts ∈ prom) (hget : mem.get? ts = some w) {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), cx.prom = prom → cx.mem = mem → Phase1Shape A tree →
      tree.RelFulfilsLive A tid iv ts cx →
      FirstStore (fun _ _ l v => l = w.loc ∧ v = w.val ∧
        ∀ p ∈ prom, p ≠ ts → ∀ w', mem.get? p = some w' → w'.loc = l → ts < p) tree
  | .done _, _, _, _, _, h => h
  | .fault _, _, _, _, _, h => h
  | .choose _ k, cx, _, _, hs, ⟨i, h⟩ => AccessFree.not_relFulfilsLive (k i) cx (hs.1 i) h
  | .fence k ret, cx, hp, hm, hs, h =>
    relFulfilsLive_firstStore hts hget (ret ()) (fenceStep cx k) (by rw [fenceStep_prom]; exact hp)
      (by rw [fenceStep_mem]; exact hm) hs h
  | .load _ _ _ ret, _, _, _, hs, ⟨x, _, h⟩ => AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h
  | .rmw k _ _ _ ret, _, _, _, hs, ⟨x, _, h⟩ => by
    rcases h with h | ⟨_, _, _, _, h⟩
    · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
    · rcases h with ⟨⟨hk, _⟩, _⟩ | h
      · exact absurd hk hs.2.1
      · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
  | .store k xcl l v ret, cx, hp, hm, hs, h => by
    rcases h with ⟨c', hc', ⟨⟨-, htc, htc'⟩, hnd⟩ | h⟩ | h
    · rcases (mem_writeSuccs A tid).mp hc' with ⟨t0, ht0, w0, hw0, hl, hv, -, -, rfl⟩ | ⟨-, rfl⟩
      · -- the write fulfils `t0`, which must be `ts`
        obtain rfl : ts = t0 := Classical.byContradiction fun hne =>
          htc' ((List.mem_erase_of_ne hne).mpr htc)
        rw [hm, hget] at hw0
        obtain rfl := Option.some.inj hw0
        refine ⟨hl.symm, hv.symm, fun p hp' hne w' hw' hl' => ?_⟩
        have hpc : p ∈ cx.prom.erase ts := (List.mem_erase_of_ne hne).mpr (hp ▸ hp')
        have h1 := hnd p hpc w' (by rw [afterWrite_mem_eq, hm]; exact hw')
        rw [afterWrite_getCoh, hl'] at h1
        simp only [↓reduceIte] at h1
        omega_t
      · -- a fresh write keeps `ts` outstanding
        exfalso
        have hle : ts ≤ cx.mem.last := cx.mem.last_le_of_get?_eq_some (hm ▸ hget)
        have hne : ts ≠ cx.mem.last + 1 := by omega_t
        exact htc' ((List.mem_erase_of_ne hne).mpr (List.mem_append_left _ htc))
    · exact (AccessFree.not_relFulfilsLive (ret true) _ (hs.2.2 true) h).elim
    · exact (AccessFree.not_relFulfilsLive (ret false) _ (hs.2.2 false) h).elim

/-! ## The store's permission at the first store -/

/-- `StoreOk` at the first store reached by fences (`fenceState`). -/
def StoreOkAt (A : Arch) (tid : Nat) (pl : Plan) {σ : Type} : EvTree σ → State I → Prop
  | .fence k ret, s => StoreOkAt A tid pl (ret ()) (fenceState s k)
  | .store k xcl l v _, s => StoreOk A tid pl s k xcl l v
  | _, _ => True

/-- **`StoreOkAt` is a live tree judgment of `EnvG`** (every store node is
permitted, `EnvG`'s `ok`). -/
def TreeJLive.storeOk (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvG I A tid pl) σ where
  W := StoreOkAt A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store hok _ := hok
  rmw _ _ := trivial
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- The env state at the first store: a `fenceState` iterate (any property
`Φ` the fence states keep), with `StoreOk` and the first store's `P`. -/
theorem FirstStore.storeOk {A : Arch} {tid : Nat} {pl : Plan} {P : StoreKind → Bool → Loc → Val → Prop}
    {Φ : State I → Prop} (hΦ : ∀ s k, Φ s → Φ (fenceState s k)) {σ : Type} :
    ∀ (tree : EvTree σ) (s : State I), FirstStore P tree → StoreOkAt A tid pl tree s → Φ s →
      ∃ s' k xcl l v, P k xcl l v ∧ StoreOk A tid pl s' k xcl l v ∧ Φ s'
  | .fence k ret, s, h, hs, hp => FirstStore.storeOk hΦ (ret ()) (fenceState s k) h hs (hΦ s k hp)
  | .store k xcl l v _, s, h, hs, hp => ⟨s, k, xcl, l, v, h, hs, hp⟩
  | .done _, _, h, _, _ => h.elim
  | .fault _, _, h, _, _ => h.elim
  | .choose _ _, _, h, _, _ => h.elim
  | .load .., _, h, _, _ => h.elim
  | .rmw .., _, h, _, _ => h.elim

/-- The env views a write bound needs, below `n`. -/
structure WBnd (vs : Views) (n : Nat) : Prop where
  coh : ∀ l, vs.getCoh l ≤ n
  vrNew : vs.vrNew ≤ n
  vrOld : vs.vrOld ≤ n
  vrOldNR : vs.vrOldNR ≤ n
  vwNew : vs.vwNew ≤ n
  vwOld : vs.vwOld ≤ n
  vwOldNT : vs.vwOldNT ≤ n
  vCAP : vs.vCAP ≤ n

theorem WBnd.writeBound {vs : Views} {n : Nat} (h : WBnd vs n) (A : Arch) (k : StoreKind) (l : Loc) :
    WriteBound A vs k l (n + 1) :=
  ⟨Nat.lt_succ_of_le h.vwNew, Nat.lt_succ_of_le h.vCAP, Nat.lt_succ_of_le (h.coh l),
    fun _ => Nat.lt_succ_of_le (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨h.vrOld, h.vrOldNR⟩, h.vwOld⟩)⟩

theorem WBnd.fence {vs : Views} {n : Nat} (h : WBnd vs n) (k : FenceKind) : WBnd (fenceViews vs k) n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  cases k <;> exact ⟨h1, by simp only [fenceViews, fenceStep, Nat.max_le]; omega_t,
    by simp only [fenceViews, fenceStep]; omega_t, by simp only [fenceViews, fenceStep]; omega_t,
    by simp only [fenceViews, fenceStep, Nat.max_le]; omega_t, by simp only [fenceViews, fenceStep]; omega_t,
    by simp only [fenceViews, fenceStep]; omega_t, by simp only [fenceViews, fenceStep]; omega_t⟩

/-- Env views related at `idUpTo n` are below `n`. -/
theorem WBnd.of_viewsLe {n : Nat} {vs' vs : Views} (h : ViewsLe (TMap.idUpTo n) vs' vs) : WBnd vs' n :=
  ⟨fun l => Nat.le_trans (h.coh l) (Nat.min_le_right _ _), Nat.le_trans h.vrNew (Nat.min_le_right _ _),
    Nat.le_trans h.vrOld (Nat.min_le_right _ _), Nat.le_trans h.vrOldNR (Nat.min_le_right _ _),
    Nat.le_trans h.vwNew (Nat.min_le_right _ _), Nat.le_trans h.vwOld (Nat.min_le_right _ _),
    Nat.le_trans h.vwOldNT (Nat.min_le_right _ _), Nat.le_trans h.vCAP (Nat.min_le_right _ _)⟩

/-! ## The own pending mark survives world growth -/

/-- With a permission for `l`, `Plan.after` has the written message in the
write set of `l`. -/
theorem Plan.after_X_self (pl : Plan) (l : Loc) (v : Val) (ts : Time) (cl : Prop) (r : Res)
    (hq : 0 < ((pl.after l v ts cl r).wr l).q) : ((pl.after l v ts cl r).wr l).X (v, ts) := by
  unfold Plan.after at hq ⊢
  cases hrl : pl.rel l v <;> simp only [hrl, Bool.false_eq_true, ↓reduceIte, Res.addW_q] at hq ⊢ <;>
    exact (Res.addW_X_self _ _ _ _).mpr (.inr ⟨hq, rfl⟩)

/-- **An outstanding own promise whose message is in the thread's write set
is pending** (erasure's `writes`: the write set is the settled messages). -/
theorem pend_of_written {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {t : Thread I}
    {r : Res} (E : Erase (setRes rF tid r) g T c) (ht : c.threads[tid]? = some t) {ts : Time} (hts : ts ∈ t.prom)
    {w : Msg} (hget : c.mem.get? ts = some w) {l : Loc} {v : Val} (hX : (r.wr l).X (v, ts))
    (hq : 0 < (r.wr l).q) : ts ∈ g.pend := by
  have hn := lt_size_of_get? ht
  have hsub : (setRes rF tid r tid).Sub (total (setRes rF tid r) g c) := sub_total_thread hn
  rw [setRes_self] at hsub
  have htr : Tracked c g (total (setRes rF tid r) g c) l := by
    have := hsub.q_le l; exact .inl (by grind)
  rcases (E.writes l htr (v, ts)).mp (hsub.X hX) with ⟨h0, -⟩ | ⟨-, -, -, -, hs⟩
  · simp only at h0
    subst h0
    simp [Memory.get?] at hget
  · rcases hs with hno | hp
    · exact absurd ⟨tid, t, ht, hts⟩ hno
    · exact hp

/-! ## The invariant core -/

/-- **The in-flight facts** of the pending own promise `ts` of `⟨l, v⟩`:
the thread's next tree is the store of `v` to `l` (`SingleAccessS` at
`pf = some (l, v)`), every other own promise to `l` lies above `ts`, and the
thread holds a permission for `l`. -/
def InflFact (A : Arch) (c : Config I) (t : Thread I) (r : Res) (l : Loc) (v : Val) (ts : Time) : Prop :=
  (∀ tree, I.exec t.st = some tree →
      SingleAccessS (LokS (some (l, v))) (SokS (some (l, v))) (RokS A (some (l, v))) (LokS (some (l, v))) tree) ∧
    (∀ p ∈ t.prom, p ≠ ts → ∀ w, c.mem.get? p = some w → w.loc = l → ts < p) ∧ 0 < (r.wr l).q

/-- **The invariant core between instructions**: `EnvRel`, pending marks
below `|M|`, and the in-flight facts of a pending own promise. -/
structure CoreAt (A : Arch) (tid : Nat) (pl : Plan) (cl : Prop) (c : Config I) (r : Res) (g : Ghost) (σ : State I)
    (t : Thread I) : Prop where
  rel : EnvRel tid pl σ c t r g cl
  pendLe : ∀ ts ∈ g.pend, ts ≤ c.mem.last
  infl : ∀ ts l v, ts ∈ t.prom → ts ∈ g.pend → c.mem.get? ts = some ⟨l, v, tid⟩ → InflFact A c t r l v ts

section Core

variable {A : Arch} {tid : Nat} {pl : Plan} {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} {σ : State I}
  {t₀ t : Thread I}

/-- **The core along environment extension and world growth** (the
`NPSafe` instance `(c₀, g₀)` to the current `(c, g)`, with erasure at `c`
and the own-pending transport of `ThreadRuleRX`). The thread keeps its ISA
state. -/
theorem CoreAt.transport (h : CoreAt A tid pl cl c₀ r g₀ σ t₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g)
    (ht : c.threads[tid]? = some t) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) {rF : Nat → Res}
    {T : Nat → Prop} (E : Erase (setRes rF tid r) g T c) :
    t.st = t₀.st ∧ CoreAt A tid pl cl c r g σ t := by
  obtain ⟨hinit, hmsgs, hth⟩ := he
  obtain ⟨ps, ht', hps⟩ := hth t₀ h.rel.ht
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  have hle : c₀.mem.last ≤ c.mem.last := by
    have := hmsgs.length_le
    simp only [Array.length_toList] at this
    unfold Memory.last; omega_t
  have hpre : c₀.mem.Prefix c.mem := ⟨hinit, hmsgs⟩
  -- an own promise pending at `g₀` is an old one
  have hnp₀ : ∀ ts ∈ t₀.prom ++ ps, ts ∈ g₀.pend → ts ∈ t₀.prom := fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · exact h'
    · have := hps ts h'; have := h.pendLe ts hpd; omega_t
  have h1 := h.rel.ext ⟨hinit, hmsgs, hth⟩ ht hnp₀
  -- the in-flight facts at `c`
  have hinfl : ∀ ts l v, ts ∈ t₀.prom ++ ps → ts ∈ g₀.pend → c.mem.get? ts = some ⟨l, v, tid⟩ →
      InflFact A c { t₀ with prom := t₀.prom ++ ps } r l v ts := by
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
  -- the own pending mark survives the growth to `g`
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

/-- **The link's start from the core**: the in-flight message `pf`, the
start facts `StartS`, the side conditions of the thread's (phase-1) tree,
and, without a release in flight, the actual resource is the env's. -/
theorem CoreAt.start (h : CoreAt A tid pl cl c r g σ t) :
    ∃ pf, StartS tid c t g pf ∧
      (∀ tree, I.exec t.st = some tree → Phase1Shape A tree →
        SingleAccessS (LokS pf) (SokS pf) (RokS A pf) (LokS pf) tree) ∧ (pf = none → r = σ.r) := by
  rcases h.rel.res with ⟨hr, hn⟩ | ⟨ts, l, v, h1, h2, h3, -, h6⟩
  · exact ⟨none, ⟨fun _ => hn, fun _ _ e => absurd e (by simp)⟩, fun _ _ hs => hs.none, fun _ => hr⟩
  · obtain ⟨htree, habove, -⟩ := h.infl ts l v h1 h2 h3
    refine ⟨some (l, v), ⟨fun e => absurd e (by simp), fun l' v' e => ?_⟩, fun tree hex _ => htree tree hex,
      fun e => absurd e (by simp)⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨ts, h1, h2, h3, habove⟩

end Core

/-! ## Phase-1 shapes with release-kind RMWs

Additive (the names above are unchanged). `Phase1ShapeR` admits RMWs of
any kind; a release-kind RMW must have an operation that never fails
(**phase-1 limit**: the only RMWs that can fulfil an in-flight prepaid
release are release-kind, `RelFulfilsLive`, and a failing one would leave the
pending promise alive after the instruction, `EnvG/LinkR.lean`).
`FirstAccess` / `relFulfilsLive_firstAccess` extend `FirstStore` /
`relFulfilsLive_firstStore` to an RMW fulfilment, with the read of the
fulfilling path; `readSuccs_unpromise` / `NodeRel.readAt_promised` transfer
that read (taken in the promised context) to the environment's `ReadAt` at
the pre-promise anchor, which `RmwOk` and `PrepayGenericRmw'` take. -/

/-- **The phase-1 tree shape with release-kind RMWs**: deterministic access,
at most one access, a release-kind RMW's operation never fails. -/
def Phase1ShapeR (A : Arch) {σ : Type} (tree : EvTree σ) : Prop :=
  DetAccess tree ∧
    SingleAccessS2 True (fun _ _ => True) (fun k _ op => effRelRmw A k → ∀ x, op x ≠ none) True tree

/-- A plain phase-1 tree is a phase-1 tree with release-kind RMWs. -/
theorem Phase1Shape.toR {A : Arch} {σ : Type} {tree : EvTree σ} (h : Phase1Shape A tree) : Phase1ShapeR A tree :=
  ⟨h.1, SingleAccessS2.mono id (fun _ _ h => h) (fun _ _ _ hk hk' => absurd hk' hk) id h.2.toS2⟩

/-- Phase-1 trees with release-kind RMWs satisfy the `R` link's side
conditions without a release in flight. -/
theorem Phase1ShapeR.none {A : Arch} {σ : Type} {tree : EvTree σ} (h : Phase1ShapeR A tree) :
    SingleAccessS2 (LokS none) (SokS none) (RokR none) (LokS none) tree :=
  SingleAccessS2.mono (fun _ => rfl) (fun _ _ _ => .inl rfl) (fun _ _ _ _ => .inl rfl) (fun _ => rfl) h.2

/-- The first access of a tree reached by fences alone (from context `cx`)
is a store satisfying `S`, or an RMW satisfying `R` at the context it is
reached in. -/
def FirstAccess (S : StoreKind → Bool → Loc → Val → Prop) (R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop)
    {σ : Type} : Ctx → EvTree σ → Prop
  | cx, .fence k ret => FirstAccess S R (fenceStep cx k) (ret ())
  | _, .store k xcl l v _ => S k xcl l v
  | cx, .rmw k noRet l op _ => R cx k noRet l op
  | _, _ => False

/-- A first store is a first access. -/
theorem FirstStore.toAccess {P : StoreKind → Bool → Loc → Val → Prop}
    {R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop} {σ : Type} :
    ∀ {tree : EvTree σ} {cx : Ctx}, FirstStore P tree → FirstAccess P R cx tree
  | .fence _ ret, _, h => FirstStore.toAccess (tree := ret ()) h
  | .store .., _, h => h
  | .done _, _, h => h.elim
  | .fault _, _, h => h.elim
  | .choose _ _, _, h => h.elim
  | .load .., _, h => h.elim
  | .rmw .., _, h => h.elim

/-- Every other own promise to `l` lies above `ts` (prepay's `NoDead`). -/
def AboveAt (prom : List Time) (mem : Memory) (ts : Time) (l : Loc) : Prop :=
  ∀ p ∈ prom, p ≠ ts → ∀ w', mem.get? p = some w' → w'.loc = l → ts < p

/-- The fulfilling write of a live fulfilment of `ts` from a context with
promises `prom` and memory `mem` (a `writeSuccs` outcome whose promise list
no longer holds `ts` and has no dead promise) writes the promised message and
leaves every other own promise to its location above `ts`. -/
theorem fulfil_write_facts {xr : View} {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {prom : List Time} {mem : Memory}
    {w : Msg} (_hts : ts ∈ prom) (hget : mem.get? ts = some w) {cx c' : Ctx} (hp : cx.prom = prom) (hm : cx.mem = mem)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {trOpt : Option Time} {extra : View}
    (hc' : c' ∈ writeSuccs A tid iv cx k xcl l v trOpt extra xr) (htc : ts ∈ cx.prom) (htc' : ts ∉ c'.prom)
    (hnd : c'.NoDead) : l = w.loc ∧ v = w.val ∧ AboveAt prom mem ts l := by
  rcases (mem_writeSuccs A tid).mp hc' with ⟨t0, ht0, w0, hw0, hl, hv, -, -, rfl⟩ | ⟨-, rfl⟩
  · obtain rfl : ts = t0 := Classical.byContradiction fun hne =>
      htc' ((List.mem_erase_of_ne hne).mpr htc)
    rw [hm, hget] at hw0
    obtain rfl := Option.some.inj hw0
    refine ⟨hl.symm, hv.symm, fun p hp' hne w' hw' hl' => ?_⟩
    have hpc : p ∈ cx.prom.erase ts := (List.mem_erase_of_ne hne).mpr (hp ▸ hp')
    have h1 := hnd p hpc w' (by rw [afterWrite_mem_eq, hm]; exact hw')
    rw [afterWrite_getCoh, hl'] at h1
    simp only [↓reduceIte] at h1
    omega_t
  · exfalso
    have hle : ts ≤ cx.mem.last := cx.mem.last_le_of_get?_eq_some (hm ▸ hget)
    have hne : ts ≠ cx.mem.last + 1 := by omega_t
    exact htc' ((List.mem_erase_of_ne hne).mpr (List.mem_append_left _ htc))

/-- **The live fulfilment of a promise by a phase-1 tree with release-kind
RMWs is its first access**: a store of the promised message, or a
release-kind, never-failing RMW of the promised location whose read (in the
context it is reached in) gives the promised value; either leaves every other
own promise to the location above the fulfilled one. -/
theorem relFulfilsLive_firstAccess {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {prom : List Time}
    {mem : Memory} {w : Msg} (hts : ts ∈ prom) (hget : mem.get? ts = some w) {σ : Type} :
    ∀ (tree : EvTree σ) (cx : Ctx), cx.prom = prom → cx.mem = mem → Phase1ShapeR A tree →
      tree.RelFulfilsLive A tid iv ts cx →
      FirstAccess (fun _ _ l v => l = w.loc ∧ v = w.val ∧ AboveAt prom mem ts l)
        (fun cxN k noRet l op => l = w.loc ∧ effRelRmw A k ∧ (∀ x, op x ≠ none) ∧ AboveAt prom mem ts l ∧
          ∃ x ∈ readSuccs A iv (fenceOptCtx A cxN) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
            op x.2.1 = some w.val) cx tree
  | .done _, _, _, _, _, h => h
  | .fault _, _, _, _, _, h => h
  | .choose _ k, cx, _, _, hs, ⟨i, h⟩ => AccessFree.not_relFulfilsLive (k i) cx (hs.1 i) h
  | .fence k ret, cx, hp, hm, hs, h =>
    relFulfilsLive_firstAccess hts hget (ret ()) (fenceStep cx k) (by rw [fenceStep_prom]; exact hp)
      (by rw [fenceStep_mem]; exact hm) hs h
  | .load _ _ _ ret, _, _, _, hs, ⟨x, _, h⟩ => AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h
  | .rmw k noRet l op ret, cx, hp, hm, hs, ⟨x, hx, h⟩ => by
    rcases h with h | ⟨new, hop, c', hc', h⟩
    · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
    · rcases h with ⟨⟨hk, htc, htc'⟩, hnd⟩ | h
      · obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
        obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
        obtain ⟨hl, hv, hab⟩ := fulfil_write_facts hts hget (hp1.trans (hp0.trans hp)) (hm1.trans (hm0.trans hm))
          hc' htc htc' hnd
        subst hv
        exact ⟨hl, hk, hs.2.1 hk, hab, x, hx, hop⟩
      · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2.2 _) h).elim
  | .store k xcl l v ret, cx, hp, hm, hs, h => by
    rcases h with ⟨c', hc', ⟨⟨-, htc, htc'⟩, hnd⟩ | h⟩ | h
    · exact fulfil_write_facts hts hget hp hm hc' htc htc' hnd
    · exact (AccessFree.not_relFulfilsLive (ret true) _ (hs.2.2 true) h).elim
    · exact (AccessFree.not_relFulfilsLive (ret false) _ (hs.2.2 false) h).elim

/-! ## The read of a promised context, at the pre-promise anchor -/

/-- **A read in the promised context is a read before the promise**: from a
context whose memory has the thread's new promise appended at `|M| + 1` (and
whose promise list has it), the same timestamp and value are read in the
context before the promise (the new message is an own promise, unreadable;
the read window only shrinks on the prefix). -/
theorem readSuccs_unpromise {A : Arch} {iv : InstrViews} {P cx : Ctx} {ts : Time} {w : Msg}
    (hv : P.views = cx.views) (hp : P.prom = cx.prom ++ [ts]) (hm : P.mem = (cx.mem.append w).1)
    (hts : ts = cx.mem.last + 1) {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv P k xcl l noRet) :
    ∃ y ∈ readSuccs A iv cx k xcl l noRet, y.1 = x.1 ∧ y.2.1 = x.2.1 := by
  obtain ⟨t', v, rfl, hle, hrd, hwi, hpc⟩ := (mem_readSuccs A).mp hx
  rw [hp] at hpc
  simp only [List.contains_append, Bool.or_eq_false_iff] at hpc
  obtain ⟨hpc1, hpc2⟩ := hpc
  have hne : t' ≠ ts := fun e => by subst e; simp at hpc2
  rw [hm, Memory.last_append] at hle
  have hle' : t' ≤ cx.mem.last := by omega_t
  have hpre := Memory.Prefix.append cx.mem w
  have hrp : readPre A iv P k = readPre A iv cx k := by unfold readPre; rw [hv]
  rw [hm, hpre.read? hle'] at hrd
  rw [hm, hrp, hv] at hwi
  exact ⟨_, (mem_readSuccs A).mpr ⟨t', v, rfl, hle', hrd, hpre.writeIn hwi, hpc1⟩, rfl, rfl⟩

/-- **The environment read of an RMW on a promised context**: at a node
related by `NodeRel` (context `cx`, anchor `c`), a read of the RMW in a
context `P` with `cx`'s views, the thread's new promise `|M| + 1` and the
memory with it appended is offered by `EnvG` at the anchor `c` (`ReadAt` from
the RMW's read views), as `RmwOk` and `PrepayGenericRmw'` take it. -/
theorem NodeRel.readAt_promised {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I}
    {t : Thread I} {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}
    (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) {A : Arch} {w : Msg} {P : Ctx} (hv : P.views = cx.views)
    (hp : P.prom = cx.prom ++ [c.mem.last + 1]) (hm : P.mem = (c.mem.append w).1) {kk : LoadKind} {l : Loc}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A P) kk false l false) :
    ReadAt A tid (rmwReadViews A σ.vs) c kk l x.1 x.2.1 := by
  obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
  obtain ⟨hmP, hpP⟩ := fenceOptCtx_memProm (A := A) P
  have hc : (fenceOptCtx A cx).mem = c.mem := hm0.trans h.mem
  obtain ⟨y, hy, e1, e2⟩ := readSuccs_unpromise (cx := fenceOptCtx A cx) (ts := c.mem.last + 1) (w := w)
    (by rw [fenceOptCtx_views, fenceOptCtx_views, hv]) (by rw [hpP, hp0, hp]) (by rw [hmP, hc, hm])
    (by rw [hc]) hx
  obtain ⟨tr, old, cy⟩ := y
  obtain ⟨cxe, hy', -⟩ := (h.ctx.fenceOpt (A := A)).read hy
  have hy0 : (tr, old, cxe) ∈ readSuccs A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) kk false l false := hy'
  rw [← e1, ← e2]
  exact (readAt_rmw hy0).1

/-! ## The RMW's permission at the first access -/

/-- `RmwOk` at the first RMW reached by fences (`fenceState`), which is
live (`noRet = false`). -/
def RmwOkAt (A : Arch) (tid : Nat) (pl : Plan) {σ : Type} : EvTree σ → State I → Prop
  | .fence k ret, s => RmwOkAt A tid pl (ret ()) (fenceState s k)
  | .rmw k noRet l op _, s => noRet = false ∧ RmwOk A tid pl s k l op
  | _, _ => True

/-- **`RmwOkAt` is a live tree judgment of `EnvG`** (every live RMW node is
permitted, `EnvG`'s `ok`). -/
def TreeJLive.rmwOk (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvG I A tid pl) σ where
  W := RmwOkAt A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose _ := trivial
  load _ _ := trivial
  store _ _ := trivial
  rmw hok _ := ⟨rfl, hok⟩
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- **The env state at the first access**: walking the fences from `(s, cx)`
(any property `Φ` of env state and context the fences keep), the first access
is a permitted store satisfying `S`, or a permitted live RMW satisfying `R` at
the context it is reached in. -/
theorem FirstAccess.accessOk {A : Arch} {tid : Nat} {pl : Plan} {S : StoreKind → Bool → Loc → Val → Prop}
    {R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop} {Φ : State I → Ctx → Prop}
    (hΦ : ∀ s cx k, Φ s cx → Φ (fenceState s k) (fenceStep cx k)) {σ : Type} :
    ∀ (tree : EvTree σ) (s : State I) (cx : Ctx), FirstAccess S R cx tree → StoreOkAt A tid pl tree s →
      RmwOkAt A tid pl tree s → Φ s cx →
      (∃ s' cx' k xcl l v, S k xcl l v ∧ StoreOk A tid pl s' k xcl l v ∧ Φ s' cx') ∨
        (∃ s' cx' k l op, R cx' k false l op ∧ RmwOk A tid pl s' k l op ∧ Φ s' cx')
  | .fence k ret, s, cx, h, hs, hr, hp =>
    FirstAccess.accessOk hΦ (ret ()) (fenceState s k) (fenceStep cx k) h hs hr (hΦ s cx k hp)
  | .store k xcl l v _, s, cx, h, hs, _, hp => .inl ⟨s, cx, k, xcl, l, v, h, hs, hp⟩
  | .rmw k noRet l op _, s, cx, h, _, ⟨hn, hr⟩, hp => by
    subst hn; exact .inr ⟨s, cx, k, l, op, h, hr, hp⟩
  | .done _, _, _, h, _, _, _ => h.elim
  | .fault _, _, _, h, _, _, _ => h.elim
  | .choose _ _, _, _, h, _, _, _ => h.elim
  | .load .., _, _, h, _, _, _ => h.elim

/-- Some first access exists. -/
theorem FirstAccess.exists {S : StoreKind → Bool → Loc → Val → Prop}
    {R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop} {σ : Type} :
    ∀ {tree : EvTree σ} {cx : Ctx}, FirstAccess S R cx tree →
      (∃ k xcl l v, S k xcl l v) ∨ ∃ cx' k noRet l op, R cx' k noRet l op
  | .fence _ ret, _, h => FirstAccess.exists (tree := ret ()) h
  | .store k xcl l v _, _, h => .inl ⟨k, xcl, l, v, h⟩
  | .rmw k noRet l op _, cx, h => .inr ⟨cx, k, noRet, l, op, h⟩
  | .done _, _, h => h.elim
  | .fault _, _, h => h.elim
  | .choose _ _, _, h => h.elim
  | .load .., _, h => h.elim

/-- A first access of a `SingleAccessS2` tree satisfies its side
conditions. -/
theorem FirstAccess.and_ok {S : StoreKind → Bool → Loc → Val → Prop}
    {R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop} {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} {σ : Type} :
    ∀ {tree : EvTree σ} {cx : Ctx}, FirstAccess S R cx tree → SingleAccessS2 Lok Sok Rok D tree →
      FirstAccess (fun k xcl l v => S k xcl l v ∧ Sok l v) (fun cx k noRet l op => R cx k noRet l op ∧ Rok k l op)
        cx tree
  | .fence _ ret, _, h, hs => FirstAccess.and_ok (tree := ret ()) h hs
  | .store .., _, h, hs => ⟨h, hs.1⟩
  | .rmw .., _, h, hs => ⟨h, hs.1⟩
  | .done _, _, h, _ => h.elim
  | .fault _, _, h, _ => h.elim
  | .choose _ _, _, h, _ => h.elim
  | .load .., _, h, _ => h.elim

/-- A single-access tree whose first access satisfies the side conditions
satisfies `SingleAccessS2` with them. -/
theorem FirstAccess.singleAccessS2 {S : StoreKind → Bool → Loc → Val → Prop}
    {R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop} {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} (hS : ∀ k xcl l v, S k xcl l v → Sok l v)
    (hR : ∀ cx k noRet l op, R cx k noRet l op → Rok k l op) {σ : Type} :
    ∀ {tree : EvTree σ} {cx : Ctx}, FirstAccess S R cx tree → SingleAccess tree → SingleAccessS2 Lok Sok Rok D tree
  | .fence _ ret, _, h, hs => FirstAccess.singleAccessS2 hS hR (tree := ret ()) h hs
  | .store .., _, h, hs => ⟨hS _ _ _ _ h, hs⟩
  | .rmw .., _, h, hs => ⟨hR _ _ _ _ _ h, hs⟩
  | .done _, _, h, _ => h.elim
  | .fault _, _, h, _ => h.elim
  | .choose _ _, _, h, _ => h.elim
  | .load .., _, h, _ => h.elim

/-! ## The invariant core with release-kind RMWs

`InflFactR` / `CoreAtR` are `InflFact` / `CoreAt` with the in-flight tree
condition `SingleAccessS2 … (RokR (some (l, v)))`: the in-flight instruction
is the store of `v` to `l` or a never-failing RMW of `l`. The proofs of
`CoreAtR.transport` / `CoreAtR.start` are those of `CoreAt` (option (A):
additive duplication). -/

/-- **The in-flight facts with release-kind RMWs** of the pending own promise
`ts` of `⟨l, v⟩` (`InflFact` with `SingleAccessS2`/`RokR`). -/
def InflFactR (c : Config I) (t : Thread I) (r : Res) (l : Loc) (v : Val) (ts : Time) : Prop :=
  (∀ tree, I.exec t.st = some tree →
      SingleAccessS2 (LokS (some (l, v))) (SokS (some (l, v))) (RokR (some (l, v))) (LokS (some (l, v))) tree) ∧
    (∀ p ∈ t.prom, p ≠ ts → ∀ w, c.mem.get? p = some w → w.loc = l → ts < p) ∧ 0 < (r.wr l).q

/-- **The invariant core with release-kind RMWs** (`CoreAt` with
`InflFactR`). -/
structure CoreAtR (tid : Nat) (pl : Plan) (cl : Prop) (c : Config I) (r : Res) (g : Ghost) (σ : State I)
    (t : Thread I) : Prop where
  rel : EnvRel tid pl σ c t r g cl
  pendLe : ∀ ts ∈ g.pend, ts ≤ c.mem.last
  infl : ∀ ts l v, ts ∈ t.prom → ts ∈ g.pend → c.mem.get? ts = some ⟨l, v, tid⟩ → InflFactR c t r l v ts

section CoreR

variable {tid : Nat} {pl : Plan} {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} {σ : State I}
  {t₀ t : Thread I}

/-- **The core with release-kind RMWs along environment extension and world
growth** (`CoreAt.transport`). -/
theorem CoreAtR.transport (h : CoreAtR tid pl cl c₀ r g₀ σ t₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g)
    (ht : c.threads[tid]? = some t) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) {rF : Nat → Res}
    {T : Nat → Prop} (E : Erase (setRes rF tid r) g T c) :
    t.st = t₀.st ∧ CoreAtR tid pl cl c r g σ t := by
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
      InflFactR c { t₀ with prom := t₀.prom ++ ps } r l v ts := by
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

/-- **The `R` link's start from the core** (`CoreAt.start` with
`Phase1ShapeR` and `RokR`). -/
theorem CoreAtR.start {A : Arch} (h : CoreAtR tid pl cl c r g σ t) :
    ∃ pf, StartS tid c t g pf ∧
      (∀ tree, I.exec t.st = some tree → Phase1ShapeR A tree →
        SingleAccessS2 (LokS pf) (SokS pf) (RokR pf) (LokS pf) tree) ∧ (pf = none → r = σ.r) := by
  rcases h.rel.res with ⟨hr, hn⟩ | ⟨ts, l, v, h1, h2, h3, -, h6⟩
  · exact ⟨none, ⟨fun _ => hn, fun _ _ e => absurd e (by simp)⟩, fun _ _ hs => hs.none, fun _ => hr⟩
  · obtain ⟨htree, habove, -⟩ := h.infl ts l v h1 h2 h3
    refine ⟨some (l, v), ⟨fun e => absurd e (by simp), fun l' v' e => ?_⟩, fun tree hex _ => htree tree hex,
      fun e => absurd e (by simp)⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨ts, h1, h2, h3, habove⟩

end CoreR

end Kraken.Promising.SLR.EnvG
