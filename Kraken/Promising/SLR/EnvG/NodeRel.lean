/-
Whole-thread environment (`EnvG`): the **relations** between `EnvG`'s state and
the actual thread. ISA-neutral.

- `Inflight`: the actual resource is the env's virtual one (no own pending
  promise), or the virtual one is the actual one after the thread's single
  in-flight prepaid release (§1d): `r = Plan.after l v ts σ.r` for the one
  pending own promise `ts` of `⟨l, v⟩`. (The rule link dropped the conjunct "`⟨l, v⟩` is
  a planned release": prepay must also cover release-kind stores of pure
  values, e.g. every x64 store, whose virtual resource is `σ.r.addW`.)
  F1: `Inflight` takes the env's `cl` and the split's knowledge is that of
  the prepay, `∃ P, (cl → P) ∧ r = Plan.after l v ts P σ.r`
  (`Inflight.mono_cl`: stable as `cl` grows).
- `FencedInv`: the fence ghost bits (§3) on the actual views:
  `fencedR → max vrOld vrOldNR ≤ vwNew`, `fencedW → max vwOld vwOldNT ≤ vwNew`.
- `NodeRel`: before the (single) access of an instruction of thread `tid`
  (state `t` in `c`, instruction views `iv`): the actual context has `c`'s
  memory and `t`'s promises, erasure holds at `c` (validity-free), the env's
  snapshot and ghost are below, and the actual context is related to the
  env's context `envCtx tid σ.vs c` by `CtxLe` (§1b: instruction-local
  fields at their defaults, instruction views `0`).
- `PostRel`: after it (snapshot below the configuration at the context, the
  env's views those of some `CtxLe`-related context).
- `EnvRel`: between instructions (`σ.snap ⊑ c`, `σ.g ≤ g`, `ViewsLe` at
  `idUpTo |M|` on the thread's views, `Inflight`, fence bits, `cl → σ.cl`);
  `EnvRel.toNodeRel` (at the instruction's start context `ctx₀`), stability
  under `Ghost.Le` (`EnvRel.ghostLe`), memory growth by other threads
  (`EnvRel.ext`) and `finishInstr` (`PostRel.finish`).

`seen` (§2.2) needs no invariant: `slot_of_seen` (`EnvG/Seen.lean`) takes its
hypotheses at use.
-/
import Kraken.Promising.SLR.EnvG.Env
import Kraken.Promising.SLR.EnvG.CtxSim
import Kraken.Promising.SLR.ReleaseStore

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- The context simulation's environment instruction views are `EnvG`'s. -/
theorem zeroIv_eq : zeroIv = iv0 := rfl

/-! ## The in-flight relation and the fence bits -/

/-- **The in-flight relation** (§1d) between the env's virtual resource `rv`
and the actual resource `r`, at ghost `g`, for promise set `prom` in memory
`mem`: no own promise is pending and `r = rv`, or exactly one own promise
`ts` is pending, its message `⟨l, v⟩` is a planned release, and `rv` counts
it as performed. -/
def Inflight (tid : Nat) (pl : Plan) (cl : Prop) (rv r : Res) (g : Ghost) (prom : List Time) (mem : Memory) :
    Prop :=
  (r = rv ∧ ∀ ts ∈ prom, ts ∉ g.pend) ∨
  ∃ ts l v, ts ∈ prom ∧ ts ∈ g.pend ∧ mem.get? ts = some ⟨l, v, tid⟩ ∧
    (∃ P : Prop, (cl → P) ∧ r = pl.after l v ts P rv) ∧ ∀ ts' ∈ prom, ts' ∈ g.pend → ts' = ts

/-- The in-flight mode: some own promise is pending. -/
def InflightMode (tid : Nat) (pl : Plan) (cl : Prop) (rv r : Res) (g : Ghost) (prom : List Time) (mem : Memory) :
    Prop :=
  ∃ ts l v, ts ∈ prom ∧ ts ∈ g.pend ∧ mem.get? ts = some ⟨l, v, tid⟩ ∧
    (∃ P : Prop, (cl → P) ∧ r = pl.after l v ts P rv) ∧ ∀ ts' ∈ prom, ts' ∈ g.pend → ts' = ts

theorem Inflight.congr {tid : Nat} {pl : Plan} {cl : Prop} {rv r : Res} {g : Ghost} {p p' : List Time}
    {m m' : Memory} (h : Inflight tid pl cl rv r g p m) (hp : p' = p) (hm : m' = m) :
    Inflight tid pl cl rv r g p' m' := by
  subst hp hm; exact h

/-- `Inflight` under stronger knowledge (the in-flight release's split was
chosen at the prepay, with knowledge the current one implies; F1). -/
theorem Inflight.mono_cl {tid : Nat} {pl : Plan} {cl cl' : Prop} {rv r : Res} {g : Ghost} {p : List Time}
    {m : Memory} (h : Inflight tid pl cl rv r g p m) (hc : cl' → cl) : Inflight tid pl cl' rv r g p m := by
  rcases h with h | ⟨ts, l, v, h1, h2, h3, ⟨P, hP, h5⟩, h6⟩
  · exact .inl h
  · exact .inr ⟨ts, l, v, h1, h2, h3, ⟨P, fun h => hP (hc h), h5⟩, h6⟩

/-- **The fence-bit invariants** (§3) on the actual views. -/
structure FencedInv (fR fW : Bool) (vs : Views) : Prop where
  r : fR = true → max vs.vrOld vs.vrOldNR ≤ vs.vwNew
  w : fW = true → max vs.vwOld vs.vwOldNT ≤ vs.vwNew

theorem FencedInv.fence {fR fW : Bool} {vs : Views} (h : FencedInv fR fW vs) (k : FenceKind) :
    FencedInv (fenceSetsR k || fR) (fenceSetsW k || fW) (fenceViews vs k) := by
  have hr := h.r; have hw := h.w
  cases k <;> refine ⟨fun e => ?_, fun e => ?_⟩ <;>
    simp only [fenceSetsR, fenceSetsW, Bool.true_or, Bool.false_or] at e <;>
    simp only [fenceViews, fenceStep] <;>
    first
    | (have := hr e; omega_t)
    | (have := hw e; omega_t)
    | omega_t

/-- A load keeps `vwOld`, `vwOldNT` and raises `vwNew`: `fencedW` survives. -/
theorem FencedInv.read {A : Arch} {iv : InstrViews} {fR fW : Bool} {cx : Ctx} (h : FencedInv fR fW cx.views)
    {k : LoadKind} {xcl : Bool} {l : Loc} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l false) :
    FencedInv false fW x.2.2.views := by
  obtain ⟨t, v, rfl, -⟩ := (mem_readSuccs A).mp hx
  refine ⟨fun e => absurd e (by decide), fun e => ?_⟩
  have := h.w e
  simp only [readNext, Views.setCoh]
  split <;> omega_t

theorem afterWrite_views_keep (A : Arch) (iv : InstrViews) (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc)
    (v : Val) (t : Time) (νfwd : View) (ful : Bool) :
    (afterWrite A iv c k xcl l v t νfwd ful).views.vrOld = c.views.vrOld ∧
    (afterWrite A iv c k xcl l v t νfwd ful).views.vrOldNR = c.views.vrOldNR ∧
    (afterWrite A iv c k xcl l v t νfwd ful).views.vwNew = c.views.vwNew := ⟨rfl, rfl, rfl⟩

/-- A write keeps `vrOld`, `vrOldNR` and `vwNew`. -/
theorem writeSuccs_views_keep (A : Arch) (tid : Nat) {iv : InstrViews} {cx : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra) :
    cx'.views.vrOld = cx.views.vrOld ∧ cx'.views.vrOldNR = cx.views.vrOldNR ∧ cx'.views.vwNew = cx.views.vwNew := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨-, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · exact afterWrite_views_keep A iv _ _ _ _ _ _ _ _
  · exact afterWrite_views_keep A iv _ _ _ _ _ _ _ _

/-- A store keeps `fencedR`'s invariant. -/
theorem FencedInv.write {A : Arch} {tid : Nat} {iv : InstrViews} {fR fW : Bool} {cx : Ctx}
    (h : FencedInv fR fW cx.views) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {cx' : Ctx} (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra) :
    FencedInv fR false cx'.views := by
  obtain ⟨e1, e2, e3⟩ := writeSuccs_views_keep A tid hc
  refine ⟨fun e => ?_, fun e => absurd e (by decide)⟩
  rw [e1, e2, e3]; exact h.r e

/-! ## Anchors and ghosts -/

theorem SnapLe.refl (tid : Nat) (c : Config I) : SnapLe tid c c :=
  ⟨rfl, List.prefix_refl _, fun t ht => ⟨t, ht, [], by simp, fun _ h => absurd h List.not_mem_nil⟩⟩

theorem SnapLe.trans {tid : Nat} {c₁ c₂ c₃ : Config I} (h₁ : SnapLe tid c₁ c₂) (h₂ : SnapLe tid c₂ c₃) :
    SnapLe tid c₁ c₃ := by
  refine ⟨h₂.init.trans h₁.init, h₁.msgs.trans h₂.msgs, fun t ht => ?_⟩
  obtain ⟨t₂, ht₂, ps, hp, hps⟩ := h₁.prom t ht
  obtain ⟨t₃, ht₃, ps', hp', hps'⟩ := h₂.prom t₂ ht₂
  have hle : c₁.mem.last ≤ c₂.mem.last := by
    have := h₁.msgs.length_le
    simp only [Array.length_toList] at this
    unfold Memory.last; omega_t
  refine ⟨t₃, ht₃, ps ++ ps', by rw [hp', hp, List.append_assoc], fun p hp'' => ?_⟩
  rcases List.mem_append.mp hp'' with h | h
  · exact hps p h
  · exact Nat.lt_of_le_of_lt hle (hps' p h)

/-- The snapshot after a write is below the configuration at the context
after it (same memory, same promises of the thread). -/
theorem snapLe_snapAfter {tid : Nat} {c : Config I} {t : Thread I} (ht : c.threads[tid]? = some t)
    {cxe cx : Ctx} (hm : cxe.mem = cx.mem) (hp : cxe.prom = cx.prom) :
    SnapLe tid (snapAfter tid c cxe) (c.withThread tid { t with prom := cx.prom } cx.mem) := by
  have hn := lt_size_of_get? ht
  refine ⟨by simp only [snapAfter, Config.withThread, hm],
    (by simp only [snapAfter, Config.withThread, hm]; exact List.prefix_refl _), fun t' ht' => ?_⟩
  have e : (snapAfter tid c cxe).threads[tid]? = some { t with prom := cxe.prom } := by
    simp only [snapAfter, Array.getElem?_modify, ht, ↓reduceIte, Option.map_some]
  rw [e] at ht'
  cases ht'
  refine ⟨{ t with prom := cx.prom }, by rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl], [], ?_,
    fun _ h => absurd h List.not_mem_nil⟩
  simp only [List.append_nil, hp]

/-- The configuration at a context with the thread's own promises and the
configuration's memory is the configuration. -/
theorem withThread_ctx {tid : Nat} {c : Config I} {t : Thread I} (ht : c.threads[tid]? = some t) {cx : Ctx}
    (hm : cx.mem = c.mem) (hp : cx.prom = t.prom) : c.withThread tid { t with prom := cx.prom } cx.mem = c := by
  rw [hm, hp]; exact Config.withThread_self c ht

theorem ownProm_eq {tid : Nat} {c : Config I} {t : Thread I} (ht : c.threads[tid]? = some t) :
    ownProm tid c = t.prom := by
  simp only [ownProm, ht, Option.map_some, Option.getD_some]

theorem Ghost.Le.unpend (g : Ghost) (ts : Time) : g.Le (unpend g ts) := ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩

theorem Ghost.Le.storeGhost (g : Ghost) (x : Loc) (tw : Time) (rel : Bool) (ss : List Slot) :
    g.Le (storeGhost g x tw rel ss) := ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩

theorem Ghost.Le.rmwGhost (g : Ghost) (x : Loc) (tr tw : Time) (rel : Bool) (ss : List Slot) :
    g.Le (rmwGhost g x tr tw rel ss) := ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩

/-! ## Erasure facts used by the transports -/

section EraseFacts

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- **An own outstanding non-pending promise has a pure value** (`Erase.pure`,
`relSettled`): its message is not in release mode. A planned release (impure,
`StoreOk`) therefore never fulfils one. -/
theorem Erase.pure_of_own (E : Erase rF g T c) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t)
    {ts : Time} (hts : ts ∈ t.prom) (hnp : ts ∉ g.pend) {l : Loc} {v : Val}
    (hget : c.mem.get? ts = some ⟨l, v, tid⟩) : Pred.Pure (g.rel l) v := by
  have hrd := read?_of_get?' hget
  refine E.pure l ts v hrd fun hk => ?_
  rcases E.relSettled _ hk with h | h
  · exact h ⟨tid, t, ht, hts⟩
  · exact hnp h

/-- **A fresh timestamp is not claimed**: claims are on messages below a
claimer in memory. -/
theorem Erase.not_claimed_fresh (E : Erase rF g T c) {l : Loc} {tw : Time} (htw : c.mem.last < tw) :
    ¬ g.Claimed (l, tw) := by
  intro h
  obtain ⟨⟨k, tw'⟩, hk, he⟩ := List.mem_map.mp h
  simp only at he
  subst he
  obtain ⟨hlt, w, hw, -⟩ := E.claimsAt _ tw' hk
  have := c.mem.last_le_of_get?_eq_some hw
  simp only at hlt
  omega_t

end EraseFacts

/-! ## The node relations -/

/-- **Before the access** (`NodeRel`) of an instruction of thread `tid` (state
`t` in `c`, instruction views `iv`, frame `rF`) that started with virtual
resource `rv₀`, ghost `g₀` and clean-erasure knowledge `cl₀`: env state `σ`,
actual resource `r`, ghost `g`, context `cx`. -/
structure NodeRel (tid : Nat) (pl : Plan) (iv : InstrViews) (rF : Nat → Res) (c : Config I) (t : Thread I)
    (rv₀ : Res) (g₀ : Ghost) (cl₀ : Prop) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx) : Prop where
  ht : c.threads[tid]? = some t
  mach : c.MachInv
  mem : cx.mem = c.mem
  prom : cx.prom = t.prom
  erase : Erase (setRes rF tid r) g (fun _ => True) c
  g0 : g = g₀
  rv : σ.r = rv₀
  snap : SnapLe tid σ.snap c
  ghost : σ.g.Le g
  ctx : CtxLe iv cx (envCtx tid σ.vs c)
  res : Inflight tid pl σ.cl σ.r r g t.prom c.mem
  cl : cl₀ → σ.cl
  fenced : FencedInv σ.fencedR σ.fencedW cx.views

/-- **After the access** (`PostRel`): the env's snapshot is below the
configuration at the context, its views those of a `CtxLe`-related context;
the clean-erasure knowledge an instruction adds (`ClAt` at the start) is in
`σ.cl`. -/
structure PostRel (tid : Nat) (pl : Plan) (iv : InstrViews) (c : Config I) (t : Thread I) (rv₀ : Res) (g₀ : Ghost)
    (cl₀ : Prop) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx) : Prop where
  snap : SnapLe tid σ.snap (c.withThread tid { t with prom := cx.prom } cx.mem)
  ghost : σ.g.Le g
  ctx : ∃ cxe, CtxLe iv cx cxe ∧ cxe.views = σ.vs
  res : Inflight tid pl σ.cl σ.r r g cx.prom cx.mem
  cl : cl₀ ∧ ClAt tid rv₀ g₀ c → σ.cl
  fenced : FencedInv σ.fencedR σ.fencedW cx.views

section Rel

variable {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {σ : State I} {r : Res} {g : Ghost} {cx : Ctx}

/-- Erasure at the context before the access. -/
theorem NodeRel.erAt (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) :
    ErAt rF (fun _ => True) c t tid r g cx := by
  unfold ErAt; rw [withThread_ctx h.ht h.mem h.prom]; exact h.erase

/-- The access's anchor is `(c, g)`. -/
theorem NodeRel.anchorOk (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) : AnchorOk tid σ c g :=
  ⟨h.snap, h.ghost, ⟨_, h.erase⟩, h.mach, lt_size_of_get? h.ht⟩

/-- An access-free tree ends where it started. -/
theorem NodeRel.post (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) :
    PostRel tid pl iv c t rv₀ g₀ cl₀ σ r g cx where
  snap := by rw [withThread_ctx h.ht h.mem h.prom]; exact h.snap
  ghost := h.ghost
  ctx := ⟨_, h.ctx, rfl⟩
  res := h.res.congr h.prom h.mem
  cl hc := h.cl hc.1
  fenced := h.fenced

/-- The fence's environment state. -/
def fenceState (σ : State I) (k : FenceKind) : State I :=
  { σ with vs := fenceViews σ.vs k, fencedR := fenceSetsR k || σ.fencedR, fencedW := fenceSetsW k || σ.fencedW }

theorem fenceOut_fenceState (σ : State I) (k : FenceKind) : FenceOut σ (fenceState σ k) k := rfl

/-- **Fence transport** before the access (`CtxLe.fence`, `CtxLe.congrT`). -/
theorem NodeRel.fence (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (k : FenceKind) :
    NodeRel tid pl iv rF c t rv₀ g₀ cl₀ (fenceState σ k) r g (fenceStep cx k) where
  ht := h.ht
  mach := h.mach
  mem := by rw [fenceStep_mem]; exact h.mem
  prom := by rw [fenceStep_prom]; exact h.prom
  erase := h.erase
  g0 := h.g0
  rv := h.rv
  snap := h.snap
  ghost := h.ghost
  ctx := (h.ctx.fence k).congrT (by rw [fenceStep_views]; rfl) (fenceStep_prom (envCtx tid σ.vs c) k).symm
    (fenceStep_mem (envCtx tid σ.vs c) k).symm
    (by cases k <;> rfl) (by cases k <;> rfl) (by cases k <;> rfl) (by cases k <;> rfl)
  res := h.res
  cl := h.cl
  fenced := by rw [fenceStep_views]; exact h.fenced.fence k

/-- **Fence transport** after the access. -/
theorem PostRel.fence (h : PostRel tid pl iv c t rv₀ g₀ cl₀ σ r g cx) (k : FenceKind) :
    PostRel tid pl iv c t rv₀ g₀ cl₀ (fenceState σ k) r g (fenceStep cx k) where
  snap := by rw [fenceStep_mem, fenceStep_prom]; exact h.snap
  ghost := h.ghost
  ctx := by
    obtain ⟨cxe, hc, hv⟩ := h.ctx
    exact ⟨_, hc.fence k, by rw [fenceStep_views, hv]; rfl⟩
  res := by rw [fenceStep_mem, fenceStep_prom]; exact h.res
  cl := h.cl
  fenced := by rw [fenceStep_views]; exact h.fenced.fence k

end Rel

/-! ## Between instructions -/

/-- **The relation between instructions** (§4.1): env state `σ`, actual
configuration `c` with thread `t`, resource `r`, ghost `g`, clean-erasure
knowledge `cl`. -/
structure EnvRel (tid : Nat) (pl : Plan) (σ : State I) (c : Config I) (t : Thread I) (r : Res) (g : Ghost)
    (cl : Prop) : Prop where
  ht : c.threads[tid]? = some t
  snap : SnapLe tid σ.snap c
  ghost : σ.g.Le g
  views : ViewsLe (TMap.idUpTo c.mem.last) σ.vs t.views
  bnd : t.Bnd c.mem.last
  res : Inflight tid pl σ.cl σ.r r g t.prom c.mem
  cl : cl → σ.cl
  fenced : FencedInv σ.fencedR σ.fencedW t.views

section EnvRel

variable {tid : Nat} {pl : Plan} {σ : State I} {c : Config I} {t : Thread I} {r : Res} {g : Ghost} {cl : Prop}

/-- **At the instruction's start** (`ctx₀`): the node relation, from
erasure, the machine invariants and the thread's promises bounded by `|M|`. -/
theorem EnvRel.toNodeRel (h : EnvRel tid pl σ c t r g cl) (rF : Nat → Res) (d : InstrDeps I.RegId)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) :
    NodeRel tid pl (instrViews t d) rF c t σ.r g cl σ r g (ctx₀ t tid c.mem) where
  ht := h.ht
  mach := hm
  mem := rfl
  prom := rfl
  erase := E
  g0 := rfl
  rv := rfl
  snap := h.snap
  ghost := h.ghost
  ctx := by
    have hp : ∀ s ∈ t.prom, s ≤ c.mem.last := fun s hs => by
      obtain ⟨w, hw, -⟩ := hm.promWf tid t h.ht s hs
      exact c.mem.last_le_of_get?_eq_some hw
    have e : envCtx tid σ.vs c = { views := σ.vs, prom := t.prom, mem := c.mem, log := [] } := by
      simp only [envCtx, ownProm_eq h.ht]
    rw [e]
    exact CtxLe.start h.views h.bnd.views hp (instrViews_le h.bnd.regs d)
  res := h.res
  cl := h.cl
  fenced := h.fenced

/-- **Stability under ghost growth.** -/
theorem EnvRel.ghostLe (h : EnvRel tid pl σ c t r g cl) {g' : Ghost} (hg : g.Le g')
    (hp : ∀ ts ∈ t.prom, (ts ∈ g'.pend ↔ ts ∈ g.pend)) : EnvRel tid pl σ c t r g' cl := by
  refine { h with ghost := h.ghost.trans hg, res := ?_ }
  rcases h.res with ⟨e, hn⟩ | ⟨ts, l, v, h1, h2, h3, h5, h6⟩
  · exact .inl ⟨e, fun ts hts h' => hn ts hts ((hp ts hts).mp h')⟩
  · exact .inr ⟨ts, l, v, h1, (hp ts h1).mpr h2, h3, h5, fun ts' h' h'' => h6 ts' h' ((hp ts' h').mp h'')⟩

/-- `ViewsLe` at `idUpTo n` lifts to any `n' ≥ n` for target views bounded
by `n`. -/
theorem viewsLe_idUpTo_mono {n n' : Nat} {vs' vs : Views} (h : ViewsLe (TMap.idUpTo n) vs' vs) (hb : vs.Bnd n)
    (hn : n ≤ n') : ViewsLe (TMap.idUpTo n') vs' vs := by
  have e : ∀ {x : Nat}, x ≤ n → (TMap.idUpTo n).fv x = (TMap.idUpTo n').fv x := fun hx => by
    show min _ _ = min _ _; omega_t
  have hl := hb.le
  refine ⟨fun l => e (hl.coh l) ▸ h.coh l, e hl.vrNew ▸ h.vrNew, e hl.vrOld ▸ h.vrOld, e hl.vrOldNR ▸ h.vrOldNR,
    e hl.vwNew ▸ h.vwNew, e hl.vwOld ▸ h.vwOld, e hl.vwOldNT ▸ h.vwOldNT, e hl.vCAP ▸ h.vCAP, e hl.vRel ▸ h.vRel,
    fun l => ?_, ?_⟩
  · have hf := h.fwd l
    revert hf
    cases hfa : vs.getFwd l <;> cases vs'.getFwd l <;> simp only [FwdLe, imp_self]
    rename_i a b
    rintro ⟨h1, h2, h3, h4, h5⟩
    have ht := hb.fwdTime l a hfa
    have hv := hl.fwd l a hfa
    refine ⟨Nat.le_trans ht hn, ?_, e hv ▸ h3, h4, e (Nat.le_trans (Nat.min_le_right _ _) ht) ▸ h5⟩
    rw [h2]; rfl
  · have hx := h.xclb
    revert hx
    cases hxa : vs.xclb with
    | none => cases vs'.xclb <;> simp only [XclLe, imp_self]
    | some p =>
      obtain ⟨a, ν, l⟩ := p
      cases vs'.xclb with
      | none => simp only [XclLe, imp_self]
      | some q =>
        obtain ⟨a', ν', l'⟩ := q
        simp only [XclLe]
        rintro ⟨h1, h2, h3, h4⟩
        have hb' := hb.xclb a ν l hxa
        refine ⟨Nat.le_trans hb'.1 hn, ?_, e hb'.2 ▸ h3, h4⟩
        rw [h2]; rfl

/-- **Stability under other threads' steps** (`EnvExt`, from the anchor's
side: memory grows by a prefix, the thread's promise list grows by promises
above the old memory, which are not pending). -/
theorem EnvRel.ext (h : EnvRel tid pl σ c t r g cl) {c₁ : Config I} (he : EnvExt tid c c₁) {t₁ : Thread I}
    (ht₁ : c₁.threads[tid]? = some t₁) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ t.prom) :
    EnvRel tid pl σ c₁ t₁ r g cl := by
  obtain ⟨hinit, hmsgs, hth⟩ := he
  obtain ⟨ps, ht', hps⟩ := hth t h.ht
  rw [ht₁] at ht'
  cases ht'
  have hle : c.mem.last ≤ c₁.mem.last := by
    have := hmsgs.length_le
    simp only [Array.length_toList] at this
    unfold Memory.last; omega_t
  have hpre : c.mem.Prefix c₁.mem := ⟨hinit, hmsgs⟩
  refine ⟨ht₁, h.snap.trans ⟨hinit, hmsgs, fun t' ht'' => ?_⟩, h.ghost,
    viewsLe_idUpTo_mono h.views h.bnd.views hle, ⟨(h.bnd.mono hle).views, (h.bnd.mono hle).regs⟩, ?_, h.cl,
    h.fenced⟩
  · rw [h.ht] at ht''; cases ht''
    exact ⟨_, ht₁, ps, rfl, hps⟩
  · rcases h.res with ⟨e, hn⟩ | ⟨ts, l, v, h1, h2, h3, h5, h6⟩
    · refine .inl ⟨e, fun ts hts hpd => ?_⟩
      exact hn ts (hnp ts hts hpd) hpd
    · refine .inr ⟨ts, l, v, List.mem_append_left _ h1, h2, ?_, h5, fun ts' h' h'' => h6 ts' (hnp ts' h' h'') h''⟩
      rw [hpre.get? (c.mem.last_le_of_get?_eq_some h3)]; exact h3

/-- **`finishInstr` re-establishes `EnvRel`**: after the instruction
(`PostRel` at the final context `cx`, thread `th` from `finishInstr`), in the
configuration `c.withThread tid th cx.mem`, provided the instruction started
without an in-flight release (`r₀ = rv₀`, so that the actual new clean
knowledge `ClAt tid r₀ g₀ c` is the env's). -/
theorem PostRel.finish {iv : InstrViews} {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop} {cx : Ctx}
    (h : PostRel tid pl iv c t rv₀ g₀ cl₀ σ r g cx) (ht : c.threads[tid]? = some t) (hb : cx.Bnd)
    (hiv : iv.Le cx.mem.last) (hregs : t.RegsLe cx.mem.last) {d : InstrDeps I.RegId} {st : I.State}
    {th : Thread I} (hth : th ∈ finishInstr t d iv st cx) :
    EnvRel tid pl σ (c.withThread tid th cx.mem) th r g (cl₀ ∧ ClAt tid rv₀ g₀ c) := by
  have hn := lt_size_of_get? ht
  obtain ⟨hp, hv⟩ := finishInstr_relKey hth
  obtain ⟨-, -, -, hcap⟩ := finishInstr_vmono hth
  have hth' : (c.withThread tid th cx.mem).threads[tid]? = some th := by
    rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl]
  have hf : ∀ {f : Views → Nat}, (∀ vs : Views, f { vs with vCAP := 0 } = f vs) → f th.views = f cx.views :=
    fun hf' => by rw [← hf', hv, hf']
  obtain ⟨cxe, hc, hcv⟩ := h.ctx
  have hvl := hc.sim.rel.views
  rw [hcv] at hvl
  refine ⟨hth', ?_, h.ghost, ?_, finishInstr_bnd hb.views hb.loadViews hb.succView hiv hregs th hth, ?_, h.cl, ?_⟩
  · refine h.snap.trans ⟨rfl, List.prefix_refl _, fun t' ht' => ?_⟩
    rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl] at ht'
    cases ht'
    exact ⟨th, hth', [], by rw [List.append_nil, hp], fun _ h => absurd h List.not_mem_nil⟩
  · have e1 : ∀ l, th.views.getCoh l = cx.views.getCoh l := fun l => hf (f := fun vs => vs.getCoh l) fun _ => rfl
    have e2 : ∀ l, th.views.getFwd l = cx.views.getFwd l := fun l => by
      have := congrArg (fun vs : Views => vs.getFwd l) hv; exact this
    have e3 : th.views.xclb = cx.views.xclb := by have := congrArg Views.xclb hv; exact this
    refine ⟨fun l => by rw [e1]; exact hvl.coh l, by rw [hf (f := Views.vrNew) fun _ => rfl]; exact hvl.vrNew,
      by rw [hf (f := Views.vrOld) fun _ => rfl]; exact hvl.vrOld,
      by rw [hf (f := Views.vrOldNR) fun _ => rfl]; exact hvl.vrOldNR,
      by rw [hf (f := Views.vwNew) fun _ => rfl]; exact hvl.vwNew,
      by rw [hf (f := Views.vwOld) fun _ => rfl]; exact hvl.vwOld,
      by rw [hf (f := Views.vwOldNT) fun _ => rfl]; exact hvl.vwOldNT,
      by have := hvl.vCAP; show _ ≤ min _ cx.mem.last; change _ ≤ min _ _ at this; omega_t,
      by rw [hf (f := Views.vRel) fun _ => rfl]; exact hvl.vRel,
      fun l => by rw [e2]; exact hvl.fwd l, by rw [e3]; exact hvl.xclb⟩
  · rw [hp]; exact h.res
  · have e : ∀ {f : Views → Nat}, (∀ vs : Views, f { vs with vCAP := 0 } = f vs) → f th.views = f cx.views := hf
    refine ⟨fun hr => ?_, fun hw => ?_⟩
    · rw [e (f := Views.vrOld) fun _ => rfl, e (f := Views.vrOldNR) fun _ => rfl, e (f := Views.vwNew) fun _ => rfl]
      exact h.fenced.r hr
    · rw [e (f := Views.vwOld) fun _ => rfl, e (f := Views.vwOldNT) fun _ => rfl, e (f := Views.vwNew) fun _ => rfl]
      exact h.fenced.w hw

end EnvRel

end Kraken.Promising.SLR.EnvG
