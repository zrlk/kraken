/-
**A generic `PromiseFresh'` discharge, part 1: the
instructions of a single-RMW dispenser thread.** ISA-neutral.

A *single-RMW dispenser* thread (`ticketlock2.kl`'s worker: one `ldadda` on
`next`, then never again a write to `next`) runs in two phases, given by
per-thread predicates `Bef`/`Aft` on its states. Its instructions' event
trees satisfy:

- `EvTree.BefX x N Bef Aft` (before the hand-out): no store to `x`; an RMW on
  `x` that writes, writes `old + 1` when `old < N` and continues in the after
  phase (`AftX`); an RMW on `x` that does not write continues before; every
  leaf is `Bef` or `Aft`.
- `EvTree.AftX x Aft` (after the hand-out): no message to `x` is written (no
  store to `x`, every RMW on `x` fails); every leaf is `Aft`.

For one instruction (`runTree`, then `stepOne`), with promise lists and
memories before (`p`, `m`) and after (`p'`, `m'`):

- `XSame x m m'`: `m'` extends `m` with no new message to `x`.
- `KeepX x p m p' m'`: `XSame`, and every outstanding promise to `x` of `p`
  is still in `p'`.
- `HandOut x N tid p m p' m' t`: the hand-out write at `t`: an RMW of `tid`
  reading `(x, tr)` (value `old`) in a memory `m1` (`XSame x m m1`), atomic
  up to `t > tr`, writing `new` (`old + 1` when `old < N`) at `t`, by
  fulfilling a promise (the message at `t` already in `m`) or appending
  (`t = |m1| + 1`); no other new message to `x`; every other outstanding
  promise to `x` kept.
- `runTree_aftX` / `stepOne_aftX`: an after-phase instruction is `KeepX` and
  ends in `Aft`.
- `runTree_befX` / `stepOne_befX`: a before-phase instruction is `KeepX`
  (ending in `Bef` or `Aft`) or a `HandOut` (ending in `Aft`).

The path argument is in `SLR/DispenserFresh.lean`.
-/
import Kraken.Promising.SLR.TicketX
import Kraken.Promising.SLR.TsoPromisePure
import Kraken.Promising.SLR.StepRunCommon
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.EvTree

/-- **After the hand-out**: the tree writes no message to `x` (no store to
`x`; every RMW on `x` fails, `op v = none`); every leaf satisfies `Aft`. -/
def AftX {σ : Type} (x : Loc) (Aft : σ → Prop) : EvTree σ → Prop
  | .done s => Aft s
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).AftX x Aft
  | .load _ _ _ ret => ∀ v, (ret v).AftX x Aft
  | .store _ _ l _ ret => l ≠ x ∧ ∀ b, (ret b).AftX x Aft
  | .rmw _ _ l op ret => (l = x → ∀ v, op v = none) ∧ ∀ v, (ret v).AftX x Aft
  | .fence _ ret => ∀ u, (ret u).AftX x Aft

/-- **Before the hand-out**: no store to `x`; an RMW on `x` that writes
(`op v = some new`) writes `v + 1` when `v < N` (no wraparound below the
dispenser bound) and continues after the hand-out (`AftX`); every other
continuation (an RMW elsewhere, a failing RMW on `x`, every other node)
stays before; every leaf satisfies `Bef` or `Aft`. -/
def BefX {σ : Type} (x : Loc) (N : Nat) (Bef Aft : σ → Prop) : EvTree σ → Prop
  | .done s => Bef s ∨ Aft s
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).BefX x N Bef Aft
  | .load _ _ _ ret => ∀ v, (ret v).BefX x N Bef Aft
  | .store _ _ l _ ret => l ≠ x ∧ ∀ b, (ret b).BefX x N Bef Aft
  | .rmw _ _ l op ret => ∀ v,
      (l = x → ∀ new, op v = some new → (v.toNat < N → new.toNat = v.toNat + 1) ∧ (ret v).AftX x Aft) ∧
      ((l = x → op v = none) → (ret v).BefX x N Bef Aft)
  | .fence _ ret => ∀ u, (ret u).BefX x N Bef Aft

end Kraken.Promising.EvTree

namespace Kraken.Promising.SLR

open Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

namespace SingleRmw

/-! ## No new message to `x`

`XSame` and its lemmas (`refl`, `trans`, `append`, `get?`) are in
`SLR/TicketX.lean` (same names). -/

/-- **No write to `x`**: no new message to `x`, and every outstanding promise
to `x` (of `p`, in `m`) is still outstanding (in `p'`). -/
def KeepX (x : Loc) (p : List Time) (m : Memory) (p' : List Time) (m' : Memory) : Prop :=
  XSame x m m' ∧ ∀ ts w, ts ∈ p → m.get? ts = some w → w.loc = x → ts ∈ p'

theorem KeepX.refl (x : Loc) (p : List Time) (m : Memory) : KeepX x p m p m :=
  ⟨XSame.refl x m, fun _ _ h _ _ => h⟩

theorem KeepX.trans {x : Loc} {p p' p'' : List Time} {m m' m'' : Memory} (h₁ : KeepX x p m p' m')
    (h₂ : KeepX x p' m' p'' m'') : KeepX x p m p'' m'' :=
  ⟨h₁.1.trans h₂.1, fun ts w hp hw hl => h₂.2 ts w (h₁.2 ts w hp hw hl) (h₁.1.get? hw) hl⟩

theorem keepX_eq {x : Loc} {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.prom = c.prom) :
    KeepX x c.prom c.mem c'.prom c'.mem := by
  rw [hm, hp]; exact KeepX.refl _ _ _

/-! ## The hand-out write -/

/-- **The hand-out write at `t`** (see the module docstring). -/
def HandOut (x : Loc) (N tid : Nat) (p : List Time) (m : Memory) (p' : List Time) (m' : Memory) (t : Time) :
    Prop :=
  ∃ (m1 m2 : Memory) (tr : Time) (old new : Val),
    XSame x m m1 ∧ m1.read? x tr = some old ∧ tr < t ∧ m1.atomic x tid tr t = true ∧
    (old.toNat < N → new.toNat = old.toNat + 1) ∧
    ((m.get? t = some ⟨x, new, tid⟩ ∧ m2 = m1) ∨ (t = m1.last + 1 ∧ m2 = (m1.append ⟨x, new, tid⟩).1)) ∧
    XSame x m2 m' ∧
    ∀ ts w, ts ∈ p → m.get? ts = some w → w.loc = x → ts ≠ t → ts ∈ p'

variable {x : Loc} {N tid : Nat} {p p1 p' : List Time} {m m1 m' : Memory} {t : Time}

theorem HandOut.prefix (h : HandOut x N tid p m p' m' t) : m.Prefix m' := by
  obtain ⟨n1, n2, _, _, _, hX, _, _, _, _, hwr, hX2, _⟩ := h
  rcases hwr with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact hX.1.trans hX2.1
  · exact hX.1.trans ((Memory.Prefix.append _ _).trans hX2.1)

/-- The messages to `x` after a hand-out: old ones, or the hand-out's (by
`tid`). -/
theorem HandOut.xmsg (h : HandOut x N tid p m p' m' t) {ts : Time} {w : Msg} (hw : m'.get? ts = some w)
    (hl : w.loc = x) : m.get? ts = some w ∨ w.tid = tid := by
  obtain ⟨n1, n2, _, _, new, hX, _, _, _, _, hwr, hX2, _⟩ := h
  have h2 := hX2.2 ts w hw hl
  rcases hwr with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact .inl (hX.2 ts w h2 hl)
  · rcases Dispenser.get?_append_cases h2 with ⟨-, hg⟩ | ⟨-, rfl⟩
    · exact .inl (hX.2 ts w hg hl)
    · exact .inr rfl

/-- A step with no write to `x`, then a hand-out. -/
theorem HandOut.pre (h₁ : KeepX x p m p1 m1) (h₂ : HandOut x N tid p1 m1 p' m' t) : HandOut x N tid p m p' m' t := by
  obtain ⟨n1, n2, tr, old, new, hX, hrd, htr, hat, hop, hwr, hX2, hpr⟩ := h₂
  refine ⟨n1, n2, tr, old, new, h₁.1.trans hX, hrd, htr, hat, hop, ?_, hX2,
    fun ts w hp hw hl hne => hpr ts w (h₁.2 ts w hp hw hl) (h₁.1.get? hw) hl hne⟩
  rcases hwr with ⟨hg, rfl⟩ | h
  · exact .inl ⟨h₁.1.2 t _ hg rfl, rfl⟩
  · exact .inr h

/-- A hand-out, then a step with no write to `x`. -/
theorem HandOut.post (h₁ : HandOut x N tid p m p1 m1 t) (h₂ : KeepX x p1 m1 p' m') : HandOut x N tid p m p' m' t := by
  have hpre := h₁.prefix
  obtain ⟨n1, n2, tr, old, new, hX, hrd, htr, hat, hop, hwr, hX2, hpr⟩ := h₁
  exact ⟨n1, n2, tr, old, new, hX, hrd, htr, hat, hop, hwr, hX2.trans h₂.1,
    fun ts w hp hw hl hne => h₂.2 ts w (hpr ts w hp hw hl hne)
      (by rw [hpre.get? (m.last_le_of_get?_eq_some hw)]; exact hw) hl⟩

/-! ## Context steps -/

section Steps

variable {A : Arch} {iv : InstrViews}

/-- A write to a location other than `x` writes no message to `x` and keeps
every outstanding promise to `x`. -/
theorem keepX_write {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time} {extra : View}
    {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) (hl : l ≠ x) :
    KeepX x c.prom c.mem c'.prom c'.mem := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, w, hw, hwl, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨XSame.refl _ _, fun ts w' hp hw' hl' => ?_⟩
    show ts ∈ c.prom.erase t
    have hne : ts ≠ t := by
      rintro rfl
      rw [hw] at hw'
      cases hw'
      exact hl (hwl.symm.trans hl')
    exact (List.mem_erase_of_ne hne).mpr hp
  · refine ⟨XSame.append c.mem (w := { loc := l, val := v, tid }) hl, fun ts w' hp hw' _ => ?_⟩
    show ts ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
    have hne : ts ≠ c.mem.last + 1 := by have := c.mem.last_le_of_get?_eq_some hw'; omega_t
    exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hp)

/-- **The RMW write on `x`** is a hand-out. -/
theorem handOut_write {c : Ctx} {k : StoreKind} {new : Val} {tr : Time} {extra : View} {c' : Ctx} {old : Val}
    (h : c' ∈ writeSuccs A tid iv c k true x new (some tr) extra) (hrd : c.mem.read? x tr = some old)
    (hop : old.toNat < N → new.toNat = old.toNat + 1) :
    ∃ t, HandOut x N tid c.prom c.mem c'.prom c'.mem t := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, w, hw, hwl, hwv, hwt, hok, rfl⟩ | ⟨hok, rfl⟩
  · obtain ⟨htr, hat⟩ := hok.2 tr rfl
    refine ⟨t, c.mem, c.mem, tr, old, new, XSame.refl _ _, hrd, htr, hat, hop, .inl ⟨?_, rfl⟩, XSame.refl _ _,
      fun ts _ hp _ _ hne => ?_⟩
    · rw [hw]; obtain ⟨wl, wv, wt⟩ := w; simp only at hwl hwv hwt; subst hwl hwv hwt; rfl
    · show ts ∈ c.prom.erase t
      exact (List.mem_erase_of_ne hne).mpr hp
  · obtain ⟨htr, hat⟩ := hok.2 tr rfl
    refine ⟨c.mem.last + 1, c.mem, _, tr, old, new, XSame.refl _ _, hrd, htr, hat, hop, .inr ⟨rfl, rfl⟩,
      XSame.refl _ _, fun ts _ hp _ _ hne => ?_⟩
    show ts ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
    exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hp)

/- `optFence_mem_prom`: an optional fence keeps the context's memory and
promises (alias of the neutral `SLR.optFence_mem_prom`,
`SLR/StepRunCommon.lean`). -/
hoist_alias [Kraken.Promising.SLR.optFence_mem_prom ↦ Kraken.Promising.SLR.SingleRmw.optFence_mem_prom]

theorem keepX_opt (c : Ctx) (b : Bool) (k : FenceKind) :
    KeepX x c.prom c.mem (if b then fenceStep c k else c).prom (if b then fenceStep c k else c).mem :=
  keepX_eq (optFence_mem_prom c b k).1 (optFence_mem_prom c b k).2

/-- The context after an RMW write: `rmwPost`, then the optional fence. -/
theorem keepX_post (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    KeepX x c.prom c.mem (if A.rmwFence then fenceStep (rmwPost A k noRet l c) .sy else rmwPost A k noRet l c).prom
      (if A.rmwFence then fenceStep (rmwPost A k noRet l c) .sy else rmwPost A k noRet l c).mem :=
  (keepX_eq (rmwPost_mem A k noRet l c) (rmwPost_prom A k noRet l c)).trans (keepX_opt _ _ _)

theorem readSuccs_memProm' {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {y : Time × Val × Ctx} (hy : y ∈ readSuccs A iv c k xcl l noRet) :
    c.mem.read? l y.1 = some y.2.1 ∧ KeepX x c.prom c.mem y.2.2.prom y.2.2.mem :=
  ⟨Kraken.Promising.SLR.readSuccs_read A iv hy,
    keepX_eq (readSuccs_memProm A iv hy).1 (readSuccs_memProm A iv hy).2⟩

end Steps

/-! ## Runs of an instruction -/

/-- **An after-phase run** writes no message to `x`, keeps every outstanding
promise to `x`, and ends in `Aft`. -/
theorem runTree_aftX (A : Arch) (tid : Nat) (iv : InstrViews) (x : Loc) {σ : Type} {Aft : σ → Prop} :
    ∀ (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      tree.AftX x Aft → KeepX x c.prom c.mem c'.prom c'.mem ∧ Aft s
  | .done _, c, s, c', h, hA => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨KeepX.refl _ _ _, hA⟩
  | .fault _, _, _, _, h, _ => by simp [runTree] at h
  | .choose _ k, c, s, c', h, hA => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact runTree_aftX A tid iv x (k i) c s c' h (hA i)
  | .load _ _ _ ret, c, s, c', h, hA => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨y, hy, h⟩ := h
    obtain ⟨h1, h2⟩ := runTree_aftX A tid iv x _ _ s c' h (hA _)
    exact ⟨(readSuccs_memProm' hy).2.trans h1, h2⟩
  | .store _ xcl l v ret, c, s, c', h, hA => by
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      obtain ⟨h1, h2⟩ := runTree_aftX A tid iv x _ c0 s c' h (hA.2 true)
      exact ⟨(keepX_write hc0 hA.1).trans h1, h2⟩
    · rw [List.mem_ite_nil_right] at h
      obtain ⟨h1, h2⟩ := runTree_aftX A tid iv x _ _ s c' h.2 (hA.2 false)
      exact ⟨(keepX_eq rfl rfl).trans h1, h2⟩
  | .fence k ret, c, s, c', h, hA => by
    simp only [runTree] at h
    obtain ⟨h1, h2⟩ := runTree_aftX A tid iv x _ _ s c' h (hA ())
    exact ⟨(keepX_eq (fenceStep_mem_prom c k).1 (fenceStep_mem_prom c k).2).trans h1, h2⟩
  | .rmw k noRet l op ret, c, s, c', h, hA => by
    simp only [runTree] at h
    have h1 := keepX_opt (x := x) c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := h1.trans (readSuccs_memProm' (x := x) h2).2
    simp only at h h12
    split at h
    · obtain ⟨h3, h4⟩ := runTree_aftX A tid iv x _ _ s c' h (hA.2 old)
      exact ⟨(h12.trans (keepX_opt c2 _ _)).trans h3, h4⟩
    · rename_i new hnew
      have hl : l ≠ x := fun e => by rw [hA.1 e old] at hnew; cases hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      obtain ⟨h3, h4⟩ := runTree_aftX A tid iv x _ _ s c' h (hA.2 old)
      exact ⟨((h12.trans (keepX_write hc3 hl)).trans (keepX_post A k noRet l c3)).trans h3, h4⟩

/-- The outcome of a before-phase run: no write to `x` (ending in `Bef` or
`Aft`), or a hand-out (ending in `Aft`). -/
def BefOut (x : Loc) (N tid : Nat) {σ : Type} (Bef Aft : σ → Prop) (p : List Time) (m : Memory) (s : σ)
    (p' : List Time) (m' : Memory) : Prop :=
  (KeepX x p m p' m' ∧ (Bef s ∨ Aft s)) ∨ ((∃ t, HandOut x N tid p m p' m' t) ∧ Aft s)

theorem BefOut.pre {σ : Type} {Bef Aft : σ → Prop} {s : σ} (h₁ : KeepX x p m p1 m1)
    (h₂ : BefOut x N tid Bef Aft p1 m1 s p' m') : BefOut x N tid Bef Aft p m s p' m' := by
  rcases h₂ with ⟨h, hs⟩ | ⟨⟨t, h⟩, hs⟩
  · exact .inl ⟨h₁.trans h, hs⟩
  · exact .inr ⟨⟨t, h.pre h₁⟩, hs⟩

/-- **A before-phase run** writes no message to `x` and keeps every
outstanding promise to `x`, or performs the hand-out; see `BefOut`. -/
theorem runTree_befX (A : Arch) (tid : Nat) (iv : InstrViews) (x : Loc) (N : Nat) {σ : Type}
    {Bef Aft : σ → Prop} :
    ∀ (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      tree.BefX x N Bef Aft → BefOut x N tid Bef Aft c.prom c.mem s c'.prom c'.mem
  | .done _, c, s, c', h, hB => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨KeepX.refl _ _ _, hB⟩
  | .fault _, _, _, _, h, _ => by simp [runTree] at h
  | .choose _ k, c, s, c', h, hB => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact runTree_befX A tid iv x N (k i) c s c' h (hB i)
  | .load _ _ _ ret, c, s, c', h, hB => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨y, hy, h⟩ := h
    exact BefOut.pre (readSuccs_memProm' hy).2 (runTree_befX A tid iv x N _ _ s c' h (hB _))
  | .store _ xcl l v ret, c, s, c', h, hB => by
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact BefOut.pre (keepX_write hc0 hB.1) (runTree_befX A tid iv x N _ c0 s c' h (hB.2 true))
    · rw [List.mem_ite_nil_right] at h
      have h' := runTree_befX A tid iv x N _ _ s c' h.2 (hB.2 false)
      exact BefOut.pre (keepX_eq rfl rfl) h'
  | .fence k ret, c, s, c', h, hB => by
    simp only [runTree] at h
    exact BefOut.pre (keepX_eq (fenceStep_mem_prom c k).1 (fenceStep_mem_prom c k).2)
      (runTree_befX A tid iv x N _ _ s c' h (hB ()))
  | .rmw k noRet l op ret, c, s, c', h, hB => by
    simp only [runTree] at h
    have h1 := keepX_opt (x := x) c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have hrd := (readSuccs_memProm' (x := x) h2).1
    have hm2 := (readSuccs_memProm A iv h2).1
    have h12 := h1.trans (readSuccs_memProm' (x := x) h2).2
    simp only at h h12 hrd hm2
    split at h
    · rename_i hnone
      exact BefOut.pre (h12.trans (keepX_opt c2 _ _))
        (runTree_befX A tid iv x N _ _ s c' h ((hB old).2 fun _ => hnone))
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      by_cases hl : l = x
      · subst hl
        obtain ⟨hop, hA⟩ := (hB old).1 rfl new hnew
        obtain ⟨h3, h4⟩ := runTree_aftX A tid iv l _ _ s c' h hA
        obtain ⟨t, ht⟩ := handOut_write (N := N) hc3 (by rw [hm2]; exact hrd) hop
        exact .inr ⟨⟨t, (ht.pre h12).post ((keepX_post A k noRet l c3).trans h3)⟩, h4⟩
      · exact BefOut.pre ((h12.trans (keepX_write hc3 hl)).trans (keepX_post A k noRet l c3))
          (runTree_befX A tid iv x N _ _ s c' h ((hB old).2 fun e => absurd e hl))

/-! ## One instruction -/

/- `stepOne_run`: the successful outcomes of `stepOne` are runs of the
instruction's tree (alias of the neutral `SLR.stepOne_run`,
`SLR/StepRunCommon.lean`). -/
hoist_alias [Kraken.Promising.SLR.stepOne_run ↦ Kraken.Promising.SLR.SingleRmw.stepOne_run]

/-- **An after-phase instruction** (`stepOne`). -/
theorem stepOne_aftX (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {Aft : I.State → Prop}
    (hA : ∀ tree, I.exec t.st = some tree → tree.AftX x Aft) :
    KeepX x t.prom mem o.thread.prom o.mem ∧ Aft o.thread.st := by
  obtain ⟨tree, iv, c', hex, hr, hp, hm⟩ := stepOne_run A hstep ho
  rw [hp, hm]
  exact runTree_aftX A tid iv x tree _ _ c' hr (hA tree hex)

/-- **A before-phase instruction** (`stepOne`). -/
theorem stepOne_befX (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {Bef Aft : I.State → Prop}
    (hB : ∀ tree, I.exec t.st = some tree → tree.BefX x N Bef Aft) :
    BefOut x N tid Bef Aft t.prom mem o.thread.st o.thread.prom o.mem := by
  obtain ⟨tree, iv, c', hex, hr, hp, hm⟩ := stepOne_run A hstep ho
  rw [hp, hm]
  exact runTree_befX A tid iv x N tree _ _ c' hr (hB tree hex)

end SingleRmw

end Kraken.Promising.SLR

#print axioms Kraken.Promising.SLR.SingleRmw.runTree_aftX
#print axioms Kraken.Promising.SLR.SingleRmw.runTree_befX
#print axioms Kraken.Promising.SLR.SingleRmw.stepOne_aftX
#print axioms Kraken.Promising.SLR.SingleRmw.stepOne_befX
