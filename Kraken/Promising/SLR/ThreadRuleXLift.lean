/-
The generic **lift** of an erasure WP (`EvTree.EraseWPR`) to the
dead-branch form (`EvTree.EraseWPRD`, `SLR/ThreadRuleX.lean`) with a
postcondition that may use two facts about every final context `cx'` of a
run from the instruction's start `ctx₀ t tid c.mem`:

- the memory only grows: `c.mem.last ≤ cx'.mem.last`;
- no promise is added: `cx'.prom ⊆ t.prom` (a fresh write appends its
  timestamp and fulfils it at once, `writeSuccs_promSub`).

`EvTree.EraseWPR.toD_run` is the general statement; `WpPostR.lift_noPend`
instantiates it for `WpPostR`: from a state with no own pending promise
(`∀ ts ∈ t.prom, ts ∉ g.pend`), after the instruction the pending marks are
still messages (`g'.pend ⊆ g.pend ⊆ ≤ c.mem.last ≤ cx'.mem.last`) and no
own promise is pending.

`EvTree.eraseWPRD_store_pendOrDead` is the `EraseWPRD` shape of a store
whose non-pending writes are all dead (`Ctx.Overtaken`).
-/
import Kraken.Promising.SLR.ThreadRuleX
import Kraken.Promising.PromOrder

namespace Kraken.Promising.SLR

variable {I : ISA}

section LiftRun

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type}

/-- The run invariant of the lift: memory above `c.mem.last`, promises among
`t`'s. -/
def RunJ (c : Config I) (t : Thread I) (cx : Ctx) : Prop :=
  c.mem.last ≤ cx.mem.last ∧ ∀ ts ∈ cx.prom, ts ∈ t.prom

theorem RunJ.of_memProm {cx cx' : Ctx} (h : RunJ c t cx) (hm : cx'.mem = cx.mem) (hp : cx'.prom = cx.prom) :
    RunJ c t cx' := by
  unfold RunJ at *; rw [hm, hp]; exact h

theorem RunJ.ctx₀ : RunJ c t (ctx₀ t tid c.mem) :=
  ⟨Nat.le_refl _, fun _ h => h⟩

/-- Under the context invariant the promises are messages. -/
theorem _root_.Kraken.Promising.Ctx.Inv.prom_le {cx : Ctx} (hi : cx.Inv tid) : ∀ p ∈ cx.prom, p ≤ cx.mem.last := fun p hp => by
  obtain ⟨w, hw, -⟩ := hi.prom p hp
  exact cx.mem.last_le_of_get?_eq_some hw

/-- A write keeps `RunJ` (from a context whose promises are messages). -/
theorem RunJ.write {xr : View} {cx cx' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} (h : RunJ c t cx) (hb : ∀ p ∈ cx.prom, p ≤ cx.mem.last)
    (hw : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra xr) : RunJ c t cx' := by
  refine ⟨?_, fun ts hts => h.2 ts (writeSuccs_promSub A tid iv hw hb ts hts)⟩
  rcases (mem_writeSuccs A tid).mp hw with ⟨-, -, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · exact h.1
  · show c.mem.last ≤ (cx.mem.append _).1.last
    rw [Memory.last_append]; exact Nat.le_succ_of_le h.1

/-- **The lift**: an `EraseWPR` proof from a context with `RunJ` is an
`EraseWPRD` proof into any postcondition that `Post` implies at contexts
with `RunJ`. -/
theorem _root_.Kraken.Promising.EvTree.EraseWPR.toD_run {Post Q : σ → Res → Ghost → Ctx → Prop}
    (hQ : ∀ s r g cx, RunJ c t cx → Post s r g cx → Q s r g cx) (tree : EvTree σ) :
    ∀ r g cx, RunJ c t cx → tree.EraseWPR A tid iv rF T c t Post r g cx →
      tree.EraseWPRD A tid iv rF T c t Q r g cx := by
  induction tree with
  | done s => exact fun r g cx hJ h => hQ s r g cx hJ h
  | fault _ => exact fun _ _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx hJ h i => ih i r g cx hJ (h i)
  | load k xcl l ret ih =>
    exact fun r g cx hJ h x hx => ih x.2.1 r g x.2.2
      (hJ.of_memProm (readSuccs_memProm A iv hx).1 (readSuccs_memProm A iv hx).2) (h x hx)
  | store k xcl l v ret ih =>
    refine fun r g cx hJ h => ⟨fun cx' hc E hi hm => ?_, fun hx => ih false r g _ (hJ.of_memProm rfl rfl) (h.2 hx)⟩
    obtain ⟨r', g', E', hR, hw⟩ := h.1 cx' hc E hi hm
    exact .inr ⟨r', g', E', hR, ih true r' g' cx' (hJ.write hi.prom_le hc) hw⟩
  | fence k ret ih =>
    exact fun r g cx hJ h => ih () r g _ (hJ.of_memProm (fenceStep_mem cx k) (fenceStep_prom cx k)) h
  | rmw k noRet l op ret ih =>
    refine fun r g cx hJ h x hx => ?_
    have hJo := hJ.of_memProm (fenceOptCtx_memProm A cx).1 (fenceOptCtx_memProm A cx).2
    have hJx := hJo.of_memProm (readSuccs_memProm A iv hx).1 (readSuccs_memProm A iv hx).2
    refine ⟨fun hop => ih x.2.1 r g _ (hJx.of_memProm (fenceOptCtx_memProm A _).1 (fenceOptCtx_memProm A _).2)
      ((h x hx).1 hop), fun new hop cx' hc E hi hm => ?_⟩
    obtain ⟨r', g', E', hR, hw⟩ := (h x hx).2 new hop cx' hc E hi hm
    have hix : ∀ p ∈ x.2.2.prom, p ≤ x.2.2.mem.last := by
      rw [(readSuccs_memProm A iv hx).1.trans (fenceOptCtx_memProm A cx).1,
        (readSuccs_memProm A iv hx).2.trans (fenceOptCtx_memProm A cx).2]
      exact hi.prom_le
    exact .inr ⟨r', g', E', hR, ih x.2.1 r' g' _
      ((hJx.write hix hc).of_memProm (rmwAfter_memProm A k noRet l cx').1 (rmwAfter_memProm A k noRet l cx').2) hw⟩

end LiftRun

section ShapesD

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- **A store that only fulfils a pending promise or is dead**: the pending
branch of `EvTree.eraseWPR_store_pend` (resource unchanged, the mark
unpended); every non-pending write overtakes an own outstanding promise. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPRD_store_pendOrDead (hn : tid < c.threads.size) {k : StoreKind}
    {l : Loc} {v : Val} {ret : Bool → EvTree σ}
    (hp : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∈ g.pend →
      (ret true).EraseWPRD A tid iv rF T c t Post r (unpend g tw) cx')
    (h : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∉ g.pend → ErAt rF T c t tid r g cx → cx.Inv tid → cx'.Overtaken) :
    (EvTree.store k false l v ret).EraseWPRD A tid iv rF T c t Post r g cx := by
  refine ⟨fun cx' hc E hi _ => ?_, fun h => absurd h (by decide)⟩
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi
  by_cases hpd : tw ∈ g.pend
  · exact .inr ⟨r, _, ErAt.fulfilPend E hn hi hev hpd, RStep.unpend tw cx', hp cx' tw hc hev hpd⟩
  · exact .inl (h cx' tw hc hev hpd E hi)

end ShapesD

end Kraken.Promising.SLR
