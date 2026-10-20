/-
`ThreadRule` with bounded reach discharged by the event rules (on
the original design's `SLR/ReachRules.lean`).

`ThreadRule.wp` asks for the erasure WP with postcondition `WpPost`, whose
`K1`/`K2` conjuncts (bounded reach of the ghost state and of the thread's
resource) are a burden on every instruction proof. `EvTree.EraseWPR` threads
`RStep` (K1/K2 for each ghost change) through the tree, discharged by its
node shapes (`eraseWPR_load`/`_store`/`_rmw`/`_store_pend`/`_rmw_pend`, …).
`ThreadRuleR` asks for `EraseWPR` with postcondition `WpPostR`, `WpPost`
without `K1`/`K2`; `ThreadRuleR.toThreadRule` recovers them from `RStep`
(`RStep.1` and `RStep.finish`).
-/
import Kraken.Promising.SLR.NPSafeInv
import Kraken.Promising.SLR.ReachRules

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `WpPost` without the bounded-reach conjuncts `K1`/`K2`, which `EraseWPR`
supplies: world growth, pending marks kept while outstanding, no new marks,
`acqLe`, a write permission for every written message, and `Inv` (at flag
`cl`) after every live `finishInstr` outcome. -/
def WpPostR (Inv : Prop → Config I → Res → Ghost → Prop) (cl : Prop) (c : Config I) (tid : Nat) (r : Res)
    (g : Ghost) (t : Thread I) : I.State → Res → Ghost → Ctx → Prop :=
  fun st r' g' cx' => g.Le g' ∧
    (∀ ts, ts ∈ g.pend → (ts ∈ cx'.prom ∨ ∃ (i : Nat) (t' : Thread I), i ≠ tid ∧ c.threads[i]? = some t' ∧ ts ∈ t'.prom) →
      ts ∈ g'.pend) ∧
    (∀ ts, ts ∈ g'.pend → ts ∈ g.pend) ∧ (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
    (∀ w, WrittenCx c t cx' w → 0 < (r.wr w.loc).q) ∧
    ∀ t' ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st cx', t'.hasDeadPromise cx'.mem = false →
      Inv cl (c.withThread tid t' cx'.mem) r' g'

/-- **`WpPostR` and `RStep` give `WpPost`.** -/
theorem WpPost.of_R {Inv : Prop → Config I → Res → Ghost → Prop} {cl : Prop} {c : Config I} {tid : Nat}
    {r : Res} {g : Ghost} {t : Thread I} {st : I.State} {r' : Res} {g' : Ghost} {cx' : Ctx}
    (h : WpPostR Inv cl c tid r g t st r' g' cx') (hR : RStep c.mem.last r g r' g' cx') :
    WpPost Inv cl c tid r g t st r' g' cx' := by
  obtain ⟨hg, hkeep, hnew, hacq, hown, hfin⟩ := h
  exact ⟨hg, hkeep, hnew, hacq, hown, hR.1, fun t' ht' hd =>
    ⟨fun b hb hv x hx => hR.finish ht' b hb hv x hx, hfin t' ht' hd⟩⟩

/-- **`WpPostR` of a silent instruction** (no memory event: final context the
start context `ctx₀`, resource and ghost unchanged): only `Inv` after the
step remains, for a thread with the new ISA state and the old promises and
views (up to register views and `vCAP`). -/
theorem WpPostR.silent {Inv : Prop → Config I → Res → Ghost → Prop} {cl : Prop} {c : Config I} {tid : Nat}
    {r : Res} {g : Ghost} {t : Thread I} {st : I.State}
    (h : ∀ t' : Thread I, t'.st = st → t'.prom = t.prom →
      ({ t'.views with vCAP := 0 } : Views) = { t.views with vCAP := 0 } →
      Inv cl (c.withThread tid t' c.mem) r g) :
    WpPostR Inv cl c tid r g t st r g (ctx₀ t tid c.mem) := by
  refine ⟨Ghost.Le.refl g, fun ts hts _ => hts, fun ts hts => hts, fun x hx => hx, ?_, fun t' ht' _ => ?_⟩
  · rintro w ⟨ts, hget, hnp, hnew⟩
    rcases hnew with hlt | hp
    · exact absurd (Memory.last_le_of_get?_eq_some _ hget) (Nat.not_le.mpr hlt)
    · exact absurd hp hnp
  · obtain ⟨hp, hv⟩ := finishInstr_relKey ht'
    exact h t' (finishInstr_st ht') hp hv

/-- **`WpPostR` of an instruction that only read** (final context `cx'` with
the start's memory and promises, e.g. after `eraseWPR_load`), resource and
ghost unchanged: only `Inv` after the step remains, for a thread with the new
ISA state, the old promises and the final context's views. -/
theorem WpPostR.noWrite {Inv : Prop → Config I → Res → Ghost → Prop} {cl : Prop} {c : Config I} {tid : Nat}
    {r : Res} {g : Ghost} {t : Thread I} {st : I.State} {cx' : Ctx} (hm : cx'.mem = c.mem)
    (hp : cx'.prom = t.prom)
    (h : ∀ t' : Thread I, t'.st = st → t'.prom = t.prom →
      ({ t'.views with vCAP := 0 } : Views) = { cx'.views with vCAP := 0 } →
      Inv cl (c.withThread tid t' c.mem) r g) :
    WpPostR Inv cl c tid r g t st r g cx' := by
  refine ⟨Ghost.Le.refl g, fun ts hts _ => hts, fun ts hts => hts, fun x hx => hx, ?_, fun t' ht' _ => ?_⟩
  · rintro w ⟨ts, hget, hnp, hnew⟩
    rw [hm] at hget
    rcases hnew with hlt | hpr
    · exact absurd (Memory.last_le_of_get?_eq_some _ hget) (Nat.not_le.mpr hlt)
    · exact absurd (hp ▸ hpr) hnp
  · obtain ⟨hpr, hv⟩ := finishInstr_relKey ht'
    rw [hm]
    exact h t' (finishInstr_st ht') (hpr.trans hp) hv

/-- **A per-thread invariant with per-instruction erasure WPs with bounded
reach**: `ThreadRule` with `wp` in `EvTree.EraseWPR` form and postcondition
`WpPostR`. -/
structure ThreadRuleR (A : Arch) (B : Config I → (model I).R → (model I).Ghost → Prop) (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  env : ∀ {cl : Prop} {c c₁ : Config I} {r : Res} {g g₁ : Ghost}, Inv cl c r g → EnvExt tid c c₁ → g.Le g₁ →
    Inv cl c₁ r g₁
  done : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost}, Inv cl c r g → cl → c.Done tid → B c r g
  wp : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c r g →
    g₀.Le g → c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPR A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)
  prepay : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c r g → g₀.Le g → c.threads[tid]? = some t₁ → Erase (setRes rF tid r) g (fun _ => True) c →
    c.MachInv → (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfils A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- **`EraseWPR` rules give a `ThreadRule`**: `EraseWPR.toEraseWP_start` at
the instruction's start context (whose memory is `c.mem`), and
`WpPost.of_R`. -/
def ThreadRuleR.toThreadRule {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleR A B tid) : ThreadRule A B tid where
  Inv := R.Inv
  env := R.env
  done := R.done
  wp := fun g₀ rF t tree h hle ht hex E hinv hwf hnp =>
    EvTree.EraseWPR.toEraseWP_start (R.wp g₀ rF t tree h hle ht hex E hinv hwf hnp) (Nat.le_refl _)
      fun _ _ _ _ hp hR => WpPost.of_R hp hR
  prepay := R.prepay

/-- **`NPSafe` from per-instruction erasure WPs with bounded reach.** -/
theorem NPSafe.of_ruleR {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleR A B tid) (n m : Nat) {cl : Prop} {c : Config I} {r : (model I).R} {g : (model I).Ghost}
    (h : R.Inv cl c r g) : NPSafe (model I) A B tid n m cl c r g :=
  NPSafe.of_rule R.toThreadRule n m h

end Kraken.Promising.SLR
