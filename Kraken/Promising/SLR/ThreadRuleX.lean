/-
A rule interface for `NPSafe` with **dead branches** and **instance
invariants** (fallback (iii), "Limits (2)").

`ThreadRuleR` (`SLR/NPSafeInvR.lean`) has two limits that a prepaid release
runs into (the SWP spinlock's `stlr` after `prepay`):

1. **Dead branches.** After a prepayment the thread no longer holds what
   the release message carries (the slots of the pending promise `ts` are in
   `u`). An outcome of the fulfilling instruction that does *not* fulfil `ts`
   but writes the location fresh above it (or fulfils a later promise)
   cannot re-establish erasure. Every such outcome leaves `ts` dead
   (`ts ≤ coh x`), so `NPSafe`'s step, which assumes `c'.WfProm tid`
   (`PromiseSafe.lean`, `NPSafe`, the hypothesis `c'.WfProm tid` of the step
   conjunct), never asks for it. `EvTree.EraseWPR` still asks for erasure
   at the write. `EvTree.EraseWPRD` is `EraseWPR` whose write nodes may
   instead show that the write **overtook** an own outstanding promise
   (`Ctx.Overtaken`: some promise of the context at or below `coh` of its
   location). That stays true for the rest of the instruction
   (`Ctx.Overtaken.dord`, from `runTree_dord`) and makes the final thread
   dead (`Ctx.Overtaken.finish`). This is `runTree_overtaken_dead` of the
   plan.
2. **Environment.** `ThreadRuleR.env` must keep `Inv` under every ghost
   growth `g ≤ g₁`, which constrains neither `pend` nor `claims`. So `Inv`
   cannot say "no own pending promise" in a form the cells can use. The
   own-pending transport `hnp` relates `g₁` only to the instance ghost `g₀`.
   `ThreadRuleRX` has no `env` field: `done`/`wp`/`prepay` receive `Inv` at
   the instance `(c₀, g₀)`, the environment extension `EnvExt tid c₀ c` and
   `g₀ ≤ g`, exactly what `NPSafe.of_inv` has at hand.

## Contents

- `Ctx.Overtaken`, `Ctx.Overtaken.dord`, `Ctx.Overtaken.finish`.
- `EvTree.EraseWPRD`, `EvTree.EraseWPR.toD` (every `EraseWPR` proof is an
  `EraseWPRD` proof, with a weaker postcondition), `runTree_eraseWPRD`,
  `Erase.npStepRD` (the per-instruction lemma under `c'.WfProm tid`).
- `ThreadRuleRX`, `NPSafe.of_ruleRX`, and `ThreadRuleR.toRX` (every
  `ThreadRuleR` is one).
-/
import Kraken.Promising.SLR.NPSafeInvR
import Kraken.Promising.LiveWfProm

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Overtaken promises -/

/-- Some outstanding promise of the context is at or below the context's
`coh` of its location: it can no longer be fulfilled (`writeSuccs` fulfils
only above `coh`). -/
def _root_.Kraken.Promising.Ctx.Overtaken (cx : Ctx) : Prop :=
  ∃ p ∈ cx.prom, ∃ w, cx.mem.get? p = some w ∧ p ≤ cx.views.getCoh w.loc

/-- An overtaken promise stays overtaken along every later context step. -/
theorem _root_.Kraken.Promising.Ctx.Overtaken.dord {cx cx' : Ctx} (h : cx.Overtaken) (hd : cx.DOrd cx') : cx'.Overtaken := by
  obtain ⟨p, hp, w, hw, hle⟩ := h
  have hp' : p ∈ cx'.prom := by
    refine Classical.byContradiction fun hn => ?_
    have := (hd.prom p hp hn).2 w hw
    omega_t
  exact ⟨p, hp', w, by rw [hd.mem.get? (cx.mem.last_le_of_get?_eq_some hw)]; exact hw,
    Nat.le_trans hle (hd.coh _)⟩

/-- **A thread finishing an instruction from an overtaken context has a dead
promise** (`finishInstr` keeps the promises and every view but `vCAP`). -/
theorem _root_.Kraken.Promising.Ctx.Overtaken.finish {cx : Ctx} (h : cx.Overtaken) {t : Thread I} {d : InstrDeps I.RegId}
    {iv : InstrViews} {st : I.State} {th : Thread I} (hth : th ∈ finishInstr t d iv st cx) :
    th.hasDeadPromise cx.mem = true := by
  obtain ⟨p, hp, w, hw, hle⟩ := h
  obtain ⟨hpr, hv⟩ := finishInstr_relKey hth
  have hcoh : th.views.getCoh w.loc = cx.views.getCoh w.loc := by
    have := congrArg Views.coh hv
    simp only at this
    simp only [Views.getCoh, this]
  unfold Thread.hasDeadPromise
  rw [List.any_eq_true]
  refine ⟨p, hpr ▸ hp, ?_⟩
  rw [hw]
  simp only [decide_eq_true_eq, hcoh]
  omega_t

/-! ## The erasure WP with dead branches -/

/-- **Erasure WP with bounded reach and dead branches**: `EvTree.EraseWPR`
whose write nodes may instead show that the write overtook an own
outstanding promise (`Ctx.Overtaken` at the write's successor); such a run
ends in a thread with a dead promise, which `NPSafe`'s step never asks
about. -/
def _root_.Kraken.Promising.EvTree.EraseWPRD (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res)
    (T : Nat → Prop) (c : Config I) (t : Thread I) {σ : Type} (Post : σ → Res → Ghost → Ctx → Prop) :
    EvTree σ → Res → Ghost → Ctx → Prop
  | .done s, r, g, cx => Post s r g cx
  | .fault _, _, _, _ => True
  | .choose _ k, r, g, cx => ∀ i, EvTree.EraseWPRD A tid iv rF T c t Post (k i) r g cx
  | .load k xcl l ret, r, g, cx => ∀ x ∈ readSuccs A iv cx k xcl l,
      EvTree.EraseWPRD A tid iv rF T c t Post (ret x.2.1) r g x.2.2
  | .store k xcl l v ret, r, g, cx =>
      (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl l v (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
        ErAt rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
        cx'.Overtaken ∨ ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' cx' ∧
          EvTree.EraseWPRD A tid iv rF T c t Post (ret true) r' g' cx') ∧
      (xcl = true → EvTree.EraseWPRD A tid iv rF T c t Post (ret false) r g (xclFailCtx cx l))
  | .fence k ret, r, g, cx => EvTree.EraseWPRD A tid iv rF T c t Post (ret ()) r g (fenceStep cx k)
  | .rmw k noRet l op ret, r, g, cx =>
      ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
        (op x.2.1 = none → EvTree.EraseWPRD A tid iv rF T c t Post (ret x.2.1) r g (fenceOptCtx A x.2.2)) ∧
        ∀ new, op x.2.1 = some new →
          ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
            ErAt rF T c t tid r g x.2.2 → cx.Inv tid → c.mem.last ≤ cx.mem.last →
            cx'.Overtaken ∨ ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' (rmwAfter A k noRet l cx') ∧
              EvTree.EraseWPRD A tid iv rF T c t Post (ret x.2.1) r' g' (rmwAfter A k noRet l cx')

section WPRD

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type}

/-- **Every `EraseWPR` proof is an `EraseWPRD` proof** (never using a dead
branch), into any weaker postcondition. -/
theorem _root_.Kraken.Promising.EvTree.EraseWPR.toD {Post Q : σ → Res → Ghost → Ctx → Prop}
    (hQ : ∀ s r g cx, Post s r g cx → Q s r g cx) (tree : EvTree σ) :
    ∀ r g cx, tree.EraseWPR A tid iv rF T c t Post r g cx → tree.EraseWPRD A tid iv rF T c t Q r g cx := by
  induction tree with
  | done s => exact fun r g cx h => hQ s r g cx h
  | fault _ => exact fun _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx h i => ih i r g cx (h i)
  | load k xcl l ret ih => exact fun r g cx h x hx => ih x.2.1 r g x.2.2 (h x hx)
  | store k xcl l v ret ih =>
    refine fun r g cx h => ⟨fun cx' hc E hi hm => ?_, fun hx => ih false r g _ (h.2 hx)⟩
    obtain ⟨r', g', E', hR, hw⟩ := h.1 cx' hc E hi hm
    exact .inr ⟨r', g', E', hR, ih true r' g' cx' hw⟩
  | fence k ret ih => exact fun r g cx h => ih () r g _ h
  | rmw k noRet l op ret ih =>
    refine fun r g cx h x hx => ⟨fun hop => ih x.2.1 r g _ ((h x hx).1 hop), fun new hop cx' hc E hi hm => ?_⟩
    obtain ⟨r', g', E', hR, hw⟩ := (h x hx).2 new hop cx' hc E hi hm
    exact .inr ⟨r', g', E', hR, ih x.2.1 r' g' _ hw⟩

/-- `EraseWPRD` is monotone in its postcondition. -/
theorem _root_.Kraken.Promising.EvTree.EraseWPRD.mono {Post Q : σ → Res → Ghost → Ctx → Prop}
    (hQ : ∀ s r g cx, Post s r g cx → Q s r g cx) (tree : EvTree σ) :
    ∀ r g cx, tree.EraseWPRD A tid iv rF T c t Post r g cx → tree.EraseWPRD A tid iv rF T c t Q r g cx := by
  induction tree with
  | done s => exact fun r g cx h => hQ s r g cx h
  | fault _ => exact fun _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx h i => ih i r g cx (h i)
  | load k xcl l ret ih => exact fun r g cx h x hx => ih x.2.1 r g x.2.2 (h x hx)
  | store k xcl l v ret ih =>
    refine fun r g cx h => ⟨fun cx' hc E hi hm => ?_, fun hx => ih false r g _ (h.2 hx)⟩
    rcases h.1 cx' hc E hi hm with ho | ⟨r', g', E', hR, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hR, ih true r' g' cx' hw⟩
  | fence k ret ih => exact fun r g cx h => ih () r g _ h
  | rmw k noRet l op ret ih =>
    refine fun r g cx h x hx => ⟨fun hop => ih x.2.1 r g _ ((h x hx).1 hop), fun new hop cx' hc E hi hm => ?_⟩
    rcases (h x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', E', hR, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hR, ih x.2.1 r' g' _ hw⟩

/-- **The frame with dead branches**: a run of an event tree with
`EraseWPRD` from a point where `KAcc` holds w.r.t. the instruction's start
`(r₀, g₀)` ends in erasure, the postcondition and `RStep` from the start, or
in an overtaken context. -/
theorem runTree_eraseWPRD {Post : σ → Res → Ghost → Ctx → Prop} (r₀ : Res) (g₀ : Ghost) (tree : EvTree σ) :
    ∀ (r : Res) (g : Ghost) (cx : Ctx) (s : σ) (cx' : Ctx), .ok (s, cx') ∈ runTree A tid iv cx tree →
      ErAt rF T c t tid r g cx → cx.Inv tid → tree.EraseWPRD A tid iv rF T c t Post r g cx →
      KAcc c r₀ g₀ r g cx →
      (∃ r' g', ErAt rF T c t tid r' g' cx' ∧ Post s r' g' cx' ∧ RStep c.mem.last r₀ g₀ r' g' cx') ∨
        cx'.Overtaken := by
  induction tree with
  | done s0 =>
    intro r g cx s cx' h E _ hw hk
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨r, g, E, hw, hk.2⟩
  | fault m => intro r g cx s cx' h; simp [runTree] at h
  | choose n k ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i r g cx s cx' h E hi (hw i) hk
  | load k xcl l ret ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hm, hp⟩ := readSuccs_memProm A iv hx
    exact ih x.2.1 r g x.2.2 s cx' h (E.congr hm hp) (readSuccs_inv A tid iv hx hi).1 (hw x hx)
      (hk.move (by rw [hm]; exact Nat.le_refl _) (readSuccs_vmono A iv hx))
  | store k xcl l v ret ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      rcases hw.1 c0 hc0 E hi hk.1 with ho | ⟨r', g', E', hR, hw'⟩
      · exact .inr (ho.dord (runTree_dord A tid iv _ c0 s cx' h))
      · obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc0 hi
        have hv := writeSuccs_vmono A tid hc0
        exact ih true r' g' c0 s cx' h E' (writeSuccs_inv A tid _ hc0 hi).1 hw'
          ⟨Nat.le_trans hk.1 hev.last_le, hk.2.trans hR hv.wfloor⟩
    · rw [List.mem_ite_nil_right] at h
      have hi' : (xclFailCtx cx l).Inv tid := (hi.of_views (c' := xclFailCtx cx l) rfl rfl rfl).1
      exact ih false r g _ s cx' h.2 (E.congr rfl rfl) hi' (hw.2 h.1)
        (hk.move (Nat.le_refl _) ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
  | fence k ret ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree] at h
    exact ih () r g _ s cx' h (E.congr (fenceStep_mem cx k) (fenceStep_prom cx k)) (fenceStep_inv tid hi k).1 hw
      (hk.move (by rw [fenceStep_mem]; exact Nat.le_refl _) (fenceStep_vmono cx k))
  | rmw k noRet l op ret ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree] at h
    have hi1 := (fenceOpt_inv tid hi A.rmwFence .sy).1
    obtain ⟨hm1, hp1⟩ := fenceOptCtx_memProm A cx
    change Except.ok (s, cx') ∈ (readSuccs A iv (fenceOptCtx A cx)
      (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet).flatMap _ at h
    rw [List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hm2, hp2⟩ := readSuccs_memProm A iv hx
    have hi2 := (readSuccs_inv A tid iv hx hi1).1
    have E2 : ErAt rF T c t tid r g x.2.2 := E.congr (hm2.trans hm1) (hp2.trans hp1)
    have hv2 : cx.VMono x.2.2 := (fenceOptCtx_vmono A cx).trans (readSuccs_vmono A iv hx)
    have hk2 : KAcc c r₀ g₀ r g x.2.2 := hk.move (by rw [hm2, hm1]; exact Nat.le_refl _) hv2
    obtain ⟨hwn, hws⟩ := hw x hx
    obtain ⟨tr, old, c2⟩ := x
    simp only at h hwn hws E2 hi2 hk2
    split at h
    · next hop =>
      obtain ⟨hm3, hp3⟩ := fenceOptCtx_memProm A c2
      exact ih old r g _ s cx' h (E2.congr hm3 hp3) (fenceOpt_inv tid hi2 A.rmwFence .sy).1 (hwn hop)
        (hk2.move (by rw [hm3]; exact Nat.le_refl _) (fenceOptCtx_vmono A _))
    · next new hop =>
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change Except.ok (s, cx') ∈ runTree A tid iv (rmwAfter A k noRet l c3) (ret old) at h
      rcases hws new hop c3 hc3 E2 hi hk.1 with ho | ⟨r', g', E3, hR, hw3⟩
      · refine .inr (ho.dord ?_)
        refine Ctx.DOrd.trans ?_ (runTree_dord A tid iv _ _ s cx' h)
        unfold rmwAfter
        exact (Ctx.DOrd.rmwPost A c3 k noRet l).trans (Ctx.DOrd.fenceOpt _ A.rmwFence .sy)
      · obtain ⟨hm4, hp4⟩ := rmwAfter_memProm A k noRet l c3
        have hi3 := (writeSuccs_inv A tid _ hc3 hi2).1
        have hi4 : (rmwAfter A k noRet l c3).Inv tid := by
          unfold rmwAfter
          exact (fenceOpt_inv tid (rmwPost_inv A tid hi3 k noRet l).1 A.rmwFence .sy).1
        obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc3 hi2
        have hv := (writeSuccs_vmono A tid hc3).trans (rmwAfter_vmono A k noRet l c3)
        refine ih old r' g' _ s cx' h (E3.congr hm4 hp4) hi4 hw3 ⟨?_, hk2.2.trans hR hv.wfloor⟩
        rw [hm4]; exact Nat.le_trans hk2.1 hev.last_le

end WPRD

/-- **Erasure and bounded reach across one instruction, with dead
branches**: `Erase.npStepR` for `EvTree.EraseWPRD`, at a step whose
post-configuration has no dead promise of `tid` (`NPSafe`'s `c'.WfProm tid`),
with the thread after the step. -/
theorem Erase.npStepRD {A : Arch} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c c' : Config I} {tid : Nat}
    {r : Res} {Post : Thread I → I.State → Res → Ghost → Ctx → Prop}
    (hinv : c.MachInv) (E : Erase (setRes rF tid r) g T c) (hs : NPStepBy A tid c c') (hwf' : c'.WfProm tid)
    (hwp : ∀ t tree, c.threads[tid]? = some t → I.exec t.st = some tree →
      tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF T c t (Post t) r g (ctx₀ t tid c.mem)) :
    ∃ t t' st r' g' cx', c.threads[tid]? = some t ∧
      t' ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st cx' ∧
      c' = c.withThread tid t' cx'.mem ∧ Post t st r' g' cx' ∧ Erase (setRes rF tid r') g' T c' ∧
      RStep c.mem.last r g r' g' cx' := by
  obtain ⟨t, t', mem', ht, ⟨outs, o, hstep, ho, he⟩, rfl⟩ := hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hn := lt_size_of_get? ht
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨res, hr, ho⟩ := ho
    cases res with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, cx'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have E0 : ErAt rF T c t tid r g (ctx₀ t tid c.mem) := by
        unfold ErAt
        rw [Config.withThread_self c ht]
        exact E
      rcases runTree_eraseWPRD r g tree r g _ st cx' hr E0 (hinv.ctxInv ht _) (hwp t tree ht hex)
          ⟨Nat.le_refl _, RStep.refl _ _ _ _⟩ with ⟨r', g', E', hpost, hR⟩ | ho
      · exact ⟨t, th, st, r', g', cx', ht, hth, rfl, hpost,
          Erase.withThread_prom E' hn (finishInstr_relKey hth).1, hR⟩
      · exfalso
        have hth' : (c.withThread tid th cx'.mem).threads[tid]? = some th := by
          rw [Config.withThread_get? c th cx'.mem hn, ite_eq_left rfl]
        have h1 := hwf' th hth'
        simp only [Config.withThread] at h1
        rw [ho.finish hth] at h1
        cases h1

/-! ## The rule interface -/

/-- **A per-thread rule with instance invariants and dead branches.** As
`ThreadRuleR`, but with no `env` field: `done`, `wp` and `prepay` receive
`Inv` at the `NPSafe` instance `(c₀, g₀)` together with the environment
extension `EnvExt tid c₀ c` and the world growth `g₀ ≤ g` (and, in `wp` and
`prepay`, the own-pending transport from `g` to `g₀`), and `wp` is an
`EvTree.EraseWPRD`. -/
structure ThreadRuleRX (A : Arch) (B : Config I → (model I).R → (model I).Ghost → Prop) (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  done : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}, Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    cl → c.Done tid → B c r g
  wp : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)
  prepay : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- **`NPSafe` from a `ThreadRuleRX`.** The induction of `NPSafe.of_inv`,
with the step from `Erase.npStepRD` (its `c'.WfProm tid` is the step's). -/
theorem NPSafe.of_ruleRX {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) :
    ∀ (n m : Nat) (cl : Prop) (c : Config I) (r : (model I).R) (g : (model I).Ghost), R.Inv cl c r g →
      NPSafe (model I) A B tid n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafe]
  | n + 1, 0, cl, c, r, g, h => by
    rw [NPSafe]
    exact fun m => NPSafe.of_ruleRX R n m cl c r g h
  | n + 1, m + 1, cl, c, r, g, h => by
    rw [NPSafe]
    intro c₁ g₁ he hg
    refine ⟨R.done h he hg, fun rF c' E hs hinv hwf hwf' hnp => ?_, fun rF t₁ w ht₁ E hinv hnp hrel => ?_⟩
    · obtain ⟨t, t', st, r', g', cx', ht, hth, rfl, hpost, E', hR⟩ := Erase.npStepRD
        (Post := fun t => WpPostR R.Inv (cl ∧ Erase (setRes rF tid r) g₁ (fun _ => False) c₁) c₁ tid r g₁ t)
        hinv E hs hwf' (fun t tree ht hex => R.wp rF t tree h he hg ht hex E hinv hwf (hnp t ht))
      obtain ⟨hg', hkeep, hnew, hacq, hown, hfin⟩ := hpost
      have hn := lt_size_of_get? ht
      have ht' : (c₁.withThread tid t' cx'.mem).threads[tid]? = some t' := by
        rw [Config.withThread_get? c₁ t' cx'.mem hn, ite_eq_left rfl]
      have hdead : t'.hasDeadPromise cx'.mem = false := by
        have := hwf' t' ht'
        simpa [Config.withThread] using this
      have hinv' := hfin t' hth hdead
      refine ⟨r', g', E', hg', ?_, hnew, NPSafe.of_ruleRX R (n + 1) m _ _ r' g' hinv', hacq,
        fun w hw => hown w (written_cx ht (finishInstr_relKey hth).1 hw), hR.1, ?_⟩
      · rintro ts hts ⟨i, ti, hi, htsi⟩
        refine hkeep ts hts ?_
        rw [Config.withThread_get? c₁ t' cx'.mem hn] at hi
        split at hi
        · next he' =>
          subst he'
          cases hi
          exact .inl ((finishInstr_relKey hth).1 ▸ htsi)
        · next he' => exact .inr ⟨i, ti, Ne.symm he', hi, htsi⟩
      · intro b hb hv x hx
        exact hR.finish hth b hb (hv t' ht') x hx
    · obtain ⟨r', g', E', hg', hpend, hkeep, hnew, h', hacq, hk1, hk2⟩ :=
        R.prepay rF t₁ w h he hg ht₁ E hinv hnp hrel
      exact ⟨r', g', E', hg', hpend, hkeep, hnew, NPSafe.of_ruleRX R (n + 1) m _ _ r' g' h', hacq, hk1, hk2⟩
termination_by n m => (n, m)

/-- **Every `ThreadRuleR` is a `ThreadRuleRX`**: `env` moves `Inv` from the
instance to the extension, and `EvTree.EraseWPR.toD`. -/
def ThreadRuleR.toRX {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleR A B tid) : ThreadRuleRX A B tid where
  Inv := R.Inv
  done h he hg := R.done (R.env h he hg)
  wp rF t tree h he hg ht hex E hinv hwf hnp :=
    EvTree.EraseWPR.toD (fun _ _ _ _ h => h) tree _ _ _
      (R.wp _ rF t tree (R.env h he hg) hg ht hex E hinv hwf hnp)
  prepay rF t₁ w h he hg ht E hinv hnp hrel :=
    R.prepay _ rF t₁ w (R.env h he hg) hg ht E hinv hnp hrel.toRelFulfils

end Kraken.Promising.SLR
