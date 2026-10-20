/-
Fence-based release (`dmb ish; str`), machine half.

Messages carry no view in Kraken, so a release store differs from a plain one
only in (1) its pre-view, which also takes `relPre = vrOld ⊔ vrOldNR ⊔ vwOld`
(`writeSuccs`), and (2) raising `vRel` (`afterWrite`), which only later
*acquire* loads read (RCsc `stlr; ldar`), not message passing. Every store's
pre-view takes `vwNew ⊔ vCAP`. `dmb ish` (`fence .sy`) puts `vwNew` above
`relPre` (and `vwOldNT`); `dmb ishst`/`dsb st` (`.st`/`.stAll`) fold only the
write views.

- `Views.FenceRel`: `relPre ≤ vwNew ⊔ vCAP`. Then a store of *any* kind has a
  bound at least a release store's: it may fulfil or write exactly the
  timestamps `stlr` could.
- `fenceStep_sy_fenceRel`: after `dmb ish`/`dsb sy`, `FenceRel` holds.
  `fenceStep_st_fenceRel`, `fenceStep_stAll_fenceRel`: after `dmb ishst` /
  `dsb st` it holds if the reads were already covered (a read before
  `dmb st` is not ordered with a later store: LB+dmb.st is allowed).
- `writeSuccs_fenceRel_relPre`: a store under `FenceRel` fulfilling `ts` has
  `relPre < ts` (the analogue of `writeSuccs_rel_relPre`).
- `EvTree.RelFulfilsF`, `EvTree.RelFulfilsF.relPre_lt`: the fence-aware
  `EvTree.RelFulfils` (a fulfilling write is a release *or* runs under
  `FenceRel`) is release-bounded. `relPre_lt` is the only fact about the
  fulfilling write that Theorem 1′'s machine side ((S2), (S1′)) uses.

**Why this file alone is not a theorem about (C).** `PromisePure`
(`RelFulfilled`) and `NPSafe`'s prepay conjunct are both keyed to
`Thread.RelFulfilsLive`, i.e. to `A.storeKind k = .rel`. A fence-release
fulfilment is never prepaid there, so its promise reaches case (d2), which
needs the value pure: `PromisePure` is false for `str data; dmb ish; str flag`
with an impure predicate at `flag`, whatever the cell condition. Covering it
needs a prepay conjunct guarded by the `RelFulfilsF` form.

**Status.** That conjunct now exists, additively (the existing
`NPSafe`/`PromisePure` are unchanged):
- the parameterised `NPSafeP G K` with the fence-aware prepay guards `GF`
  (`RelFulfilsLiveF`) and `GHyb rel` (the current guard, or a fence-aware
  fulfilment of an impure value), `SLR/NPSafePFence.lean`;
- the cell condition `EvTree.RelWritesF` and Theorem 1′ at those guards,
  `theorem1IIPure_of_relWritesF` (`SLR/PromisePureF.lean`);
- message passing with a `dmb ish; str` writer end to end: `MpFence.mp_fence`
  (`SLR/MpFence.lean`), and the same statement on the whole-thread
  environment, `mp_fence_envG` (`SLR/EnvG/FenceEnvMpPublic.lean`;
  rule `ThreadRuleRXG.ofEnvGHyb`, `SLR/EnvG/FenceEnv.lean`).

Still open (`KNOWN_GAPS.md`): `dmb ishst`/`dsb st` publishers (they never set
the flag here, as herd allows LB+dmb.st, so a plain store after them is not
release-bounded), fence-aware release RMWs, and a generic `ThreadRuleRX` →
`GHyb` producer.
-/
import Kraken.Promising.ReleasePrefix

namespace Kraken.Promising

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- **Fence-release views**: every earlier read and write of the thread
(`relPre`) is below the views every later store's pre-view takes
(`vwNew ⊔ vCAP`). A store issued from such views is release-bounded like
`stlr`. -/
def Views.FenceRel (vs : Views) : Prop := vs.relPre ≤ max vs.vwNew vs.vCAP

/-- `dmb ish` / `dmb sy` / `dsb sy` establish `FenceRel`. -/
theorem fenceStep_sy_fenceRel (c : Ctx) : (fenceStep c .sy).views.FenceRel := by
  simp only [fenceStep, Views.FenceRel, Views.relPre]; omega_t

/-- `dmb ishst` / `dmb st` establish `FenceRel` when the earlier reads were
already covered. -/
theorem fenceStep_st_fenceRel {c : Ctx} (h : max c.views.vrOld c.views.vrOldNR ≤ max c.views.vwNew c.views.vCAP) :
    (fenceStep c .st).views.FenceRel := by
  simp only [fenceStep, Views.FenceRel, Views.relPre]; omega_t

/-- `dsb st` establishes `FenceRel` when the earlier reads were already
covered. -/
theorem fenceStep_stAll_fenceRel {c : Ctx}
    (h : max c.views.vrOld c.views.vrOldNR ≤ max c.views.vwNew c.views.vCAP) :
    (fenceStep c .stAll).views.FenceRel := by
  simp only [fenceStep, Views.FenceRel, Views.relPre]; omega_t

private theorem mem_ite_nil'' {α : Type} {p : Prop} [Decidable p] {ys : List α} {x : α}
    (h : x ∈ (if p then ys else [])) : x ∈ ys := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A store under `FenceRel` fulfilling `ts` has `relPre < ts`**, whatever
its kind (the fence-aware `writeSuccs_rel_relPre`). -/
theorem writeSuccs_fenceRel_relPre {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr)
    (hF : c.views.FenceRel) {ts : Time} (hin : ts ∈ c.prom) (hout : ts ∉ c'.prom) : c.views.relPre < ts := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨hc, h⟩ := Option.ite_none_right_eq_some.mp h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [afterWrite] at hout
        have hts : ts = t := by
          by_cases hne : ts = t
          · exact hne
          · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
        subst hts
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨-, hb, -⟩ := hc
        simp only [Views.FenceRel] at hF
        generalize (if (A.storeKind k == StoreKind.rel) = true then
          max (max c.views.vrOld c.views.vrOldNR) c.views.vwOld
          else if (A.storeKind k == StoreKind.nt) = true then max c.views.vrOld c.views.vrOldNR else 0) = e at hb
        omega_t
    · cases h
  · have h := mem_ite_nil'' h
    rw [List.mem_singleton] at h
    subst h
    exfalso
    apply hout
    simp only [afterWrite]
    by_cases hne : ts = c.mem.msgs.size + 1
    · subst hne
      rw [List.erase_append_left _ hin]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)

/-- **Fence-aware `EvTree.RelFulfils`**: some run of the tree from `c`
fulfils `ts` with a write that is a release (`A.storeKind`) *or* is issued
from `FenceRel` views (e.g. a plain `str` after `dmb ish` with no access in
between). -/
def EvTree.RelFulfilsF {σ : Type} (ts : Time) : Ctx → EvTree σ → Prop
  | _, .done _ => False
  | _, .fault _ => False
  | c, .choose _ k => ∃ i, RelFulfilsF ts c (k i)
  | c, .load k xcl l ret => ∃ x ∈ readSuccs A iv c k xcl l, RelFulfilsF ts x.2.2 (ret x.2.1)
  | c, .store k xcl l v ret =>
    (∃ c' ∈ writeSuccs A tid (iv.forStore c.stores) c k xcl l v
        (if xcl then c.views.xclb.map (·.1) else none) 0 (if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0),
      ((A.storeKind k = .rel ∨ c.views.FenceRel) ∧ ts ∈ c.prom ∧ ts ∉ c'.prom) ∨ RelFulfilsF ts c' (ret true)) ∨
    RelFulfilsF ts
      { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } (ret false)
  | c, .fence k ret => RelFulfilsF ts (fenceStep c k) (ret ())
  | c, .rmw k noRet l op ret =>
    ∃ x ∈ readSuccs A iv (if A.rmwFence then fenceStep c .sy else c)
        (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      RelFulfilsF ts (if A.rmwFence then fenceStep x.2.2 .sy else x.2.2) (ret x.2.1) ∨
      ∃ new, op x.2.1 = some new ∧
        ∃ c' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
          ((A.storeKind (A.rmwKind k).storeKind = .rel ∨ x.2.2.views.FenceRel) ∧ ts ∈ x.2.2.prom ∧ ts ∉ c'.prom) ∨
          RelFulfilsF ts
            (if A.rmwFence then fenceStep (rmwPost A k noRet l c') .sy else rmwPost A k noRet l c') (ret x.2.1)

/-- Every release fulfilment is a fence-aware one. -/
theorem EvTree.RelFulfils.toF {ts : Time} {σ : Type} :
    ∀ (tree : EvTree σ) (c : Ctx), tree.RelFulfils A tid iv ts c → tree.RelFulfilsF A tid iv ts c
  | .done _, _, h => h
  | .fault _, _, h => h
  | .choose _ k, c, ⟨i, h⟩ => ⟨i, toF (k i) c h⟩
  | .load _ _ _ ret, _, ⟨x, hx, h⟩ => ⟨x, hx, toF (ret x.2.1) _ h⟩
  | .store _ _ _ _ ret, _, h => by
    rcases h with ⟨c', hc', ⟨hk, h⟩ | h⟩ | h
    · exact .inl ⟨c', hc', .inl ⟨.inl hk, h⟩⟩
    · exact .inl ⟨c', hc', .inr (toF (ret true) _ h)⟩
    · exact .inr (toF (ret false) _ h)
  | .fence _ ret, _, h => toF (ret ()) _ h
  | .rmw _ _ _ _ ret, _, ⟨x, hx, h⟩ => by
    rcases h with h | ⟨new, hop, c', hc', ⟨hk, h⟩ | h⟩
    · exact ⟨x, hx, .inl (toF (ret x.2.1) _ h)⟩
    · exact ⟨x, hx, .inr ⟨new, hop, c', hc', .inl ⟨.inl hk, h⟩⟩⟩
    · exact ⟨x, hx, .inr ⟨new, hop, c', hc', .inr (toF (ret x.2.1) _ h)⟩⟩

/-- **A fence-aware release fulfilment of `ts` is release-bounded**: `c`'s
`relPre` is below `ts` (the fence-aware `EvTree.RelFulfils.relPre_lt`, which
is all Theorem 1′'s (S2)/(S1′) use of the fulfilling write). -/
theorem EvTree.RelFulfilsF.relPre_lt {ts : Time} {σ : Type} (tree : EvTree σ) :
    ∀ c : Ctx, c.views.FwdOk → EvTree.RelFulfilsF A tid iv ts c tree → c.views.relPre < ts := by
  induction tree with
  | done s => intro c _ h; exact h.elim
  | fault m => intro c _ h; exact h.elim
  | choose n k ih =>
    intro c hf ⟨i, h⟩
    exact ih i c hf h
  | load k xcl l ret ih =>
    intro c hf ⟨x, hx, h⟩
    have hs := readSuccs_silent A iv hf hx
    exact Nat.lt_of_le_of_lt hs.relPre (ih x.2.1 x.2.2 hs.fwd h)
  | store k xcl l v ret ih =>
    intro c hf h
    rcases h with ⟨c', hc', ⟨hk | hk, h⟩ | h⟩ | h
    · exact writeSuccs_rel_relPre A tid _ hc' hk h.1 h.2
    · exact writeSuccs_fenceRel_relPre A tid _ hc' hk h.1 h.2
    · have hs := writeSuccs_silent A tid _ hf hc'
      exact Nat.lt_of_le_of_lt hs.relPre (ih true c' hs.fwd h)
    · have hs : Ctx.Silent c
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl, by simp⟩
      exact Nat.lt_of_le_of_lt hs.relPre (ih false _ hs.fwd h)
  | fence k ret ih =>
    intro c hf h
    have hs := Ctx.Silent.fenceStep hf k
    exact Nat.lt_of_le_of_lt hs.relPre (ih () _ hs.fwd h)
  | rmw k noRet l op ret ih =>
    intro c hf ⟨x, hx, h⟩
    have h1 := Ctx.Silent.fenceOpt hf A.rmwFence .sy
    have h2 := h1.trans (readSuccs_silent A iv h1.fwd hx)
    rcases h with h | ⟨new, -, c', hc', ⟨hk | hk, h⟩ | h⟩
    · have h3 := h2.trans (Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy)
      exact Nat.lt_of_le_of_lt h3.relPre (ih x.2.1 _ h3.fwd h)
    · exact Nat.lt_of_le_of_lt h2.relPre (writeSuccs_rel_relPre A tid _ hc' hk h.1 h.2)
    · exact Nat.lt_of_le_of_lt h2.relPre (writeSuccs_fenceRel_relPre A tid _ hc' hk h.1 h.2)
    · have h3 := h2.trans (writeSuccs_silent A tid _ h2.fwd hc')
      have h4 := h3.trans (Ctx.Silent.rmwPost h3.fwd A k noRet l)
      have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
      exact Nat.lt_of_le_of_lt h5.relPre (ih x.2.1 _ h5.fwd h)

end Rules

end Kraken.Promising
