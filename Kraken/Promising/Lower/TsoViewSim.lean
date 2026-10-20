/-
**`fence .st` on `Arch.tso` is a stutter up to an
invisible `vwNew` difference** (ISA-neutral).

`Lower/TsoCollapse.lean` ((B1)) showed that `fence .st` is not a
literal stutter: it sets `vwNew := vwNew ⊔ vwOld ⊔ vwOldNT`
(`fenceStep_st`). This file shows that, on the fuel-free machine
(`InstrSemInf`/`PromSemInf`/`StepSemInf`, `CertOk`, `ReachableSemInf`), the
raised `vwNew` is invisible as long as the thread makes no non-temporal store,
by a lockstep simulation for a relation that equates everything but `vwNew`.

## The relation

- `setVw c w` / `vwT w t`: the context / thread with `vwNew := w`.
- `CtxVw c c'`: `c'` is `c` but for `vwNew`, and `vwNew ⊔ vwOld` agree.
- `VwNewEquiv t t'`: the same for threads (state, register views, promises
  and every other view component equal). Symmetric (`VwNewEquiv.symm`).
- `CfgVwEquiv P tid c c'`: same memory, same threads but `tid`, where the two
  threads are `VwNewEquiv`, and the thread's state satisfies `P`.

## Side conditions

- **(S1) No non-temporal store from here on** (`NTFreeInv P`: every tree of
  a `P`-state makes no `.nt` store, `EvTree.NoNT Arch.tso`, and its leaves
  satisfy `P`). The relation itself needs nothing else: every NT-free step
  preserves it. WeakCore's x64 lowering never emits `movnti`.
- **(S2) No outstanding non-temporal store**, only to *enter* the relation
  at a `fence .st`: `NoOutNT t := vwOldNT ≤ vwNew ⊔ vwOld` (implied by
  `vwOldNT = 0`). NT-free steps preserve it (`cfgNoOutNT_reachable`), and it
  holds initially (`cfgNoOutNT_init`).

Both are necessary. Litmus witnesses (x86, `sfence` is `.fence .st`; the
reader `mov r1, [y]; mov r2, [x]` is TSO-ordered), outcome `r1 = 1 ∧ r2 = 0`:
- (S2 fails) `movnti [x], 1; sfence; mov [y], 1`: forbidden with the
  `sfence`, allowed without it (`mov [y]`'s release pre-view takes `vwOld`,
  not `vwOldNT`; only the fence's raised `vwNew` orders it after the NT store).
- (S1 fails) `mov [x], 1; sfence; movnti [y], 1`: forbidden with the
  `sfence`, allowed without it (an NT store's pre-view takes `vwNew` but not
  `vwOld`, `writeSuccs`).

The direction "larger `vwNew` simulated by smaller" holds even with NT stores
(a smaller pre-view admits every timestamp a larger one does); the backward
simulation of the lowering needs the other direction (target without the
fence, smaller `vwNew`, simulated by the source), which is where (S1) is used.

## Every reader of `vwNew` (checked)

1. `readSuccs`/`readNext`: writes only (an acquire joins `νpost` into it);
   `readPre` uses `vrNew`/`vRel`. Commutes with `setVw` (`readNext_setVw`).
2. `writeSuccs` (`writePre`): reads `vwNew`. For `.rel` (every TSO plain or
   release store, `Arch.tso.storeKind`) it is joined with `vwOld`, so the
   pre-view, `writeOk`, and the `promisedNow` bound depend only on
   `vwNew ⊔ vwOld` (`writePre_setVw`). For `.nt` it is not: (S1).
   `afterWrite` leaves `vwNew` and raises `vwOld`.
3. `fenceStep`: `.sy`/`.ld`/`.st`/`.stAll` join a view into `vwNew`
   (compatible with the relation); `.isb` does not touch it.
4. RMWs on TSO start with `fence .sy`, whose view is `≥ vwOld`: after it the
   two contexts are equal (`fenceStep_sy_setVw`). `rmwBump` joins `coh l`.
5. The store-exclusive failure branch, `finishInstr` (copies the context's
   views; a branch raises `vCAP`) and `promThread`: no access.
6. `CertOk`/`ThreadNP`: only through `stepOne` (`certOk_vw`).
7. `Thread.hasDeadPromise` reads `vwNew`; it is used only by the executable
   `certify`'s pruning, not by the fuel-free machine. **The executable
   checker (`certify`, `certifiedPromises`, `succs`) is therefore not covered
   by this simulation**; it is a statement about the semantic machine only.

## Results

- `runTree_vw`: lockstep at the tree level.
- `runOut_vw`, `threadStep_vw`: one instruction; same memory, same
  promises, related threads.
- Monotonicity, explicit: `runTree_vwOld_mono` (`vwOld` never decreases,
  any `Arch`); `Grow`/`TGrow` from `runTree_vw`/`runOut_vw` (TSO, NT-free:
  `vwOld` and `vwNew` grow, `vwOldNT` fixed).
- `certOk_vw`: `CertOk` transfers across `VwNewEquiv` (under (S1)).
- `instrSemInf_vw`, `promSemInf_vw`, `stepSemInf_vw`, `reachableSemInf_vw`:
  every step of `c` is matched by a step of `c'` with the same memory and
  promise effect, and the results are again `CfgVwEquiv`. Both directions:
  `CfgVwEquiv.symm`.
- **`fence .st` as a stutter up to `~`**: `instrSemInf_fence_st_vw` (exact
  form) and `instrSemInf_fence_st_stutter_vw`: a `fence .st` step from `c`
  yields a configuration `CfgVwEquiv` to the no-event outcome (the thread's
  own context, `finishInstr` at `ctx0`), which is `CertOk`.
-/
import Kraken.Promising.Lower.TsoCollapse

namespace Kraken.Promising.Lower.Tso

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep
open Kraken.Promising.Live.Sem

variable {I : ISA}

/-! ## The relation -/

/-- The context with `vwNew := w`. -/
def setVw (c : Ctx) (w : View) : Ctx := { c with views := { c.views with vwNew := w } }

/-- The thread with `vwNew := w`. -/
def vwT (w : View) (t : Thread I) : Thread I := { t with views := { t.views with vwNew := w } }

/-- Two contexts equal but for `vwNew`, with the same `vwNew ⊔ vwOld`. -/
def CtxVw (c c' : Ctx) : Prop := ∃ w, c' = setVw c w ∧ max c.views.vwNew c.views.vwOld = max w c.views.vwOld

/-- **The view relation**: two threads equal but for `vwNew`, with the same
`vwNew ⊔ vwOld`. -/
def VwNewEquiv (t t' : Thread I) : Prop :=
  ∃ w, t' = vwT w t ∧ max t.views.vwNew t.views.vwOld = max w t.views.vwOld

theorem setVw_self (c : Ctx) : setVw c c.views.vwNew = c := rfl

theorem vwT_self (t : Thread I) : vwT t.views.vwNew t = t := rfl

theorem CtxVw.refl (c : Ctx) : CtxVw c c := ⟨_, (setVw_self c).symm, rfl⟩

theorem CtxVw.symm {c c' : Ctx} (h : CtxVw c c') : CtxVw c' c := by
  obtain ⟨w, rfl, h⟩ := h
  exact ⟨c.views.vwNew, rfl, h.symm⟩

theorem VwNewEquiv.refl (t : Thread I) : VwNewEquiv t t := ⟨_, (vwT_self t).symm, rfl⟩

theorem VwNewEquiv.symm {t t' : Thread I} (h : VwNewEquiv t t') : VwNewEquiv t' t := by
  obtain ⟨w, rfl, h⟩ := h
  exact ⟨t.views.vwNew, rfl, h.symm⟩

theorem VwNewEquiv.st {t t' : Thread I} (h : VwNewEquiv t t') : t'.st = t.st := by
  obtain ⟨w, rfl, -⟩ := h; rfl

theorem VwNewEquiv.prom {t t' : Thread I} (h : VwNewEquiv t t') : t'.prom = t.prom := by
  obtain ⟨w, rfl, -⟩ := h; rfl

/-! ## The rules commute with `setVw` -/

section Rules

variable (iv : InstrViews)

/-- `max a o = max b o` survives raising `o` and joining the same view into
`a` and `b`. -/
private theorem max_vw {a b o o' ν : View} (h : max a o = max b o) (ho : o ≤ o') :
    max (max a ν) o' = max (max b ν) o' := by
  simp only [View] at *; omega

private theorem max_vw' {a b o o' : View} (h : max a o = max b o) (ho : o ≤ o') :
    max a o' = max b o' := by
  simp only [View] at *; omega

theorem readNext_setVw (c : Ctx) (w : View) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (t : Time)
    (v : Val) :
    readNext Arch.tso iv (setVw c w) k xcl l noRet t v =
      setVw (readNext Arch.tso iv c k xcl l noRet t v)
        (if (Arch.tso.loadKind k).isAcquire then
          max w (max (readPre Arch.tso iv c k) (readView Arch.tso (Arch.tso.loadKind k) (c.views.getFwd l) t))
         else w) := by
  unfold readNext
  split <;> rfl

/-- A read from related contexts: the same timestamps and values, related
contexts after. -/
theorem readSuccs_vw {c : Ctx} {w : View} (hw : max c.views.vwNew c.views.vwOld = max w c.views.vwOld)
    {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {t : Time} {v : Val} {c1 : Ctx}
    (h : (t, v, c1) ∈ readSuccs Arch.tso iv c k xcl l noRet) :
    ∃ w1, (t, v, setVw c1 w1) ∈ readSuccs Arch.tso iv (setVw c w) k xcl l noRet ∧
      max c1.views.vwNew c1.views.vwOld = max w1 c1.views.vwOld := by
  obtain ⟨t', v', he, h1, h2, h3, h4⟩ := (mem_readSuccs Arch.tso).mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  refine ⟨_, (mem_readSuccs Arch.tso).mpr ⟨t, v, congrArg (fun x => (t, v, x)) (readNext_setVw iv c w k xcl l noRet t v).symm, h1, h2, h3, h4⟩, ?_⟩
  have e1 : (readNext Arch.tso iv c k xcl l noRet t v).views.vwOld = c.views.vwOld := rfl
  have e2 : (readNext Arch.tso iv c k xcl l noRet t v).views.vwNew =
      if (Arch.tso.loadKind k).isAcquire then
        max c.views.vwNew (max (readPre Arch.tso iv c k) (readView Arch.tso (Arch.tso.loadKind k) (c.views.getFwd l) t))
      else c.views.vwNew := rfl
  rw [e1, e2]
  split
  · exact max_vw hw (Nat.le_refl _)
  · exact hw

theorem afterWrite_setVw (c : Ctx) (w : View) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time)
    (νf : View) (b : Bool) :
    afterWrite Arch.tso iv (setVw c w) k xcl l v t νf b = setVw (afterWrite Arch.tso iv c k xcl l v t νf b) w :=
  rfl

/-- The release pre-view depends only on `vwNew ⊔ vwOld`. -/
theorem writePre_setVw {c : Ctx} {w : View} (hw : max c.views.vwNew c.views.vwOld = max w c.views.vwOld)
    (extra : View) : writePre iv (setVw c w) .rel extra = writePre iv c .rel extra := by
  have e1 : (StoreKind.rel == StoreKind.rel) = true := rfl
  simp only [writePre, setVw, e1, ite_true]
  have e : ∀ a : View, max (max a c.views.vCAP) (max (max c.views.vrOld c.views.vrOldNR) c.views.vwOld) =
      max (max a c.views.vwOld) (max c.views.vCAP (max c.views.vrOld c.views.vrOldNR)) := by
    intro a; simp only [View]; omega
  rw [e, e, hw]

theorem afterWrite_vwOld_ge {xr : View} (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time)
    (νf : View) (b : Bool) : c.views.vwOld ≤ (afterWrite Arch.tso iv c k xcl l v t νf b xr).views.vwOld := by
  simp only [afterWrite]; split <;> simp only [View] at * <;> omega

theorem afterWrite_vwNew {xr : View} (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time)
    (νf : View) (b : Bool) : (afterWrite Arch.tso iv c k xcl l v t νf b xr).views.vwNew = c.views.vwNew := rfl

/-- A non-NT write from related contexts: the same writes, related contexts
after (same memory, promises and `promisedNow`). -/
theorem writeSuccs_vw {xr : View} (tid : Nat) {c : Ctx} {w : View}
    (hw : max c.views.vwNew c.views.vwOld = max w c.views.vwOld) {k : StoreKind}
    (hk : Arch.tso.storeKind k ≠ .nt) {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time} {extra : View}
    {c1 : Ctx} (h : c1 ∈ writeSuccs Arch.tso tid iv c k xcl l v tr extra xr) :
    setVw c1 w ∈ writeSuccs Arch.tso tid iv (setVw c w) k xcl l v tr extra xr ∧
      max c1.views.vwNew c1.views.vwOld = max w c1.views.vwOld := by
  have hrel : Arch.tso.storeKind k = .rel := by cases k <;> first | rfl | exact absurd rfl hk
  have hok : ∀ t, writeOk tid iv (setVw c w) .rel l tr extra t = writeOk tid iv c .rel l tr extra t := by
    intro t; simp only [writeOk, writePre_setVw iv hw]; rfl
  rw [mem_writeSuccs_iff] at h ⊢
  rw [hrel] at h ⊢
  rcases h with ⟨t, ht, hg, h1, rfl⟩ | ⟨h1, rfl⟩
  · refine ⟨.inl ⟨t, ht, hg, (hok t).trans h1, rfl⟩, ?_⟩
    exact max_vw' hw (afterWrite_vwOld_ge iv _ _ _ _ _ _ _ _)
  · refine ⟨.inr ⟨(hok _).trans h1, ?_⟩, ?_⟩
    · simp only [promiseNowCtx, writePre_setVw iv hw]; rfl
    · exact max_vw' hw (afterWrite_vwOld_ge iv _ _ xcl l v _ _ false)

/-- A fence from related contexts gives related contexts. -/
theorem fenceStep_vw {c : Ctx} {w : View} (hw : max c.views.vwNew c.views.vwOld = max w c.views.vwOld)
    (k : FenceKind) : ∃ w', fenceStep (setVw c w) k = setVw (fenceStep c k) w' ∧
      max (fenceStep c k).views.vwNew (fenceStep c k).views.vwOld = max w' (fenceStep c k).views.vwOld := by
  cases k
  · exact ⟨_, rfl, max_vw hw (Nat.le_refl _)⟩
  · exact ⟨_, rfl, max_vw hw (Nat.le_refl _)⟩
  · exact ⟨_, rfl, max_vw hw (Nat.le_refl _)⟩
  · exact ⟨_, rfl, max_vw hw (Nat.le_refl _)⟩
  · exact ⟨_, rfl, hw⟩

/-- **`fence .sy` (an RMW's leading fence on TSO) removes the difference.** -/
theorem fenceStep_sy_setVw {c : Ctx} {w : View} (hw : max c.views.vwNew c.views.vwOld = max w c.views.vwOld) :
    fenceStep (setVw c w) .sy = fenceStep c .sy := by
  have : max w (max (max c.views.vrOld c.views.vrOldNR) (max c.views.vwOld c.views.vwOldNT)) =
      max c.views.vwNew (max (max c.views.vrOld c.views.vrOldNR) (max c.views.vwOld c.views.vwOldNT)) := by
    simp only [View] at *; omega
  simp only [fenceStep, setVw, this]

end Rules

/-! ## Monotonicity: `vwOld` and `vwNew` never decrease -/

/-- Along an NT-free run on TSO, `vwOld` and `vwNew` only grow and `vwOldNT`
is unchanged. (The relation `CtxVw` is preserved because of the first two:
`max a o = max b o` survives `o ≤ o'` and joining a view into `a` and `b`.) -/
def Grow (c c' : Ctx) : Prop :=
  c.views.vwOld ≤ c'.views.vwOld ∧ c.views.vwNew ≤ c'.views.vwNew ∧ c'.views.vwOldNT = c.views.vwOldNT

theorem Grow.refl (c : Ctx) : Grow c c := ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩

theorem Grow.trans {a b c : Ctx} (h1 : Grow a b) (h2 : Grow b c) : Grow a c :=
  ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2.1 h2.2.1, h2.2.2.trans h1.2.2⟩

section GrowRules

variable (iv : InstrViews)

theorem readSuccs_grow {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (h : x ∈ readSuccs Arch.tso iv c k xcl l noRet) : Grow c x.2.2 := by
  obtain ⟨t, v, rfl, -⟩ := (mem_readSuccs Arch.tso).mp h
  refine ⟨Nat.le_refl _, ?_, rfl⟩
  show c.views.vwNew ≤ (if (Arch.tso.loadKind k).isAcquire then max c.views.vwNew _ else c.views.vwNew)
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_refl _

theorem writeSuccs_grow' {xr : View} (tid : Nat) {c : Ctx} {k : StoreKind} (hk : Arch.tso.storeKind k ≠ .nt) {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} {c1 : Ctx}
    (h : c1 ∈ writeSuccs Arch.tso tid iv c k xcl l v tr extra xr) : Grow c c1 := by
  have hrel : Arch.tso.storeKind k = .rel := by cases k <;> first | rfl | exact absurd rfl hk
  have e2 : (StoreKind.rel == StoreKind.nt) = false := rfl
  have key : ∀ (c0 : Ctx) xcl t νf b, c0.views = c.views →
      Grow c (afterWrite Arch.tso iv c0 .rel xcl l v t νf b xr) := by
    intro c0 xcl t νf b hv
    refine ⟨?_, ?_, ?_⟩
    · rw [← hv]; exact afterWrite_vwOld_ge iv _ _ _ _ _ _ _ _
    · rw [afterWrite_vwNew, hv]; exact Nat.le_refl _
    · simp only [afterWrite, e2, Bool.false_eq_true, ite_false, hv]
  rw [mem_writeSuccs_iff, hrel] at h
  rcases h with ⟨t, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · exact key _ _ _ _ _ rfl
  · exact key _ _ _ _ _ rfl

theorem fenceStep_grow (c : Ctx) (k : FenceKind) : Grow c (fenceStep c k) := by
  cases k
  · exact ⟨Nat.le_refl _, Nat.le_max_left _ _, rfl⟩
  · exact ⟨Nat.le_refl _, Nat.le_max_left _ _, rfl⟩
  · exact ⟨Nat.le_refl _, Nat.le_max_left _ _, rfl⟩
  · exact ⟨Nat.le_refl _, Nat.le_max_left _ _, rfl⟩
  · exact Grow.refl c

end GrowRules

/-! ## Lockstep at the tree level -/

/-- The pairing test of a store exclusive (`runTree`'s `paired`). -/
def pairedF (xb : Option (Time × View × Loc)) (l : Loc) : Bool :=
  match xb with
  | some (_, _, l') => l' == l
  | none => false

/-- The context of a failed store exclusive (`runTree`'s `fail` branch). -/
def xclFailCtx (c : Ctx) (l : Loc) : Ctx :=
  { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }

/-- **The tree-level lockstep** (TSO, NT-free tree): every successful run
from `c` is matched by a run from `setVw c w` (when `vwNew ⊔ vwOld` agree)
with the same final state and related contexts (so the same memory,
promises and `promisedNow`). The run also only grows `vwOld`/`vwNew` and
keeps `vwOldNT` (`Grow`). -/
theorem runTree_vw (tid : Nat) (iv : InstrViews) {σ : Type} (tree : EvTree σ) (hnt : tree.NoNT Arch.tso) :
    ∀ (c : Ctx) (w : View) (s : σ) (c1 : Ctx), max c.views.vwNew c.views.vwOld = max w c.views.vwOld →
      .ok (s, c1) ∈ runTree Arch.tso tid iv c tree →
      Grow c c1 ∧ ∃ c2, .ok (s, c2) ∈ runTree Arch.tso tid iv (setVw c w) tree ∧ CtxVw c1 c2 := by
  induction tree with
  | done s0 =>
    intro c w s c1 hw h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grow.refl _, setVw _ w, List.mem_singleton.mpr rfl, w, rfl, hw⟩
  | fault m => intro c w s c1 _ h; simp [runTree] at h
  | choose n k ih =>
    intro c w s c1 hw h
    simp only [runTree, List.mem_flatMap, List.mem_finRange, true_and] at h ⊢
    obtain ⟨i, h⟩ := h
    obtain ⟨hg, c2, h2, hr⟩ := ih i (hnt i) c w s c1 hw h
    exact ⟨hg, c2, ⟨i, h2⟩, hr⟩
  | load k xcl l ret ih =>
    intro c w s c1 hw h
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨⟨t, v, c'⟩, hx, h⟩ := h
    obtain ⟨w1, hx', hw1⟩ := readSuccs_vw iv hw hx
    obtain ⟨hg, c2, h2, hr⟩ := ih v (hnt v) c' w1 s c1 hw1 h
    exact ⟨(readSuccs_grow iv hx).trans hg, c2, ⟨(t, v, setVw c' w1), hx', h2⟩, hr⟩
  | store k xcl l v ret ih =>
    intro c w s c1 hw h
    obtain ⟨hk, hnt⟩ := hnt
    have key : ∀ c0 : Ctx, runTree Arch.tso tid iv c0 (.store k xcl l v ret) =
        (if (xcl && !pairedF c0.views.xclb l) = true then [] else
          (writeSuccs Arch.tso tid (iv.forStore c0.stores) c0 k xcl l v
            (if xcl then c0.views.xclb.map (·.1) else none) 0
            (if xcl then (c0.views.xclb.map (·.2.1)).getD 0 else 0)).flatMap fun c' =>
              runTree Arch.tso tid iv c' (ret true)) ++
        (if xcl then runTree Arch.tso tid iv (xclFailCtx c0 l) (ret false) else []) := fun _ => rfl
    have hx : (setVw c w).views.xclb = c.views.xclb := rfl
    have hs : (setVw c w).stores = c.stores := rfl
    have hf : xclFailCtx (setVw c w) l = setVw (xclFailCtx c l) w := rfl
    rw [key, List.mem_append] at h
    rw [key]
    simp only [List.mem_append, hx, hs, hf]
    rcases h with h | h
    · split at h
      · simp at h
      · rename_i hp
        rw [List.mem_flatMap] at h
        obtain ⟨c', hw', h⟩ := h
        obtain ⟨hw'', hm⟩ := writeSuccs_vw _ tid hw hk hw'
        obtain ⟨hg, c2, h2, hr⟩ := ih true (hnt true) c' w s c1 hm h
        refine ⟨(writeSuccs_grow' _ tid hk hw').trans hg, c2, .inl ?_, hr⟩
        simp only [hp, Bool.false_eq_true, ite_false, List.mem_flatMap]
        exact ⟨setVw c' w, hw'', h2⟩
    · cases xcl
      · simp at h
      · simp only [ite_true] at h ⊢
        obtain ⟨hg, c2, h2, hr⟩ := ih false (hnt false) (xclFailCtx c l) w s c1 hw h
        exact ⟨Grow.trans (c := c1) (b := xclFailCtx c l) ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩ hg, c2, .inr h2, hr⟩
  | rmw k noRet l op ret ih =>
    intro c w s c1 hw h
    have hrf : Arch.tso.rmwFence = true := rfl
    have e : runTree Arch.tso tid iv (setVw c w) (.rmw k noRet l op ret) =
        runTree Arch.tso tid iv c (.rmw k noRet l op ret) := by
      simp only [runTree, hrf, ite_true, fenceStep_sy_setVw hw]
    refine ⟨?_, c1, e ▸ h, CtxVw.refl c1⟩
    simp only [runTree, hrf, ite_true, List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c'⟩, hx, h⟩ := h
    have g1 := (fenceStep_grow c .sy).trans (readSuccs_grow iv hx)
    cases hop : op old with
    | none =>
      simp only [hop] at h
      exact g1.trans ((fenceStep_grow _ _).trans (ih old (hnt.2 old) _ _ s c1 rfl h).1)
    | some new =>
      simp only [hop, List.mem_flatMap] at h
      obtain ⟨c'', hw'', h⟩ := h
      refine g1.trans ((writeSuccs_grow' iv tid hnt.1 hw'').trans
        (Grow.trans ?_ ((fenceStep_grow _ _).trans (ih old (hnt.2 old) _ _ s c1 rfl h).1)))
      split
      · exact ⟨Nat.le_refl _, Nat.le_max_left _ _, rfl⟩
      · exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
  | fence k ret ih =>
    intro c w s c1 hw h
    obtain ⟨w', e, hw'⟩ := fenceStep_vw hw k
    obtain ⟨hg, c2, h2, hr⟩ := ih () hnt (fenceStep c k) w' s c1 hw' h
    refine ⟨(fenceStep_grow c k).trans hg, c2, ?_, hr⟩
    show _ ∈ runTree Arch.tso tid iv (fenceStep (setVw c w) k) (ret ())
    rw [e]; exact h2

/-- **`vwOld` never decreases along a run, under any `Arch`** (NT stores
included). Together with `runTree_vw`'s `Grow` (TSO, NT-free: also `vwNew`
grows and `vwOldNT` is fixed), this is what keeps `max vwNew vwOld` agreeing. -/
theorem runTree_vwOld_mono (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} (tree : EvTree σ) (c : Ctx)
    (s : σ) (c' : Ctx) (h : .ok (s, c') ∈ runTree A tid iv c tree) : c.views.vwOld ≤ c'.views.vwOld := by
  refine runTree_preserves A tid iv (fun c c' => c.views.vwOld ≤ c'.views.vwOld) (fun _ => Nat.le_refl _)
    (fun _ _ _ h1 h2 => Nat.le_trans h1 h2) ?_ ?_ ?_ ?_ ?_ tree c s c' h
  · intro c k xcl l noRet x hx
    obtain ⟨t, v, rfl, -⟩ := (mem_readSuccs A).mp hx
    exact Nat.le_refl _
  · intro c iv' k xcl l v tr extra xr c' hc'
    have key : ∀ (c0 : Ctx) k' t νf b, c0.views.vwOld = c.views.vwOld →
        c.views.vwOld ≤ (afterWrite A iv' c0 k' xcl l v t νf b xr).views.vwOld := by
      intro c0 k' t νf b hv
      simp only [afterWrite, hv]; split <;> simp only [View] at * <;> omega
    rcases (mem_writeSuccs_iff A tid iv').mp hc' with ⟨t, -, -, -, rfl⟩ | ⟨-, rfl⟩
    · exact key _ _ _ _ _ rfl
    · exact key _ _ _ _ _ rfl
  · intro c k; cases k <;> exact Nat.le_refl _
  · intro c l; exact Nat.le_refl _
  · intro c k noRet l; unfold rmwPost; split <;> exact Nat.le_refl _

/-! ## One instruction -/

section Instr

private theorem foldl_vwT {α : Type} (w : View) (f : Thread I → α → Thread I)
    (hf : ∀ t a, f (vwT w t) a = vwT w (f t a)) :
    ∀ (l : List α) (t : Thread I), l.foldl f (vwT w t) = vwT w (l.foldl f t)
  | [], _ => rfl
  | a :: l, t => by simp only [List.foldl_cons, hf]; exact foldl_vwT w f hf l (f t a)

/-- `finishInstr` copies the context's `vwNew`. -/
theorem finishInstr_setVw (t : Thread I) (d : InstrDeps I.RegId) (iv : InstrViews) (st : I.State) (c : Ctx)
    (w : View) : finishInstr t d iv st (setVw c w) = (finishInstr t d iv st c).map (vwT w) := by
  have h0 : ({ t with st, views := (setVw c w).views, prom := (setVw c w).prom } : Thread I) =
      vwT w { t with st, views := c.views, prom := c.prom } := rfl
  unfold finishInstr
  simp only
  rw [h0]
  repeat (rw [foldl_vwT w _ ?hf]; case hf => intro t a; first | rfl | (cases a; rfl))
  have hr : (setVw c w).rmwWrote = c.rmwWrote := rfl
  have hl : (setVw c w).loadViews = c.loadViews := rfl
  have hsv : (setVw c w).succView = c.succView := rfl
  simp only [hr, hl, hsv]
  by_cases h1 : (d.casLike && c.rmwWrote) = true <;> by_cases h2 : d.isBranch = true <;>
    by_cases h3 : (d.loadDefs.length == c.loadViews.length) = true <;>
    simp only [h1, h2, h3, ite_true, ite_false, Bool.false_eq_true, List.map_cons, List.map_nil] <;> rfl


theorem instrViews_vwT (w : View) (t : Thread I) (d : InstrDeps I.RegId) : instrViews (vwT w t) d = instrViews t d :=
  rfl

theorem finishInstr_vwT (w : View) (t : Thread I) (d : InstrDeps I.RegId) (iv : InstrViews) (st : I.State)
    (c : Ctx) : finishInstr (vwT w t) d iv st c = finishInstr t d iv st c := rfl

/-- One instruction only grows `vwOld`/`vwNew` and keeps `vwOldNT` (thread
level `Grow`). -/
def TGrow (t th : Thread I) : Prop :=
  t.views.vwOld ≤ th.views.vwOld ∧ t.views.vwNew ≤ th.views.vwNew ∧ th.views.vwOldNT = t.views.vwOldNT

/-- **One instruction, lockstep** (TSO, NT-free tree): every outcome of the
thread `t` is matched by an outcome of `vwT w t` (same `vwNew ⊔ vwOld`) with
the same memory and related threads. -/
theorem runOut_vw (tid : Nat) {t : Thread I} {mem : Memory} {tree : EvTree I.State} (hnt : tree.NoNT Arch.tso)
    {w : View} (hw : max t.views.vwNew t.views.vwOld = max w t.views.vwOld) {th : Thread I} {mem' : Memory}
    (h : RunOut Arch.tso tid t mem tree th mem') :
    ∃ th', RunOut Arch.tso tid (vwT w t) mem tree th' mem' ∧ VwNewEquiv th th' ∧ TGrow t th := by
  obtain ⟨st, c1, hr, hth, rfl⟩ := h
  obtain ⟨hg, c2, hr2, w2, rfl, hw2⟩ := runTree_vw tid _ tree hnt _ w st c1 hw hr
  have hk := (finishInstr_relKey hth).2
  have e1 : th.views.vwNew = c1.views.vwNew := by
    have h := congrArg (fun v : Views => v.vwNew) hk; exact h
  have e2 : th.views.vwOld = c1.views.vwOld := by
    have h := congrArg (fun v : Views => v.vwOld) hk; exact h
  have e3 : th.views.vwOldNT = c1.views.vwOldNT := by
    have h := congrArg (fun v : Views => v.vwOldNT) hk; exact h
  refine ⟨vwT w2 th, ⟨st, setVw c1 w2, hr2, ?_, rfl⟩, ⟨w2, rfl, by rw [e1, e2]; exact hw2⟩, ?_⟩
  · show vwT w2 th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st (setVw c1 w2)
    rw [finishInstr_setVw]
    exact List.mem_map.mpr ⟨th, hth, rfl⟩
  · rw [TGrow, e1, e2, e3]; exact hg

/-- **(S1)** The program makes no non-temporal store from a `P`-state on:
every tree of a `P`-state has no `.nt` store (`EvTree.NoNT Arch.tso`) and
only `P`-leaves. WeakCore's x64 lowering never emits `movnti`. Without it,
`mov [x], 1; sfence; movnti [y], 1 || mov r1, [y]; mov r2, [x]` separates
the source from the fence-free target (`r1 = 1 ∧ r2 = 0` forbidden with the
`sfence`, allowed without: the NT store's pre-view takes `vwNew`, not
`vwOld`). -/
def NTFreeInv (P : I.State → Prop) : Prop :=
  ∀ s tree, P s → I.exec s = some tree → tree.NoNT Arch.tso ∧ tree.All P

variable {P : I.State → Prop}

/-- **One promise-free thread step, lockstep** (TSO, under (S1)). -/
theorem threadStep_vw (hP : NTFreeInv P) {tid : Nat} {t : Thread I} (hp : P t.st) {w : View}
    (hw : max t.views.vwNew t.views.vwOld = max w t.views.vwOld) {mem : Memory} {q : Thread I × Memory}
    (h : ThreadStep Arch.tso tid (t, mem) q) :
    ∃ th', ThreadStep Arch.tso tid (vwT w t, mem) (th', q.2) ∧ VwNewEquiv q.1 th' ∧ P q.1.st ∧ TGrow t q.1 := by
  obtain ⟨outs, o, hs, ho, rfl⟩ := h
  cases hex : I.exec t.st with
  | none => simp [stepOne, hex] at hs
  | some tree =>
    obtain ⟨hnt, hall⟩ := hP _ _ hp hex
    have hr := (stepOne_ok_iff Arch.tso tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
    obtain ⟨th', hr', he, hg⟩ := runOut_vw tid hnt hw hr
    have hex' : I.exec (vwT w t).st = some tree := hex
    obtain ⟨outs', o', hs', ho', h1, h2⟩ := (stepOne_ok_iff Arch.tso tid hex').mpr hr'
    refine ⟨th', ⟨outs', o', hs', ho', by rw [h1, h2]⟩, he, stepOne_leaf Arch.tso hs ho fun tr htr => ?_, hg⟩
    rw [hex] at htr; cases htr; exact hall

/-- **`CertOk` transfers across `VwNewEquiv`** (TSO, under (S1)). -/
theorem certOk_vw (hP : NTFreeInv P) {tid : Nat} {t t' : Thread I} (hp : P t.st) (h : VwNewEquiv t t')
    {mem : Memory} (hc : CertOk Arch.tso tid t mem) : CertOk Arch.tso tid t' mem := by
  have aux : ∀ {p r : Thread I × Memory}, ThreadNP Arch.tso tid p r → ∀ t', VwNewEquiv p.1 t' → P p.1.st →
      ∃ r', ThreadNP Arch.tso tid (t', p.2) r' ∧ VwNewEquiv r.1 r'.1 := by
    intro p r h
    induction h with
    | refl p => intro t' h _; exact ⟨(t', p.2), .refl _, h⟩
    | step hs _ ih =>
      intro t' h hp
      obtain ⟨w, rfl, hw⟩ := h
      obtain ⟨th', hs', he, hp', -⟩ := threadStep_vw hP hp hw hs
      obtain ⟨r', hr', hrel⟩ := ih th' he hp'
      exact ⟨r', .step hs' hr', hrel⟩
  obtain ⟨t1, mem1, hnp, hprom⟩ := hc
  obtain ⟨r', hr', hrel⟩ := aux hnp t' h hp
  exact ⟨r'.1, r'.2, hr', hrel.prom.trans hprom⟩

end Instr

/-! ## The machine -/

section Machine

variable {P : I.State → Prop}

/-- **Configurations related by `VwNewEquiv` at thread `tid`**: the same
memory, the same threads but `tid`, where the two threads are
`VwNewEquiv`, and the thread's state satisfies `P` (the (S1) invariant). -/
def CfgVwEquiv (P : I.State → Prop) (tid : Nat) (c c' : Config I) : Prop :=
  c'.mem = c.mem ∧ (∀ i, i ≠ tid → c'.threads[i]? = c.threads[i]?) ∧
    ∃ t t', c.threads[tid]? = some t ∧ c'.threads[tid]? = some t' ∧ VwNewEquiv t t' ∧ P t.st

theorem CfgVwEquiv.symm {tid : Nat} {c c' : Config I} (h : CfgVwEquiv P tid c c') : CfgVwEquiv P tid c' c := by
  obtain ⟨hm, ho, t, t', ht, ht', he, hp⟩ := h
  exact ⟨hm.symm, fun i hi => (ho i hi).symm, t', t, ht', ht, he.symm, by rw [he.st]; exact hp⟩

theorem CfgVwEquiv.refl {tid : Nat} {c : Config I} {t : Thread I} (ht : c.threads[tid]? = some t) (hp : P t.st) :
    CfgVwEquiv P tid c c :=
  ⟨rfl, fun _ _ => rfl, t, t, ht, ht, .refl t, hp⟩

variable (hP : NTFreeInv P)
include hP

/-- **Instruction steps, lockstep**: every instruction step of any thread
of `c` is matched by one of `c'`, with the same memory and promise effect,
and the results are again related. -/
theorem instrSemInf_vw {tid j : Nat} {c c' c1 : Config I} (hc : CfgVwEquiv P tid c c')
    (h : InstrSemInf Arch.tso j c c1) : ∃ c1', InstrSemInf Arch.tso j c' c1' ∧ CfgVwEquiv P tid c1 c1' := by
  obtain ⟨hm, ho, t, t', ht, ht', he, hp⟩ := hc
  obtain ⟨tj, outs, o, htj, hs, hoo, hcert, rfl⟩ := h
  by_cases hj : j = tid
  · subst hj
    obtain rfl : tj = t := Option.some.inj (htj.symm.trans ht)
    obtain ⟨w, rfl, hw⟩ := he
    obtain ⟨th', ⟨outs', o', hs', ho', hq⟩, he', hp', -⟩ := threadStep_vw hP hp hw ⟨outs, o, hs, hoo, rfl⟩
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, hmem⟩ := hq
    refine ⟨c'.withThread j o'.thread o'.mem, ⟨vwT w tj, outs', o', ht', by rw [hm]; exact hs', ho',
      hmem ▸ certOk_vw hP hp' he' hcert, rfl⟩, hmem.symm, fun i hi => ?_,
      o.thread, o'.thread, withThread_get_self ht, withThread_get_self ht', he', hp'⟩
    rw [withThread_get_ne ht' hi, withThread_get_ne ht hi]; exact ho i hi
  · have htj' : c'.threads[j]? = some tj := (ho j hj).trans htj
    refine ⟨c'.withThread j o.thread o.mem, ⟨tj, outs, o, htj', by rw [hm]; exact hs, hoo, hcert, rfl⟩, rfl,
      fun i hi => ?_, t, t', ?_, ?_, he, hp⟩
    · by_cases hij : i = j
      · subst hij; rw [withThread_get_self htj', withThread_get_self htj]
      · rw [withThread_get_ne htj' hij, withThread_get_ne htj hij]; exact ho i hi
    · rw [withThread_get_ne htj (Ne.symm hj)]; exact ht
    · rw [withThread_get_ne htj' (Ne.symm hj)]; exact ht'

/-- **Promise steps, lockstep.** -/
theorem promSemInf_vw {tid j : Nat} {c c' c1 : Config I} (hc : CfgVwEquiv P tid c c')
    (h : PromSemInf Arch.tso j c c1) : ∃ c1', PromSemInf Arch.tso j c' c1' ∧ CfgVwEquiv P tid c1 c1' := by
  obtain ⟨hm, ho, t, t', ht, ht', he, hp⟩ := hc
  obtain ⟨tj, m, htj, hmt, hcert, rfl⟩ := h
  by_cases hj : j = tid
  · subst hj
    obtain rfl : tj = t := Option.some.inj (htj.symm.trans ht)
    obtain ⟨w, rfl, hw⟩ := he
    have he' : VwNewEquiv (promThread tj c.mem m) (promThread (vwT w tj) c.mem m) := ⟨w, rfl, hw⟩
    refine ⟨c'.withThread j (promThread (vwT w tj) c.mem m) (c.mem.append m).1,
      ⟨vwT w tj, m, ht', hmt, by rw [hm]; exact certOk_vw hP (t := promThread tj c.mem m) hp he' hcert, by rw [hm]⟩, rfl, fun i hi => ?_,
      _, _, withThread_get_self ht, withThread_get_self ht', he', hp⟩
    rw [withThread_get_ne ht' hi, withThread_get_ne ht hi]; exact ho i hi
  · have htj' : c'.threads[j]? = some tj := (ho j hj).trans htj
    refine ⟨c'.withThread j (promThread tj c.mem m) (c.mem.append m).1,
      ⟨tj, m, htj', hmt, by rw [hm]; exact hcert, by rw [hm]⟩, rfl, fun i hi => ?_, t, t', ?_, ?_, he, hp⟩
    · by_cases hij : i = j
      · subst hij; rw [withThread_get_self htj', withThread_get_self htj]
      · rw [withThread_get_ne htj' hij, withThread_get_ne htj hij]; exact ho i hi
    · rw [withThread_get_ne htj (Ne.symm hj)]; exact ht
    · rw [withThread_get_ne htj' (Ne.symm hj)]; exact ht'

/-- **Machine steps, lockstep.** -/
theorem stepSemInf_vw {tid j : Nat} {c c' c1 : Config I} (hc : CfgVwEquiv P tid c c')
    (h : StepSemInf Arch.tso j c c1) : ∃ c1', StepSemInf Arch.tso j c' c1' ∧ CfgVwEquiv P tid c1 c1' := by
  rcases h with h | h
  · obtain ⟨c1', h', hc'⟩ := instrSemInf_vw hP hc h; exact ⟨c1', .inl h', hc'⟩
  · obtain ⟨c1', h', hc'⟩ := promSemInf_vw hP hc h; exact ⟨c1', .inr h', hc'⟩

/-- **Reachability, lockstep**: every run of the fuel-free machine from `c`
is matched step for step from `c'`. With `CfgVwEquiv.symm`, both
directions. -/
theorem reachableSemInf_vw {tid : Nat} {c c' c2 : Config I} (h : ReachableSemInf Arch.tso c c2)
    (hc : CfgVwEquiv P tid c c') : ∃ c2', ReachableSemInf Arch.tso c' c2' ∧ CfgVwEquiv P tid c2 c2' := by
  induction h generalizing c' with
  | refl => exact ⟨c', .refl _, hc⟩
  | step j hs _ ih =>
    obtain ⟨c1', hs', hc1⟩ := stepSemInf_vw hP hc hs
    obtain ⟨c2', hr, hc2⟩ := ih hc1
    exact ⟨c2', .step j hs' hr, hc2⟩

end Machine

/-! ## `fence .st` is a stutter up to `~` -/

section Fence

variable {P : I.State → Prop}

/-- **(S2)** No outstanding non-temporal store: `vwOldNT ≤ vwNew ⊔ vwOld`
(e.g. `vwOldNT = 0`). Without it, `movnti [x], 1; sfence; mov [y], 1 ||
mov r1, [y]; mov r2, [x]` separates the source from the fence-free target
(`r1 = 1 ∧ r2 = 0` forbidden with the `sfence`, allowed without: `mov [y]`'s
release pre-view takes `vwOld`, not `vwOldNT`). -/
def NoOutNT (t : Thread I) : Prop := t.views.vwOldNT ≤ max t.views.vwNew t.views.vwOld

variable (hP : NTFreeInv P) {tid : Nat} {c c' : Config I} {t : Thread I} (ht : c.threads[tid]? = some t)
include hP ht

/-- **`fence .st` on TSO, exact form**: its outcomes are the no-event
outcomes (`finishInstr` at the thread's own context `ctx0`) with `vwNew`
raised by `vwOld ⊔ vwOldNT`, and certification is that of the no-event
outcome (under (S1) and (S2)). -/
theorem instrSemInf_fence_st_vw {s : I.State} (hex : I.exec t.st = some (.fence .st fun _ => .done s))
    (hs : P s) (hnt : NoOutNT t) :
    InstrSemInf Arch.tso tid c c' ↔ ∃ th0, th0 ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s
        (ctx0 tid t c.mem) ∧ CertOk Arch.tso tid th0 c.mem ∧
      c' = c.withThread tid (vwT (max t.views.vwNew (max t.views.vwOld t.views.vwOldNT)) th0) c.mem := by
  rw [instrSemInf_fence_st_iff Arch.tso tid ht hex]
  show (∃ th, th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s
      (setVw (ctx0 tid t c.mem) (max t.views.vwNew (max t.views.vwOld t.views.vwOldNT))) ∧ _ ∧ _) ↔ _
  rw [finishInstr_setVw]
  have key : ∀ th0 ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s (ctx0 tid t c.mem),
      P th0.st ∧ VwNewEquiv th0 (vwT (max t.views.vwNew (max t.views.vwOld t.views.vwOldNT)) th0) := by
    intro th0 h0
    have hk := (finishInstr_relKey h0).2
    have e1 : th0.views.vwNew = t.views.vwNew := by
      have h := congrArg (fun v : Views => v.vwNew) hk; exact h
    have e2 : th0.views.vwOld = t.views.vwOld := by
      have h := congrArg (fun v : Views => v.vwOld) hk; exact h
    refine ⟨(finishInstr_st h0) ▸ hs, _, rfl, ?_⟩
    rw [e1, e2]; unfold NoOutNT at hnt; simp only [View] at *; omega
  constructor
  · rintro ⟨th, hth, hc, rfl⟩
    obtain ⟨th0, h0, rfl⟩ := List.mem_map.mp hth
    exact ⟨th0, h0, certOk_vw hP (t := vwT (max t.views.vwNew (max t.views.vwOld t.views.vwOldNT)) th0) (key th0 h0).1 (key th0 h0).2.symm hc, rfl⟩
  · rintro ⟨th0, h0, hc, rfl⟩
    exact ⟨_, List.mem_map.mpr ⟨th0, h0, rfl⟩, certOk_vw hP (key th0 h0).1 (key th0 h0).2 hc, rfl⟩

/-- **`fence .st` on TSO is a stutter up to `~`**: a `fence .st` step from
`c` yields a configuration `CfgVwEquiv` (at `tid`) to the installed no-event
outcome, which is certifiable (under (S1) and (S2)). Conversely every
certifiable no-event outcome arises so (`instrSemInf_fence_st_vw`). -/
theorem instrSemInf_fence_st_stutter_vw {s : I.State} (hex : I.exec t.st = some (.fence .st fun _ => .done s))
    (hs : P s) (hnt : NoOutNT t) (h : InstrSemInf Arch.tso tid c c') :
    ∃ th0, th0 ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s (ctx0 tid t c.mem) ∧
      CertOk Arch.tso tid th0 c.mem ∧ CfgVwEquiv P tid c' (c.withThread tid th0 c.mem) := by
  obtain ⟨th0, h0, hc, rfl⟩ := (instrSemInf_fence_st_vw hP ht hex hs hnt).mp h
  have hk := (finishInstr_relKey h0).2
  have e1 : th0.views.vwNew = t.views.vwNew := by
    have h := congrArg (fun v : Views => v.vwNew) hk; exact h
  have e2 : th0.views.vwOld = t.views.vwOld := by
    have h := congrArg (fun v : Views => v.vwOld) hk; exact h
  refine ⟨th0, h0, hc, rfl, fun i hi => ?_, _, th0, withThread_get_self ht, withThread_get_self ht,
    ⟨_, rfl, ?_⟩, (finishInstr_st h0) ▸ hs⟩
  · rw [withThread_get_ne ht hi, withThread_get_ne ht hi]
  · show max (max t.views.vwNew (max t.views.vwOld t.views.vwOldNT)) th0.views.vwOld = max th0.views.vwNew th0.views.vwOld
    rw [e1, e2]; unfold NoOutNT at hnt; simp only [View] at *; omega

end Fence

/-! ## (S1) and (S2) along the machine -/

section Inv

variable {P : I.State → Prop}

/-- Every thread is in a `P`-state with no outstanding NT store. -/
def CfgNTFree (P : I.State → Prop) (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → P t.st ∧ NoOutNT t

theorem cfgNoOutNT_init {states : List I.State} (initMem : List (Loc × Val)) (h : ∀ s ∈ states, P s) :
    CfgNTFree P (Config.init states initMem : Config I) := by
  intro i t ht
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
  obtain ⟨st, hst, rfl⟩ := ht
  exact ⟨h st (List.mem_of_getElem? hst), Nat.zero_le _⟩

variable (hP : NTFreeInv P)
include hP

theorem stepSemInf_cfgNTFree {j : Nat} {c c' : Config I} (hc : CfgNTFree P c) (h : StepSemInf Arch.tso j c c') :
    CfgNTFree P c' := by
  rcases h with ⟨tj, outs, o, htj, hs, ho, -, rfl⟩ | ⟨tj, m, htj, -, -, rfl⟩
  · intro i t' h
    rw [Config.withThread_get? c _ _ (lt_size_of_get? htj)] at h
    split at h
    · obtain rfl := Option.some.inj h
      obtain ⟨hp, hn⟩ := hc j tj htj
      obtain ⟨-, -, -, hp', g1, g2, g3⟩ := threadStep_vw hP hp (w := tj.views.vwNew) rfl ⟨outs, o, hs, ho, rfl⟩
      refine ⟨hp', ?_⟩
      unfold NoOutNT at *; simp only [View] at *; omega
    · exact hc i t' h
  · intro i t' h
    rw [Config.withThread_get? c _ _ (lt_size_of_get? htj)] at h
    split at h
    · obtain rfl := Option.some.inj h; exact hc j tj htj
    · exact hc i t' h

/-- **(S1) and (S2) are invariants of the fuel-free machine** for an NT-free
program. -/
theorem cfgNoOutNT_reachable {c c' : Config I} (h : ReachableSemInf Arch.tso c c') (hc : CfgNTFree P c) :
    CfgNTFree P c' := by
  induction h with
  | refl => exact hc
  | step j hs _ ih => exact ih (stepSemInf_cfgNTFree hP hc hs)

end Inv

section Witness

/-! Concrete contexts for (S1): after `mov [x], 1` at timestamp `2`
(`vwOld = 2`) the source has passed `sfence` (`vwNew = 2`), the target has
not (`vwNew = 0`). The two are `CtxVw`. A release store's pre-view is the
same (`2`); an NT store's is not (`2` against `0`), so the target's
`movnti [y]` may take a timestamp below `x`'s. -/

private def wSrc : Ctx := { views := { vwNew := 2, vwOld := 2 }, prom := [], mem := { init := [], msgs := #[] } }
private def wIv : InstrViews := { addrR := 0, addrW := 0, dataR := 0, dataW := 0, condW := 0 }

example : CtxVw wSrc (setVw wSrc 0) := ⟨0, rfl, rfl⟩
example : writePre wIv wSrc .rel 0 = 2 ∧ writePre wIv (setVw wSrc 0) .rel 0 = 2 := by decide
example : writePre wIv wSrc .nt 0 = 2 ∧ writePre wIv (setVw wSrc 0) .nt 0 = 0 := by decide

end Witness

end Kraken.Promising.Lower.Tso
