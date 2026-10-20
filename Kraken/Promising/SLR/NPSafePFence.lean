/-
**Prototype.** The fence-aware prepay guard
against `GuardOK`.

`EvTree.RelFulfilsLiveF` is `EvTree.RelFulfilsLive` (the prepay guard of
`NPSafe`) with the fence-aware write case of `EvTree.RelFulfilsF`
(`Promising/FenceRelease.lean`): the fulfilling write is a release *or* is
issued from `FenceRel` views; no promise is left dead (`Ctx.NoDead`).

- `EvTree.RelFulfilsLiveF.toF`: it is a `RelFulfilsF` (hence release-bounded,
  `EvTree.RelFulfilsF.relPre_lt`).
- `EvTree.RelFulfilsLive.toLiveF`: the current guard is below it.
- `EvTree.RelFulfilsLiveF.restrict`: the copy of
  `EvTree.RelFulfilsLive.restrict` (`Promising/RelFulfilsLive.lean`), same
  proof; at a fulfilling write the bound comes from
  `writeSuccs_fenceRel_relPre` in the fence case, and `FenceRel` survives
  `Ctx.restrict`, which keeps the views.
- `guardOK_GF`: so `GF` satisfies `GuardOK`, and the generic chain gives
  Theorem 1′ for `NPSafeP GF K`.

Nothing imports this file.
-/
import Kraken.Promising.FenceRelease
import Kraken.Promising.SLR.NPSafeP

namespace Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **Fence-aware live release fulfilment**: `EvTree.RelFulfilsLive` whose
fulfilling write is a release or runs under `FenceRel`. -/
def EvTree.RelFulfilsLiveF (ts : Time) {σ : Type} : Ctx → EvTree σ → Prop
  | _, .done _ => False
  | _, .fault _ => False
  | c, .choose _ k => ∃ i, RelFulfilsLiveF ts c (k i)
  | c, .load k xcl l ret => ∃ x ∈ readSuccs A iv c k xcl l, RelFulfilsLiveF ts x.2.2 (ret x.2.1)
  | c, .store k xcl l v ret =>
    (∃ c' ∈ writeSuccs A tid (iv.forStore c.stores) c k xcl l v
        (if xcl then c.views.xclb.map (·.1) else none) 0 (if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0),
      (((A.storeKind k = .rel ∨ c.views.FenceRel) ∧ ts ∈ c.prom ∧ ts ∉ c'.prom) ∧ c'.NoDead) ∨
        RelFulfilsLiveF ts c' (ret true)) ∨
    RelFulfilsLiveF ts
      { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } (ret false)
  | c, .fence k ret => RelFulfilsLiveF ts (fenceStep c k) (ret ())
  | c, .rmw k noRet l op ret =>
    ∃ x ∈ readSuccs A iv (if A.rmwFence then fenceStep c .sy else c)
        (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      RelFulfilsLiveF ts (if A.rmwFence then fenceStep x.2.2 .sy else x.2.2) (ret x.2.1) ∨
      ∃ new, op x.2.1 = some new ∧
        ∃ c' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
          (((A.storeKind (A.rmwKind k).storeKind = .rel ∨ x.2.2.views.FenceRel) ∧ ts ∈ x.2.2.prom ∧ ts ∉ c'.prom) ∧
              c'.NoDead) ∨
          RelFulfilsLiveF ts
            (if A.rmwFence then fenceStep (rmwPost A k noRet l c') .sy else rmwPost A k noRet l c') (ret x.2.1)

/-- A fence-aware live fulfilment is a fence-aware fulfilment. -/
theorem EvTree.RelFulfilsLiveF.toF {ts : Time} {σ : Type} :
    ∀ (tree : EvTree σ) (c : Ctx), tree.RelFulfilsLiveF A tid iv ts c → tree.RelFulfilsF A tid iv ts c
  | .done _, _, h => h
  | .fault _, _, h => h
  | .choose _ k, c, ⟨i, h⟩ => ⟨i, toF (k i) c h⟩
  | .load _ _ _ ret, _, ⟨x, hx, h⟩ => ⟨x, hx, toF (ret x.2.1) _ h⟩
  | .store _ _ _ _ ret, _, h => by
    rcases h with ⟨c', hc', ⟨h, -⟩ | h⟩ | h
    · exact .inl ⟨c', hc', .inl h⟩
    · exact .inl ⟨c', hc', .inr (toF (ret true) _ h)⟩
    · exact .inr (toF (ret false) _ h)
  | .fence _ ret, _, h => toF (ret ()) _ h
  | .rmw _ _ _ _ ret, _, ⟨x, hx, h⟩ => by
    rcases h with h | ⟨new, hop, c', hc', ⟨h, -⟩ | h⟩
    · exact ⟨x, hx, .inl (toF (ret x.2.1) _ h)⟩
    · exact ⟨x, hx, .inr ⟨new, hop, c', hc', .inl h⟩⟩
    · exact ⟨x, hx, .inr ⟨new, hop, c', hc', .inr (toF (ret x.2.1) _ h)⟩⟩

/-- The current guard is below the fence-aware one. -/
theorem EvTree.RelFulfilsLive.toLiveF {ts : Time} {σ : Type} :
    ∀ (tree : EvTree σ) (c : Ctx), tree.RelFulfilsLive A tid iv ts c → tree.RelFulfilsLiveF A tid iv ts c
  | .done _, _, h => h
  | .fault _, _, h => h
  | .choose _ k, c, ⟨i, h⟩ => ⟨i, toLiveF (k i) c h⟩
  | .load _ _ _ ret, _, ⟨x, hx, h⟩ => ⟨x, hx, toLiveF (ret x.2.1) _ h⟩
  | .store _ _ _ _ ret, _, h => by
    rcases h with ⟨c', hc', ⟨⟨hk, h⟩, hd⟩ | h⟩ | h
    · exact .inl ⟨c', hc', .inl ⟨⟨.inl hk, h⟩, hd⟩⟩
    · exact .inl ⟨c', hc', .inr (toLiveF (ret true) _ h)⟩
    · exact .inr (toLiveF (ret false) _ h)
  | .fence _ ret, _, h => toLiveF (ret ()) _ h
  | .rmw _ _ _ _ ret, _, ⟨x, hx, h⟩ => by
    rcases h with h | ⟨new, hop, c', hc', ⟨⟨hk, h⟩, hd⟩ | h⟩
    · exact ⟨x, hx, .inl (toLiveF (ret x.2.1) _ h)⟩
    · exact ⟨x, hx, .inr ⟨new, hop, c', hc', .inl ⟨⟨.inl hk, h⟩, hd⟩⟩⟩
    · exact ⟨x, hx, .inr ⟨new, hop, c', hc', .inr (toLiveF (ret x.2.1) _ h)⟩⟩

/-- A store whose kind is a release or whose views are `FenceRel`,
fulfilling `ts`, has `relPre < ts`. -/
theorem writeSuccs_relF_relPre {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr)
    (hk : A.storeKind k = .rel ∨ c.views.FenceRel) {ts : Time} (hin : ts ∈ c.prom) (hout : ts ∉ c'.prom) :
    c.views.relPre < ts :=
  hk.elim (fun hk => writeSuccs_rel_relPre A tid iv h hk hin hout)
    (fun hk => writeSuccs_fenceRel_relPre A tid iv h hk hin hout)

/-- **A fence-aware live fulfilment replays on a memory prefix**: the copy
of `EvTree.RelFulfilsLive.restrict`. -/
theorem EvTree.RelFulfilsLiveF.restrict {M M' : Memory} (hM : M.Prefix M') {ts : Time} (hts : ts ≤ M.last)
    {σ : Type} (tree : EvTree σ) :
    ∀ c : Ctx, c.views.FwdOk → c.mem = M' → EvTree.RelFulfilsLiveF A tid iv ts c tree →
      c.views.vwOldNT ≤ M.last → tree.NoNT A →
      EvTree.RelFulfilsLiveF A tid iv ts (c.restrict M) tree := by
  have hML := hM.last_le
  induction tree with
  | done s => intro c _ _ h; exact h.elim
  | fault m => intro c _ _ h; exact h.elim
  | choose n k ih =>
    intro c hf hm ⟨i, h⟩ hnt hno
    exact ⟨i, ih i c hf hm h hnt (hno i)⟩
  | load k xcl l ret ih =>
    intro c hf hm ⟨x, hx, h⟩ hnt hno
    have hs := readSuccs_silent A iv hf hx
    have hnt' : x.2.2.views.vwOldNT ≤ M.last := (readSuccs_vwOldNT A iv hx) ▸ hnt
    have hlt := EvTree.RelFulfilsF.relPre_lt A tid iv _ _ hs.fwd (EvTree.RelFulfilsLiveF.toF A tid iv _ _ h)
    have hle : x.1 ≤ M.last := by
      have := readSuccs_le A iv hf hx; simp only [Views.relPreNT] at this; omega_t
    exact ⟨_, readSuccs_restrict A iv (hm ▸ hM) hx hle,
      ih x.2.1 x.2.2 hs.fwd ((readSuccs_mp A iv hx).1.trans hm) h hnt' (hno x.2.1)⟩
  | store k xcl l v ret ih =>
    intro c hf hm h hnt hno
    rcases h with ⟨c', hc', ⟨h, hnd⟩ | h⟩ | h
    · have hlt := writeSuccs_relF_relPre A tid _ hc' h.1 h.2.1 h.2.2
      have hvw := writeSuccs_fulfil A tid _ hc' h.2.1 h.2.2
      have hnt' := writeSuccs_vwOldNT A tid _ hc' hno.1
      have hs := writeSuccs_silent A tid _ hf hc'
      have hle : c'.views.vwAll ≤ M.last := by simp only [Views.relPre, Views.vwAll] at hlt ⊢; omega_t
      have hm' : c'.mem = M' := by
        rcases hs.mem with h0 | h0
        · exact h0.trans hm
        · exfalso; rw [hm] at h0; omega_t
      refine Or.inl ⟨c'.restrict M, writeSuccs_restrict A tid _ (hm ▸ hM) hc' hle, Or.inl ⟨⟨h.1, ?_, ?_⟩, ?_⟩⟩
      · exact List.mem_filter.mpr ⟨h.2.1, by simpa using hts⟩
      · exact fun hc => h.2.2 (List.mem_filter.mp hc).1
      · exact Ctx.NoDead.restrict (hm' ▸ hM) hnd
    · have hs := writeSuccs_silent A tid _ hf hc'
      have hlt := EvTree.RelFulfilsF.relPre_lt A tid iv _ _ hs.fwd (EvTree.RelFulfilsLiveF.toF A tid iv _ _ h)
      have hnt' := writeSuccs_vwOldNT A tid _ hc' hno.1
      have hle : c'.views.vwAll ≤ M.last := by simp only [Views.relPre, Views.vwAll] at hlt ⊢; omega_t
      have hm' : c'.mem = M' := by
        rcases hs.mem with h0 | h0
        · exact h0.trans hm
        · exfalso; rw [hm] at h0; omega_t
      exact Or.inl ⟨c'.restrict M, writeSuccs_restrict A tid _ (hm ▸ hM) hc' hle,
        Or.inr (ih true c' hs.fwd hm' h (hnt'.symm ▸ hnt) (hno.2 true))⟩
    · have hs : Ctx.Silent c
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl, by simp⟩
      exact Or.inr (ih false _ hs.fwd hm h hnt (hno.2 false))
  | fence k ret ih =>
    intro c hf hm h hnt hno
    show EvTree.RelFulfilsLiveF A tid iv ts (fenceStep (c.restrict M) k) (ret ())
    rw [fenceStep_restrict]
    exact ih () _ (Ctx.Silent.fenceStep hf k).fwd ((fenceStep_mem c k).trans hm) h
      ((fenceStep_fields c k).2.2.2.2.2.2 ▸ hnt) hno
  | rmw k noRet l op ret ih =>
    intro c hf hm ⟨x, hx, h⟩ hnt hno
    have h1 := Ctx.Silent.fenceOpt hf A.rmwFence .sy
    have hm1 : (if A.rmwFence then fenceStep c .sy else c).mem = M' := by
      split <;> simp only [fenceStep_mem, hm]
    have h2 := readSuccs_silent A iv h1.fwd hx
    have hm2 : x.2.2.mem = M' := (readSuccs_mp A iv hx).1.trans hm1
    have hnt2 : x.2.2.views.vwOldNT ≤ M.last := by
      rw [readSuccs_vwOldNT A iv hx, fenceOpt_vwOldNT]; exact hnt
    have hread : x.2.2.views.relPre < ts →
        (x.1, x.2.1, x.2.2.restrict M) ∈ readSuccs A iv (if A.rmwFence then fenceStep (c.restrict M) .sy
          else c.restrict M) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet := by
      intro hlt
      rw [fenceOpt_restrict]
      refine readSuccs_restrict A iv (hm1 ▸ hM) hx ?_
      have := readSuccs_le A iv h1.fwd hx; simp only [Views.relPreNT] at this; omega_t
    rcases h with h | ⟨new, hop, c', hc', ⟨h, hnd⟩ | h⟩
    · have h3 := Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy
      have hlt := EvTree.RelFulfilsF.relPre_lt A tid iv _ _ h3.fwd (EvTree.RelFulfilsLiveF.toF A tid iv _ _ h)
      refine ⟨_, hread (Nat.lt_of_le_of_lt h3.relPre hlt), Or.inl ?_⟩
      show EvTree.RelFulfilsLiveF A tid iv ts (if A.rmwFence then fenceStep (x.2.2.restrict M) .sy
        else x.2.2.restrict M) (ret x.2.1)
      rw [fenceOpt_restrict]
      have hm3 : (if A.rmwFence then fenceStep x.2.2 .sy else x.2.2).mem = M' := by
        split <;> simp only [fenceStep_mem, hm2]
      exact ih x.2.1 _ h3.fwd hm3 h ((fenceOpt_vwOldNT _ _ _).symm ▸ hnt2) (hno.2 x.2.1)
    · have hlt := writeSuccs_relF_relPre A tid _ hc' h.1 h.2.1 h.2.2
      have hvw := writeSuccs_fulfil A tid _ hc' h.2.1 h.2.2
      have hnt' := writeSuccs_vwOldNT A tid _ hc' hno.1
      have h3 := writeSuccs_silent A tid _ h2.fwd hc'
      have hle : c'.views.vwAll ≤ M.last := by simp only [Views.relPre, Views.vwAll] at hlt ⊢; omega_t
      have hm3 : c'.mem = M' := by
        rcases h3.mem with h0 | h0
        · exact h0.trans hm2
        · exfalso; rw [hm2] at h0; omega_t
      refine ⟨_, hread hlt, Or.inr ⟨new, hop, c'.restrict M,
        writeSuccs_restrict A tid _ (hm2 ▸ hM) hc' hle, Or.inl ⟨⟨h.1, ?_, ?_⟩, ?_⟩⟩⟩
      · exact List.mem_filter.mpr ⟨h.2.1, by simpa using hts⟩
      · exact fun hc => h.2.2 (List.mem_filter.mp hc).1
      · exact Ctx.NoDead.restrict (hm3 ▸ hM) hnd
    · have h3 := writeSuccs_silent A tid _ h2.fwd hc'
      have h4 := h3.trans (Ctx.Silent.rmwPost h3.fwd A k noRet l)
      have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
      have hlt := EvTree.RelFulfilsF.relPre_lt A tid iv _ _ h5.fwd (EvTree.RelFulfilsLiveF.toF A tid iv _ _ h)
      have hnt' := writeSuccs_vwOldNT A tid _ hc' hno.1
      have hvw3 : c'.views.vwAll ≤ M.last := by
        have := ((Ctx.Silent.rmwPost h3.fwd A k noRet l).trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)).relPre
        simp only [Views.relPre, Views.vwAll] at this hlt ⊢; omega_t
      have hm3 : c'.mem = M' := by
        rcases h3.mem with h0 | h0
        · exact h0.trans hm2
        · exfalso; rw [hm2] at h0; omega_t
      refine ⟨_, hread (Nat.lt_of_le_of_lt h3.relPre (Nat.lt_of_le_of_lt
        ((Ctx.Silent.rmwPost h3.fwd A k noRet l).trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)).relPre hlt)),
        Or.inr ⟨new, hop, c'.restrict M, writeSuccs_restrict A tid _ (hm2 ▸ hM) hc' hvw3, Or.inr ?_⟩⟩
      rw [rmwPost_restrict, fenceOpt_restrict]
      have hm5 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c') .sy else rmwPost A k noRet l c').mem = M' := by
        split <;> simp only [fenceStep_mem, rmwPost_mem, hm3]
      have hnt5 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c') .sy else rmwPost A k noRet l c').views.vwOldNT
          ≤ M.last := by
        rw [fenceOpt_vwOldNT, rmwPost_vwOldNT, hnt']; exact hnt2
      exact ih x.2.1 _ h5.fwd hm5 h hnt5 (hno.2 x.2.1)

end Rules

/-- The next instruction of `t` can fulfil `ts` with a release or fenced
store, leaving no promise dead. -/
def Thread.RelFulfilsLiveF (A : Arch) (tid : Nat) (ts : Time) (t : Thread I) (mem : Memory) : Prop :=
  ∃ tree, I.exec t.st = some tree ∧
    EvTree.RelFulfilsLiveF A tid (instrViews t (I.deps t.st)) ts
      { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } tree

theorem Thread.RelFulfilsLiveF.relPre_lt {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory}
    (h : t.RelFulfilsLiveF A tid ts mem) (hf : t.views.FwdOk) : t.views.relPre < ts := by
  obtain ⟨tree, -, h⟩ := h
  exact EvTree.RelFulfilsF.relPre_lt A tid _ tree _ hf (EvTree.RelFulfilsLiveF.toF A tid _ tree _ h)

theorem Thread.RelFulfilsLiveF.restrict {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {M M' : Memory}
    (hM : M.Prefix M') (hts : ts ≤ M.last) (hf : t.views.FwdOk) (h : t.RelFulfilsLiveF A tid ts M')
    (hnt : t.views.vwOldNT ≤ M.last) (hnx : t.NextNoNT A) :
    (t.restrict M).RelFulfilsLiveF A tid ts M := by
  obtain ⟨tree, hex, h⟩ := h
  exact ⟨tree, hex, EvTree.RelFulfilsLiveF.restrict A tid _ hM hts tree _ hf rfl h hnt (hnx tree hex)⟩

theorem Thread.RelFulfilsLive.toLiveF {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory}
    (h : t.RelFulfilsLive A tid ts mem) : t.RelFulfilsLiveF A tid ts mem := by
  obtain ⟨tree, hex, h⟩ := h
  exact ⟨tree, hex, EvTree.RelFulfilsLive.toLiveF A tid _ tree _ h⟩

/-- The fence-aware prepay guard. -/
abbrev GF : PrepayGuard I := fun A tid ts t mem => t.RelFulfilsLiveF A tid ts mem

/-- **The fence-aware guard satisfies `GuardOK`.** -/
theorem guardOK_GF : GuardOK (I := I) GF where
  relPre_lt h hf := Thread.RelFulfilsLiveF.relPre_lt h hf
  restrict hM hts hf h hnt hnx := Thread.RelFulfilsLiveF.restrict hM hts hf h hnt hnx

/-- `G₀ ⊆ GF`: `NPSafeP GF K` asks for *more* prepayments than `NPSafe`, so
existing `NPSafe` proofs do not transfer (`NPSafeP.mono` goes the other
way); each rule's prepay obligation must cover the new promises. -/
theorem G₀_le_GF {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory} (h : G₀ A tid ts t mem) :
    GF A tid ts t mem :=
  Thread.RelFulfilsLive.toLiveF h

/-- **The impure-only fence-aware guard** for a program with release
predicates `rel` (fixed: `Ghost.Le` keeps `rel`): the current guard, or a
fence-aware live fulfilment of a promise whose value is impure. A program
whose plain stores write pure values then owes no new prepayments except at
fence-released impure stores, i.e. exactly the new `dmb ish; str` publishers;
pure fence-released promises keep going to case (d2). -/
def GHyb (rel : Loc → SLR.Pred) : PrepayGuard I := fun A tid ts t mem =>
  t.RelFulfilsLive A tid ts mem ∨
    (t.RelFulfilsLiveF A tid ts mem ∧ ∃ w, mem.get? ts = some w ∧ ¬ SLR.Pred.Pure (rel w.loc) w.val)

theorem guardOK_GHyb (rel : Loc → SLR.Pred) : GuardOK (I := I) (GHyb rel) where
  relPre_lt h hf := h.elim (fun h => h.toRelFulfils.relPre_lt hf) (fun h => Thread.RelFulfilsLiveF.relPre_lt h.1 hf)
  restrict hM hts hf h hnt hnx := h.imp (fun h => Thread.RelFulfilsLive.restrict hM hts hf h hnt hnx)
    (fun ⟨h, w, hw, hp⟩ => ⟨Thread.RelFulfilsLiveF.restrict hM hts hf h hnt hnx, w, by rw [← hM.get? hts]; exact hw, hp⟩)

theorem G₀_le_GHyb (rel : Loc → SLR.Pred) {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory}
    (h : G₀ A tid ts t mem) : GHyb rel A tid ts t mem :=
  .inl h

#print axioms guardOK_GF
#print axioms guardOK_GHyb

end Kraken.Promising
