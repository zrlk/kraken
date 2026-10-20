/-
Machine facts about `EvTree.RelFulfilsLive` (T1c (4)): the form of
`Thread.RelFulfils` that `NPSafe`'s prepay conjunct asks for, a release
fulfilment after which no outstanding promise of the thread is dead
(`Ctx.NoDead`).

- `Ctx.NoDead.restrict`: `NoDead` survives restriction to a memory prefix.
- `EvTree.RelFulfilsLive.restrict`, `Thread.RelFulfilsLive.restrict`: the
  `Live` copies of `EvTree.RelFulfils.restrict`/`Thread.RelFulfils.restrict`
  (`ReleasePrefix.lean`), (S1′)'s replay on a memory prefix.
- `Ctx.NoDead.back`: `NoDead` propagates backwards along a context run
  (`Ctx.DOrd`, `Ctx.WOrd`): a promise fulfilled later lies above the views
  then, which only grew.
- `Ctx.noDead_of_finish`: a thread outcome with no dead promise
  (`Thread.hasDeadPromise = false`) has a `NoDead` pre-`finishInstr` context.
-/
import Kraken.Promising.LiveWfProm

namespace Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

theorem Ctx.NoDead.restrict {M : Memory} {c : Ctx} (hM : M.Prefix c.mem) (h : c.NoDead) :
    (c.restrict M).NoDead := by
  intro p hp w hw
  obtain ⟨hp, hle⟩ := List.mem_filter.mp hp
  have hle : p ≤ M.last := by simpa using hle
  have hw' : c.mem.get? p = some w := by rw [hM.get? hle]; exact hw
  exact h p hp w hw'

/-- **`NoDead` propagates backwards along a run**: if `c'` follows `c`
(`Ctx.DOrd`, `Ctx.WOrd`), a promise of `c` is either still outstanding at
`c'` (above `c'`'s views, which bound `c`'s), or was fulfilled in between
(above `c`'s `vCAP`, `coh` and `vwNew`). -/
theorem Ctx.NoDead.back {c c' : Ctx} (hd : c.DOrd c') (hw : c.WOrd c') (h : c'.NoDead) : c.NoDead := by
  intro p hp w hgw
  by_cases hp' : p ∈ c'.prom
  · have hgw' : c'.mem.get? p = some w := by
      rw [hd.mem.get? (c.mem.last_le_of_get?_eq_some hgw)]; exact hgw
    have h1 := h p hp' w hgw'
    have h2 := hd.coh w.loc
    have h3 := hd.vCAP
    have h4 := hw.vwNew
    omega_t
  · obtain ⟨h1, h2⟩ := hd.prom p hp hp'
    have h3 := h2 w hgw
    have h4 := hw.prom p hp hp'
    omega_t

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A live release fulfilment replays on a memory prefix**: the `Live`
copy of `EvTree.RelFulfils.restrict` (same proof; `Ctx.NoDead.restrict` at
the fulfilling write). -/
theorem EvTree.RelFulfilsLive.restrict {M M' : Memory} (hM : M.Prefix M') {ts : Time} (hts : ts ≤ M.last)
    {σ : Type} (tree : EvTree σ) :
    ∀ c : Ctx, c.views.FwdOk → c.mem = M' → EvTree.RelFulfilsLive A tid iv ts c tree →
      c.views.vwOldNT ≤ M.last → tree.NoNT A →
      EvTree.RelFulfilsLive A tid iv ts (c.restrict M) tree := by
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
    have hlt := EvTree.RelFulfils.relPre_lt A tid iv _ _ hs.fwd (EvTree.RelFulfilsLive.toRelFulfils _ _ h)
    have hle : x.1 ≤ M.last := by
      have := readSuccs_le A iv hf hx; simp only [Views.relPreNT] at this; omega_t
    exact ⟨_, readSuccs_restrict A iv (hm ▸ hM) hx hle,
      ih x.2.1 x.2.2 hs.fwd ((readSuccs_mp A iv hx).1.trans hm) h hnt' (hno x.2.1)⟩
  | store k xcl l v ret ih =>
    intro c hf hm h hnt hno
    rcases h with ⟨c', hc', ⟨h, hnd⟩ | h⟩ | h
    · have hlt := writeSuccs_rel_relPre A tid _ hc' h.1 h.2.1 h.2.2
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
      have hlt := EvTree.RelFulfils.relPre_lt A tid iv _ _ hs.fwd (EvTree.RelFulfilsLive.toRelFulfils _ _ h)
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
    show EvTree.RelFulfilsLive A tid iv ts (fenceStep (c.restrict M) k) (ret ())
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
      have hlt := EvTree.RelFulfils.relPre_lt A tid iv _ _ h3.fwd (EvTree.RelFulfilsLive.toRelFulfils _ _ h)
      refine ⟨_, hread (Nat.lt_of_le_of_lt h3.relPre hlt), Or.inl ?_⟩
      show EvTree.RelFulfilsLive A tid iv ts (if A.rmwFence then fenceStep (x.2.2.restrict M) .sy
        else x.2.2.restrict M) (ret x.2.1)
      rw [fenceOpt_restrict]
      have hm3 : (if A.rmwFence then fenceStep x.2.2 .sy else x.2.2).mem = M' := by
        split <;> simp only [fenceStep_mem, hm2]
      exact ih x.2.1 _ h3.fwd hm3 h ((fenceOpt_vwOldNT _ _ _).symm ▸ hnt2) (hno.2 x.2.1)
    · have hlt := writeSuccs_rel_relPre A tid _ hc' h.1 h.2.1 h.2.2
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
      have hlt := EvTree.RelFulfils.relPre_lt A tid iv _ _ h5.fwd (EvTree.RelFulfilsLive.toRelFulfils _ _ h)
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

theorem Thread.RelFulfilsLive.restrict {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {M M' : Memory}
    (hM : M.Prefix M') (hts : ts ≤ M.last) (hf : t.views.FwdOk) (h : t.RelFulfilsLive A tid ts M')
    (hnt : t.views.vwOldNT ≤ M.last) (hnx : t.NextNoNT A) :
    (t.restrict M).RelFulfilsLive A tid ts M := by
  obtain ⟨tree, hex, h⟩ := h
  exact ⟨tree, hex, EvTree.RelFulfilsLive.restrict A tid _ hM hts tree _ hf rfl h hnt (hnx tree hex)⟩

/-- A thread produced by `finishInstr` from the context `c` with no dead
promise against `c.mem` makes `c` itself `NoDead` (`finishInstr` keeps the
promises, `coh` and `vwNew`, and only raises `vCAP`). -/
theorem Ctx.noDead_of_finish {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {th : Thread I} (h : th ∈ finishInstr t d iv st c) (hd : th.hasDeadPromise c.mem = false) : c.NoDead := by
  obtain ⟨hp, hv⟩ := finishInstr_relKey h
  have hcoh : th.views.coh = c.views.coh := by have := congrArg Views.coh hv; exact this
  have hnew : th.views.vwNew = c.views.vwNew := by have := congrArg Views.vwNew hv; exact this
  have hcap := finishInstr_vCAP h
  intro p hpc w hw
  unfold Thread.hasDeadPromise at hd
  rw [List.any_eq_false] at hd
  have := hd p (hp ▸ hpc)
  rw [hw] at this
  simp only [decide_eq_true_eq, Nat.not_le] at this
  have hg : th.views.getCoh w.loc = c.views.getCoh w.loc := by simp only [Views.getCoh, hcoh]
  rw [hg, hnew] at this
  omega_t

end Kraken.Promising
