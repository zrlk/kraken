/-
Whole-thread environment (`EnvG`), phase 2 (the multi-access link prototype): **the
instruction-local context fields do not matter to the next access**.
ISA-neutral.

`EnvG` runs every access on a context whose instruction-local fields
(`loadViews`, `succView`, `stores`, `rmwWrote`) are at their defaults; the
phase-1 link relates it to the actual context by
`CtxLe`, whose `CtxRel` pins those fields (`loadViews` by `Rel2`, equal
`stores`/`rmwWrote`). That is exact for the first access of an instruction
only. This file shows that the actual rules read none of the local fields
except `stores` (the data view of the next store, `InstrViews.forStore`) and
the last entry of `loadViews` right after an RMW's read (its `extra` view),
so an access from the actual context and one from the context with the local
fields reset have the same outcomes up to those fields:

- `Ctx.reset`: the context with the local fields (and the log) at their
  defaults;
- `Ctx.Same cx cy`: equal views, promises, memory, `stores`, `rmwWrote`;
  `Ctx.Same.read`, `.write`, `.fence`, `.fenceOpt`, `.rmwAfter`: the outcome
  correspondences; `.overtaken`, `.inv`, `.erAt`, `.rStep`: what
  `EvTree.EraseWPRD` asks of an outcome depends on `Same` fields only;
- `CtxLe.transfer`: a `CtxLe` of `cy` gives one of any `Same` `cx` (with the
  environment's `loadViews`/`succView` re-chosen), so phase-1 `PostRel`s
  transfer.

This is the "local-field" part of the multi-access follow-up ("a `CtxRel`
variant"), done without a new `CtxRel`: the Sim library is
used as is.
-/
import Kraken.Promising.SLR.EnvG.CtxSim

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

/-- The context with the instruction-local fields, the promise log and the
trace at their defaults. -/
def _root_.Kraken.Promising.Ctx.reset (cx : Ctx) : Ctx := { views := cx.views, prom := cx.prom, mem := cx.mem }

@[simp] theorem Ctx.reset_views (cx : Ctx) : cx.reset.views = cx.views := rfl
@[simp] theorem Ctx.reset_prom (cx : Ctx) : cx.reset.prom = cx.prom := rfl
@[simp] theorem Ctx.reset_mem (cx : Ctx) : cx.reset.mem = cx.mem := rfl
@[simp] theorem Ctx.reset_stores (cx : Ctx) : cx.reset.stores = 0 := rfl
@[simp] theorem Ctx.reset_rmwWrote (cx : Ctx) : cx.reset.rmwWrote = false := rfl
@[simp] theorem Ctx.reset_loadViews (cx : Ctx) : cx.reset.loadViews = [] := rfl
@[simp] theorem Ctx.reset_succView (cx : Ctx) : cx.reset.succView = 0 := rfl

/-- **Same up to local fields**: equal views, promises, memory, and the two
local fields the rules or the relation read (`stores`, `rmwWrote`). -/
structure _root_.Kraken.Promising.Ctx.Same (cx cy : Ctx) : Prop where
  views : cx.views = cy.views
  prom : cx.prom = cy.prom
  mem : cx.mem = cy.mem
  stores : cx.stores = cy.stores
  rmwWrote : cx.rmwWrote = cy.rmwWrote

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.Ctx.Same

open Kraken.Promising.SLR

variable {A : Arch} {tid : Nat} {iv : InstrViews} {cx cy : Ctx}

theorem refl (cx : Ctx) : cx.Same cx := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem symm (h : cx.Same cy) : cy.Same cx := ⟨h.1.symm, h.2.symm, h.3.symm, h.4.symm, h.5.symm⟩

theorem trans {cz : Ctx} (h₁ : cx.Same cy) (h₂ : cy.Same cz) : cx.Same cz :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2, h₁.3.trans h₂.3, h₁.4.trans h₂.4, h₁.5.trans h₂.5⟩

/-- A context with no local writes yet is `Same` as its reset. -/
theorem reset (hs : cx.stores = 0) (hw : cx.rmwWrote = false) : cx.Same cx.reset := ⟨rfl, rfl, rfl, hs, hw⟩

/-- Reduce `Same` to equal fields (for proofs by `cases`). -/
private theorem eq_fields (h : cx.Same cy) :
    ∃ vs p m s w, cx.views = vs ∧ cy.views = vs ∧ cx.prom = p ∧ cy.prom = p ∧ cx.mem = m ∧ cy.mem = m ∧
      cx.stores = s ∧ cy.stores = s ∧ cx.rmwWrote = w ∧ cy.rmwWrote = w :=
  ⟨_, _, _, _, _, h.1, rfl, h.2, rfl, h.3, rfl, h.4, rfl, h.5, rfl⟩

/-- **The read correspondence**: every read outcome from `cx` is one from
`cy` with the same timestamp and value, a `Same` context, and the same last
load view. -/
theorem read (h : cx.Same cy) {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv cx k xcl l noRet) :
    ∃ y ∈ readSuccs A iv cy k xcl l noRet, y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ x.2.2.Same y.2.2 ∧
      x.2.2.loadViews.getLastD 0 = y.2.2.loadViews.getLastD 0 := by
  obtain ⟨t, v, rfl, h1, h2, h3, h4⟩ := (mem_readSuccs A).mp hx
  have hpre : readPre A iv cx k = readPre A iv cy k := by unfold readPre; rw [h.views]
  refine ⟨(t, v, readNext A iv cy k xcl l noRet t v), (mem_readSuccs A).mpr ⟨t, v, rfl, h.mem ▸ h1, h.mem ▸ h2,
    by rw [← h.mem, ← h.views, ← hpre]; exact h3, h.prom ▸ h4⟩, rfl, rfl, ?_, ?_⟩
  · refine ⟨?_, h.prom, h.mem, h.stores, h.rmwWrote⟩
    simp only [readNext, hpre, h.views]
  · simp only [readNext, hpre, h.views, List.getLastD_concat]

theorem fence (h : cx.Same cy) (k : FenceKind) : (fenceStep cx k).Same (fenceStep cy k) := by
  cases k <;> exact ⟨by simp only [fenceStep, h.views], by simp only [fenceStep, h.prom],
    by simp only [fenceStep, h.mem], by simp only [fenceStep, h.stores], by simp only [fenceStep, h.rmwWrote]⟩

theorem fenceOpt (h : cx.Same cy) (A : Arch) : (fenceOptCtx A cx).Same (fenceOptCtx A cy) := by
  unfold SLR.fenceOptCtx; split
  · exact h.fence .sy
  · exact h

theorem rmwPost (h : cx.Same cy) (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) :
    (Kraken.Promising.rmwPost A k noRet l cx).Same (Kraken.Promising.rmwPost A k noRet l cy) := by
  unfold Kraken.Promising.rmwPost
  simp only
  split
  · exact ⟨by simp only [h.views], h.prom, h.mem, h.stores, rfl⟩
  · exact ⟨h.views, h.prom, h.mem, h.stores, rfl⟩

theorem rmwAfter (h : cx.Same cy) (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) :
    (SLR.rmwAfter A k noRet l cx).Same (SLR.rmwAfter A k noRet l cy) := by
  unfold SLR.rmwAfter; split
  · exact (h.rmwPost A k noRet l).fence .sy
  · exact h.rmwPost A k noRet l

theorem writeOk (h : cx.Same cy) {ivs : InstrViews} {k : StoreKind} {l : Loc} {tr : Option Time} {extra : View}
    {t : Time} (hok : WriteOk A tid ivs cx k l tr extra t) : WriteOk A tid ivs cy k l tr extra t := by
  have hpre : writePre A ivs cx k extra = writePre A ivs cy k extra := by unfold writePre; rw [h.views]
  unfold WriteOk at hok ⊢
  rw [← hpre, ← h.views, ← h.mem]
  exact hok

theorem afterWrite (h : cx.Same cy) {ivs : InstrViews} (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time)
    (νfwd : View) (ful : Bool) :
    (Kraken.Promising.afterWrite A ivs cx k xcl l v t νfwd ful).Same
      (Kraken.Promising.afterWrite A ivs cy k xcl l v t νfwd ful) :=
  ⟨by simp only [Kraken.Promising.afterWrite, h.views], by simp only [Kraken.Promising.afterWrite, h.prom],
    by simp only [Kraken.Promising.afterWrite, h.mem], by simp only [Kraken.Promising.afterWrite, h.stores],
    by simp only [Kraken.Promising.afterWrite, h.rmwWrote]⟩

/-- **The write correspondence**: every write outcome from `cx` is one from
`cy` (same instruction views, read timestamp and extra view) with a `Same`
context. -/
theorem write (h : cx.Same cy) {ivs : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} {cx' : Ctx} (hc : cx' ∈ writeSuccs A tid ivs cx k xcl l v tr extra) :
    ∃ cy' ∈ writeSuccs A tid ivs cy k xcl l v tr extra, cx'.Same cy' := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, ht, w, hw, hl, hv, htid, hok, rfl⟩ | ⟨hok, rfl⟩
  · exact ⟨_, (mem_writeSuccs A tid).mpr (.inl ⟨t, h.prom ▸ ht, w, h.mem ▸ hw, hl, hv, htid, h.writeOk hok, rfl⟩),
      h.afterWrite _ _ _ _ _ _ _⟩
  · refine ⟨_, (mem_writeSuccs A tid).mpr (.inr ⟨by rw [← h.mem]; exact h.writeOk hok, rfl⟩), ?_⟩
    have h' : ({ cx with
        mem := (cx.mem.append { loc := l, val := v, tid }).1
        prom := cx.prom ++ [cx.mem.last + 1]
        promisedNow := cx.promisedNow ++
          [({ loc := l, val := v, tid }, max (writePre A ivs cx k extra) (cx.views.getCoh l))] } : Ctx).Same
        { cy with
          mem := (cy.mem.append { loc := l, val := v, tid }).1
          prom := cy.prom ++ [cy.mem.last + 1]
          promisedNow := cy.promisedNow ++
            [({ loc := l, val := v, tid }, max (writePre A ivs cy k extra) (cy.views.getCoh l))] } :=
      ⟨h.views, by simp only [h.prom, h.mem], by simp only [h.mem], h.stores, h.rmwWrote⟩
    rw [h.mem] at h' ⊢
    exact h'.afterWrite _ _ _ _ _ _ _

theorem overtaken (h : cx.Same cy) (ho : cy.Overtaken) : cx.Overtaken := by
  obtain ⟨p, hp, w, hw, hle⟩ := ho
  exact ⟨p, h.prom ▸ hp, w, h.mem ▸ hw, h.views ▸ hle⟩

theorem inv (h : cx.Same cy) (hi : cx.Inv tid) : cy.Inv tid := by
  obtain ⟨vs, p, m, s, w, e1, e2, e3, e4, e5, e6, -, -, -, -⟩ := h.eq_fields
  obtain ⟨h1, h2, h3⟩ := hi
  refine ⟨?_, ?_, ?_⟩
  · rw [e4, e6]; rw [e3, e5] at h1; exact h1
  · rw [e4]; rw [e3] at h2; exact h2
  · unfold Ctx.OwnCoh at h3 ⊢; rw [e2, e4, e6]; rw [e1, e3, e5] at h3; exact h3

theorem erAt (h : cx.Same cy) {I : ISA} {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I}
    {r : Res} {g : Ghost} (he : ErAt rF T c t tid r g cy) : ErAt rF T c t tid r g cx := by
  unfold ErAt at he ⊢; rw [h.prom, h.mem]; exact he

theorem rStep (h : cx.Same cy) {B : Time} {r r' : Res} {g g' : Ghost} (hr : RStep B r g r' g' cy) :
    RStep B r g r' g' cx := by
  unfold RStep at hr ⊢; rw [h.views]; exact hr

end Kraken.Promising.Ctx.Same

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

/-! ## `CtxLe` across `Same` -/

section Transfer

variable {iv : InstrViews} {cx cy cxe : Ctx}

/-- The environment context `cxe` with its local fields re-chosen for an
actual context with `loadViews` `ls`. -/
def envLocals (cxe : Ctx) (ls : List View) : Ctx := { cxe with loadViews := ls.map fun _ => 0, succView := 0 }

/-- **`CtxLe` transfers to a `Same` context** (bounded), the environment's
`loadViews` and `succView` re-chosen (zeros): `CtxRel` only bounds them
from above. -/
theorem CtxLe.transfer (h : CtxLe iv cy cxe) (hs : cx.Same cy) (hb : cx.Bnd) :
    CtxLe iv cx (envLocals cxe cx.loadViews) := by
  obtain ⟨⟨⟨r1, r2, r3, -, -, r6, r7⟩, -, hpd, hda, hivr, hivb, hnle, hfgn⟩, hme, hpe⟩ := h
  have hl : Rel2 (fun a' a => a' ≤ (TMap.idUpTo cx.mem.last).fv a) (cx.loadViews.map fun _ => (0 : View))
      cx.loadViews := by
    generalize cx.loadViews = ls
    induction ls with
    | nil => exact .nil
    | cons a ls ih => exact .cons (Nat.zero_le _) ih
  refine ⟨⟨⟨?_, ?_, ?_, hl, Nat.zero_le _, ?_, ?_⟩, hb, ?_, ?_, by rw [hs.mem]; exact hivr, ?_, Nat.zero_le _, ?_⟩, ?_, ?_⟩
  · show MemRel _ cx.mem cxe.mem; rw [hs.mem]; exact r1
  · show ViewsLe _ cxe.views cx.views; rw [hs.views, hs.mem]; exact r2
  · show PromRel _ cx.prom cxe.prom; rw [hs.prom, hs.mem]; exact r3
  · show cxe.rmwWrote = cx.rmwWrote; rw [hs.rmwWrote]; exact r6
  · show cxe.stores = cx.stores; rw [hs.stores]; exact r7
  · rw [hs.prom, hs.mem]; exact hpd
  · rw [hs.mem]; exact hda
  · rw [hs.mem]; exact hivb
  · show FgnSep _ cxe.mem _ _; rw [hs.mem]; exact hfgn
  · show cxe.mem = cx.mem; rw [hs.mem]; exact hme
  · show cxe.prom = cx.prom; rw [hs.prom]; exact hpe

theorem envLocals_views (cxe : Ctx) (ls : List View) : (envLocals cxe ls).views = cxe.views := rfl

/-- A `CtxLe` of a context with no local writes gives one of its reset with
the environment's locals reset. -/
theorem CtxLe.reset (h : CtxLe iv cx cxe) : CtxLe iv cx.reset cxe.reset := by
  obtain ⟨⟨⟨r1, r2, r3, -, -, -, -⟩, hb, hpd, hda, hivr, hivb, hnle, hfgn⟩, hme, hpe⟩ := h
  exact ⟨⟨⟨r1, r2, r3, .nil, Nat.zero_le _, rfl, rfl⟩, ⟨hb.views, fun _ h => absurd h List.not_mem_nil,
    Nat.zero_le _⟩, hpd, hda, hivr, hivb, hnle, hfgn⟩, hme, hpe⟩

end Transfer

end Kraken.Promising.SLR.EnvG
