/-
**View domination and the iteration cut** (ISA-neutral,
architecture-neutral, program-independent; executable `Thread` rules only).

`CertBoundedFrom` (`LiveCertBounded.lean`) asks for a certification of
bounded length. For a spin-lock client the given certification may spin: a
waiting thread's solo run can go round its loop reading one lock message
after another, so neither `ThreadNPn.shorten` (which needs every solo run
bounded) nor a plain pigeonhole on thread states (the views differ at every
iteration) applies. What does hold is **view monotonicity**: a thread with
the same `st`, promises and memory but *lower* views has *more* behaviours.
Reads are allowed below a smaller coherence bound, fulfilments above a
smaller pre-view, and every view after the step is a `max` of inputs. So if
a certifying run passes through `p` and later through `q` with `p ≼ q`
(`Thread.Dom`: same `st`, `prom`, memory; every view of `p` at most the
corresponding view of `q`), `q`'s continuation replays from `p` and the loop
`p →* q` can be cut out.

- `Views.Dom`, `InstrViews.Dom`, `Ctx.Dom`, `Thread.Dom`: the relations
  (`FwdDom`: the same forwarding entry up to its view; `XclbDom`: the same
  pending load exclusive up to its view; register views pointwise, `ArrLe`).
- The replay, rule by rule: `readSuccs_dom`, `afterWrite_dom`,
  `writeSuccs_dom`, `fenceStep_dom`, `rmwPost_dom`, `runTree_dom` (every
  event tree), `instrViews_dom`, `finishInstr_dom`, `stepOne_dom`,
  `ThreadStep.dom`, `ThreadNPn.dom`, `CertOkN.of_dom`.
- **The iteration cut** `ThreadNPn.cut`: a certifying run `p →ᵃ q →ᵇ q' →ᶜ r`
  with `q ≼ q'` (and the same memory) gives a certifying run of length
  `a + c` from `p`.
- `Views.Grow` and `stepOne_grow`: along any instruction, every scalar view
  and every coherence view grows, memory extends, and without a write (same
  `|M|` and promise count) the forwarding table is unchanged. This is the
  sanity check of `Dom` (nothing a step does lowers a view) and the way the
  per-program bound establishes `p ≼ q` between two visits of a loop head.
  Register views are *not* monotone along a run (an instruction resets its
  destinations' views to its inputs' join), so `stepOne_grow` says nothing
  about them; the per-program argument compares them directly.
- `EvTree.NoXclLoad`, `stepOne_xclb_none`: without load exclusives the
  pending-exclusive slot stays empty (so `XclbDom` is trivial).
-/
import Kraken.Promising.LiveSemShape

namespace Kraken.Promising.Live.CertCut

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.TicketStep

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

theorem max_le_max {a b c d : View} (h1 : a ≤ b) (h2 : c ≤ d) : max a c ≤ max b d := by omega_t

theorem ite_le_ite {P : Prop} [Decidable P] {a b c d : View} (h1 : a ≤ b) (h2 : c ≤ d) :
    (if P then a else c) ≤ (if P then b else d) := by
  split <;> assumption

/-! ## Pointwise order on lists and arrays of views -/

/-- Pointwise `≤` on two lists of the same length. -/
inductive ListLe : List View → List View → Prop
  | nil : ListLe [] []
  | cons {x y : View} {xs ys : List View} : x ≤ y → ListLe xs ys → ListLe (x :: xs) (y :: ys)

theorem ListLe.refl : ∀ xs : List View, ListLe xs xs
  | [] => .nil
  | _ :: xs => .cons (Nat.le_refl _) (ListLe.refl xs)

theorem ListLe.length_eq {xs ys : List View} (h : ListLe xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ListLe.append_single {xs ys : List View} (h : ListLe xs ys) {x y : View} (hxy : x ≤ y) :
    ListLe (xs ++ [x]) (ys ++ [y]) := by
  induction h with
  | nil => exact .cons hxy .nil
  | cons h _ ih => exact .cons h ih

theorem ListLe.foldl_max {xs ys : List View} (h : ListLe xs ys) : ∀ {a b : View}, a ≤ b →
    xs.foldl max a ≤ ys.foldl max b := by
  induction h with
  | nil => intro a b hab; exact hab
  | cons h _ ih => intro a b hab; exact ih (max_le_max hab h)

theorem ListLe.getLastD {xs ys : List View} (h : ListLe xs ys) : xs.getLastD 0 ≤ ys.getLastD 0 := by
  induction h with
  | nil => exact Nat.le_refl _
  | @cons x y xs ys hxy h ih =>
    cases h with
    | nil => exact hxy
    | @cons x' y' xs' ys' h' h'' =>
      show (x' :: xs').getLastD x ≤ (y' :: ys').getLastD y
      rw [List.getLastD_cons, List.getLastD_cons]
      rw [List.getLastD_cons, List.getLastD_cons] at ih
      exact ih

/-- Pointwise `≤` on two arrays of the same size. -/
def ArrLe (a b : Array View) : Prop := a.size = b.size ∧ ∀ i : Nat, (a[i]! : View) ≤ b[i]!

theorem ArrLe.refl (a : Array View) : ArrLe a a := ⟨rfl, fun _ => Nat.le_refl _⟩

theorem ArrLe.setIfInBounds {a b : Array View} (h : ArrLe a b) (i : Nat) {x y : View} (hxy : x ≤ y) :
    ArrLe (a.setIfInBounds i x) (b.setIfInBounds i y) := by
  refine ⟨by simp [h.1], fun j => ?_⟩
  have := h.2 j
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at this ⊢
  rw [← h.1]
  split
  · split
    · exact hxy
    · exact Nat.le_refl _
  · exact this

/-! ## The relations -/

/-- The same forwarding entry up to its view. -/
def FwdDom : Option FwdItem → Option FwdItem → Prop
  | none, none => True
  | some f, some g => f.time = g.time ∧ f.xcl = g.xcl ∧ f.view ≤ g.view ∧ f.xclRead ≤ g.xclRead
  | _, _ => False

/-- The same pending load exclusive up to its view. -/
def XclbDom : Option (Time × View × Loc) → Option (Time × View × Loc) → Prop
  | none, none => True
  | some (t, ν, l), some (t', ν', l') => t = t' ∧ ν ≤ ν' ∧ l = l'
  | _, _ => False

theorem FwdDom.refl : ∀ f : Option FwdItem, FwdDom f f
  | none => trivial
  | some _ => ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem XclbDom.refl : ∀ x : Option (Time × View × Loc), XclbDom x x
  | none => trivial
  | some (_, _, _) => ⟨rfl, Nat.le_refl _, rfl⟩

theorem XclbDom.xclRead : ∀ {x y : Option (Time × View × Loc)}, XclbDom x y →
    (x.map (·.2.1)).getD 0 ≤ (y.map (·.2.1)).getD 0
  | none, none, _ => Nat.le_refl _
  | some (_, _, _), some (_, _, _), h => h.2.1

/-- **Views dominated pointwise**: `a ≼ b`. -/
structure _root_.Kraken.Promising.Views.Dom (a b : Views) : Prop where
  coh : ∀ l, a.getCoh l ≤ b.getCoh l
  vrNew : a.vrNew ≤ b.vrNew
  vrOld : a.vrOld ≤ b.vrOld
  vrOldNR : a.vrOldNR ≤ b.vrOldNR
  vwNew : a.vwNew ≤ b.vwNew
  vwOld : a.vwOld ≤ b.vwOld
  vwOldNT : a.vwOldNT ≤ b.vwOldNT
  vCAP : a.vCAP ≤ b.vCAP
  vRel : a.vRel ≤ b.vRel
  fwd : ∀ l, FwdDom (a.getFwd l) (b.getFwd l)
  xclb : XclbDom a.xclb b.xclb

theorem _root_.Kraken.Promising.Views.Dom.refl (a : Views) : a.Dom a :=
  ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
   Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ => FwdDom.refl _, XclbDom.refl _⟩

/-- Per-instruction views dominated pointwise. -/
structure _root_.Kraken.Promising.InstrViews.Dom (a b : InstrViews) : Prop where
  addrR : a.addrR ≤ b.addrR
  addrW : a.addrW ≤ b.addrW
  dataR : a.dataR ≤ b.dataR
  dataW : a.dataW ≤ b.dataW
  condW : a.condW ≤ b.condW
  dataPer : a.dataPer.length = b.dataPer.length ∧
    ∀ (i : Nat) (p q : View × View), a.dataPer[i]? = some p → b.dataPer[i]? = some q → p.1 ≤ q.1 ∧ p.2 ≤ q.2

theorem _root_.Kraken.Promising.InstrViews.Dom.forStore {a b : InstrViews} (h : a.Dom b) (i : Nat) :
    (a.forStore i).Dom (b.forStore i) := by
  have hlen := h.dataPer.1
  unfold InstrViews.forStore
  cases ha : a.dataPer[i]? with
  | none =>
    cases hb : b.dataPer[i]? with
    | none => exact h
    | some q =>
      exfalso
      have h1 := List.getElem?_eq_none_iff.mp ha
      have h2 := (List.getElem?_eq_some_iff.mp hb).1
      omega
  | some p =>
    cases hb : b.dataPer[i]? with
    | none =>
      exfalso
      have h1 := List.getElem?_eq_none_iff.mp hb
      have h2 := (List.getElem?_eq_some_iff.mp ha).1
      omega
    | some q =>
      obtain ⟨h1, h2⟩ := h.dataPer.2 i p q ha hb
      exact ⟨h.addrR, h.addrW, h1, h2, h.condW, h.dataPer⟩

theorem _root_.Kraken.Promising.InstrViews.Dom.refl (a : InstrViews) : a.Dom a :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, rfl,
   fun _ p q hp hq => by rw [hp] at hq; cases hq; exact ⟨Nat.le_refl _, Nat.le_refl _⟩⟩

/-- Contexts dominated: the same promises and memory, dominated views. -/
structure _root_.Kraken.Promising.Ctx.Dom (c c' : Ctx) : Prop where
  views : c.views.Dom c'.views
  prom : c.prom = c'.prom
  mem : c.mem = c'.mem
  loadViews : ListLe c.loadViews c'.loadViews
  succView : c.succView ≤ c'.succView
  rmwWrote : c.rmwWrote = c'.rmwWrote
  stores : c.stores = c'.stores

/-- **Threads dominated**: the same `st` and promises, every view (scalar,
coherence, forwarding, register) of `t` at most that of `t'`. -/
structure _root_.Kraken.Promising.Thread.Dom (t t' : Thread I) : Prop where
  st : t.st = t'.st
  rview : ArrLe t.rview t'.rview
  wview : ArrLe t.wview t'.wview
  views : t.views.Dom t'.views
  prom : t.prom = t'.prom

theorem _root_.Kraken.Promising.Thread.Dom.refl (t : Thread I) : t.Dom t :=
  ⟨rfl, ArrLe.refl _, ArrLe.refl _, Views.Dom.refl _, rfl⟩

/-! ## Views after a read, a write, a fence -/

theorem readView_dom (A : Arch) (k : LoadKind) {f g : Option FwdItem} (h : FwdDom f g) (t : Time) :
    readView A k f t ≤ readView A k g t := by
  cases f with
  | none =>
    cases g with
    | none => exact Nat.le_refl _
    | some _ => exact h.elim
  | some a =>
    cases g with
    | none => exact h.elim
    | some b =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      simp only [readView, h1, h2]
      split
      · split <;> simp only [Time, View] at * <;> omega
      · exact Nat.le_refl _

theorem _root_.Kraken.Promising.Views.Dom.read {vs vs' : Views} (h : vs.Dom vs') {l : Loc} {ν ν' a a' : View}
    {acq xcl noRet : Bool} {t : Time} (hν : ν ≤ ν') (ha : a ≤ a') :
    Views.Dom
      { (vs.setCoh l ν) with
        vrOld := if noRet then vs.vrOld else max vs.vrOld ν
        vrOldNR := if noRet then max vs.vrOldNR ν else vs.vrOldNR
        vrNew := if acq then max vs.vrNew ν else vs.vrNew
        vwNew := if acq then max vs.vwNew ν else vs.vwNew
        vCAP := max vs.vCAP a
        xclb := if xcl then some (t, ν, l) else vs.xclb }
      { (vs'.setCoh l ν') with
        vrOld := if noRet then vs'.vrOld else max vs'.vrOld ν'
        vrOldNR := if noRet then max vs'.vrOldNR ν' else vs'.vrOldNR
        vrNew := if acq then max vs'.vrNew ν' else vs'.vrNew
        vwNew := if acq then max vs'.vwNew ν' else vs'.vwNew
        vCAP := max vs'.vCAP a'
        xclb := if xcl then some (t, ν', l) else vs'.xclb } := by
  refine ⟨fun l' => ?_, ?_, ?_, ?_, ?_, h.vwOld, h.vwOldNT, max_le_max h.vCAP ha, h.vRel, h.fwd, ?_⟩
  · show (vs.setCoh l ν).getCoh l' ≤ (vs'.setCoh l ν').getCoh l'
    rw [Views.getCoh_setCoh, Views.getCoh_setCoh]
    split
    · exact max_le_max (h.coh l) hν
    · exact h.coh l'
  · show (if acq = true then max vs.vrNew ν else vs.vrNew) ≤ (if acq = true then max vs'.vrNew ν' else vs'.vrNew)
    split
    · exact max_le_max h.vrNew hν
    · exact h.vrNew
  · show (if noRet = true then vs.vrOld else max vs.vrOld ν) ≤ (if noRet = true then vs'.vrOld else max vs'.vrOld ν')
    split
    · exact h.vrOld
    · exact max_le_max h.vrOld hν
  · show (if noRet = true then max vs.vrOldNR ν else vs.vrOldNR) ≤
      (if noRet = true then max vs'.vrOldNR ν' else vs'.vrOldNR)
    split
    · exact max_le_max h.vrOldNR hν
    · exact h.vrOldNR
  · show (if acq = true then max vs.vwNew ν else vs.vwNew) ≤ (if acq = true then max vs'.vwNew ν' else vs'.vwNew)
    split
    · exact max_le_max h.vwNew hν
    · exact h.vwNew
  · show XclbDom (if xcl = true then some (t, ν, l) else vs.xclb) (if xcl = true then some (t, ν', l) else vs'.xclb)
    cases xcl
    · exact h.xclb
    · exact ⟨rfl, hν, rfl⟩

theorem _root_.Kraken.Promising.Views.Dom.setNew {vs vs' : Views} (h : vs.Dom vs') {r r' w w' : View} (hr : r ≤ r')
    (hw : w ≤ w') : ({ vs with vrNew := r, vwNew := w } : Views).Dom { vs' with vrNew := r', vwNew := w' } :=
  ⟨h.coh, hr, h.vrOld, h.vrOldNR, hw, h.vwOld, h.vwOldNT, h.vCAP, h.vRel, h.fwd, h.xclb⟩

theorem _root_.Kraken.Promising.Views.Dom.setVCAP {vs vs' : Views} (h : vs.Dom vs') {x x' : View} (hx : x ≤ x') :
    ({ vs with vCAP := x } : Views).Dom { vs' with vCAP := x' } :=
  ⟨h.coh, h.vrNew, h.vrOld, h.vrOldNR, h.vwNew, h.vwOld, h.vwOldNT, hx, h.vRel, h.fwd, h.xclb⟩

theorem _root_.Kraken.Promising.Views.Dom.xclbNone {vs vs' : Views} (h : vs.Dom vs') :
    ({ vs with xclb := none } : Views).Dom { vs' with xclb := none } :=
  ⟨h.coh, h.vrNew, h.vrOld, h.vrOldNR, h.vwNew, h.vwOld, h.vwOldNT, h.vCAP, h.vRel, h.fwd, trivial⟩

section Rules

variable (A : Arch) (tid : Nat)

/-- The pre-view of a read is monotone. -/
theorem readPre_dom {iv iv' : InstrViews} (hiv : iv.Dom iv') {c c' : Ctx} (hc : c.views.Dom c'.views) (k : LoadKind) :
    readPre A iv c k ≤ readPre A iv' c' k :=
  max_le_max hiv.addrR (max_le_max hc.vrNew (ite_le_ite hc.vRel (Nat.le_refl 0)))

/-- **A read replays below**: a read of the dominating context is a read of
the same timestamp and value by the dominated one, with dominated results. -/
theorem readSuccs_dom {iv iv' : InstrViews} (hiv : iv.Dom iv') {c c' : Ctx} (hc : c.Dom c') {k : LoadKind}
    {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv' c' k xcl l noRet) :
    ∃ c2, (x.1, x.2.1, c2) ∈ readSuccs A iv c k xcl l noRet ∧ c2.Dom x.2.2 := by
  obtain ⟨t, v, rfl, hle, hr, hw, hp⟩ := (mem_readSuccs A).mp hx
  have hpre := readPre_dom A hiv hc.views k
  refine ⟨readNext A iv c k xcl l noRet t v, (mem_readSuccs A).mpr ⟨t, v, rfl, hc.mem ▸ hle, hc.mem ▸ hr, ?_, hc.prom ▸ hp⟩, ?_⟩
  · rw [hc.mem]
    exact SpinSemSwpSolo.writeIn_le hw (max_le_max hpre (hc.views.coh l))
  · have hν : max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) t) ≤
        max (readPre A iv' c' k) (readView A (A.loadKind k) (c'.views.getFwd l) t) :=
      max_le_max hpre (readView_dom A _ (hc.views.fwd l) t)
    exact ⟨hc.views.read hν hiv.addrW, hc.prom, hc.mem, hc.loadViews.append_single hν, hc.succView,
      hc.rmwWrote, hc.stores⟩

/-- `afterWrite` on dominated contexts, at the same timestamp. -/
theorem afterWrite_dom {iv iv' : InstrViews} (hiv : iv.addrW ≤ iv'.addrW) {c c' : Ctx} (hc : c.Dom c')
    (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time) {νfwd νfwd' : View} (hν : νfwd ≤ νfwd')
    (ful ful' : Bool) {xr xr' : View} (hxr : xr ≤ xr') :
    (afterWrite A iv c k xcl l v t νfwd ful xr).Dom (afterWrite A iv' c' k xcl l v t νfwd' ful' xr') := by
  have hv := hc.views
  refine ⟨⟨fun l' => ?_, hv.vrNew, hv.vrOld, hv.vrOldNR, hv.vwNew, ?_, ?_, max_le_max hv.vCAP hiv, ?_,
    fun l' => ?_, ?_⟩, by simp only [afterWrite]; rw [hc.prom], hc.mem, hc.loadViews, ?_, hc.rmwWrote,
    by simp only [afterWrite]; rw [hc.stores]⟩
  · rw [afterWrite_getCoh, afterWrite_getCoh]
    split
    · exact max_le_max (hv.coh l) (Nat.le_refl _)
    · exact hv.coh l'
  · show (if (k == StoreKind.nt) = true then c.views.vwOld else max c.views.vwOld t) ≤
      (if (k == StoreKind.nt) = true then c'.views.vwOld else max c'.views.vwOld t)
    split
    · exact hv.vwOld
    · exact max_le_max hv.vwOld (Nat.le_refl _)
  · show (if (k == StoreKind.nt) = true then max c.views.vwOldNT t else c.views.vwOldNT) ≤
      (if (k == StoreKind.nt) = true then max c'.views.vwOldNT t else c'.views.vwOldNT)
    split
    · exact max_le_max hv.vwOldNT (Nat.le_refl _)
    · exact hv.vwOldNT
  · show (if (k == StoreKind.rel) = true then max c.views.vRel t else c.views.vRel) ≤
      (if (k == StoreKind.rel) = true then max c'.views.vRel t else c'.views.vRel)
    split
    · exact max_le_max hv.vRel (Nat.le_refl _)
    · exact hv.vRel
  · rw [afterWrite_getFwd, afterWrite_getFwd]
    split
    · exact ⟨rfl, rfl, hν, hxr⟩
    · exact hv.fwd l'
  · show XclbDom (if xcl = true then none else c.views.xclb) (if xcl = true then none else c'.views.xclb)
    cases xcl
    · exact hv.xclb
    · trivial
  · show (if A.succViewBot = true then 0 else t) ≤ (if A.succViewBot = true then 0 else t)
    exact Nat.le_refl _

/-- The pre-view of a write is monotone. -/
theorem writePre_dom {iv iv' : InstrViews} (hiv : iv.Dom iv') {c c' : Ctx} (hc : c.views.Dom c'.views)
    (k : StoreKind) {extra extra' : View} (he : extra ≤ extra') :
    writePre A iv c k extra ≤ writePre A iv' c' k extra' :=
  max_le_max (max_le_max hiv.addrW (max_le_max hiv.dataW (max_le_max hiv.condW he)))
    (max_le_max (max_le_max hc.vwNew hc.vCAP)
      (ite_le_ite (max_le_max (max_le_max hc.vrOld hc.vrOldNR) hc.vwOld)
        (ite_le_ite (max_le_max hc.vrOld hc.vrOldNR) (Nat.le_refl 0))))

/-- **A write replays below**: a write of the dominating context (a
fulfilment or an append) is a write of the same timestamp by the dominated
one, with dominated results. -/
theorem writeSuccs_dom {iv iv' : InstrViews} (hiv : iv.Dom iv') {c c' : Ctx} (hc : c.Dom c') {k : StoreKind}
    {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time} {extra extra' : View} (he : extra ≤ extra')
    {xr xr' : View} (hxr : xr ≤ xr') {c2' : Ctx} (h : c2' ∈ writeSuccs A tid iv' c' k xcl l v tr extra' xr') :
    ∃ c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr, c2.Dom c2' := by
  have hok : ∀ t, WriteOk A tid iv' c' k l tr extra' t → WriteOk A tid iv c k l tr extra t := by
    intro t ⟨h1, h2⟩
    refine ⟨Nat.lt_of_le_of_lt (max_le_max (writePre_dom A hiv hc.views k he) (hc.views.coh l)) h1,
      fun a ha => ?_⟩
    rw [hc.mem]; exact h2 a ha
  have hν : max iv.addrR (max iv.dataR extra) ≤ max iv'.addrR (max iv'.dataR extra') :=
    max_le_max hiv.addrR (max_le_max hiv.dataR he)
  rcases (mem_writeSuccs A tid).mp h with ⟨t, ht, w, hw, h1, h2, h3, h4, rfl⟩ | ⟨h4, rfl⟩
  · refine ⟨_, (mem_writeSuccs A tid).mpr (.inl ⟨t, hc.prom ▸ ht, w, hc.mem ▸ hw, h1, h2, h3, hok t h4, rfl⟩),
      afterWrite_dom A hiv.addrW hc _ _ _ _ _ hν _ _ hxr⟩
  · refine ⟨_, (mem_writeSuccs A tid).mpr (.inr ⟨by rw [hc.mem]; exact hok _ h4, rfl⟩), ?_⟩
    rw [hc.mem]
    refine afterWrite_dom A hiv.addrW ?_ _ _ _ _ _ hν _ _ hxr
    refine ⟨hc.views, ?_, rfl, hc.loadViews, hc.succView, hc.rmwWrote, hc.stores⟩
    simp only; rw [hc.prom]

end Rules

theorem fenceStep_dom {c c' : Ctx} (hc : c.Dom c') (k : FenceKind) : (fenceStep c k).Dom (fenceStep c' k) := by
  have hv := hc.views
  have key : ∀ (r r' w w' : View), r ≤ r' → w ≤ w' →
      Ctx.Dom { c with views := { c.views with vrNew := r, vwNew := w }, log := c.log ++ [TraceEv.fence k] }
        { c' with views := { c'.views with vrNew := r', vwNew := w' }, log := c'.log ++ [TraceEv.fence k] } :=
    fun r r' w w' hr hw => ⟨hv.setNew hr hw, hc.prom, hc.mem, hc.loadViews, hc.succView, hc.rmwWrote, hc.stores⟩
  have := hv.vrNew; have := hv.vwNew; have := hv.vrOld; have := hv.vrOldNR; have := hv.vwOld; have := hv.vwOldNT
  have := hv.vCAP
  cases k
  · exact key _ _ _ _ (by omega_t) (by omega_t)
  · exact key _ _ _ _ (by omega_t) (by omega_t)
  · exact key _ _ _ _ (by omega_t) (by omega_t)
  · exact key _ _ _ _ (by omega_t) (by omega_t)
  · exact key _ _ _ _ (by omega_t) (by omega_t)

theorem fenceOpt_dom {c c' : Ctx} (hc : c.Dom c') (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).Dom (if b then fenceStep c' k else c') := by
  cases b
  · exact hc
  · exact fenceStep_dom hc k

theorem rmwPost_dom (A : Arch) {c c' : Ctx} (hc : c.Dom c') (k : RmwKind) (noRet : Bool) (l : Loc) :
    (rmwPost A k noRet l c).Dom (rmwPost A k noRet l c') := by
  have hv := hc.views
  unfold rmwPost
  split
  · exact ⟨hv.setNew (max_le_max hv.vrNew (hv.coh l)) (max_le_max hv.vwNew (hv.coh l)), hc.prom, hc.mem,
      hc.loadViews, hc.succView, rfl, hc.stores⟩
  · exact ⟨hv, hc.prom, hc.mem, hc.loadViews, hc.succView, rfl, hc.stores⟩

theorem xclFail_dom {c c' : Ctx} (hc : c.Dom c') (l : Loc) :
    Ctx.Dom { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }
      { c' with views := { c'.views with xclb := none }, succView := 0, log := c'.log ++ [.xclFail l] } :=
  ⟨hc.views.xclbNone, hc.prom, hc.mem, hc.loadViews, Nat.le_refl _, hc.rmwWrote, hc.stores⟩

section Rules

variable (A : Arch) (tid : Nat)

/-- **An event tree replays below**: a run of the tree from the dominating
context is matched, with the same final state, by a run from the dominated
one, ending in a dominated context. -/
theorem runTree_dom {σ : Type} {iv iv' : InstrViews} (hiv : iv.Dom iv') (tree : EvTree σ) :
    ∀ (c c' : Ctx) (s : σ) (c2' : Ctx), c.Dom c' → .ok (s, c2') ∈ runTree A tid iv' c' tree →
      ∃ c2, .ok (s, c2) ∈ runTree A tid iv c tree ∧ c2.Dom c2' := by
  induction tree with
  | done s0 =>
    intro c c' s c2' hc h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨c, by simp [runTree], hc⟩
  | fault msg =>
    intro c c' s c2' _ h
    simp [runTree] at h
  | choose n k ih =>
    intro c c' s c2' hc h
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨i, hi, h⟩ := h
    obtain ⟨c2, h', hd⟩ := ih i c c' s c2' hc h
    exact ⟨c2, ⟨i, hi, h'⟩, hd⟩
  | load k xcl l ret ih =>
    intro c c' s c2' hc h
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨⟨t, v, c0'⟩, hx, h⟩ := h
    obtain ⟨c0, hx', hd0⟩ := readSuccs_dom A hiv hc hx
    obtain ⟨c2, h', hd⟩ := ih v c0 c0' s c2' hd0 h
    exact ⟨c2, ⟨(t, v, c0), hx', h'⟩, hd⟩
  | store k xcl l v ret ih =>
    intro c c' s c2' hc h
    have hsh : (if xcl then c.views.xclb.map (·.1) else none) = (if xcl then c'.views.xclb.map (·.1) else none) := by
      have hx := hc.views.xclb
      revert hx
      generalize c.views.xclb = a
      generalize c'.views.xclb = b
      rcases a with _ | ⟨a1, a2, l1⟩ <;> rcases b with _ | ⟨b1, b2, l2⟩ <;> intro hx
      · rfl
      · exact hx.elim
      · exact hx.elim
      · obtain ⟨rfl, -, rfl⟩ := hx; rfl
    simp only [runTree, List.mem_append] at h ⊢
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨hp, c0', hc0', h⟩ := h
      have hivs : (iv.forStore c.stores).Dom (iv'.forStore c'.stores) := hc.stores ▸ hiv.forStore c.stores
      obtain ⟨c0, hc0, hd0⟩ := writeSuccs_dom A tid hivs hc (Nat.le_refl 0)
        (xr := if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0)
        (by cases xcl; exact Nat.le_refl _; exact hc.views.xclb.xclRead) (hsh ▸ hc0')
      obtain ⟨c2, h', hd⟩ := ih true c0 c0' s c2' hd0 h
      refine ⟨c2, Or.inl ?_, hd⟩
      rw [List.mem_ite_nil_left, List.mem_flatMap]
      refine ⟨?_, c0, hc0, h'⟩
      have hx := hc.views.xclb
      revert hp hx
      generalize c.views.xclb = a
      generalize c'.views.xclb = b
      rcases a with _ | ⟨a1, a2, l1⟩ <;> rcases b with _ | ⟨b1, b2, l2⟩ <;> intro hp hx
      · exact hp
      · exact hx.elim
      · exact hx.elim
      · obtain ⟨-, -, rfl⟩ := hx; exact hp
    · rw [List.mem_ite_nil_right] at h
      obtain ⟨c2, h', hd⟩ := ih false _ _ s c2' (xclFail_dom hc l) h.2
      refine ⟨c2, Or.inr ?_, hd⟩
      rw [List.mem_ite_nil_right]
      exact ⟨h.1, h'⟩
  | fence k ret ih =>
    intro c c' s c2' hc h
    simp only [runTree] at h ⊢
    exact ih () _ _ s c2' (fenceStep_dom hc k) h
  | rmw k noRet l op ret ih =>
    intro c c' s c2' hc h
    simp only [runTree] at h ⊢
    have hc1 := fenceOpt_dom hc A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at hc1 ⊢
    generalize (if A.rmwFence then fenceStep c' .sy else c') = c1' at hc1 h
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c3'⟩, hx, h⟩ := h
    obtain ⟨c3, hx', hd3⟩ := readSuccs_dom A hiv hc1 hx
    simp only at h
    split at h
    · rename_i hop
      obtain ⟨c2, h', hd⟩ := ih old _ _ s c2' (fenceOpt_dom hd3 A.rmwFence .sy) h
      refine ⟨c2, List.mem_flatMap.mpr ⟨(tr, old, c3), hx', ?_⟩, hd⟩
      simp only [hop]
      exact h'
    · rename_i new hop
      rw [List.mem_flatMap] at h
      obtain ⟨c4', hc4', h⟩ := h
      change .ok (s, c2') ∈ runTree A tid iv'
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c4') .sy else rmwPost A k noRet l c4') (ret old) at h
      obtain ⟨c4, hc4, hd4⟩ := writeSuccs_dom A tid hiv hd3 hd3.loadViews.getLastD (Nat.le_refl 0) hc4'
      obtain ⟨c2, h', hd⟩ := ih old _ _ s c2' (fenceOpt_dom (rmwPost_dom A hd4 k noRet l) A.rmwFence .sy) h
      refine ⟨c2, List.mem_flatMap.mpr ⟨(tr, old, c3), hx', ?_⟩, hd⟩
      simp only [hop, List.mem_flatMap]
      exact ⟨c4, hc4, h'⟩

end Rules

/-! ## Threads: register views and `finishInstr` -/

theorem _root_.Kraken.Promising.Thread.Dom.rviewOf {t t' : Thread I} (h : t.Dom t') (r : I.RegId) :
    t.rviewOf r ≤ t'.rviewOf r := h.rview.2 _

theorem _root_.Kraken.Promising.Thread.Dom.wviewOf {t t' : Thread I} (h : t.Dom t') (r : I.RegId) :
    t.wviewOf r ≤ t'.wviewOf r := h.wview.2 _

theorem _root_.Kraken.Promising.Thread.Dom.setRegView {t t' : Thread I} (h : t.Dom t') (r : I.RegId) {rv rv' wv wv' : View}
    (hr : rv ≤ rv') (hw : wv ≤ wv') : (t.setRegView r rv wv).Dom (t'.setRegView r rv' wv') :=
  ⟨h.st, by simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; exact h.rview.setIfInBounds _ hr,
   by simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; exact h.wview.setIfInBounds _ hw, h.views, h.prom⟩

private theorem foldl_rel {α β γ : Type} (R : β → γ → Prop) (f : β → α → β) (g : γ → α → γ)
    (hf : ∀ b c x, R b c → R (f b x) (g c x)) : ∀ (xs : List α) (b : β) (c : γ), R b c → R (xs.foldl f b) (xs.foldl g c)
  | [], _, _, h => h
  | x :: xs, b, c, h => foldl_rel R f g hf xs (f b x) (g c x) (hf b c x h)

theorem joinViews_dom {t t' : Thread I} (h : t.Dom t') (rs : List I.RegId) :
    (t.joinViews rs).1 ≤ (t'.joinViews rs).1 ∧ (t.joinViews rs).2 ≤ (t'.joinViews rs).2 := by
  unfold Thread.joinViews
  apply foldl_rel (fun (a b : View × View) => a.1 ≤ b.1 ∧ a.2 ≤ b.2)
  · intro a b x hab
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    exact ⟨max_le_max hab.1 (h.rviewOf x), max_le_max hab.2 (h.wviewOf x)⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩

private theorem map_joinViews_dom {t t' : Thread I} (h : t.Dom t') : ∀ (rss : List (List I.RegId)) (i : Nat) (p q : View × View),
    (rss.map t.joinViews)[i]? = some p → (rss.map t'.joinViews)[i]? = some q → p.1 ≤ q.1 ∧ p.2 ≤ q.2
  | [], _, _, _, hp, _ => by simp at hp
  | rs :: rss, 0, p, q, hp, hq => by
    simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hp hq
    subst hp hq
    exact joinViews_dom h rs
  | _ :: rss, i + 1, p, q, hp, hq => map_joinViews_dom h rss i p q hp hq

/-- The per-instruction views of dominated threads are dominated. -/
theorem instrViews_dom {t t' : Thread I} (h : t.Dom t') (d : InstrDeps I.RegId) :
    (instrViews t d).Dom (instrViews t' d) := by
  have ha := joinViews_dom h d.addrRegs
  have hd := joinViews_dom h d.dataRegs
  have hc := joinViews_dom h d.condRegs
  have hdv : (if d.dataRegsPer.isEmpty = true then t.joinViews d.dataRegs else (0, 0)).1 ≤
      (if d.dataRegsPer.isEmpty = true then t'.joinViews d.dataRegs else (0, 0)).1 ∧
      (if d.dataRegsPer.isEmpty = true then t.joinViews d.dataRegs else (0, 0)).2 ≤
      (if d.dataRegsPer.isEmpty = true then t'.joinViews d.dataRegs else (0, 0)).2 := by
    split
    · exact hd
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨ha.1, ha.2, hdv.1, hdv.2, hc.2, ?_, map_joinViews_dom h d.dataRegsPer⟩
  show (d.dataRegsPer.map t.joinViews).length = (d.dataRegsPer.map t'.joinViews).length
  simp

theorem zip_fold_dom : ∀ (rs : List I.RegId) (xs ys : List View) (a b : Thread I), ListLe xs ys → a.Dom b →
    ((rs.zip xs).foldl (fun t (rv : I.RegId × View) => t.setRegView rv.1 rv.2 rv.2) a).Dom
      ((rs.zip ys).foldl (fun t (rv : I.RegId × View) => t.setRegView rv.1 rv.2 rv.2) b)
  | [], _, _, _, _, _, hab => by simpa using hab
  | _ :: _, [], [], _, _, _, hab => by simpa using hab
  | r :: rs, x :: xs, y :: ys, a, b, h, hab => by
    cases h with
    | cons hxy h =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      exact zip_fold_dom rs xs ys _ _ h (hab.setRegView r hxy hxy)

/-- **`finishInstr` on dominated threads, contexts and instruction views.** -/
theorem finishInstr_dom {t t' : Thread I} {d : InstrDeps I.RegId} {iv iv' : InstrViews} {st : I.State}
    {c c' : Ctx} (h : t.Dom t') (hc : c.Dom c') (hiv : iv.Dom iv') :
    ∀ th' ∈ finishInstr t' d iv' st c', ∃ th ∈ finishInstr t d iv st c, th.Dom th' := by
  intro th' hth'
  have hload := hc.loadViews.foldl_max (Nat.le_refl 0)
  have hlen : (d.loadDefs.length == c.loadViews.length) = (d.loadDefs.length == c'.loadViews.length) := by
    rw [hc.loadViews.length_eq]
  have hinR : (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW) ≤
      (if d.isPick then max iv'.addrR iv'.dataR else max (max iv'.addrR iv'.dataR) iv'.condW) := by
    split
    · exact max_le_max hiv.addrR hiv.dataR
    · exact max_le_max (max_le_max hiv.addrR hiv.dataR) hiv.condW
  have hinW := max_le_max (max_le_max hiv.addrW hiv.dataW) hiv.condW
  have h1 : Thread.Dom { t with st, views := c.views, prom := c.prom } { t' with st, views := c'.views, prom := c'.prom } :=
    ⟨rfl, h.rview, h.wview, hc.views, hc.prom⟩
  have h2 : Thread.Dom
      (d.statusDefs.foldl (fun t r => t.setRegView r c.succView c.succView)
        (d.defs.foldl (fun t r => t.setRegView r
          (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW)
          (max (max iv.addrW iv.dataW) iv.condW)) { t with st, views := c.views, prom := c.prom }))
      (d.statusDefs.foldl (fun t r => t.setRegView r c'.succView c'.succView)
        (d.defs.foldl (fun t r => t.setRegView r
          (if d.isPick then max iv'.addrR iv'.dataR else max (max iv'.addrR iv'.dataR) iv'.condW)
          (max (max iv'.addrW iv'.dataW) iv'.condW)) { t' with st, views := c'.views, prom := c'.prom })) := by
    apply foldl_rel Thread.Dom
    · intro a b x hab; exact hab.setRegView x hc.succView hc.succView
    · apply foldl_rel Thread.Dom _ _ _ _ _ _ h1
      intro a b x hab; exact hab.setRegView x hinR hinW
  have finish : ∀ a b : Thread I, a.Dom b →
      Thread.Dom (if d.isBranch then { a with views := { a.views with vCAP := max a.views.vCAP iv.condW } } else a)
        (if d.isBranch then { b with views := { b.views with vCAP := max b.views.vCAP iv'.condW } } else b) := by
    intro a b hab
    split
    · exact ⟨hab.st, hab.rview, hab.wview, hab.views.setVCAP (max_le_max hab.views.vCAP hiv.condW), hab.prom⟩
    · exact hab
  have h3 : ∀ a b : Thread I, a.Dom b → Thread.Dom
      (if d.loadDefs.length == c.loadViews.length then
        (d.loadDefs.zip c.loadViews).foldl (fun t (r, v) => t.setRegView r v v) a
      else d.loadDefs.foldl (fun t r => t.setRegView r (c.loadViews.foldl max 0) (c.loadViews.foldl max 0)) a)
      (if d.loadDefs.length == c'.loadViews.length then
        (d.loadDefs.zip c'.loadViews).foldl (fun t (r, v) => t.setRegView r v v) b
      else d.loadDefs.foldl (fun t r => t.setRegView r (c'.loadViews.foldl max 0) (c'.loadViews.foldl max 0)) b) := by
    intro a b hab
    rw [← hlen]
    split
    · exact zip_fold_dom _ _ _ _ _ hc.loadViews hab
    · apply foldl_rel Thread.Dom _ _ _ _ _ _ hab
      intro a b x hab; exact hab.setRegView x hload hload
  have h4 : ∀ a b : Thread I, a.Dom b → Thread.Dom
      (d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r) (max (t.wviewOf r) (c.loadViews.foldl max 0))) a)
      (d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r) (max (t.wviewOf r) (c'.loadViews.foldl max 0))) b) := by
    intro a b hab
    apply foldl_rel Thread.Dom _ _ _ _ _ _ hab
    intro a b x hab; exact hab.setRegView x (hab.rviewOf x) (max_le_max (hab.wviewOf x) hload)
  simp only [finishInstr] at hth' ⊢
  rw [hc.rmwWrote]
  split at hth'
  · rename_i hcw
    simp only [hcw, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hth' ⊢
    rcases hth' with rfl | rfl
    · exact ⟨_, .inl rfl, finish _ _ (h4 _ _ h2)⟩
    · exact ⟨_, .inr rfl, finish _ _ (h3 _ _ h2)⟩
  · rename_i hcw
    simp only [hcw, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hth' ⊢
    subst hth'
    exact ⟨_, rfl, finish _ _ (h3 _ _ h2)⟩

/-! ## One instruction, a run, the cut -/

/-- **An instruction replays below**: an instruction of the dominating thread
is matched by an instruction of the dominated one, against the same memory,
with the same resulting memory and a dominated resulting thread. -/
theorem stepOne_dom (A : Arch) {tid : Nat} {t t' : Thread I} {mem : Memory} (h : t.Dom t')
    {outs' : List (Except String (Outcome I))} (hstep : stepOne A t' tid mem = some outs')
    {o' : Outcome I} (ho : .ok o' ∈ outs') :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.Dom o'.thread ∧ o.mem = o'.mem := by
  unfold stepOne at hstep ⊢
  rw [h.st]
  cases hex : I.exec t'.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs' := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c2'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th', hth', rfl⟩ := ho
      have hiv := instrViews_dom h (I.deps t'.st)
      have hc : Ctx.Dom { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t'.st)] }
          { views := t'.views, prom := t'.prom, mem, log := [.instr tid (I.showInstr t'.st)] } :=
        ⟨h.views, h.prom, rfl, .nil, Nat.le_refl _, rfl, rfl⟩
      obtain ⟨c2, hr', hd2⟩ := runTree_dom A tid hiv tree _ _ st c2' hc hr
      obtain ⟨th, hth, hdom⟩ := finishInstr_dom h hd2 hiv th' hth'
      exact ⟨_, _, rfl, List.mem_flatMap.mpr ⟨.ok (st, c2), hr', List.mem_map.mpr ⟨th, hth, rfl⟩⟩, hdom, hd2.mem⟩

/-- **A solo step replays below.** -/
theorem _root_.Kraken.Promising.ThreadStep.dom {A : Arch} {tid : Nat} {t t' : Thread I} {mem : Memory} {q' : Thread I × Memory}
    (h : t.Dom t') (hs : ThreadStep A tid (t', mem) q') :
    ∃ q, ThreadStep A tid (t, mem) q ∧ q.1.Dom q'.1 ∧ q.2 = q'.2 := by
  obtain ⟨outs', o', hstep, ho, rfl⟩ := hs
  obtain ⟨outs, o, hstep', ho', hd, hm⟩ := stepOne_dom A h hstep ho
  exact ⟨(o.thread, o.mem), ⟨outs, o, hstep', ho', rfl⟩, hd, hm⟩

/-- **A solo run replays below**, step for step. -/
theorem _root_.Kraken.Promising.Live.ThreadNPn.dom {A : Arch} {tid : Nat} :
    ∀ {n : Nat} {p' q' : Thread I × Memory}, ThreadNPn A tid n p' q' →
      ∀ p : Thread I × Memory, p.1.Dom p'.1 → p.2 = p'.2 →
        ∃ q, ThreadNPn A tid n p q ∧ q.1.Dom q'.1 ∧ q.2 = q'.2 := by
  intro n p' q' h
  induction h with
  | refl n p' => intro p hd hm; exact ⟨p, .refl _ _, hd, hm⟩
  | @step n p' q' r' hs _ ih =>
    intro p hd hm
    obtain ⟨t, mem⟩ := p
    obtain ⟨t', mem'⟩ := p'
    simp only at hd hm
    subst hm
    obtain ⟨q, hs', hdq, hmq⟩ := hs.dom hd
    obtain ⟨r, hr, hdr, hmr⟩ := ih q hdq hmq
    exact ⟨r, .step hs' hr, hdr, hmr⟩

/-- A certification of the dominating thread is one of the dominated. -/
theorem _root_.Kraken.Promising.Live.CertOkN.of_dom {A : Arch} {tid n : Nat} {t t' : Thread I} {mem : Memory}
    (h : t.Dom t') (hc : CertOkN A tid t' mem n) : CertOkN A tid t mem n := by
  obtain ⟨t'', mem'', hr, hp⟩ := hc
  obtain ⟨⟨u, memu⟩, hr', hd, -⟩ := hr.dom (t, mem) h rfl
  exact ⟨u, memu, hr', hd.prom.trans hp⟩

theorem _root_.Kraken.Promising.Live.ThreadNPn.trans {A : Arch} {tid : Nat} {n m : Nat} {p q r : Thread I × Memory}
    (h₁ : ThreadNPn A tid n p q) (h₂ : ThreadNPn A tid m q r) : ThreadNPn A tid (n + m) p r := by
  induction h₁ with
  | refl n p => exact h₂.mono (Nat.le_add_left _ _)
  | @step n p q r' hs _ ih => exact (ThreadNPn.step hs (ih h₂)).mono (by omega)

/-- **The iteration cut.** A certifying run `p →ᵃ q →ᵇ q' →ᶜ r` whose two
intermediate points have the same memory and `q ≼ q'` (same `st`, promises,
lower views) is matched by a certifying run of length `a + c` from `p`: the
loop `q →ᵇ q'` is cut out and `q'`'s continuation replays from `q`. -/
theorem _root_.Kraken.Promising.Live.ThreadNPn.cut {A : Arch} {tid : Nat} {a b c : Nat} {p q q' r : Thread I × Memory}
    (h₁ : ThreadNPn A tid a p q) (_h₂ : ThreadNPn A tid b q q') (hd : q.1.Dom q'.1) (hm : q.2 = q'.2)
    (h₃ : ThreadNPn A tid c q' r) (hr : r.1.prom = []) :
    ∃ r', ThreadNPn A tid (a + c) p r' ∧ r'.1.prom = [] := by
  obtain ⟨r', hr', hdr, -⟩ := h₃.dom q hd hm
  exact ⟨r', h₁.trans hr', hdr.prom.trans hr⟩

/-! ## Exact-length runs and the bound from cuts -/

/-- Solo runs of exactly `n` instructions (`ThreadNPn` allows fewer). -/
inductive _root_.Kraken.Promising.Live.ThreadRun (A : Arch) (tid : Nat) : Nat → Thread I × Memory → Thread I × Memory → Prop
  | refl (p : Thread I × Memory) : ThreadRun A tid 0 p p
  | step {n : Nat} {p q r : Thread I × Memory} : ThreadStep A tid p q → ThreadRun A tid n q r →
      ThreadRun A tid (n + 1) p r

theorem _root_.Kraken.Promising.Live.ThreadRun.toNPn {A : Arch} {tid n : Nat} {p q : Thread I × Memory}
    (h : ThreadRun A tid n p q) : ThreadNPn A tid n p q := by
  induction h with
  | refl p => exact .refl _ _
  | step hs _ ih => exact .step hs ih

/-- A run of at most `n` instructions is a run of exactly `m ≤ n`. -/
theorem _root_.Kraken.Promising.Live.ThreadNPn.toRun {A : Arch} {tid n : Nat} {p q : Thread I × Memory}
    (h : ThreadNPn A tid n p q) : ∃ m, m ≤ n ∧ ThreadRun A tid m p q := by
  induction h with
  | refl n p => exact ⟨0, Nat.zero_le _, .refl _⟩
  | step hs _ ih =>
    obtain ⟨m, hm, hr⟩ := ih
    exact ⟨m + 1, by omega, .step hs hr⟩

/-- **The bound from cuts** (the per-program interface of the iteration
cut). If every certifying run of the thread longer than `F` splits as
`p →ᵃ q →ᵇ q' →ᶜ r` with a non-empty middle segment, the same memory at `q`
and `q'`, and `q ≼ q'`, then every certification is within `F`. -/
theorem _root_.Kraken.Promising.Live.CertOkN.bound_of_cuts {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory} (F : Nat)
    (hcut : ∀ (n : Nat) (r : Thread I × Memory), ThreadRun A tid n (t, mem) r → r.1.prom = [] → F < n →
      ∃ (a b c : Nat) (q q' : Thread I × Memory), a + b + c = n ∧ 0 < b ∧ ThreadRun A tid a (t, mem) q ∧
        ThreadRun A tid b q q' ∧ ThreadRun A tid c q' r ∧ q.1.Dom q'.1 ∧ q.2 = q'.2)
    {n : Nat} (h : CertOkN A tid t mem n) : CertOkN A tid t mem F := by
  suffices key : ∀ (m : Nat) (r : Thread I × Memory), ThreadRun A tid m (t, mem) r → r.1.prom = [] →
      CertOkN A tid t mem F by
    obtain ⟨t', mem', hr, hp⟩ := h
    obtain ⟨m, -, hr⟩ := hr.toRun
    exact key m (t', mem') hr hp
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro r hr hp
    by_cases hm : m ≤ F
    · exact ⟨r.1, r.2, hr.toNPn.mono hm, hp⟩
    · obtain ⟨a, b, c, q, q', hn, hb, h₁, h₂, h₃, hd, hmem⟩ := hcut m r hr hp (Nat.lt_of_not_le hm)
      obtain ⟨r', hrr, hpr⟩ := h₁.toNPn.cut h₂.toNPn hd hmem h₃.toNPn hp
      obtain ⟨k, hk, hrk⟩ := hrr.toRun
      exact ih k (by omega) r' hrk hpr

/-- **The bound from shorter runs**: if every certifying run longer than `F`
has a shorter certifying run beside it, every certification is within `F`
(`bound_of_cuts` without the shape of the shortening). -/
theorem _root_.Kraken.Promising.Live.CertOkN.bound_of_shorter {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory} (F : Nat)
    (hsh : ∀ (n : Nat) (r : Thread I × Memory), ThreadRun A tid n (t, mem) r → r.1.prom = [] → F < n →
      ∃ m, m < n ∧ CertOkN A tid t mem m)
    {n : Nat} (h : CertOkN A tid t mem n) : CertOkN A tid t mem F := by
  suffices key : ∀ (m : Nat) (r : Thread I × Memory), ThreadRun A tid m (t, mem) r → r.1.prom = [] →
      CertOkN A tid t mem F by
    obtain ⟨t', mem', hr, hp⟩ := h
    obtain ⟨m, -, hr⟩ := hr.toRun
    exact key m (t', mem') hr hp
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro r hr hp
    by_cases hm : m ≤ F
    · exact ⟨r.1, r.2, hr.toNPn.mono hm, hp⟩
    · obtain ⟨m', hm', t', mem', hr', hp'⟩ := hsh m r hr hp (Nat.lt_of_not_le hm)
      obtain ⟨k, hk, hrk⟩ := hr'.toRun
      exact ih k (by omega) (t', mem') hrk hp'

/-! ## Decomposing an instruction, and the register views of simple
instructions -/

/-- An outcome of `stepOne`, decomposed: a run of the instruction's tree and
`finishInstr` on its final context. -/
theorem stepOne_fi (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    ∃ tree st c', I.exec t.st = some tree ∧
      .ok (st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree ∧
      o.thread ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st c' ∧ o.mem = c'.mem := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      exact ⟨tree, st, c', rfl, hr, hth, rfl⟩

/-- The converse: a run of the tree finished by `finishInstr` is an outcome. -/
theorem stepOne_of_fi (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {tree : EvTree I.State}
    (hex : I.exec t.st = some tree) {st : I.State} {c' : Ctx}
    (hr : .ok (st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree) {th : Thread I}
    (hth : th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st c') :
    ∃ outs, stepOne A t tid mem = some outs ∧
      .ok { thread := th, mem := c'.mem, promisedNow := c'.promisedNow, log := c'.log } ∈ outs := by
  refine ⟨_, by unfold stepOne; rw [hex]; rfl, ?_⟩
  rw [List.mem_flatMap]
  exact ⟨.ok (st, c'), hr, List.mem_map.mpr ⟨th, hth, rfl⟩⟩

/-- `finishInstr` with no destination register: register views unchanged. -/
theorem finishInstr_regs_nil {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    (hd : d.defs = []) (hl : d.loadDefs = []) (hs : d.statusDefs = []) {th : Thread I}
    (h : th ∈ finishInstr t d iv st c) : th.rview = t.rview ∧ th.wview = t.wview := by
  unfold finishInstr at h
  simp only [hd, hl, hs, List.foldl_nil, List.zip_nil_left, List.length_nil] at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> split <;> (try split) <;> exact ⟨rfl, rfl⟩
  · simp only [List.mem_singleton] at h
    subst h
    split <;> (try split) <;> exact ⟨rfl, rfl⟩

/-- `finishInstr` with one ALU destination, no load and no branch: the
destination gets the inputs' joins, nothing else changes. -/
theorem finishInstr_def1 {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {r : I.RegId} (hd : d.defs = [r]) (hl : d.loadDefs = []) (hs : d.statusDefs = []) (hc : d.casLike = false)
    (hb : d.isBranch = false) (hp : d.isPick = false) {th : Thread I} (h : th ∈ finishInstr t d iv st c) :
    th = { t with st := st, views := c.views, prom := c.prom }.setRegView r
      (max (max iv.addrR iv.dataR) iv.condW) (max (max iv.addrW iv.dataW) iv.condW) := by
  unfold finishInstr at h
  simp only [hd, hl, hs, hc, hb, hp, List.foldl_nil, List.foldl_cons, List.zip_nil_left, List.length_nil,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.mem_singleton, ite_self] at h
  exact h

/-- `finishInstr` with one load destination, no write performed and no
branch: the destination gets the load's post-view, nothing else changes. -/
theorem finishInstr_load1 {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {r : I.RegId} (hd : d.defs = []) (hl : d.loadDefs = [r]) (hs : d.statusDefs = []) (hw : c.rmwWrote = false)
    (hb : d.isBranch = false) {ν : View} (hlv : c.loadViews = [ν]) {th : Thread I}
    (h : th ∈ finishInstr t d iv st c) :
    th = { t with st := st, views := c.views, prom := c.prom }.setRegView r ν ν := by
  unfold finishInstr at h
  simp only [hd, hl, hs, hw, hb, hlv, List.foldl_nil, List.foldl_cons, List.zip_cons_cons, List.zip_nil_right,
    List.length_cons, List.length_nil, Bool.and_false, Bool.false_eq_true, ↓reduceIte, List.mem_singleton,
    beq_self_eq_true] at h
  exact h

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readNext_loadViews (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (t : Time) (v : Val) :
    (readNext A iv c k xcl l noRet t v).loadViews =
      c.loadViews ++ [max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) t)] := rfl

theorem readNext_rmwWrote (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (t : Time) (v : Val) :
    (readNext A iv c k xcl l noRet t v).rmwWrote = c.rmwWrote := rfl

/-- A load's run: the read it made. -/
theorem run_load_ctx {σ : Type} {c c' : Ctx} {k : LoadKind} {l : Loc} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.load k false l fun v => .done (f v))) :
    ∃ t v, (t, v, c') ∈ readSuccs A iv c k false l false ∧ st = f v := by
  simp only [runTree, List.mem_flatMap] at h
  obtain ⟨⟨t, v, c1⟩, hx, h⟩ := h
  obtain ⟨rfl, rfl⟩ := run_done A tid iv h
  exact ⟨t, v, hx, rfl⟩

/-- A conditional RMW's run (no RMW fence): the read it made; if the
operation declines, the read's context is the final one. -/
theorem run_rmwo_ctx {σ : Type} (hA : A.rmwFence = false) {c c' : Ctx} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.rmw k false l op fun v => .done (f v))) :
    ∃ tr old c1, (tr, old, c1) ∈ readSuccs A iv c (A.rmwKind k).loadKind false l false ∧ st = f old ∧
      (op old = none → c' = c1) := by
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at h
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := h
  simp only at h
  split at h
  · rename_i hop
    obtain ⟨rfl, hc⟩ := run_done A tid iv h
    exact ⟨tr, old, c1, hx, rfl, fun _ => hc⟩
  · rename_i new hop
    rw [List.mem_flatMap] at h
    obtain ⟨c2, -, h⟩ := h
    simp only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨tr, old, c1, hx, rfl, fun h0 => by rw [h0] at hop; cases hop⟩

end Rules

/-! ## Views grow along a step -/

/-- **Scalar and coherence views grow** (`a ⊑ b`). -/
structure _root_.Kraken.Promising.Views.Grow (a b : Views) : Prop where
  coh : ∀ l, a.getCoh l ≤ b.getCoh l
  vrNew : a.vrNew ≤ b.vrNew
  vrOld : a.vrOld ≤ b.vrOld
  vrOldNR : a.vrOldNR ≤ b.vrOldNR
  vwNew : a.vwNew ≤ b.vwNew
  vwOld : a.vwOld ≤ b.vwOld
  vwOldNT : a.vwOldNT ≤ b.vwOldNT
  vCAP : a.vCAP ≤ b.vCAP
  vRel : a.vRel ≤ b.vRel

theorem _root_.Kraken.Promising.Views.Grow.refl (a : Views) : a.Grow a :=
  ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
   Nat.le_refl _, Nat.le_refl _⟩

theorem _root_.Kraken.Promising.Views.Grow.trans {a b c : Views} (h₁ : a.Grow b) (h₂ : b.Grow c) : a.Grow c :=
  ⟨fun l => Nat.le_trans (h₁.coh l) (h₂.coh l), Nat.le_trans h₁.vrNew h₂.vrNew, Nat.le_trans h₁.vrOld h₂.vrOld,
   Nat.le_trans h₁.vrOldNR h₂.vrOldNR, Nat.le_trans h₁.vwNew h₂.vwNew, Nat.le_trans h₁.vwOld h₂.vwOld,
   Nat.le_trans h₁.vwOldNT h₂.vwOldNT, Nat.le_trans h₁.vCAP h₂.vCAP, Nat.le_trans h₁.vRel h₂.vRel⟩

/-- Grown views with the same forwarding table and pending exclusive are
dominated. -/
theorem _root_.Kraken.Promising.Views.Grow.dom {a b : Views} (h : a.Grow b) (hf : a.fwdb = b.fwdb) (hx : a.xclb = b.xclb) :
    a.Dom b :=
  ⟨h.coh, h.vrNew, h.vrOld, h.vrOldNR, h.vwNew, h.vwOld, h.vwOldNT, h.vCAP, h.vRel,
   fun l => by simp only [Views.getFwd, hf]; exact FwdDom.refl _, hx ▸ XclbDom.refl _⟩

/-- **One context step of an event tree**: views grow, memory extends, and
without a write (the same `|M|` and the same number of promises) the
forwarding table and the promises are unchanged. -/
structure _root_.Kraken.Promising.Ctx.Grow (c c' : Ctx) : Prop where
  views : c.views.Grow c'.views
  last : c.mem.last ≤ c'.mem.last
  noWrite : c'.mem.last = c.mem.last → c'.prom.length ≤ c.prom.length ∧
    (c'.prom.length = c.prom.length → c'.views.fwdb = c.views.fwdb ∧ c'.prom = c.prom)

theorem _root_.Kraken.Promising.Ctx.Grow.refl (c : Ctx) : c.Grow c :=
  ⟨Views.Grow.refl _, Nat.le_refl _, fun _ => ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩⟩

theorem _root_.Kraken.Promising.Ctx.Grow.trans {a b c : Ctx} (h₁ : a.Grow b) (h₂ : b.Grow c) : a.Grow c := by
  refine ⟨h₁.views.trans h₂.views, Nat.le_trans h₁.last h₂.last, fun hl => ?_⟩
  have hb : b.mem.last = a.mem.last := by have := h₁.last; have := h₂.last; omega_t
  have hc : c.mem.last = b.mem.last := by omega_t
  obtain ⟨l1, f1⟩ := h₁.noWrite hb
  obtain ⟨l2, f2⟩ := h₂.noWrite hc
  refine ⟨Nat.le_trans l2 l1, fun he => ?_⟩
  obtain ⟨g1, p1⟩ := f1 (by omega)
  obtain ⟨g2, p2⟩ := f2 (by omega)
  exact ⟨g2.trans g1, p2.trans p1⟩

/-- A step that keeps memory, promises and the forwarding table. -/
theorem _root_.Kraken.Promising.Ctx.Grow.of_eq {c c' : Ctx} (hv : c.views.Grow c'.views) (hm : c'.mem = c.mem)
    (hp : c'.prom = c.prom) (hf : c'.views.fwdb = c.views.fwdb) : c.Grow c' :=
  ⟨hv, by rw [hm]; exact Nat.le_refl _, fun _ => ⟨by rw [hp]; exact Nat.le_refl _, fun _ => ⟨hf, hp⟩⟩⟩

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_grow {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv c k xcl l noRet) : c.Grow x.2.2 := by
  obtain ⟨t, v, rfl, -, -, -, -⟩ := (mem_readSuccs A).mp hx
  refine .of_eq ⟨fun l' => Views.getCoh_le_setCoh _ _ _ _, ?_, ?_, ?_, ?_, Nat.le_refl _, Nat.le_refl _, ?_,
    Nat.le_refl _⟩ rfl rfl rfl
  · show c.views.vrNew ≤ (if (A.loadKind k).isAcquire = true then max c.views.vrNew _ else c.views.vrNew)
    split <;> omega_t
  · show c.views.vrOld ≤ (if noRet = true then c.views.vrOld else max c.views.vrOld _)
    split <;> omega_t
  · show c.views.vrOldNR ≤ (if noRet = true then max c.views.vrOldNR _ else c.views.vrOldNR)
    split <;> omega_t
  · show c.views.vwNew ≤ (if (A.loadKind k).isAcquire = true then max c.views.vwNew _ else c.views.vwNew)
    split <;> omega_t
  · show c.views.vCAP ≤ max c.views.vCAP iv.addrW
    omega_t

theorem afterWrite_grow {xr : View} (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time) (νfwd : View) (ful : Bool) :
    c.views.Grow (afterWrite A iv c k xcl l v t νfwd ful xr).views := by
  refine ⟨fun l' => ?_, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
  · rw [afterWrite_getCoh]
    split
    · rename_i e; subst e; omega_t
    · exact Nat.le_refl _
  · show c.views.vwOld ≤ (if (k == StoreKind.nt) = true then c.views.vwOld else max c.views.vwOld t)
    split <;> omega_t
  · show c.views.vwOldNT ≤ (if (k == StoreKind.nt) = true then max c.views.vwOldNT t else c.views.vwOldNT)
    split <;> omega_t
  · show c.views.vCAP ≤ max c.views.vCAP iv.addrW
    omega_t
  · show c.views.vRel ≤ (if (k == StoreKind.rel) = true then max c.views.vRel t else c.views.vRel)
    split <;> omega_t

theorem writeSuccs_grow {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : c.Grow c' := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, ht, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨afterWrite_grow A iv _ _ _ _ _ _ _ _, Nat.le_refl _, fun _ => ⟨?_, fun he => ?_⟩⟩
    · show (c.prom.erase t).length ≤ c.prom.length
      exact List.length_erase_le
    · exfalso
      have : (c.prom.erase t).length = c.prom.length := he
      rw [List.length_erase_of_mem ht] at this
      have := List.length_pos_of_mem ht
      omega
  · have hg := afterWrite_grow A iv
      { c with
        mem := (c.mem.append { loc := l, val := v, tid }).1
        prom := c.prom ++ [c.mem.last + 1]
        promisedNow := c.promisedNow ++ [({ loc := l, val := v, tid }, max (writePre A iv c k extra) (c.views.getCoh l))] }
      (A.storeKind k) xcl l v (c.mem.last + 1) (max iv.addrR (max iv.dataR extra)) false (xr := xr)
    refine ⟨hg, ?_, fun he => ?_⟩
    · show c.mem.last ≤ (c.mem.append _).1.last
      rw [Memory.last_append]; omega_t
    · exfalso
      have : (c.mem.append { loc := l, val := v, tid }).1.last = c.mem.last := he
      rw [Memory.last_append] at this
      omega_t

theorem fenceStep_views_grow (c : Ctx) (k : FenceKind) : c.views.Grow (fenceStep c k).views := by
  cases k
  · exact ⟨fun _ => Nat.le_refl _, Nat.le_max_left _ _, Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _,
      Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨fun _ => Nat.le_refl _, Nat.le_max_left _ _, Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _,
      Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _,
      Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨fun _ => Nat.le_refl _, Nat.le_max_left _ _, Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _,
      Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨fun _ => Nat.le_refl _, Nat.le_max_left _ _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem fenceStep_grow (c : Ctx) (k : FenceKind) : c.Grow (fenceStep c k) :=
  .of_eq (fenceStep_views_grow c k) (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1
    (fenceStep_fields c k).2.2.2.1

theorem fenceOpt_grow (c : Ctx) (b : Bool) (k : FenceKind) : c.Grow (if b then fenceStep c k else c) := by
  cases b
  · exact .refl c
  · exact fenceStep_grow c k

theorem rmwPost_grow (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) : c.Grow (rmwPost A k noRet l c) := by
  unfold rmwPost
  split
  · exact .of_eq ⟨fun _ => Nat.le_refl _, Nat.le_max_left _ _, Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _,
      Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩ rfl rfl rfl
  · exact .of_eq (Views.Grow.refl _) rfl rfl rfl

theorem xclFail_grow (c : Ctx) (l : Loc) :
    c.Grow { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
  .of_eq ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩ rfl rfl rfl

/-- **Along an event tree, views grow** (and without a write the forwarding
table is unchanged). -/
theorem runTree_grow {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → c.Grow c' := by
  induction tree with
  | done s =>
    intro c s' c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact .refl _
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i c s c' h
  | load k xcl l ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact (readSuccs_grow A iv hx).trans (ih x.2.1 x.2.2 s c' h)
  | store k xcl l v ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (writeSuccs_grow A tid _ hc0).trans (ih true c0 s c' h)
    · rw [List.mem_ite_nil_right] at h
      exact (xclFail_grow c l).trans (ih false _ s c' h.2)
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (fenceStep_grow c k).trans (ih () _ s c' h)
  | rmw k noRet l op ret ih =>
    intro c s c' h
    simp only [runTree] at h
    have h1 := fenceOpt_grow c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := h1.trans (readSuccs_grow A iv h2)
    simp only at h
    split at h
    · exact (h12.trans (fenceOpt_grow c2 A.rmwFence .sy)).trans (ih old _ s c' h)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      refine ((h12.trans (writeSuccs_grow A tid _ hc3)).trans ?_).trans (ih old _ s c' h)
      exact (rmwPost_grow A c3 k noRet l).trans (fenceOpt_grow _ A.rmwFence .sy)

end Rules

private theorem foldl_views {α : Type} (f : Thread I → α → Thread I)
    (hf : ∀ t a, (f t a).views = t.views) : ∀ (l : List α) (t : Thread I), (l.foldl f t).views = t.views
  | [], _ => rfl
  | a :: l, t => (foldl_views f hf l (f t a)).trans (hf t a)

/-- Close `(l₁.foldl f₁ (… (lₙ.foldl fₙ t))).views = k` where each `fᵢ` only
sets register views (as `LiveWfProm.lean`). -/
local macro "views_foldl" : tactic =>
  `(tactic| (repeat (refine (foldl_views _ ?_ _ _).trans ?_; (intro t a; first | rfl | (cases a; rfl)))
             try rfl))

/-- `finishInstr` keeps the context's views but for `vCAP`, which it may
raise (the fields other than `vCAP`, and `vCAP ≤`). -/
theorem finishInstr_views {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {th : Thread I} (h : th ∈ finishInstr t d iv st c) :
    th.views = c.views ∨ th.views = { c.views with vCAP := max c.views.vCAP iv.condW } := by
  have key : ∀ t' : Thread I, t'.views = c.views →
      (if d.isBranch then { t' with views := { t'.views with vCAP := max t'.views.vCAP iv.condW } } else t').views = c.views ∨
      (if d.isBranch then { t' with views := { t'.views with vCAP := max t'.views.vCAP iv.condW } } else t').views =
        { c.views with vCAP := max c.views.vCAP iv.condW } := by
    intro t' ht'
    split
    · right; simp only [ht']
    · left; exact ht'
  unfold finishInstr at h
  simp only at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · refine key _ ?_
      views_foldl
    · refine key _ ?_
      split <;> views_foldl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    refine key _ ?_
    split <;> views_foldl

/-- **One instruction: views grow**, memory extends, and without a write
(the same `|M|` and the same number of promises) the forwarding table and
the promises are unchanged. The sanity check of `Thread.Dom`: no instruction
lowers a scalar, coherence or forwarding view. (Register views are reset by
the instructions that write them and are not covered.) -/
theorem stepOne_grow (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    t.views.Grow o.thread.views ∧ mem.last ≤ o.mem.last ∧
      (o.mem.last = mem.last → o.thread.prom.length ≤ t.prom.length ∧
        (o.thread.prom.length = t.prom.length → o.thread.views.fwdb = t.views.fwdb ∧ o.thread.prom = t.prom)) := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hg := runTree_grow A tid _ tree _ st c' hr
      have hp : th.prom = c'.prom := (finishInstr_relKey hth).1
      have hv : c'.views.Grow th.views ∧ th.views.fwdb = c'.views.fwdb := by
        rcases finishInstr_views hth with h | h <;> rw [h]
        · exact ⟨Views.Grow.refl _, rfl⟩
        · exact ⟨⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
            Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _, Nat.le_refl _⟩, rfl⟩
      refine ⟨hg.views.trans hv.1, hg.last, fun hl => ?_⟩
      obtain ⟨l1, f1⟩ := hg.noWrite hl
      rw [hp]
      exact ⟨l1, fun he => let ⟨a, b⟩ := f1 he; ⟨hv.2.trans a, b⟩⟩

/-! ## No load exclusive: the pending-exclusive slot stays empty -/

/-- The tree performs no load exclusive. -/
def _root_.Kraken.Promising.EvTree.NoXclLoad {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).NoXclLoad
  | .load _ xcl _ ret => xcl = false ∧ ∀ v, (ret v).NoXclLoad
  | .store _ _ _ _ ret => ∀ b, (ret b).NoXclLoad
  | .fence _ ret => ∀ u, (ret u).NoXclLoad
  | .rmw _ _ _ _ ret => ∀ v, (ret v).NoXclLoad

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem fenceStep_xclb (c : Ctx) (k : FenceKind) : (fenceStep c k).views.xclb = c.views.xclb := by
  cases k <;> rfl

theorem readSuccs_xclb {c : Ctx} {k : LoadKind} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv c k false l noRet) : x.2.2.views.xclb = c.views.xclb := by
  obtain ⟨t, v, rfl, -, -, -, -⟩ := (mem_readSuccs A).mp hx
  rfl

theorem writeSuccs_xclb {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) (hc : c.views.xclb = none) :
    c'.views.xclb = none := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩ <;>
    · show (if xcl = true then none else c.views.xclb) = none
      cases xcl
      · exact hc
      · rfl

/-- Along a tree without load exclusives, an empty pending-exclusive slot
stays empty. -/
theorem runTree_xclb_none {σ : Type} (tree : EvTree σ) (hnx : tree.NoXclLoad) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → c.views.xclb = none →
      c'.views.xclb = none := by
  induction tree with
  | done s =>
    intro c s' c' h hc
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hc
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h hc
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i (hnx i) c s c' h hc
  | load k xcl l ret ih =>
    intro c s c' h hc
    obtain ⟨rfl, hnx⟩ := hnx
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact ih x.2.1 (hnx _) _ s c' h ((readSuccs_xclb A iv hx).trans hc)
  | store k xcl l v ret ih =>
    intro c s c' h hc
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact ih true (hnx true) c0 s c' h (writeSuccs_xclb A tid _ hc0 hc)
    · rw [List.mem_ite_nil_right] at h
      exact ih false (hnx false) _ s c' h.2 rfl
  | fence k ret ih =>
    intro c s c' h hc
    simp only [runTree] at h
    exact ih () (hnx ()) _ s c' h ((fenceStep_xclb c k).trans hc)
  | rmw k noRet l op ret ih =>
    intro c s c' h hc
    simp only [runTree] at h
    have h1 : (if A.rmwFence then fenceStep c .sy else c).views.xclb = none := by
      split
      · exact (fenceStep_xclb c .sy).trans hc
      · exact hc
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 : c2.views.xclb = none := (readSuccs_xclb A iv h2).trans h1
    simp only at h
    split at h
    · refine ih old (hnx old) _ s c' h ?_
      split
      · exact (fenceStep_xclb c2 .sy).trans h12
      · exact h12
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      have h3 : (rmwPost A k noRet l c3).views.xclb = none := by
        have := writeSuccs_xclb A tid iv hc3 h12
        unfold rmwPost
        split <;> exact this
      refine ih old (hnx old) _ s c' h ?_
      split
      · exact (fenceStep_xclb _ .sy).trans h3
      · exact h3

end Rules

/-- **One instruction without a load exclusive keeps the pending-exclusive
slot empty.** -/
theorem stepOne_xclb_none (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {tree : EvTree I.State}
    (hex : I.exec t.st = some tree) (hnx : tree.NoXclLoad)
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hx : t.views.xclb = none) : o.thread.views.xclb = none := by
  unfold stepOne at hstep
  rw [hex] at hstep
  have hstep' : _ = outs := Option.some.inj hstep
  subst hstep'
  rw [List.mem_flatMap] at ho
  obtain ⟨r, hr, ho⟩ := ho
  cases r with
  | error m => simp at ho
  | ok p =>
    obtain ⟨st, c'⟩ := p
    simp only [List.mem_map, Except.ok.injEq] at ho
    obtain ⟨th, hth, rfl⟩ := ho
    have h1 := runTree_xclb_none A tid _ tree hnx _ st c' hr hx
    rcases finishInstr_views hth with h | h <;> rw [h] <;> exact h1

end Kraken.Promising.Live.CertCut
