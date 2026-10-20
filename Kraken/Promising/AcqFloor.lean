/-
Machine side of Theorem 1′'s condition (3) (obligation
O6b): **acquire-type steps raise the write floor**, and **in a
live configuration every outstanding promise lies above its thread's write
floor**.

The *write floor* of a thread is `max vwNew vCAP` (`Views.wfloor`): both are
part of the pre-view of every write (`writeSuccs`), so every later write of
the thread, and in particular every later fulfilment of a promise, lies
strictly above it. `ReleasePrefix.lean` proves the `vwNew` half of the live
bound (`Config.Live.vwNew_lt`); this file adds the `vCAP` half
(`Config.Live.vCAP_lt`) and combines them (`Config.Live.wfloor_lt`).

Acquire-type events, i.e. the events after which the resource logic may let a
thread use what a message `q` carries for writing (SLR's acquire read, and
its relaxed read under `▽` discharged by a fence-acquire), all put the write
floor at or above `q` (`AcqStep.le_wfloor`):

- an acquire load (`LDAR`, `LDAPR`; x64 TSO loads are `acqPc`), and the read of
  an acquire RMW: `vwNew ≥ q` (`readSuccs_acq_vwNew`, ReleasePrefix);
- an acquire-release RMW: `vwNew ≥ coh l ≥ tw > tr` (`rmwPost`);
- a relaxed read raises `vrOld` (a `noRet` read: `vrOldNR`) to `q`
  (`readSuccs_vrOld`, `readSuccs_vrOldNR`), and `DMB LD` folds `vrOld`,
  `DMB SY` (and `mfence`, a locked RMW's `rmwFence`) folds `vrOld ⊔ vrOldNR`,
  into `vwNew` (`fenceStep_ld_vwNew`, `fenceStep_sy_vwNew`);
- a branch on a register whose view is `≥ q` (a control dependency) raises
  `vCAP` (`finishInstr`'s `branch`).

Every view involved only grows along an instruction (`runTree_vmono`,
`finishInstr_vmono`, `stepOne_vmono`), so an acquisition at any event of an
instruction bounds the floor of the thread after it, and of all later states.

No hypothesis on programs; nothing here depends on certification.
-/
import Kraken.Promising.ReleasePrefix

namespace Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- The **write floor**: every later write of the thread lies strictly above
it (both components are in every write's pre-view, `writeSuccs`). -/
def Views.wfloor (v : Views) : View := max v.vwNew v.vCAP

/-! ## A generic preservation lemma for `runTree` -/

section Generic

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- A relation on contexts that holds across every kind of context step of
`runTree` holds across every run of an event tree. -/
theorem runTree_preserves (P : Ctx → Ctx → Prop) (hrefl : ∀ c, P c c)
    (htrans : ∀ a b c, P a b → P b c → P a c)
    (hread : ∀ c k xcl l noRet (x : Time × Val × Ctx), x ∈ readSuccs A iv c k xcl l noRet → P c x.2.2)
    (hwrite : ∀ c (iv' : InstrViews) k xcl l v tr extra xr c', c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr → P c c')
    (hfence : ∀ c k, P c (fenceStep c k))
    (hxcl : ∀ (c : Ctx) l, P c { c with views := { c.views with xclb := none }, succView := 0,
                                         log := c.log ++ [.xclFail l] })
    (hpost : ∀ c k noRet l, P c (rmwPost A k noRet l c))
    {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → P c c' := by
  have hopt : ∀ c (b : Bool) k, P c (if b then fenceStep c k else c) := by
    intro c b k; cases b
    · exact hrefl c
    · exact hfence c k
  induction tree with
  | done s =>
    intro c s' c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hrefl _
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
    exact htrans _ _ _ (hread _ _ _ _ _ x hx) (ih x.2.1 x.2.2 s c' h)
  | store k xcl l v ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact htrans _ _ _ (hwrite _ _ _ _ _ _ _ _ _ _ hc0) (ih true c0 s c' h)
    · rw [List.mem_ite_nil_right] at h
      exact htrans _ _ _ (hxcl c l) (ih false _ s c' h.2)
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact htrans _ _ _ (hfence c k) (ih () _ s c' h)
  | rmw k noRet l op ret ih =>
    intro c s c' h
    simp only [runTree] at h
    have h1 := hopt c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := htrans _ _ _ h1 (hread _ _ _ _ _ _ h2)
    simp only at h
    split at h
    · exact htrans _ _ _ (htrans _ _ _ h12 (hopt c2 A.rmwFence .sy)) (ih old _ s c' h)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      refine htrans _ _ _ (htrans _ _ _ (htrans _ _ _ h12 (hwrite _ _ _ _ _ _ _ _ _ _ hc3)) ?_) (ih old _ s c' h)
      exact htrans _ _ _ (hpost c3 k noRet l) (hopt _ A.rmwFence .sy)

end Generic

/-! ## Views only grow along an instruction -/

/-- The views that bound later writes and the views that a fence-acquire
folds into them only grow. -/
structure Ctx.VMono (c c' : Ctx) : Prop where
  vwNew : c.views.vwNew ≤ c'.views.vwNew
  vCAP : c.views.vCAP ≤ c'.views.vCAP
  vrOld : c.views.vrOld ≤ c'.views.vrOld
  vrOldNR : c.views.vrOldNR ≤ c'.views.vrOldNR

theorem Ctx.VMono.refl (c : Ctx) : c.VMono c := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem Ctx.VMono.trans {a b c : Ctx} (h₁ : a.VMono b) (h₂ : b.VMono c) : a.VMono c :=
  ⟨Nat.le_trans h₁.vwNew h₂.vwNew, Nat.le_trans h₁.vCAP h₂.vCAP, Nat.le_trans h₁.vrOld h₂.vrOld,
    Nat.le_trans h₁.vrOldNR h₂.vrOldNR⟩

theorem Ctx.VMono.wfloor {c c' : Ctx} (h : c.VMono c') : c.views.wfloor ≤ c'.views.wfloor := by
  have := h.vwNew; have := h.vCAP
  simp only [Views.wfloor]; omega_t

/-- `vCAP` orders writes: it only grows, and a promise that disappears was
fulfilled above the old `vCAP` (the twin of `Ctx.WOrd` for `vwNew`). -/
structure Ctx.COrd (c c' : Ctx) : Prop where
  vCAP : c.views.vCAP ≤ c'.views.vCAP
  prom : ∀ ts ∈ c.prom, ts ∉ c'.prom → c.views.vCAP < ts

theorem Ctx.COrd.refl (c : Ctx) : c.COrd c := ⟨Nat.le_refl _, fun _ h h' => absurd h h'⟩

theorem Ctx.COrd.trans {c c' c'' : Ctx} (h₁ : c.COrd c') (h₂ : c'.COrd c'') : c.COrd c'' := by
  refine ⟨Nat.le_trans h₁.vCAP h₂.vCAP, fun ts h h'' => ?_⟩
  by_cases h' : ts ∈ c'.prom
  · exact Nat.lt_of_le_of_lt h₁.vCAP (h₂.prom ts h' h'')
  · exact h₁.prom ts h h'

theorem Ctx.COrd.of_eq {c c' : Ctx} (h1 : c.views.vCAP ≤ c'.views.vCAP) (h2 : c'.prom = c.prom) : c.COrd c' :=
  ⟨h1, fun _ h h' => absurd (h2 ▸ h) h'⟩

private theorem ite_none_left' {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rwa [ite_eq_right hp] at h

section Steps

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_shape {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    ∃ v, c.mem.read? l x.1 = some v ∧ x.2.1 = v ∧
      let k' := A.loadKind k
      let νpre := max iv.addrR (max c.views.vrNew (if k' == .acq then c.views.vRel else 0))
      let νpost := max νpre (readView A k' (c.views.getFwd l) x.1)
      x.2.2 = { c with
        views := { (c.views.setCoh l νpost) with
          vrOld := if noRet then c.views.vrOld else max c.views.vrOld νpost
          vrOldNR := if noRet then max c.views.vrOldNR νpost else c.views.vrOldNR
          vrNew := if k'.isAcquire then max c.views.vrNew νpost else c.views.vrNew
          vwNew := if k'.isAcquire then max c.views.vwNew νpost else c.views.vwNew
          vCAP := max c.views.vCAP iv.addrW
          xclb := if xcl then some (x.1, νpost, l) else c.views.xclb }
        loadViews := c.loadViews ++ [νpost], log := c.log ++ [.read l x.1 x.2.1 νpost] } := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · rename_i v hv
    have h := ite_none_left' ht
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨v, hv, rfl, rfl⟩

theorem readSuccs_vmono {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : c.VMono x.2.2 := by
  obtain ⟨v, -, -, h⟩ := readSuccs_shape A iv hx
  rw [h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> (try split) <;> omega_t

theorem readSuccs_cord {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : c.COrd x.2.2 := by
  obtain ⟨v, -, -, h⟩ := readSuccs_shape A iv hx
  rw [h]
  exact .of_eq (by simp only; omega_t) rfl

/-- A read that is not forwarded from the thread's own write raises `vrOld`
(a `noRet` read: `vrOldNR`) to the timestamp read. -/
theorem readSuccs_vrOld {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet)
    (hfw : ∀ f, c.views.getFwd l = some f → f.time ≠ x.1) :
    x.1 ≤ (if noRet then x.2.2.views.vrOldNR else x.2.2.views.vrOld) := by
  obtain ⟨v, -, -, h⟩ := readSuccs_shape A iv hx
  have hrv : x.1 ≤ readView A (A.loadKind k) (c.views.getFwd l) x.1 := by
    unfold readView
    split
    · rename_i f hf
      have := hfw f hf
      simp only [this, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact Nat.le_refl _
    · exact Nat.le_refl _
  rw [h]
  cases noRet <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega_t

theorem writeSuccs_vmono {xr : View} {c : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) :
    c.VMono c' := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [afterWrite, Views.setCoh] <;> omega_t
    · cases h
  · split at h
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [afterWrite, Views.setCoh] <;> omega_t

theorem writeSuccs_cord {xr : View} {c : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) :
    c.COrd c' := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨hc, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨-, hb, -⟩ := hc
      refine ⟨by simp only [afterWrite, Views.setCoh]; omega_t, fun ts hin hout => ?_⟩
      simp only [afterWrite] at hout
      have hts : ts = t := by
        by_cases hne : ts = t
        · exact hne
        · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
      subst hts
      omega_t
    · cases h
  · split at h
    rename_i t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨hcond, rfl⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    refine ⟨by simp only [afterWrite, Views.setCoh]; omega_t, fun ts hin hout => ?_⟩
    simp only [afterWrite] at hout
    by_cases hne : ts = t
    · subst hne; omega_t
    · exact absurd ((List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)) hout

theorem fenceStep_vCAP (c : Ctx) (k : FenceKind) : (fenceStep c k).views.vCAP = c.views.vCAP := by
  cases k <;> rfl

theorem fenceStep_vmono (c : Ctx) (k : FenceKind) : c.VMono (fenceStep c k) := by
  obtain ⟨h1, h2, -, -, -, -, -⟩ := fenceStep_fields c k
  refine ⟨?_, (fenceStep_vCAP c k).symm ▸ Nat.le_refl _, h1 ▸ Nat.le_refl _, h2 ▸ Nat.le_refl _⟩
  cases k <;> simp only [fenceStep] <;> omega_t

theorem fenceStep_cord (c : Ctx) (k : FenceKind) : c.COrd (fenceStep c k) :=
  .of_eq (Nat.le_of_eq (fenceStep_vCAP c k).symm) (fenceStep_fields c k).2.2.2.2.1

/-- `DMB LD` (`fence .ld`) folds `vrOld` into `vwNew`: a fence-acquire after
relaxed reads. -/
theorem fenceStep_ld_vwNew (c : Ctx) : c.views.vrOld ≤ (fenceStep c .ld).views.vwNew := by
  simp only [fenceStep]; omega_t

/-- `DMB SY` (`fence .sy`; x64 `mfence` and a locked RMW's `rmwFence`) folds
`vrOld` and `vrOldNR` into `vwNew`: a fence-acquire after relaxed and `noRet`
reads. -/
theorem fenceStep_sy_vwNew (c : Ctx) : max c.views.vrOld c.views.vrOldNR ≤ (fenceStep c .sy).views.vwNew := by
  simp only [fenceStep]; omega_t

theorem rmwPost_vmono (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) : c.VMono (rmwPost A k noRet l c) := by
  unfold rmwPost
  split
  · exact ⟨by simp only; omega_t, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem rmwPost_cord (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) : c.COrd (rmwPost A k noRet l c) := by
  unfold rmwPost
  split
  · exact .of_eq (Nat.le_refl _) rfl
  · exact .of_eq (Nat.le_refl _) rfl

/-- An acquire-release RMW (not `noRet`) folds the coherence view of its
location, which its write has raised to the write's timestamp, into `vwNew`. -/
theorem rmwPost_vwNew (c : Ctx) {k : RmwKind} {noRet : Bool} (l : Loc)
    (hk : (A.rmwKind k == .acqRel && !noRet) = true) : c.views.getCoh l ≤ (rmwPost A k noRet l c).views.vwNew := by
  unfold rmwPost
  simp only [hk, ↓reduceIte]
  omega_t

/-- A write raises the coherence view of its location above the message an
RMW read (`tr < t ≤ coh l`). -/
theorem writeSuccs_tr_lt_coh {c : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Time} {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv' c k xcl l v (some tr) extra) :
    tr < c'.views.getCoh l := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨hc, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨-, -, htr, -⟩ := hc
      show tr < (c.views.setCoh l t).getCoh l
      simp only [Views.getCoh_setCoh, ↓reduceIte]
      omega_t
    · cases h
  · split at h
    rename_i t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨hcond, rfl⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨-, htr, -⟩ := hcond
    show tr < (c.views.setCoh l t).getCoh l
    simp only [Views.getCoh_setCoh, ↓reduceIte]
    omega_t

theorem runTree_vmono {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → c.VMono c' :=
  runTree_preserves A tid iv Ctx.VMono Ctx.VMono.refl (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun _ _ _ _ _ _ hx => readSuccs_vmono A iv hx) (fun _ _ _ _ _ _ _ _ _ _ h => writeSuccs_vmono A tid h)
    fenceStep_vmono (fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    (fun c k noRet l => rmwPost_vmono A c k noRet l) tree

theorem runTree_cord {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → c.COrd c' :=
  runTree_preserves A tid iv Ctx.COrd Ctx.COrd.refl (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun _ _ _ _ _ _ hx => readSuccs_cord A iv hx) (fun _ _ _ _ _ _ _ _ _ _ h => writeSuccs_cord A tid h)
    fenceStep_cord (fun _ _ => .of_eq (Nat.le_refl _) rfl) (fun c k noRet l => rmwPost_cord A c k noRet l) tree

end Steps

/-! ## Acquire-type events -/

/-- **The acquire-type context steps** of an instruction, with the
timestamp `q` of the message they acquire from (O6b). -/
inductive AcqStep (A : Arch) (iv : InstrViews) : Ctx → Ctx → Time → Prop
  /-- An acquire read (an acquire load, x64's `acqPc` TSO load, the read of an
  acquire RMW) of a message not forwarded from the thread's own write. -/
  | acqRead {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx} :
      x ∈ readSuccs A iv c k xcl l noRet → (A.loadKind k).isAcquire = true →
      (∀ f, c.views.getFwd l = some f → f.time ≠ x.1) → AcqStep A iv c x.2.2 x.1
  /-- `DMB LD` after a relaxed read of `q` (which raised `vrOld` to `q`,
  `readSuccs_vrOld`). -/
  | fenceLd {c : Ctx} {q : Time} : q ≤ c.views.vrOld → AcqStep A iv c (fenceStep c .ld) q
  /-- `DMB SY` (`mfence`, `rmwFence`) after a relaxed or `noRet` read of `q`. -/
  | fenceSy {c : Ctx} {q : Time} : q ≤ max c.views.vrOld c.views.vrOldNR → AcqStep A iv c (fenceStep c .sy) q
  /-- The end of an acquire-release RMW whose write raised `coh l` above the
  message `q` it read (`writeSuccs_tr_lt_coh`). -/
  | rmwAcqRel {c : Ctx} {k : RmwKind} {noRet : Bool} {l : Loc} {q : Time} :
      (A.rmwKind k == .acqRel && !noRet) = true → q ≤ c.views.getCoh l → AcqStep A iv c (rmwPost A k noRet l c) q

/-- **O6b, context level**: an acquire-type step puts `vwNew`, hence the write
floor, at or above the message it acquires from. -/
theorem AcqStep.le_vwNew {A : Arch} {iv : InstrViews} {c c' : Ctx} {q : Time} (h : AcqStep A iv c c' q) :
    q ≤ c'.views.vwNew := by
  cases h with
  | acqRead hx hk hfw => exact readSuccs_acq_vwNew A iv hx hk hfw
  | fenceLd hq => exact Nat.le_trans hq (fenceStep_ld_vwNew _)
  | fenceSy hq => exact Nat.le_trans hq (fenceStep_sy_vwNew _)
  | rmwAcqRel hk hq => exact Nat.le_trans hq (rmwPost_vwNew A _ _ hk)

theorem AcqStep.le_wfloor {A : Arch} {iv : InstrViews} {c c' : Ctx} {q : Time} (h : AcqStep A iv c c' q) :
    q ≤ c'.views.wfloor := Nat.le_trans h.le_vwNew (Nat.le_max_left _ _)

/-! ## One instruction -/

private theorem foldl_views {α : Type} (f : Thread I → α → Thread I) (hf : ∀ t a, (f t a).views = t.views) :
    ∀ (l : List α) (t : Thread I), (l.foldl f t).views = t.views
  | [], _ => rfl
  | a :: l, t => (foldl_views f hf l (f t a)).trans (hf t a)

/-- Close `(l₁.foldl f₁ (… (lₙ.foldl fₙ t))).views = v` where each `fᵢ` only
sets register views. -/
local macro "views_foldl" : tactic =>
  `(tactic| (repeat (refine (foldl_views _ ?_ _ _).trans ?_; (intro t a; first | rfl | (cases a; rfl)))
             try rfl))

/-- `finishInstr` takes the context's views, raising only `vCAP` (for a
branch: a control dependency). -/
theorem finishInstr_vmono {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {th : Thread I} (h : th ∈ finishInstr t d iv st c) :
    th.views.vwNew = c.views.vwNew ∧ th.views.vrOld = c.views.vrOld ∧ th.views.vrOldNR = c.views.vrOldNR ∧
      c.views.vCAP ≤ th.views.vCAP := by
  obtain ⟨-, hv⟩ := finishInstr_relKey h
  have h1 := congrArg Views.vwNew hv
  have h2 := congrArg Views.vrOld hv
  have h3 := congrArg Views.vrOldNR hv
  simp only at h1 h2 h3
  refine ⟨h1, h2, h3, ?_⟩
  clear hv h1 h2 h3
  suffices hb : ∀ u : Thread I, u.views = c.views → c.views.vCAP ≤
      (if d.isBranch then { u with views := { u.views with vCAP := max u.views.vCAP iv.condW } } else u).views.vCAP by
    unfold finishInstr at h
    simp only at h
    split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> apply hb <;> (try split) <;> views_foldl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      apply hb
      split <;> views_foldl
  intro u hu
  split
  · simp only [hu]; omega_t
  · rw [hu]; exact Nat.le_refl _

/-- **One instruction**: the views bounding writes only grow, and a promise
the instruction fulfils lies above the thread's old `vCAP`. -/
theorem stepOne_vmono (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    t.views.vwNew ≤ o.thread.views.vwNew ∧ t.views.vCAP ≤ o.thread.views.vCAP ∧
      t.views.vrOld ≤ o.thread.views.vrOld ∧ t.views.vrOldNR ≤ o.thread.views.vrOldNR ∧
      ∀ ts ∈ t.prom, ts ∉ o.thread.prom → t.views.vCAP < ts := by
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
      have hm := runTree_vmono A tid _ tree _ st c' hr
      have hc := runTree_cord A tid _ tree _ st c' hr
      obtain ⟨e1, e2, e3, e4⟩ := finishInstr_vmono hth
      have hp := (finishInstr_relKey hth).1
      simp only [e1, e2, e3, hp]
      exact ⟨hm.vwNew, Nat.le_trans hm.vCAP e4, hm.vrOld, hm.vrOldNR, hc.prom⟩

/-- One instruction never lowers the write floor. -/
theorem stepOne_wfloor (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) : t.views.wfloor ≤ o.thread.views.wfloor := by
  obtain ⟨h1, h2, -⟩ := stepOne_vmono A hstep ho
  simp only [Views.wfloor]; omega_t

/-- **O6b, instruction level**: if some context step of an instruction's run
is acquire-type for the message `q`, the thread after the instruction has
its write floor at or above `q` (the rest of the run and `finishInstr` only
raise it). -/
theorem AcqStep.le_finish {A : Arch} {tid : Nat} {iv : InstrViews} {c₁ c₂ : Ctx} {q : Time}
    (h : AcqStep A iv c₁ c₂ q) {σ : Type} {tree : EvTree σ} {s : σ} {c' : Ctx}
    (hrun : .ok (s, c') ∈ runTree A tid iv c₂ tree)
    {t : Thread I} {d : InstrDeps I.RegId} {st : I.State} {th : Thread I} (hth : th ∈ finishInstr t d iv st c') :
    q ≤ th.views.wfloor := by
  have h1 := Nat.le_trans h.le_wfloor (runTree_vmono A tid iv tree c₂ s c' hrun).wfloor
  obtain ⟨e1, -, -, e4⟩ := finishInstr_vmono hth
  simp only [Views.wfloor, e1] at h1 ⊢
  omega_t

/-! ## Live configurations -/

/-- In a `LiveK` configuration every outstanding promise lies above its
thread's `vCAP` (the `ReachableK` twin of `Config.Live.vCAP_lt`, fuel-free). -/
theorem Config.LiveK.vCAP_lt {A : Arch} {c : Config I} (hl : c.LiveK A)
    {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.vCAP < ts := by
  obtain ⟨cf, hr, hf⟩ := hl
  induction hr generalizing t with
  | refl =>
    exfalso
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
    have := (Array.all_eq_true.mp hf) i hi
    simp only [Bool.and_eq_true, List.isEmpty_iff] at this
    rw [this.2] at hts
    cases hts
  | @step c c' c'' hs _ ih =>
    have hlt := lt_size_of_get? ht
    cases hs with
    | @instr j tj outs o hj hstep ho =>
      by_cases hij : j = i
      · subst hij
        rw [ht] at hj; cases hj
        obtain ⟨-, hle, -, -, hful⟩ := stepOne_vmono A hstep ho
        by_cases hin : ts ∈ o.thread.prom
        · have h1 : (c.withThread j o.thread o.mem).threads[j]? = some o.thread := by
            simp only [Config.withThread_get? c _ _ hlt, ↓reduceIte]
          exact Nat.lt_of_le_of_lt hle (ih h1 hin hf)
        · exact hful ts hts hin
      · have h1 : (c.withThread j o.thread o.mem).threads[i]? = some t := by
          simp only [Config.withThread_get? c _ _ (lt_size_of_get? hj), hij, ↓reduceIte, ht]
        exact ih h1 hts hf
    | @promise j tj p hj _ =>
      by_cases hij : j = i
      · subst hij
        rw [ht] at hj; cases hj
        have h1 := (Config.withThread_get? c (i := j) { t with prom := t.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 hlt)
        simp only [↓reduceIte] at h1
        have := ih h1 (List.mem_append_left _ hts) hf
        exact this
      · have h1 := (Config.withThread_get? c (i := i) { tj with prom := tj.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 (lt_size_of_get? hj))
        simp only [hij, ↓reduceIte, ht] at h1
        exact ih h1 hts hf

/-- **In a live configuration every outstanding promise lies above its
thread's `vCAP`** (the twin of `Config.Live.vwNew_lt`): on a path to a final
configuration it is fulfilled by its thread, above the thread's `vCAP` then,
which only grows. -/
theorem Config.Live.vCAP_lt {A : Arch} [I.LawfulState] {fuel : Nat} {c : Config I} (hl : c.Live A fuel)
    {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.vCAP < ts :=
  (Config.LiveK.of_live hl).vCAP_lt ht hts

/-- In a `LiveK` configuration every outstanding promise lies above its
thread's write floor (the `ReachableK` twin of `Config.Live.wfloor_lt`, fuel-free). -/
theorem Config.LiveK.wfloor_lt {A : Arch} {c : Config I} (hl : c.LiveK A)
    {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.wfloor < ts := by
  have h1 := hl.vwNew_lt ht hts
  have h2 := hl.vCAP_lt ht hts
  simp only [Views.wfloor]; omega_t

/-- **In a live configuration every outstanding promise lies above its
thread's write floor.** With O6b (`AcqStep.le_finish`): a thread that has
acquired from a message `q` by an acquire-type event has no live outstanding
promise at or below `q`. This is step 3 of the argument for condition (3). -/
theorem Config.Live.wfloor_lt {A : Arch} [I.LawfulState] {fuel : Nat} {c : Config I} (hl : c.Live A fuel)
    {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.wfloor < ts :=
  (Config.LiveK.of_live hl).wfloor_lt ht hts

end Kraken.Promising
