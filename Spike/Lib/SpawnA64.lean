import Scc.Cert.SpawnA64

/-!
# `placeOK2` from `placeOK` (AArch64)

The lemmas of `Scc/Cert/SpawnA64.lean`'s check, kept out of the trusted
check text: each relaxed component from the frozen one (`a11'_of_a11` off
the thread-id shape, `a12'_of_a12` always, `a13_of_noClone` off the spawn
path; A7 is `placeOK`'s own), and `placeOK2_of_placeOK`, `placeOK2` from `placeOK` on a program
that neither takes its thread id nor spawns (`hello1.w`, `ret0.w`).
-/

namespace Spike.Lib.Spawn.A64

open Scc.Cert.Spawn.A64

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Flow (classify AI)
open Spike.Lib.A64Consumer (aiTgts blkPh)
open Spike.Lib.LowerA64 (proL ovfBlk stkHead proPhOk proLabs blkLabs raL)
open Scc.Emit.A64 (FnCtx directives argRegs)
open Scc.Cert.Rt.A64 (codeT phTabBy sitesBy inRs RGrp PhFact rtIn)
open Scc.Cert.Code1A64 (blockItems spills hasAddChk callees rtDepth rtOk needOk1)
open Scc.Cert.Ph1A64 (runs runPhB runPh blocksPh fnPhF)

/-- **A11' from A11** off the thread-id shape. -/
theorem a11'_of_a11 {o : Scc.Cert.PlaceOK.A64.Out} {t : Tables} (hn : tidOf o = false) (h : a11 o t = true) : a11' o t = true := by
  simp only [a11', hn, Bool.false_and, Bool.false_eq_true, ↓reduceIte, h]

theorem rtDepth'_le_headroom : ∀ e ∈ rtDepth', e.2 ≤ Scc.IR.Tcb.headroom := by decide

theorem lookup_append_of_some {l₁ l₂ : List (String × Nat)} {g : String} {d : Nat}
    (h : l₁.lookup g = some d) : (l₁ ++ l₂).lookup g = some d := by
  induction l₁ with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.cons_append, List.lookup] at h ⊢
    cases hb : g == k
    · simp only [hb] at h ⊢; exact ih h
    · simp only [hb] at h ⊢; exact h

theorem rtOk'_of {g : String} (h : rtOk g = true) : rtOk' g = true := by
  unfold rtOk at h
  unfold rtOk'
  cases hl : rtDepth.lookup g with
  | none => simp [hl] at h
  | some d =>
    simp only [hl] at h
    simp only [rtDepth', lookup_append_of_some hl, h]

theorem all_mono {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a, p a = true → q a = true)
    (hp : l.all p = true) : l.all q = true := by
  simp only [List.all_eq_true] at *
  exact fun a ha => h a (hp a ha)

theorem needOk1'_of {tbl : List Scc.Cert.NeedA64.Row} {name : String} {frame : Nat} {f : Scc.IR.Func}
    (h : needOk1 tbl name frame f = true) : needOk1' tbl name frame f = true := by
  unfold needOk1 at h
  unfold needOk1'
  rcases hr : Scc.Cert.NeedA64.row? tbl name with _ | ⟨_, fr, nf⟩
  · simp [hr] at h
  · simp only [hr, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨⟨⟨h1, h2⟩, all_mono (fun g hg => ?_) h3⟩, all_mono (fun g hg => ?_) h4⟩
    · rcases hg' : Scc.Cert.NeedA64.row? tbl g with _ | ⟨_, _, ng⟩ <;> simp only [hg'] at hg ⊢
      · exact rtOk'_of hg
      · exact hg
    · rcases hg' : Scc.Cert.NeedA64.row? tbl g with _ | ⟨_, _, ng⟩ <;> simp only [hg'] at hg ⊢
      · exact rtOk'_of hg
      · exact hg

theorem fnOk1K'_of {T : List (Nat × Nat × List Directive)} {tbl : List Scc.Cert.NeedA64.Row} {c : FnCtx}
    {f : Scc.IR.Func} (h : fnOk1K T tbl c f = true) : fnOk1K' T tbl c f = true := by
  unfold fnOk1K at h
  unfold fnOk1K'
  split at h
  · next hb _ =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    rw [hb] at h4
    simp only [*, needOk1'_of h6, Bool.and_true]
    exact h1
  · simp at h

theorem fnCode1OkK'_of {T : List (Nat × Nat × List Directive)} {tbl : List Scc.Cert.NeedA64.Row}
    {ir : Scc.IR.Program} (h : fnCode1OkK T tbl ir = true) : fnCode1OkK' T tbl ir = true := by
  unfold fnCode1OkK at h
  unfold fnCode1OkK'
  refine all_mono (fun fn hf => ?_) h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf ⊢
  exact hf.imp_right fnOk1K'_of

theorem runPhB2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {blk : List Directive} (h : runPhB okPc ph lab pc ra blk = true) :
    runPhB2 okPc ph lk lab pc ra blk = true := by
  unfold runPhB at h
  unfold runPhB2
  refine all_mono (fun k hk => ?_) h
  simp only [Bool.and_eq_true] at hk ⊢
  refine ⟨hk.1, ?_⟩
  revert hk
  generalize blk[k]? = o
  cases o with
  | none => simp
  | some d =>
    intro hk
    exact all_mono (fun t ht => by simp only [Bool.or_eq_true]; exact Or.inl ht) hk.2

theorem runPh2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {ra : Int64} {r : Label × List Directive} (h : runPh okPc ph lab res ra r = true) :
    runPh2 okPc ph lk lab res ra r = true := by
  unfold runPh at h
  unfold runPh2
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, runPhB2_of h.2⟩

theorem blocksPh2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {c : FnCtx} {ra : Int64} :
    ∀ {k : Nat} {bs : List Scc.IR.Block},
      blocksPh okPc ph lab res c ra k bs = true → blocksPh2 okPc ph lk lab res c ra k bs = true
  | _, [], _ => rfl
  | k, b :: bs, h => by
    simp only [blocksPh, Bool.and_eq_true] at h
    simp only [blocksPh2, Bool.and_eq_true]
    refine ⟨?_, blocksPh2_of h.2⟩
    have h1 := h.1
    rcases hl : c.blockLabel b.label with _ | l <;> rcases hc : blockItems c k b with _ | code <;>
      simp only [hl, hc, Bool.false_eq_true] at h1 ⊢
    refine all_mono (fun r hr => ?_) h1
    simp only [Bool.and_eq_true] at hr ⊢
    exact ⟨runPh2_of hr.1, hr.2⟩

theorem fnPhF2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {c : FnCtx} {f : Scc.IR.Func} {ra : Int64} (h : fnPhF okPc ph lab res c f ra = true) :
    fnPhF2 okPc ph lk lab res c f ra = true := by
  unfold fnPhF at h
  unfold fnPhF2
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    simp only [*, blocksPh2_of h5, Bool.and_self]
  · simp at h

theorem fnPhAll1K2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {ir : Scc.IR.Program} {ra : Int64} (h : fnPhAll1K okPc ph lab res ir ra = true) :
    fnPhAll1K2 okPc ph lk lab res ir ra = true := by
  unfold fnPhAll1K at h
  unfold fnPhAll1K2
  refine all_mono (fun fn hf => ?_) h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf ⊢
  exact hf.imp_right fnPhF2_of

theorem fnPh1OkK2_of {lo : Nat} {Λ : Scc.Sem.Layout} {prog : Program} {ir : Scc.IR.Program}
    (h : fnPh1OkK lo Λ prog ir = true) : fnPh1OkK2 lo Λ prog ir = true := by
  unfold fnPh1OkK at h
  unfold fnPh1OkK2
  split at h
  · simp only [Bool.and_eq_true] at h
    simp only [*, fnPhAll1K2_of h.2, Bool.and_self]
  · simp at h

/-- **A12' from A12.** -/
theorem a12'_of_a12 {o : Scc.Cert.PlaceOK.A64.Out} {t : Tables} (h : a12 o t = true) : a12' o t = true := by
  rw [← a12fast_eq] at h
  unfold a12fast at h
  unfold a12' a12code' a12ph'
  cases hir : o.place.ir with
  | none => simp [hir] at h
  | some ir =>
    simp only [hir, Bool.and_eq_true] at h ⊢
    exact ⟨fnCode1OkK'_of h.1, fnPh1OkK2_of h.2⟩

theorem a13_of_noClone {o : Scc.Cert.PlaceOK.A64.Out} {t : Tables} (h : spawnsOf o = false) : a13 o t = true := by
  simp [a13, h]

/-- **`placeOK2` from `placeOK`** on a program neither of the thread-id
shape nor spawning (`hello1.w`, `ret0.w`). -/
theorem placeOK2_of_placeOK {cfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} (hn : tidOf o = false)
    (hs : spawnsOf o = false) (h : placeOK cfg o = true) : placeOK2 cfg o = true := by
  refine Scc.Cert.PlaceOK.Checks.ok_of (C := checks2 cfg)
    (Scc.Cert.PlaceOK.Checks.a1_of_ok (C := checks cfg) h) (Scc.Cert.PlaceOK.Checks.a2_of_ok (C := checks cfg) h)
    (Scc.Cert.PlaceOK.Checks.a3_of_ok (C := checks cfg) h) (Scc.Cert.PlaceOK.Checks.a4_of_ok (C := checks cfg) h)
    (Scc.Cert.PlaceOK.Checks.a5_of_ok (C := checks cfg) h) (Scc.Cert.PlaceOK.Checks.a6_of_ok (C := checks cfg) h)
    (Scc.Cert.PlaceOK.Checks.a7_of_ok (C := checks cfg) h)
    (Scc.Cert.PlaceOK.Checks.a8_of_ok (C := checks cfg) h)
    (Scc.Cert.PlaceOK.Checks.a9_of_ok (C := checks cfg) h)
    (a11'_of_a11 hn (Scc.Cert.PlaceOK.Checks.a11_of_ok (C := checks cfg) h)) ?_
  show a12' o _ && a13 o _ = true
  rw [a12'_of_a12 (Scc.Cert.PlaceOK.Checks.a12_of_ok (C := checks cfg) h), a13_of_noClone hs]
  rfl

end Spike.Lib.Spawn.A64
