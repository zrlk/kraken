import Scc.Cert.SpawnX64

/-!
# `placeOK2` from `placeOK` (x86-64)

The lemmas of `Scc/Cert/SpawnX64.lean`'s check, kept out of the trusted
check text: each relaxed component from the frozen one (`a11'_of_a11` off
the thread-id shape, `a12'_of_a12` always, `a13_of_noClone` off the spawn
path), and `placeOK2_of_placeOK`, `placeOK2` from `placeOK` on a program
that neither takes its thread id nor spawns (`hello1.w`, `ret0.w`).
-/

namespace Spike.Lib.Spawn.X64

open Scc.Cert.Spawn.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.X64.Parser
open Scc.Cert.PlaceOK.X64
open Spike.Lib.LowerX64 (proL ovfL ovfBlk stkHead proPhOk proLabs blkLabs raL)
open Spike.Lib.X64 (cellOff classify AI)
open Spike.Lib.X64Consumer (aiTgts)
open Scc.Emit.X64 (Frame labelOf directives)
open Scc.Cert.Rt.X64 (codeT phTabBy sitesBy inRs RGrp PhFact rtIn)
open Scc.Cert.Code1X64 (blockItems hasAddChk chkL starts callees rtDepth rtOk needOk1)
open Scc.Cert.Ph1X64 (runs runPhB runPh)

/-- **A11' from A11** off the thread-id shape. -/
theorem a11'_of_a11 {o : Scc.Cert.PlaceOK.X64.Out} {t : Tables} (hn : tidOf o = false) (h : a11 o t = true) : a11' o t = true := by
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

theorem needOk1'_of {tbl : List Scc.Cert.NeedX64.Row} {name : String} {size : Nat} {f : Scc.IR.Func}
    (h : needOk1 tbl name size f = true) : needOk1' tbl name size f = true := by
  unfold needOk1 at h
  unfold needOk1'
  rcases hr : Scc.Cert.NeedX64.row? tbl name with _ | ⟨_, fr, nf⟩
  · simp [hr] at h
  · simp only [hr, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨⟨⟨h1, h2⟩, all_mono (fun g hg => ?_) h3⟩, all_mono (fun g hg => ?_) h4⟩
    · rcases hg' : Scc.Cert.NeedX64.row? tbl g with _ | ⟨_, _, ng⟩ <;> simp only [hg'] at hg ⊢
      · exact rtOk'_of hg
      · exact hg
    · rcases hg' : Scc.Cert.NeedX64.row? tbl g with _ | ⟨_, _, ng⟩ <;> simp only [hg'] at hg ⊢
      · exact rtOk'_of hg
      · exact hg

theorem fnOk1K'_of {T : List (Nat × Nat × List (Directive × Nat))} {tbl : List Scc.Cert.NeedX64.Row}
    {ir : Scc.IR.Program} {n : Nat} {f : Scc.IR.Func} (h : fnOk1K T tbl ir n f = true) :
    fnOk1K' T tbl ir n f = true := by
  unfold fnOk1K at h
  unfold fnOk1K'
  dsimp only at h ⊢
  split at h
  · next hb _ =>
    split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
      rw [hb] at h5
      simp only [*, needOk1'_of h7, Bool.and_self]
    · simp at h
  · simp at h

theorem fnCode1OkK'_of {T : List (Nat × Nat × List (Directive × Nat))} {tbl : List Scc.Cert.NeedX64.Row}
    {ir : Scc.IR.Program} (h : fnCode1OkK T tbl ir = true) : fnCode1OkK' T tbl ir = true := by
  unfold fnCode1OkK at h
  unfold fnCode1OkK'
  refine all_mono (fun fn hf => ?_) h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf ⊢
  exact hf.imp_right fnOk1K'_of

theorem runPhB2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {blk : List (Directive × Nat)} (h : runPhB okPc ph lab pc ra blk = true) :
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
  | some dz =>
    intro hk
    exact all_mono (fun t ht => by simp only [Bool.or_eq_true]; exact Or.inl ht) hk.2

theorem runPh2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {ra : Int64} {r : Label × List (Directive × Nat)} (h : runPh okPc ph lab res ra r = true) :
    runPh2 okPc ph lk lab res ra r = true := by
  unfold runPh at h
  unfold runPh2
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, runPhB2_of h.2⟩

theorem blocksPhK2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {T : List (Nat × Nat × List (Directive × Nat))} {fr : Frame} {ra : Int64} :
    ∀ {n : Nat} {bs : List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry))},
      blocksPhK okPc ph lab res T fr ra n bs = true → blocksPhK2 okPc ph lk lab res T fr ra n bs = true
  | _, [], _ => rfl
  | n, (b, ms) :: bs, h => by
    simp only [blocksPhK] at h
    simp only [blocksPhK2]
    rcases hb : blockItems fr n b ms with _ | ⟨code, n'⟩
    · simp [hb] at h
    · simp only [hb, Bool.and_eq_true] at h ⊢
      refine ⟨all_mono (fun r hr => ?_) h.1, blocksPhK2_of h.2⟩
      simp only [Bool.and_eq_true] at hr ⊢
      exact ⟨runPh2_of hr.1, hr.2⟩

theorem fnPhFK2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {T : List (Nat × Nat × List (Directive × Nat))} {ir : Scc.IR.Program} {n : Nat} {f : Scc.IR.Func}
    {ra : Int64} (h : fnPhFK okPc ph lab res T ir n f ra = true) : fnPhFK2 okPc ph lk lab res T ir n f ra = true := by
  unfold fnPhFK at h
  unfold fnPhFK2
  dsimp only at h ⊢
  split at h
  · split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
      simp only [*, blocksPhK2_of h5, Bool.and_self]
    · simp at h
  · simp at h

theorem fnPhAll1K2_of {okPc : Nat → Bool} {ph lk : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {T : List (Nat × Nat × List (Directive × Nat))} {ir : Scc.IR.Program} {ra : Int64}
    (h : fnPhAll1K okPc ph lab res T ir ra = true) : fnPhAll1K2 okPc ph lk lab res T ir ra = true := by
  unfold fnPhAll1K at h
  unfold fnPhAll1K2
  refine all_mono (fun fn hf => ?_) h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf ⊢
  exact hf.imp_right fnPhFK2_of

theorem fnPh1OkK2_of {T : List (Nat × Nat × List (Directive × Nat))} {lo : Nat} {Λ : Scc.Sem.Layout}
    {cells : List (Directive × Nat)} {ir : Scc.IR.Program} (h : fnPh1OkK T lo Λ cells ir = true) :
    fnPh1OkK2 T lo Λ cells ir = true := by
  unfold fnPh1OkK at h
  unfold fnPh1OkK2
  split at h
  · simp only [Bool.and_eq_true] at h
    simp only [*, fnPhAll1K2_of h.2, Bool.and_self]
  · simp at h

/-- **A12' from A12.** -/
theorem a12'_of_a12 {o : Scc.Cert.PlaceOK.X64.Out} {t : Tables} (h : a12 o t = true) : a12' o t = true := by
  rw [← a12fast_eq] at h
  unfold a12fast at h
  unfold a12' a12code' a12ph'
  cases hir : o.place.ir with
  | none => simp [hir] at h
  | some ir =>
    simp only [hir, Bool.and_eq_true] at h ⊢
    exact ⟨fnCode1OkK'_of h.1, fnPh1OkK2_of h.2⟩

theorem a13_of_noClone {o : Scc.Cert.PlaceOK.X64.Out} {t : Tables} (h : spawnsOf o = false) : a13 o t = true := by
  simp [a13, h]

/-- **`placeOK2` from `placeOK`** on a program neither of the thread-id
shape nor spawning (`hello1.w`, `ret0.w`). -/
theorem placeOK2_of_placeOK {cfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} (hn : tidOf o = false)
    (hs : spawnsOf o = false) (h : placeOK cfg o = true) : placeOK2 cfg o = true := by
  refine Scc.Cert.PlaceOK.Checks.ok_of (C := checks2 cfg)
    (Scc.Cert.PlaceOK.Checks.a1_of_ok (C := checks cfg) h) (Scc.Cert.PlaceOK.Checks.a2_of_ok (C := checks cfg) h)
    (Scc.Cert.PlaceOK.Checks.a3_of_ok (C := checks cfg) h) (Scc.Cert.PlaceOK.Checks.a4_of_ok (C := checks cfg) h)
    (Scc.Cert.PlaceOK.Checks.a5_of_ok (C := checks cfg) h) (Scc.Cert.PlaceOK.Checks.a6_of_ok (C := checks cfg) h)
    (Scc.Cert.PlaceOK.Checks.a7_of_ok (C := checks cfg) h) (Scc.Cert.PlaceOK.Checks.a8_of_ok (C := checks cfg) h)
    (Scc.Cert.PlaceOK.Checks.a9_of_ok (C := checks cfg) h)
    (a11'_of_a11 hn (Scc.Cert.PlaceOK.Checks.a11_of_ok (C := checks cfg) h)) ?_
  show a12' o _ && a13 o _ = true
  rw [a12'_of_a12 (Scc.Cert.PlaceOK.Checks.a12_of_ok (C := checks cfg) h), a13_of_noClone hs]
  rfl

end Spike.Lib.Spawn.X64
