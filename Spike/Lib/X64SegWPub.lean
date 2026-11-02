/-
**Segments whose rows may start after the source's publication** (x86-64;
no AArch64 twin): `SegW`, `SegWS` and `SegInvS` with every row of the
invariant either an `Out` row at the pair's control or, off a system call
where the memory side admits the publication (`MemSide.pub`), an `Out` row
at the control the source's publication (`PubStep .st`) lands at, that
control again a pair of the invariant. This is the segment-side form of
`NodesA.out`'s `PubOut` disjunct (`Spike/Lib/X64ConsumerA.lean`).

Where x86-64 differs from AArch64: AArch64 takes the source's publication
with the fence row after the stores (`Out.fence`, `FenceRun.pub`). x86-64
has no instruction for that fence under TSO, so the source publishes as a
stutter before the row of the next instruction. The publication is not a
`LocalStep` (it fences the source's view), so it cannot ride a row's local
runs.

- `OutP`: a row at `c`, or a publication from `c` into `Y` and a row from
  there. `OutP.mono`, `Out.toP`.
- `SegWP`: `SegW` with `OutP` rows, the publication landing in the
  invariant. `SegW.toP`; `SegWP.mono_pre`, `mono_post`, `mono_W`, `seq`,
  `or_pre`, `exists_pre`; `SegWP.pub`: a segment from `P₁` is one from the
  pairs that are in `P₁` or publish into `P₁`, none of them moved from
  outside (the stutter); `SegW.pubP`: the same from a `SegW`.
- `OutSP`, `SegWSP`, `SegInvSP`: the same at any frames. `OutS.toP`,
  `OutSP.mono`, `OutSP.mono_xa`; `SegWS.toP`, `SegWSP.liftS` (a `SegWP` at
  fixed frames), `seq`, `mono_pre`, `mono_post`, `or_pre`, `post_run`,
  `empty`, `exists_pre`, `mono_K`, `mono_xa`;
  `SegInvS.toP`, `SegInvSP.ofSegWSP`, `SegInvSP.weakW`, `SegInvSP.mono_xa`.
- `GfpSP`, `le_gfpSP`, `segInvSP_gfpSP`, `gfpSP_of_segWSP`: the greatest
  closed invariant inside a fragment (as `X64GfpS`'s).
- `out_or_pub`: an `OutSP` row under `msOfAX` with the publication landing in
  the fragment is `NodesA.out`'s disjunction.
-/
import Spike.Lib.X64SegInstA
import Spike.Lib.X64GfpS

namespace Spike.Lib.X64SegWPub

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena Frag FragS Out OutS KOut KOutS SegW SegWS MemSide Pend PubStep LocalRun FrameRun Ctl)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA

variable {p : Prog} {lbl : Lbl}

/-! ## Rows after a publication -/

/-- **A row at `c`, or after the source's publication from `c`**: an `Out`
row from `c` into `X`, or, off a system call where `ms` admits it, the
publication from `c` to a control `c₁` of `Y` and an `Out` row from `c₁` into
`X`. -/
def OutP (p : Prog) (lbl : Lbl) (ms : MemSide isa) (Y X : Frag isa) (s : State) (c : Ctl) : Prop :=
  Out p lbl ms X s c ∨
    (abi.atSys s = false ∧ ms.pub ∧ ∃ c₁, PubStep .st c c₁ ∧ Y s c₁ ∧ Out p lbl ms X s c₁)

/-- An `Out` row is an `OutP` row. -/
theorem _root_.Spike.Lib.Out.toP {ms : MemSide isa} {Y X : Frag isa} {s : State} {c : Ctl} (h : Out p lbl ms X s c) :
    OutP p lbl ms Y X s c :=
  .inl h

theorem OutP.mono {ms : MemSide isa} {Y Y' X X' : Frag isa} {s : State} {c : Ctl} (h : OutP p lbl ms Y X s c)
    (hY : ∀ s c, Y s c → Y' s c) (hX : ∀ s c, X s c → X' s c) : OutP p lbl ms Y' X' s c :=
  h.imp (·.mono hX) fun ⟨hns, hp, c₁, hps, hy, ho⟩ => ⟨hns, hp, c₁, hps, hY _ _ hy, ho.mono hX⟩

/-! ## Segments with rows after a publication -/

/-- **`SegW` with rows after a publication**: every pair of `P` lies in an
invariant inside `W` whose every outside move lands in the invariant or the
exit `Q`, and whose pairs `K` does not move take an `OutP` row there, the
publication landing in the invariant. -/
def SegWP (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : Lbl) (ms : MemSide isa)
    (P Q : Frag isa) : Prop :=
  ∃ inv : Frag isa, (∀ s c, P s c → inv s c) ∧ (∀ s c, inv s c → W s c) ∧
    ∀ s c, inv s c → ((∀ s', ¬ K s s') → OutP p lbl ms inv (fun s c => inv s c ∨ Q s c) s c) ∧
      KOut K p (fun s c => inv s c ∨ Q s c) s c

/-- The closure of a `SegWP` invariant, moved along `Y ⊆ Y'` and `X ⊆ X'`. -/
theorem koutP_mono {K : State → State → Prop} {ms : MemSide isa} {Y Y' X X' : Frag isa}
    {s : State} {c : Ctl} (h : ((∀ s', ¬ K s s') → OutP p lbl ms Y X s c) ∧ KOut K p X s c)
    (hY : ∀ s c, Y s c → Y' s c) (hX : ∀ s c, X s c → X' s c) :
    ((∀ s', ¬ K s s') → OutP p lbl ms Y' X' s c) ∧ KOut K p X' s c :=
  ⟨fun hk => (h.1 hk).mono hY hX, h.2.mono hX⟩

/-- A `SegW` is a `SegWP`. -/
theorem _root_.Spike.Lib.SegW.toP {W : Frag isa} {K : State → State → Prop} {ms : MemSide isa}
    {P Q : Frag isa} (h : SegW W K p lbl ms P Q) : SegWP W K p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c hi => ⟨fun hk => ((ho s c hi).1 hk).toP, (ho s c hi).2⟩⟩

namespace SegWP

variable {W W' : Frag isa} {K : State → State → Prop} {ms : MemSide isa} {P P' Q Q' R : Frag isa}

theorem mono_pre (h : SegWP W K p lbl ms P Q) (hP : ∀ s c, P' s c → P s c) : SegWP W K p lbl ms P' Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, fun s c h => hs s c (hP s c h), hw, ho⟩

theorem mono_post (h : SegWP W K p lbl ms P Q) (hQ : ∀ s c, Q s c → Q' s c) : SegWP W K p lbl ms P Q' :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c h => koutP_mono (ho s c h) (fun _ _ h => h) fun s c h => h.imp_right (hQ s c)⟩

/-- A weaker predicate. -/
theorem mono_W (h : SegWP W K p lbl ms P Q) (hW : ∀ s c, W s c → W' s c) : SegWP W' K p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c h => hW s c (hw s c h), ho⟩

/-- **Sequencing.** -/
theorem seq (h₁ : SegWP W K p lbl ms P Q) (h₂ : SegWP W K p lbl ms Q R) : SegWP W K p lbl ms P R := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), fun s c h => h.elim (hw₁ s c) (hw₂ s c), ?_⟩
  have m₁ : ∀ s c, (i₁ s c ∨ Q s c) → (i₁ s c ∨ i₂ s c) ∨ R s c :=
    fun s c h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c h))
  have m₂ : ∀ s c, (i₂ s c ∨ R s c) → (i₁ s c ∨ i₂ s c) ∨ R s c :=
    fun s c h => h.elim (fun h => .inl (.inr h)) .inr
  rintro s c (h | h)
  · exact koutP_mono (ho₁ s c h) (fun _ _ => .inl) m₁
  · exact koutP_mono (ho₂ s c h) (fun _ _ => .inr) m₂

/-- A case split on the entry. -/
theorem or_pre (h : SegWP W K p lbl ms P Q) (h' : SegWP W K p lbl ms P' Q) :
    SegWP W K p lbl ms (fun s c => P s c ∨ P' s c) Q := by
  obtain ⟨i, hs, hw, ho⟩ := h
  obtain ⟨i', hs', hw', ho'⟩ := h'
  refine ⟨fun s c => i s c ∨ i' s c, fun s c h => h.imp (hs s c) (hs' s c),
    fun s c h => h.elim (hw s c) (hw' s c), ?_⟩
  rintro s c (h | h)
  · exact koutP_mono (ho s c h) (fun _ _ => .inl) fun s c h => h.imp_left .inl
  · exact koutP_mono (ho' s c h) (fun _ _ => .inr) fun s c h => h.imp_left .inr

/-- **Ghost parameters.** -/
theorem exists_pre {γ : Sort _} {P : γ → Frag isa} (h : ∀ g, SegWP W K p lbl ms (P g) Q) :
    SegWP W K p lbl ms (fun s c => ∃ g, P g s c) Q := by
  refine ⟨fun s c => ∃ g, Classical.choose (h g) s c,
    fun s c ⟨g, hg⟩ => ⟨g, (Classical.choose_spec (h g)).1 s c hg⟩,
    fun s c ⟨g, hg⟩ => (Classical.choose_spec (h g)).2.1 s c hg, ?_⟩
  rintro s c ⟨g, hg⟩
  exact koutP_mono ((Classical.choose_spec (h g)).2.2 s c hg) (fun _ _ h => ⟨g, h⟩)
    fun _ _ h => h.imp_left fun h => ⟨g, h⟩

/-- **The publication as a stutter before a segment**: a segment from `P₁`
is one from the pairs of `P₀` or `P₁`, given that every pair of `P₀` is
inside `W`, not moved from outside, and in `P₁` or, off a system call where
`ms` admits it, publishing into a control of `P₁` (whose row is then the
pair's). -/
theorem pub {P₀ P₁ : Frag isa} (h : SegWP W K p lbl ms P₁ Q)
    (hP : ∀ s c, P₀ s c → W s c ∧ (∀ s', ¬ K s s') ∧
      (P₁ s c ∨ abi.atSys s = false ∧ ms.pub ∧ ∃ c₁, PubStep .st c c₁ ∧ P₁ s c₁ ∧
        ∀ c₂, ¬ PubStep .st c₁ c₂)) :
    SegWP W K p lbl ms (fun s c => P₀ s c ∨ P₁ s c) Q := by
  obtain ⟨i, hs, hw, ho⟩ := h
  refine ⟨fun s c => i s c ∨ P₀ s c, fun s c h => h.elim .inr fun h => .inl (hs s c h),
    fun s c h => h.elim (hw s c) fun h => (hP s c h).1, ?_⟩
  have mY : ∀ s c, i s c → i s c ∨ P₀ s c := fun _ _ => .inl
  have mX : ∀ s c, (i s c ∨ Q s c) → (i s c ∨ P₀ s c) ∨ Q s c := fun _ _ h => h.imp_left .inl
  rintro s c (h | h)
  · exact koutP_mono (ho s c h) mY mX
  · obtain ⟨-, hk, h1 | ⟨hns, hpub, c₁, hps, h1, hnp⟩⟩ := hP s c h
    · exact koutP_mono (ho s c (hs s c h1)) mY mX
    · have hi₁ := hs s c₁ h1
      refine ⟨fun _ => .inr ⟨hns, hpub, c₁, hps, .inl hi₁, ?_⟩, KOut.none hk⟩
      rcases (ho s c₁ hi₁).1 hk with ho₁ | ⟨-, -, c₂, hps₂, -⟩
      · exact ho₁.mono mX
      · exact (hnp c₂ hps₂).elim

end SegWP

/-- **The publication as a stutter before a `SegW`**: `SegWP.pub` where the
segment from `P₁` is a `SegW`, whose rows are `Out` rows, so no second
publication is asked of the landing. -/
theorem _root_.Spike.Lib.SegW.pubP {W : Frag isa} {K : State → State → Prop} {ms : MemSide isa}
    {P₀ P₁ Q : Frag isa} (h : SegW W K p lbl ms P₁ Q)
    (hP : ∀ s c, P₀ s c → W s c ∧ (∀ s', ¬ K s s') ∧
      (P₁ s c ∨ abi.atSys s = false ∧ ms.pub ∧ ∃ c₁, PubStep .st c c₁ ∧ P₁ s c₁)) :
    SegWP W K p lbl ms (fun s c => P₀ s c ∨ P₁ s c) Q := by
  obtain ⟨i, hs, hw, ho⟩ := h
  refine ⟨fun s c => i s c ∨ P₀ s c, fun s c h => h.elim .inr fun h => .inl (hs s c h),
    fun s c h => h.elim (hw s c) fun h => (hP s c h).1, ?_⟩
  have mX : ∀ s c, (i s c ∨ Q s c) → (i s c ∨ P₀ s c) ∨ Q s c := fun _ _ h => h.imp_left .inl
  rintro s c (h | h)
  · exact ⟨fun hk => (((ho s c h).1 hk).mono mX).toP, (ho s c h).2.mono mX⟩
  · obtain ⟨-, hk, h1 | ⟨hns, hpub, c₁, hps, h1⟩⟩ := hP s c h
    · have h' := ho s c (hs s c h1)
      exact ⟨fun hk => ((h'.1 hk).mono mX).toP, h'.2.mono mX⟩
    · exact ⟨fun _ => .inr ⟨hns, hpub, c₁, hps, .inl (hs s c₁ h1), ((ho s c₁ (hs s c₁ h1)).1 hk).mono mX⟩,
        KOut.none hk⟩

/-! ## At any frames -/

/-- **A row at depth at `c`, or after the source's publication from `c`**:
an `OutS` row from `(c, fs)` into `X`, or, off a system call where the
memory side at `fs` admits it, the publication from `c` to a control `c₁`
with `Y s c₁ fs` and an `OutS` row from `(c₁, fs)` into `X`. -/
def OutSP (p : Prog) (lbl : Lbl) (ms : List TermRun.Frame → MemSide isa) (Y X : FragS isa) (s : State) (c : Ctl)
    (fs : List TermRun.Frame) : Prop :=
  OutS p lbl ms X s c fs ∨
    (abi.atSys s = false ∧ (ms fs).pub ∧ ∃ c₁, PubStep .st c c₁ ∧ Y s c₁ fs ∧ OutS p lbl ms X s c₁ fs)

section Frames

variable {ms ms' : List TermRun.Frame → MemSide isa} {W W' : FragS isa} {K : State → State → Prop}
  {P P' Q Q' R Y Y' X X' : FragS isa} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- An `OutS` row is an `OutSP` row. -/
theorem _root_.Spike.Lib.OutS.toP (h : OutS p lbl ms X s c fs) : OutSP p lbl ms Y X s c fs := .inl h

theorem OutSP.mono (h : OutSP p lbl ms Y X s c fs) (hY : ∀ s c fs, Y s c fs → Y' s c fs)
    (hX : ∀ s c fs, X s c fs → X' s c fs) : OutSP p lbl ms Y' X' s c fs :=
  h.imp (·.mono hX) fun ⟨hns, hp, c₁, hps, hy, ho⟩ => ⟨hns, hp, c₁, hps, hY _ _ _ hy, ho.mono hX⟩

/-- `OutS.mono_xa` for `OutSP`: `ms'` is `ms` but for `xa` (so `pub` is
kept). -/
theorem OutSP.mono_xa (h : OutSP p lbl ms Y X s c fs) (he : ∀ fs, ms' fs = { ms fs with xa := (ms' fs).xa })
    (hxa : ∀ fs l b n s c, (ms fs).xa l b n s c → (ms' fs).xa l b n s c) : OutSP p lbl ms' Y X s c fs := by
  have hp : (ms' fs).pub = (ms fs).pub := by rw [he fs]
  exact h.imp (OutS.mono_xa · he hxa) fun ⟨hns, hpub, c₁, hps, hy, ho⟩ =>
    ⟨hns, hp ▸ hpub, c₁, hps, hy, OutS.mono_xa ho he hxa⟩

/-- **`SegWS` with rows after a publication**: as `SegWS`, the rows of the
invariant `OutSP` rows, the publication landing in the invariant. -/
def SegWSP (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : Lbl)
    (ms : List TermRun.Frame → MemSide isa) (P Q : FragS isa) : Prop :=
  ∃ inv : FragS isa, (∀ s c fs, P s c fs → inv s c fs) ∧ (∀ s c fs, inv s c fs → W s c fs) ∧
    ∀ s c fs, inv s c fs →
      ((∀ s', ¬ K s s') → OutSP p lbl ms inv (Pend p fun s c fs => inv s c fs ∨ Q s c fs) s c fs) ∧
      KOutS K p (fun s c fs => inv s c fs ∨ Q s c fs) s c fs

/-- The closure of a `SegWSP` invariant, moved along `Y ⊆ Y'` and the
landing `X ⊆ X'`. -/
theorem kOutSP_mono {X X' : FragS isa}
    (h : ((∀ s', ¬ K s s') → OutSP p lbl ms Y (Pend p X) s c fs) ∧ KOutS K p X s c fs)
    (hY : ∀ s c fs, Y s c fs → Y' s c fs) (hX : ∀ s c fs, X s c fs → X' s c fs) :
    ((∀ s', ¬ K s s') → OutSP p lbl ms Y' (Pend p X') s c fs) ∧ KOutS K p X' s c fs :=
  ⟨fun hk => (h.1 hk).mono hY fun _ _ _ h => h.mono hX, h.2.mono hX⟩

/-- A `SegWS` is a `SegWSP`. -/
theorem _root_.Spike.Lib.SegWS.toP (h : SegWS W K p lbl ms P Q) : SegWSP W K p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c fs hi => ⟨fun hk => ((ho s c fs hi).1 hk).toP, (ho s c fs hi).2⟩⟩

namespace SegWSP

/-- **A segment at fixed frames**: a `SegWP` under the memory side at `fs`,
inside `W` at `fs`. -/
theorem liftS {W₀ P₀ Q₀ : Frag isa} (fs : List TermRun.Frame) (h : SegWP W₀ K p lbl (ms fs) P₀ Q₀)
    (hW : ∀ s c, W₀ s c → W s c fs) : SegWSP W K p lbl ms (P₀.at fs) (Q₀.at fs) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  refine ⟨inv.at fs, fun s c fs' ⟨h, e⟩ => ⟨hP s c h, e⟩, fun s c fs' ⟨h, e⟩ => e ▸ hW s c (hiW s c h), ?_⟩
  have hX : ∀ s c, (inv s c ∨ Q₀ s c) → Pend p (fun s c fs' => inv.at fs s c fs' ∨ Q₀.at fs s c fs') s c fs :=
    fun s c h => .of (h.imp (fun h => ⟨h, rfl⟩) (fun h => ⟨h, rfl⟩))
  rintro s c fs' ⟨hi, rfl⟩
  obtain ⟨hout, hk⟩ := hcl s c hi
  refine ⟨fun hK => ?_, KOutS.ofKOut hk fun s c h => h.imp (fun h => ⟨h, rfl⟩) (fun h => ⟨h, rfl⟩)⟩
  rcases hout hK with ho | ⟨hns, hp, c₁, hps, hy, ho⟩
  · exact .inl (.lift (ho.mono hX))
  · exact .inr ⟨hns, hp, c₁, hps, ⟨hy, rfl⟩, .lift (ho.mono hX)⟩

/-- **Sequencing.** -/
theorem seq (h₁ : SegWSP W K p lbl ms P Q) (h₂ : SegWSP W K p lbl ms Q R) : SegWSP W K p lbl ms P R := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), ?_⟩
  rintro s c fs (h | h)
  · exact kOutSP_mono (ho₁ s c fs h) (fun _ _ _ => .inl)
      fun s c fs h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c fs h))
  · exact kOutSP_mono (ho₂ s c fs h) (fun _ _ _ => .inr) fun s c fs h => h.elim (fun h => .inl (.inr h)) .inr

theorem mono_pre (h : SegWSP W K p lbl ms P Q) (hP : ∀ s c fs, P' s c fs → P s c fs) :
    SegWSP W K p lbl ms P' Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, fun s c fs h => hs s c fs (hP s c fs h), hw, ho⟩

theorem mono_post (h : SegWSP W K p lbl ms P Q) (hQ : ∀ s c fs, Q s c fs → Q' s c fs) :
    SegWSP W K p lbl ms P Q' :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c fs h => kOutSP_mono (ho s c fs h) (fun _ _ _ h => h) fun s c fs h => h.imp_right (hQ s c fs)⟩

/-- A weaker predicate. -/
theorem mono_W (h : SegWSP W K p lbl ms P Q) (hW : ∀ s c fs, W s c fs → W' s c fs) : SegWSP W' K p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c fs h => hW s c fs (hw s c fs h), ho⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegWSP W K p lbl ms P Q) (h' : SegWSP W K p lbl ms P' Q) :
    SegWSP W K p lbl ms (fun s c fs => P s c fs ∨ P' s c fs) Q := by
  obtain ⟨i, hs, hw, ho⟩ := h
  obtain ⟨i', hs', hw', ho'⟩ := h'
  refine ⟨fun s c fs => i s c fs ∨ i' s c fs, fun s c fs h => h.imp (hs s c fs) (hs' s c fs),
    fun s c fs h => h.elim (hw s c fs) (hw' s c fs), ?_⟩
  rintro s c fs (h | h)
  · exact kOutSP_mono (ho s c fs h) (fun _ _ _ => .inl) fun s c fs h => h.imp_left .inl
  · exact kOutSP_mono (ho' s c fs h) (fun _ _ _ => .inr) fun s c fs h => h.imp_left .inr

/-- **A frame run after a segment** (`SegWS.post_run`). -/
theorem post_run (h : SegWSP W K p lbl ms P (Pend p Q)) : SegWSP W K p lbl ms P Q := by
  obtain ⟨inv, hs, hw, ho⟩ := h
  refine ⟨inv, hs, hw, fun s c fs hi => ⟨fun hK => ((ho s c fs hi).1 hK).mono (fun _ _ _ h => h)
    fun _ _ _ h => h.or_pend, ?_⟩⟩
  intro s' hk
  obtain ⟨c', fs', hr, h⟩ := (ho s c fs hi).2 s' hk
  rcases h with h | ⟨c'', fs'', hr', h⟩
  · exact ⟨c', fs', hr, .inl h⟩
  · exact ⟨c'', fs'', hr.trans hr', .inr h⟩

/-- **No entry** (`SegWS.empty`). -/
theorem empty (h : ∀ s c fs, ¬ P s c fs) : SegWSP W K p lbl ms P Q :=
  ⟨fun _ _ _ => False, fun s c fs hP => h s c fs hP, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩

/-- **An entry family** (`SegWS.exists_pre`): segments from each `P g` give one from their union. -/
theorem exists_pre {γ : Sort _} {P : γ → FragS isa} (h : ∀ g, SegWSP W K p lbl ms (P g) Q) :
    SegWSP W K p lbl ms (fun s c fs => ∃ g, P g s c fs) Q := by
  refine ⟨fun s c fs => ∃ g, Classical.choose (h g) s c fs,
    fun s c fs ⟨g, hg⟩ => ⟨g, (Classical.choose_spec (h g)).1 s c fs hg⟩,
    fun s c fs ⟨g, hg⟩ => (Classical.choose_spec (h g)).2.1 s c fs hg, ?_⟩
  rintro s c fs ⟨g, hg⟩
  exact kOutSP_mono ((Classical.choose_spec (h g)).2.2 s c fs hg) (fun _ _ _ h => ⟨g, h⟩)
    fun _ _ _ h => h.imp_left fun h => ⟨g, h⟩

/-- **Outside moves `K'` moving the invariant's states as `K` does** (`SegWS.mono_K`). -/
theorem mono_K {K' : State → State → Prop} (h : SegWSP W K p lbl ms P Q)
    (hK : ∀ s c fs, W s c fs → ∀ s', K' s s' ↔ K s s') : SegWSP W K' p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c fs h =>
    ⟨fun hn => (ho s c fs h).1 fun s' hk => hn s' ((hK s c fs (hw s c fs h) s').2 hk),
      fun s' hk => (ho s c fs h).2 s' ((hK s c fs (hw s c fs h) s').1 hk)⟩⟩

/-- **Larger allocation fragments** (`KeepUnS.SegWS.mono_xa`): `ms'` is `ms` but for `xa`, which it extends. -/
theorem mono_xa (h : SegWSP W K p lbl ms P Q) (he : ∀ fs, ms' fs = { ms fs with xa := (ms' fs).xa })
    (hxa : ∀ fs l b n s c, (ms fs).xa l b n s c → (ms' fs).xa l b n s c) : SegWSP W K p lbl ms' P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c fs h => ⟨fun hk => ((ho s c fs h).1 hk).mono_xa he hxa, (ho s c fs h).2⟩⟩

end SegWSP

/-! ## Explicit invariants -/

/-- **`SegInvS` with rows after a publication**: every pair of `inv` is in
`W`, takes an `OutSP` row off `K` (the publication landing in `inv`), and its
outside moves land in `inv`. -/
def SegInvSP (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : Lbl)
    (ms : List TermRun.Frame → MemSide isa) (inv : FragS isa) : Prop :=
  ∀ s c fs, inv s c fs →
    W s c fs ∧ ((∀ s', ¬ K s s') → OutSP p lbl ms inv (Pend p inv) s c fs) ∧ KOutS K p inv s c fs

/-- A `SegInvS` is a `SegInvSP`. -/
theorem _root_.Spike.Lib.X64ConsumerA.SegInvS.toP {inv : FragS isa} (h : SegInvS W K p lbl ms inv) :
    SegInvSP W K p lbl ms inv :=
  fun s c fs hi => let h := h s c fs hi; ⟨h.1, fun hk => (h.2.1 hk).toP, h.2.2⟩

namespace SegInvSP

variable {inv : FragS isa}

/-- **The witness of a segment with no exit.** -/
theorem ofSegWSP (h : SegWSP W K p lbl ms P (fun _ _ _ => False)) :
    ∃ inv, (∀ s c fs, P s c fs → inv s c fs) ∧ SegInvSP W K p lbl ms inv := by
  obtain ⟨inv, hP, hW, hcl⟩ := h
  refine ⟨inv, hP, fun s c fs hi => ⟨hW s c fs hi, fun hk => ?_, ?_⟩⟩
  · exact ((hcl s c fs hi).1 hk).mono (fun _ _ _ h => h) fun _ _ _ h => h.mono fun _ _ _ h => h.elim id False.elim
  · exact (hcl s c fs hi).2.mono fun _ _ _ h => h.elim id False.elim

/-- A weaker predicate. -/
theorem weakW (h : SegInvSP W' K p lbl ms inv) (hW : ∀ s c fs, W' s c fs → W s c fs) :
    SegInvSP W K p lbl ms inv :=
  fun s c fs hi => let h' := h s c fs hi; ⟨hW s c fs h'.1, h'.2⟩

/-- **Under a memory side with a larger allocation fragment.** -/
theorem mono_xa (h : SegInvSP W K p lbl ms inv) (he : ∀ fs, ms' fs = { ms fs with xa := (ms' fs).xa })
    (hxa : ∀ fs l b n s c, (ms fs).xa l b n s c → (ms' fs).xa l b n s c) : SegInvSP W K p lbl ms' inv :=
  fun s c fs hi => let h := h s c fs hi; ⟨h.1, fun hk => (h.2.1 hk).mono_xa he hxa, h.2.2⟩

end SegInvSP

/-! ## The greatest closed invariant -/

/-- A pair's closure moved along `inv ⊆ inv'`. -/
theorem closeSP_mono {inv inv' : FragS isa} (hI : ∀ s c fs, inv s c fs → inv' s c fs)
    (h : ((∀ s', ¬ K s s') → OutSP p lbl ms inv (Pend p inv) s c fs) ∧ KOutS K p inv s c fs) :
    ((∀ s', ¬ K s s') → OutSP p lbl ms inv' (Pend p inv') s c fs) ∧ KOutS K p inv' s c fs :=
  kOutSP_mono h hI hI

/-- **The greatest closed invariant inside `W`**: the pairs of some
`SegInvSP` invariant inside `W`. -/
def GfpSP (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : Lbl)
    (ms : List TermRun.Frame → MemSide isa) : FragS isa :=
  fun s c fs => ∃ inv, SegInvSP W K p lbl ms inv ∧ inv s c fs

/-- Every `SegInvSP` invariant's pairs are `GfpSP`'s. -/
theorem le_gfpSP {inv : FragS isa} (h : SegInvSP W K p lbl ms inv) :
    ∀ s c fs, inv s c fs → GfpSP W K p lbl ms s c fs :=
  fun _ _ _ hi => ⟨inv, h, hi⟩

/-- **`GfpSP` is a `SegInvSP` invariant.** -/
theorem segInvSP_gfpSP : SegInvSP W K p lbl ms (GfpSP W K p lbl ms) := by
  rintro s c fs ⟨inv, h, hi⟩
  obtain ⟨hw, hcl⟩ := h s c fs hi
  exact ⟨hw, closeSP_mono (le_gfpSP h) hcl⟩

/-- **The start of a segment with no exit is in `GfpSP`.** -/
theorem gfpSP_of_segWSP (h : SegWSP W K p lbl ms P (fun _ _ _ => False)) :
    ∀ s c fs, P s c fs → GfpSP W K p lbl ms s c fs := by
  obtain ⟨inv, hP, hS⟩ := SegInvSP.ofSegWSP h
  exact fun s c fs hp => le_gfpSP hS s c fs (hP s c fs hp)

end Frames

/-! ## `NodesA.out`'s rows -/

/-- **An `OutSP` row is `NodesA.out`'s**: under `msOfAX … ab`, with the
publication landing in the fragment `I lbl lsize`, it is an `OutS` row or
`PubOut`. -/
theorem out_or_pub {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)} {lsize : Lsize} {s : State} {c : Ctl}
    {fs : List TermRun.Frame} {Y : FragS isa} (hY : ∀ s c fs, Y s c fs → I lbl lsize s c fs)
    (hp : (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).pub → ar.pub)
    (h : OutSP p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize) Y (Pend p (I lbl lsize)) s c fs) :
    OutS p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize) (Pend p (I lbl lsize)) s c fs ∨
      PubOut Λ p μ rd G own ar I ab lbl lsize s c fs :=
  h.imp id fun ⟨hns, hpub, c₁, hps, hy, ho⟩ => ⟨hns, hp hpub, c₁, hps, hY _ _ _ hy, ho⟩

/-- `msOfAX`'s publication is the arena's. -/
theorem msOfAX_pub {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)} {lsize : Lsize}
    {fs : List TermRun.Frame} : (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).pub = ar.pub := by
  cases ab <;> rfl

end Spike.Lib.X64SegWPub

-- No axioms beyond Lean's.
/-- info: 'Spike.Lib.Out.toP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Out.toP

/-- info: 'Spike.Lib.SegW.toP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.SegW.toP

/-- info: 'Spike.Lib.X64SegWPub.SegWP.seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWP.seq

/-- info: 'Spike.Lib.X64SegWPub.SegWP.or_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWP.or_pre

/-- info: 'Spike.Lib.X64SegWPub.SegWP.exists_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWP.exists_pre

/-- info: 'Spike.Lib.X64SegWPub.SegWP.pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWP.pub

/-- info: 'Spike.Lib.SegW.pubP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.SegW.pubP

/-- info: 'Spike.Lib.SegWS.toP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.SegWS.toP

/-- info: 'Spike.Lib.X64SegWPub.SegWSP.liftS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWSP.liftS

/-- info: 'Spike.Lib.X64SegWPub.SegWSP.seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWSP.seq

/-- info: 'Spike.Lib.X64SegWPub.SegWSP.post_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWSP.post_run

/-- info: 'Spike.Lib.X64ConsumerA.SegInvS.toP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.SegInvS.toP

/-- info: 'Spike.Lib.X64SegWPub.SegInvSP.ofSegWSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegInvSP.ofSegWSP

/-- info: 'Spike.Lib.X64SegWPub.SegInvSP.mono_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegInvSP.mono_xa

/-- info: 'Spike.Lib.X64SegWPub.segInvSP_gfpSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.segInvSP_gfpSP

/-- info: 'Spike.Lib.X64SegWPub.gfpSP_of_segWSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.gfpSP_of_segWSP

/-- info: 'Spike.Lib.X64SegWPub.out_or_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.out_or_pub

/-- info: 'Spike.Lib.X64SegWPub.msOfAX_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.msOfAX_pub

/-- info: 'Spike.Lib.X64SegWPub.SegWSP.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWSP.empty

/-- info: 'Spike.Lib.X64SegWPub.SegWSP.exists_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWSP.exists_pre

/-- info: 'Spike.Lib.X64SegWPub.SegWSP.mono_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWSP.mono_K

/-- info: 'Spike.Lib.X64SegWPub.SegWSP.mono_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWSP.mono_xa
