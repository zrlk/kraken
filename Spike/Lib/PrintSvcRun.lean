/-
**The source's runs from `print`'s output `write`**, on any ISA: from the
loop top with a byte left (`PrintSvc`) every frame run stays at the same
frames, before the byte's `emit`, at no hold and at a term of `printL`'s
body (`PrintTop`); every byte step's landing (`ByteOut`) can be cut down to
such controls. The ISA consumers (`emitA_of_nodes`,
`Spike/Lib/A64EmitOfNodes.lean`, `Spike/Lib/X64EmitOfNodes.lean`) restrict
the fragment's own `Out.emit` row with these to the emit rows (`EmitA`).

- `printTerms t`: `t` followed down through `let`, `split` and both arms of
  `ifeq` (every other constructor a leaf, `ret` kept); `PrintTop c`: the
  control's term is one of `printTerms printLBody`.
- `PrintShape`: a term of only `let`s off `callc`, `split`s, `ifeq`s, `ret ()`s
  and tail calls of `printL`; `printShape_printLBody`, `PrintShape.mem`.
- `LocalStepS.det`, `FrameStep.of_local`, `LocalStepS.not_ext`: a local step
  is determined, is the only frame step where it exists, and is not an
  extern's.
- `localStepS_printTop`, `localRunS_printTop`: local runs stay in
  `PrintTop` (a tail call of `printL` enters `printLBody`).
- `frameRun_printSvc`: the frame runs from `PrintSvc`.
- `byteOut_printTop`: `ByteOut` into its landing at no hold and in
  `PrintTop`.
-/
import Spike.Lib.PrintSvc
import Spike.Lib.ByteOut
import Spike.Lib.Hello1oRuns

namespace Spike.Lib.PrintSvc

open CoreLang CoreTerm
open Spike.Lib Spike.Lib.PrintSrc
open Spike.Lib.ByteOut (ByteOut)

variable {p : Prog}

/-! ## The terms of `printL` -/

/-- **A term followed down** through `let`, `split` and both arms of
`ifeq`: the term itself and every term a thread running it reaches without
a call, a return or a tail call. Every other constructor is a leaf. -/
def printTerms : Expr → List Expr
  | e@(.let_ _ _ b) => e :: printTerms b
  | e@(.split _ _ _ b) => e :: printTerms b
  | e@(.ifeq _ _ y n) => e :: (printTerms y ++ printTerms n)
  | e => [e]

/-- **The control is in `printL`'s body**: its term is one of
`printTerms printLBody`. -/
def PrintTop (c : Ctl) : Prop := c.term ∈ printTerms printLBody

theorem self_mem_printTerms (t : Expr) : t ∈ printTerms t := by
  cases t <;> simp [printTerms]

/-- `printTerms` is transitive. -/
theorem printTerms_trans {t u v : Expr} (hu : u ∈ printTerms t) (hv : v ∈ printTerms u) : v ∈ printTerms t := by
  induction t generalizing u
  case let_ x op b ih =>
    simp only [printTerms, List.mem_cons] at hu ⊢
    rcases hu with rfl | hu
    · simpa [printTerms] using hv
    · exact .inr (ih hu hv)
  case split a x y b ih =>
    simp only [printTerms, List.mem_cons] at hu ⊢
    rcases hu with rfl | hu
    · simpa [printTerms] using hv
    · exact .inr (ih hu hv)
  case ifeq a b y n ihy ihn =>
    simp only [printTerms, List.mem_cons, List.mem_append] at hu ⊢
    rcases hu with rfl | hu | hu
    · simpa [printTerms] using hv
    · exact .inr (.inl (ihy hu hv))
    · exact .inr (.inr (ihn hu hv))
  all_goals
    simp only [printTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    exact hv

/-- **The shape of `printL`'s body**: `let`s off `callc`, `split`s, `ifeq`s,
`ret ()`s and tail calls of `printL` only. -/
def PrintShape : Expr → Prop
  | .let_ _ op b => (∀ f a, op ≠ .callc f a) ∧ PrintShape b
  | .split _ _ _ b => PrintShape b
  | .ifeq _ _ y n => PrintShape y ∧ PrintShape n
  | .ret a => a = .unit
  | .tail f _ _ _ => f = "printL"
  | _ => False

theorem printShape_printLBody : PrintShape printLBody := by
  simp [PrintShape, printLBody, printAdv, printLoad, printLane, printEmit, printNext]

/-- Every term followed down from a term of the shape has the shape. -/
theorem PrintShape.mem {t u : Expr} (ht : PrintShape t) (hu : u ∈ printTerms t) : PrintShape u := by
  induction t
  case let_ x op b ih =>
    simp only [printTerms, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ht
    · exact ih ht.2 hu
  case split a x y b ih =>
    simp only [printTerms, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ht
    · exact ih ht hu
  case ifeq a b y n ihy ihn =>
    simp only [printTerms, List.mem_cons, List.mem_append] at hu
    rcases hu with rfl | hu | hu
    · exact ht
    · exact ihy ht.1 hu
    · exact ihn ht.2 hu
  all_goals
    simp only [printTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    exact ht

/-! ## Local steps -/

/-- The global context of the steps below (any would do). -/
private def gP (p : Prog) : TermRun.G := { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }

/-- **A local step is determined** by its control. -/
theorem LocalStepS.det {c c₁ c₂ : Ctl} (h₁ : LocalStepS p c c₁) (h₂ : LocalStepS p c c₂) : c₁ = c₂ := by
  have e₁ := h₁.2 (gP p) #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl
  have e₂ := h₂.2 (gP p) #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl
  rw [e₁] at e₂
  have ht := congrArg (fun l => l.head?.map (·.2.2.term)) e₂
  have he := congrArg (fun l => l.head?.map (·.2.2.env)) e₂
  simp only [List.head?_cons, Option.map_some, Option.some.injEq] at ht he
  obtain ⟨t₁, v₁, o₁⟩ := c₁
  obtain ⟨t₂, v₂, o₂⟩ := c₂
  have o₁0 : o₁ = none := h₁.1
  have o₂0 : o₂ = none := h₂.1
  simp only at ht he
  subst ht he o₁0 o₂0
  rfl

/-- **A local step is the only frame step** of a control that takes one: a
control at a call or a return takes none. -/
theorem FrameStep.of_local {c c' : Ctl} {fs : List TermRun.Frame} {q : Ctl × List TermRun.Frame}
    (h : LocalStepS p c c') (hq : FrameStep p (c, fs) q) : q = (c', fs) := by
  cases hq with
  | loc h' => rw [LocalStepS.det h h']
  | call ht _ _ => exact (h.not_call ht).elim
  | ret ht _ _ => exact (h.not_ret _ ht).elim

/-- **An extern's `let` takes no local step**: `evalOp` has no successor
there (the extern is a configuration step). -/
theorem LocalStepS.not_ext {c c' : Ctl} (h : LocalStepS p c c') {x : String} {n : ExtName} {a : At} {e : Expr}
    (ht : c.term = .let_ x (.ext n a) e) : False := by
  have := h.2 (gP p) #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl
  simp [TermRun.tstep, ht, TermRun.evalOp] at this

/-- **A local step from a term of the shape** moves to a term followed down
from it, or (a tail call of `printL`) to `printLBody`. -/
theorem localStepS_shape (hd : p.find? (·.name == "printL") = some printLD) {c c' : Ctl} (h : LocalStepS p c c')
    (hs : PrintShape c.term) : c'.term ∈ printTerms c.term ∨ c'.term = printLBody := by
  obtain ⟨t, env, o⟩ := c
  simp only at hs ⊢
  cases t
  case let_ x op b =>
    left
    cases op
    case call f is a ts => exact (h.not_call rfl).elim
    case callc f a => exact (hs.1 f a rfl).elim
    all_goals
      rw [Hello1Runs.localStepS_let h rfl (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)]
      exact List.mem_cons_of_mem _ (self_mem_printTerms _)
  case split a x y b =>
    left
    rw [Hello1Runs.localStepS_split h rfl]
    exact List.mem_cons_of_mem _ (self_mem_printTerms _)
  case ifeq a b y n =>
    left
    rcases Hello1oRuns.localStepS_ifeq_mem h rfl with e | e <;> rw [e]
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (self_mem_printTerms _))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (self_mem_printTerms _))
  case ret a => exact (h.not_ret a rfl).elim
  case tail f is a ts =>
    right
    obtain ⟨d, hf, e⟩ := Hello1Runs.localStepS_tail h rfl
    simp only [PrintShape] at hs
    subst hs
    rw [hd] at hf
    cases hf
    exact e
  all_goals exact hs.elim

/-- **A local step stays in `printL`'s body.** -/
theorem localStepS_printTop (hd : p.find? (·.name == "printL") = some printLD) {c c' : Ctl} (h : LocalStepS p c c')
    (ht : PrintTop c) : PrintTop c' := by
  rcases localStepS_shape hd h (printShape_printLBody.mem ht) with h' | h'
  · exact printTerms_trans ht h'
  · unfold PrintTop
    rw [h']
    exact self_mem_printTerms _

/-- **A local run stays in `printL`'s body.** -/
theorem localRunS_printTop (hd : p.find? (·.name == "printL") = some printLD) {c c' : Ctl} (h : LocalRunS p c c')
    (ht : PrintTop c) : PrintTop c' := by
  induction h with
  | refl => exact ht
  | step hs _ ih => exact ih (localStepS_printTop hd hs ht)

theorem printTop_printLane : printLane ∈ printTerms printLBody := by
  simp [printTerms, printLBody, printAdv, printLoad, printLane, printEmit, printNext]

theorem printTop_printEmit : printEmit ∈ printTerms printLBody := by
  simp [printTerms, printLBody, printAdv, printLoad, printLane, printEmit, printNext]

theorem printTop_printNext : printNext ∈ printTerms printLBody := by
  simp [printTerms, printLBody, printAdv, printLoad, printLane, printEmit, printNext]

/-! ## Frame runs from the output `write` -/

/-- **The controls before the byte's `emit`**, from `c0` with a local run
to the element load `L`: on that run, or at the lane or the `emit` with no
hold. -/
def PreEmit (p : Prog) (c0 L c : Ctl) : Prop :=
  (LocalRunS p c0 c ∧ LocalRunS p c L) ∨ (c.term = printLane ∧ c.hold = none) ∨
    (c.term = printEmit ∧ c.hold = none)

/-- **A frame step keeps `PreEmit`** and the frames. -/
theorem preEmit_step {c0 L c : Ctl} {fs : List TermRun.Frame} {q : Ctl × List TermRun.Frame}
    (hL : L.term = printLoad) (h : PreEmit p c0 L c) (hq : FrameStep p (c, fs) q) : q.2 = fs ∧ PreEmit p c0 L q.1 := by
  rcases h with ⟨h0, hl⟩ | ⟨ht, hh⟩ | ⟨ht, _⟩
  · cases hl with
    | refl =>
      cases hq with
      | loc h' =>
        have hL' : L.term = .let_ "wd" (.loadAt (.var "b") (.var "iv")) printLane := by rw [hL]; rfl
        refine ⟨rfl, .inr (.inl ⟨?_, h'.1⟩)⟩
        exact Hello1Runs.localStepS_let h' hL' (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      | call ht _ _ => rw [hL] at ht; simp [printLoad] at ht
      | ret ht _ _ => rw [hL] at ht; simp [printLoad] at ht
    | step hs hr =>
      rw [FrameStep.of_local hs hq]
      exact ⟨rfl, .inl ⟨h0.trans (.single hs), hr⟩⟩
  · cases hq with
    | loc h' =>
      have ht' : c.term = .let_ "x" (.lane (.var "wd") (.var "j")) printEmit := by rw [ht]; rfl
      refine ⟨rfl, .inr (.inr ⟨?_, h'.1⟩)⟩
      exact Hello1Runs.localStepS_let h' ht' (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
    | call ht' _ _ => rw [ht] at ht'; simp [printLane] at ht'
    | ret ht' _ _ => rw [ht] at ht'; simp [printLane] at ht'
  · cases hq with
    | loc h' => exact (LocalStepS.not_ext h' (by rw [ht]; rfl)).elim
    | call ht' _ _ => rw [ht] at ht'; simp [printEmit] at ht'
    | ret ht' _ _ => rw [ht] at ht'; simp [printEmit] at ht'

/-- **A frame run keeps `PreEmit`** and the frames. -/
theorem preEmit_run {c0 L : Ctl} {fs : List TermRun.Frame} {q q' : Ctl × List TermRun.Frame}
    (hL : L.term = printLoad) (hr : FrameRun p q q') (hq : q.2 = fs) (h : PreEmit p c0 L q.1) :
    q'.2 = fs ∧ PreEmit p c0 L q'.1 := by
  induction hr with
  | refl => exact ⟨hq, h⟩
  | @step q q₁ q' hs _ ih =>
    obtain ⟨c, fs'⟩ := q
    simp only at hq h
    subst hq
    obtain ⟨h1, h2⟩ := preEmit_step hL h hs
    exact ih h1 h2

/-- **The frame runs from the output `write`**: from the loop top with a
byte left (`PrintSvc`), every frame run keeps the frames and ends at no
hold in `printL`'s body. -/
theorem frameRun_printSvc (hd : p.find? (·.name == "printL") = some printLD) {c c₁ : Ctl}
    {fs fs₁ : List TermRun.Frame} (h : PrintSvc c fs) (hr : FrameRun p (c, fs) (c₁, fs₁)) :
    fs₁ = fs ∧ c₁.hold = none ∧ PrintTop c₁ := by
  obtain ⟨-, pw, wn, n, m, k, hc, hk⟩ := h
  have hL := printC_load hd hc hk
  obtain ⟨i, j, ht, -, hh, -⟩ := hc
  have htop : PrintTop c := by unfold PrintTop; rw [ht]; exact self_mem_printTerms _
  obtain ⟨h1, h2⟩ := preEmit_run (c0 := c) rfl hr rfl (.inl ⟨.refl _, hL⟩)
  refine ⟨h1, ?_⟩
  rcases h2 with ⟨h0, -⟩ | ⟨ht', hh'⟩ | ⟨ht', hh'⟩
  · exact ⟨LocalRunS.hold_none h0 hh, localRunS_printTop hd h0 htop⟩
  · exact ⟨hh', by unfold PrintTop; rw [ht']; exact printTop_printLane⟩
  · exact ⟨hh', by unfold PrintTop; rw [ht']; exact printTop_printEmit⟩

/-! ## The byte step -/

/-- **A byte step into its landing at no hold in `printL`'s body**: the
control after the `emit` (`nextC`) is at `printNext` with no hold, and runs
locally. -/
theorem byteOut_printTop (hd : p.find? (·.name == "printL") = some printLD) {I : Kraken.Promising.ISA}
    {lbl : WeakMem.AllocLabel → Option Nat} {s : I.State} {a : Nat} {c1 : Ctl} {Q : Ctl → Prop}
    (h : ByteOut p lbl s a c1 Q) : ByteOut p lbl s a c1 (fun c => Q c ∧ c.hold = none ∧ PrintTop c) := by
  obtain ⟨pw, wn, l, b, m, k, hpw, hl, ha, hrun, hQ⟩ := h
  refine ⟨pw, wn, l, b, m, k, hpw, hl, ha, hrun, fun mw n hmw => ?_⟩
  obtain ⟨c2, r2, h2⟩ := hQ mw n hmw
  refine ⟨c2, r2, h2, LocalRunS.hold_none r2.toS rfl, localRunS_printTop hd r2.toS ?_⟩
  exact printTop_printNext

end Spike.Lib.PrintSvc
