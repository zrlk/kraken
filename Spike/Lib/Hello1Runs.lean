/-
**The controls `hello1.w`'s frame runs reach** (ISA-neutral): every term
along a frame run (`FrameRun`, `Spike/Lib/SegS.lean`) of `hello1Src` from
the setup block's start is a suffix of the start term or of one of the
program's bodies, and so is every suspended frame's body (`Good1H`, kept by
every frame step: `good1H_run`). Such a control is at no load or store, and
its only buffer allocation is `rodata`'s of `LanesU8` elements; the
counterpart of `Spike/Lib/Frames1.lean`'s `Good1` for a program that stores
and allocates.

- `localStepS_let`, `localStepS_split`, `localStepS_unpack`,
  `localStepS_tail`, `localStepS_not_ret`: where a local step at each of
  `hello1Src`'s constructs moves.
- `hello1Terms`: the suffixes of the start term `setupStartTerm` (the
  setup block's call, then `main`'s tail call), `print`'s, `rodata`'s and
  `main`'s bodies; `Good1H`.
- `good1H_step`, `good1H_run`: a frame step and a frame run keep `Good1H`.
- `Good1H.not_load`, `Good1H.not_store`, `Good1H.newBuf_ty`.
-/
import Spike.Lib.Hello1RodataSrc
import Spike.Lib.Frames1

namespace Spike.Lib.Hello1Runs

open CoreLang CoreTerm
open Spike.Lib (Ctl LocalStepS FrameStep FrameRun)
open Spike.Lib.Hello1Src (hello1Src sliceTy)
open Spike.Lib.Hello1RodataSrc

/-! ## Where a local step moves -/

variable {p : Prog} {c c' : Ctl}

/-- The global context of the steps below (any would do). -/
private def gH (p : Prog) : TermRun.G := { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }

/-- **A local step at a `let` of anything but a call** moves to the `let`'s
body. -/
theorem localStepS_let (h : LocalStepS p c c') {x : String} {op : Op} {e : Expr} (ht : c.term = .let_ x op e)
    (hc : ∀ f is a ts, op ≠ .call f is a ts) (hcc : ∀ f a, op ≠ .callc f a) : c'.term = e := by
  have := h.2 (gH p) #[] [] { term := .let_ x op e, env := c.env } rfl ht.symm rfl rfl
  cases op
  case call f is a ts => exact (hc f is a ts rfl).elim
  case callc f a => exact (hcc f a rfl).elim
  case new a T =>
    simp only [TermRun.tstep, List.map_eq_singleton_iff] at this
    obtain ⟨_, -, hf⟩ := this
    have := congrArg (fun q => q.2.2.term) hf
    first
      | (rw [← this]; split <;> rfl)
      | (simp only at this; rw [← this]; split <;> rfl)
  all_goals
    simp only [TermRun.tstep, List.map_eq_singleton_iff] at this
    obtain ⟨_, -, hf⟩ := this
    have := congrArg (fun q => q.2.2.term) hf
    simpa [TermRun.withS] using this.symm

/-- **A local step at a `split`** moves to its body. -/
theorem localStepS_split (h : LocalStepS p c c') {a : At} {x y : String} {e : Expr} (ht : c.term = .split a x y e) :
    c'.term = e := by
  have := h.2 (gH p) #[] [] { term := .split a x y e, env := c.env } rfl ht.symm rfl rfl
  simp only [TermRun.tstep] at this
  repeat' split at this
  all_goals first
    | (have := congrArg (fun l => l.head?.map (·.2.2.term)) this; simpa using this.symm)
    | cases this

/-- **A local step at an `unpack`** moves to its body. -/
theorem localStepS_unpack (h : LocalStepS p c c') {a : At} {i x : String} {e : Expr}
    (ht : c.term = .unpack a i x e) : c'.term = e := by
  have := h.2 (gH p) #[] [] { term := .unpack a i x e, env := c.env } rfl ht.symm rfl rfl
  simp only [TermRun.tstep] at this
  repeat' split at this
  all_goals first
    | (have := congrArg (fun l => l.head?.map (·.2.2.term)) this; simpa using this.symm)
    | cases this

/-- **A local step at a tail call into `f`** moves to `f`'s body. -/
theorem localStepS_tail (h : LocalStepS p c c') {f : String} {is : List String} {a : At} {ts : List Ty}
    (ht : c.term = .tail f is a ts) : ∃ d, p.find? (·.name == f) = some d ∧ c'.term = d.body := by
  have := h.2 (gH p) #[] [] { term := .tail f is a ts, env := c.env } rfl ht.symm rfl rfl
  simp only [TermRun.tstep, TermRun.enter, TermRun.ol, gH] at this
  cases hd : p.find? (·.name == f) with
  | none => simp [hd] at this
  | some d =>
    refine ⟨d, rfl, ?_⟩
    cases hv : TermRun.evalAt c.env a with
    | none => simp [hd, hv] at this
    | some v =>
      have := congrArg (fun l => l.head?.map (·.2.2.term)) this
      simpa [hd, hv] using this.symm

/-- A control at `ret` takes no local step (no frame is on the stack of the
step's thread). -/
theorem localStepS_not_ret (h : LocalStepS p c c') : ∀ a, c.term ≠ .ret a := by
  intro a hc
  have := h.2 (gH p) #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl
  simp [TermRun.tstep, hc] at this

/-! ## The terms -/

/-- **The start term**: the setup block's call into `r`, the pair `a` of it
and `me`, then `main`'s tail call (`Spike.Test.SetupStartSrc.setupTerm`). -/
def setupStartTerm : Expr :=
  .let_ "r" (.call "rodata" [] (.var "u")) (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")))

/-- `main`'s body. -/
def mainBody : Expr :=
  .split (.var "a") "sl0" "me" <|
  .unpack (.var "sl0") "q" "sl" <|
  .let_ "u" (.call "print" ["q"] (.var "sl") []) <|
  .ret (.lit 0)

/-- **The terms of `hello1.w`'s runs**: the suffixes of the start term, of
`print`'s, `rodata`'s and `main`'s bodies. -/
def hello1Terms : List Expr :=
  [setupStartTerm, .let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")),
    .tail "main" [] (.var "a"),
    .ret .unit,
    rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet,
    mainBody, .unpack (.var "sl0") "q" "sl" (.let_ "u" (.call "print" ["q"] (.var "sl") []) (.ret (.lit 0))),
    .let_ "u" (.call "print" ["q"] (.var "sl") []) (.ret (.lit 0)), .ret (.lit 0)]

/-- Every body of `hello1Src` is among its runs' terms. -/
theorem body_mem {d : Decl} (hd : d ∈ hello1Src) : d.body ∈ hello1Terms := by
  simp only [hello1Src, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> simp [hello1Terms, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0,
    ePack, eRet, mainBody, setupStartTerm]

/-- The body of a `let` among the terms is among them. -/
theorem let_mem {x : String} {op : Op} {e : Expr} (h : .let_ x op e ∈ hello1Terms) : e ∈ hello1Terms := by
  simp only [hello1Terms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
    | (simp only [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody,
        Expr.let_.injEq, reduceCtorEq] at h; done)
    | (simp only [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody,
        Expr.let_.injEq, reduceCtorEq] at h
       obtain ⟨-, -, rfl⟩ := h
       simp [hello1Terms, setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet,
         mainBody])

/-- The body of a `split` among the terms is among them. -/
theorem split_mem {a : At} {x y : String} {e : Expr} (h : .split a x y e ∈ hello1Terms) : e ∈ hello1Terms := by
  simp only [hello1Terms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
    | (simp only [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody,
        Expr.split.injEq, reduceCtorEq] at h; done)
    | (simp only [mainBody, Expr.split.injEq] at h
       obtain ⟨-, -, -, rfl⟩ := h
       simp [hello1Terms])

/-- The body of an `unpack` among the terms is among them. -/
theorem unpack_mem {a : At} {i x : String} {e : Expr} (h : .unpack a i x e ∈ hello1Terms) : e ∈ hello1Terms := by
  simp only [hello1Terms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
    | (simp only [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody,
        Expr.unpack.injEq, reduceCtorEq] at h; done)
    | (simp only [Expr.unpack.injEq] at h
       obtain ⟨-, -, -, rfl⟩ := h
       simp [hello1Terms])

/-- The only tail call among the terms is into `main`. -/
theorem tail_mem {f : String} {is : List String} {a : At} {ts : List Ty} (h : .tail f is a ts ∈ hello1Terms) :
    f = "main" := by
  simp only [hello1Terms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp_all [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody]

/-! ## The controls a frame run reaches -/

/-- **A control with frames `hello1.w`'s runs reach**: its term and every
suspended frame's body among `hello1Terms`. -/
def Good1H (q : Ctl × List TermRun.Frame) : Prop :=
  q.1.term ∈ hello1Terms ∧ ∀ f ∈ q.2, f.body ∈ hello1Terms

/-- **A local step keeps the terms.** -/
theorem term_localStepS (hs : LocalStepS hello1Src c c') (h : c.term ∈ hello1Terms) : c'.term ∈ hello1Terms := by
  cases hc : c.term with
  | let_ x op e =>
    rw [hc] at h
    cases op
    case call f is a ts => exact (Spike.Lib.LocalStepS.not_call hs hc).elim
    case callc f a =>
      exfalso
      simp only [hello1Terms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody] at h
    all_goals
      rw [localStepS_let hs hc (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)]
      exact let_mem h
  | split a x y e => rw [localStepS_split hs hc]; exact split_mem (hc ▸ h)
  | unpack a i x e => rw [localStepS_unpack hs hc]; exact unpack_mem (hc ▸ h)
  | tail f is a ts =>
    obtain ⟨d, hd, he⟩ := localStepS_tail hs hc
    rw [he]
    exact body_mem (List.mem_of_find?_eq_some hd)
  | ret a => exact (localStepS_not_ret hs a hc).elim
  | _ =>
    exfalso
    rw [hc] at h
    simp only [hello1Terms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody] at h

/-- **A frame step keeps `Good1H`.** -/
theorem good1H_step {q q' : Ctl × List TermRun.Frame} (h : FrameStep hello1Src q q') (hg : Good1H q) :
    Good1H q' := by
  cases h with
  | loc hs => exact ⟨term_localStepS hs hg.1, hg.2⟩
  | @call c fs x f is a e d t ws ht hd ha =>
    refine ⟨body_mem (List.mem_of_find?_eq_some hd), ?_⟩
    rintro f' hf'
    rcases List.mem_cons.mp hf' with rfl | hf'
    · exact let_mem (ht ▸ hg.1)
    · exact hg.2 f' hf'
  | @ret c fr fs a t ws ht hσ ha =>
    exact ⟨hg.2 fr List.mem_cons_self, fun f hf => hg.2 f (List.mem_cons_of_mem _ hf)⟩

/-- **A frame run keeps `Good1H`.** -/
theorem good1H_run {q q' : Ctl × List TermRun.Frame} (h : FrameRun hello1Src q q') (hg : Good1H q) :
    Good1H q' := by
  induction h with
  | refl => exact hg
  | step hs _ ih => exact ih (good1H_step hs hg)

/-- A `Good1H` control is at no load. -/
theorem Good1H.not_load {q : Ctl × List TermRun.Frame} (h : Good1H q) :
    ∀ x k a e, q.1.term ≠ .let_ x (.load k a) e := by
  intro x k a e ht
  have h1 := h.1
  rw [ht] at h1
  simp only [hello1Terms, List.mem_cons, List.not_mem_nil, or_false] at h1
  rcases h1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody] at h

/-- A `Good1H` control is at no store. -/
theorem Good1H.not_store {q : Ctl × List TermRun.Frame} (h : Good1H q) :
    ∀ x k a b o e, q.1.term ≠ .let_ x (.store k a b o) e := by
  intro x k a b o e ht
  have h1 := h.1
  rw [ht] at h1
  simp only [hello1Terms, List.mem_cons, List.not_mem_nil, or_false] at h1
  rcases h1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody] at h

/-- **A `Good1H` control's only buffer allocation** is `rodata`'s, of
`LanesU8` elements. -/
theorem Good1H.newBuf_ty {q : Ctl × List TermRun.Frame} (h : Good1H q) {x : String} {a : At} {τ : Ty} {e : Expr}
    (ht : q.1.term = .let_ x (.newBuf a τ) e) : τ = .lanes false .w8 := by
  have h1 := h.1
  rw [ht] at h1
  simp only [hello1Terms, List.mem_cons, List.not_mem_nil, or_false] at h1
  rcases h1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp_all [setupStartTerm, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, mainBody]

end Spike.Lib.Hello1Runs
