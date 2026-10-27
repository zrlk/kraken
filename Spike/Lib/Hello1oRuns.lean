/-
**The controls `hello1o`'s frame runs reach** (ISA-neutral): the counterpart
of `Spike/Lib/Hello1Runs.lean` for `hello1o` (`Spike/Test/Hello1MainSrc.lean`),
`hello1.w`'s program with `print` linked (`printL`'s loop: `ifeq`s, an element
`loadAt`, a `lane`, an `emit`, tail calls into `printL`). Every term along a
frame run from the setup block's start is a suffix (`Suffix`: through `let`,
`split`, `unpack` bodies and both `ifeq` branches) of the start term or of a
body of the program, and so is every suspended frame's body (`Good1Ho`, kept
by every frame step: `good1Ho_run`). The argument is generic in the program:
it asks that every suffix of every body pass the check `goodB` (`ProgOk`),
which `hello1o` does by evaluation (`hello1o_ok`). Such a control is at no
`load` or `store` (`printL` reads its slot by `loadAt`), and its only buffer
allocation is of `LanesU8` elements.

- `Suffix`, `allSuf`, `allSuf_of_suffix`: suffixes and a check of all of them.
- `goodB`: a term whose local step stays among suffixes and bodies: a `let`
  of anything but `callc`, `load`, `store` or a non-`LanesU8` `newBuf`; a
  `split`, `unpack`, `ifeq`, `ret` or tail call. `ProgOk`, `hello1o_ok`.
- `localStepS_ifeq_mem`: a local step at an `ifeq` moves to a branch.
- `InT`, `Good1Ho`, `inT_localStepS`, `good1Ho_step`, `good1Ho_run`.
- `Good1Ho.not_load`, `Good1Ho.not_store`, `Good1Ho.newBuf_ty`.
- `sufs`, `hello1oTerms`, `inT_of_mem`: the suffixes as a list, for callers
  that check a concrete term's membership by `simp`.
-/
import Spike.Lib.Hello1Runs
import Spike.Test.Hello1MainSrc

namespace Spike.Lib.Hello1oRuns

open CoreLang CoreTerm
open Spike.Lib (Ctl LocalStepS FrameStep FrameRun)
open Spike.Lib.Hello1Runs (setupStartTerm)
open Spike.Test.Hello1MainSrc (hello1o)

/-! ## Suffixes -/

/-- **`e` is a suffix of `r`**: reached from `r` through `let`, `split` and
`unpack` bodies and both branches of `ifeq`. -/
inductive Suffix (r : Expr) : Expr → Prop
  | refl : Suffix r r
  | let_ {x : String} {op : Op} {e : Expr} : Suffix r (.let_ x op e) → Suffix r e
  | split {a : At} {x y : String} {e : Expr} : Suffix r (.split a x y e) → Suffix r e
  | unpack {a : At} {i x : String} {e : Expr} : Suffix r (.unpack a i x e) → Suffix r e
  | yes {a b : At} {y n : Expr} : Suffix r (.ifeq a b y n) → Suffix r y
  | no {a b : At} {y n : Expr} : Suffix r (.ifeq a b y n) → Suffix r n

/-- **`P` holds at every suffix of `e`.** -/
def allSuf (P : Expr → Bool) (e : Expr) : Bool :=
  P e && match e with
    | .let_ _ _ e' => allSuf P e'
    | .split _ _ _ e' => allSuf P e'
    | .unpack _ _ _ e' => allSuf P e'
    | .ifeq _ _ y n => allSuf P y && allSuf P n
    | _ => true

theorem allSuf_self {P : Expr → Bool} {e : Expr} (h : allSuf P e = true) : P e = true := by
  unfold allSuf at h
  exact (Bool.and_eq_true _ _ ▸ h).1

/-- **The check passes at every suffix.** -/
theorem allSuf_of_suffix {P : Expr → Bool} {r e : Expr} (h : Suffix r e) (hr : allSuf P r = true) :
    allSuf P e = true := by
  induction h with
  | refl => exact hr
  | let_ _ ih => unfold allSuf at ih; simp only [Bool.and_eq_true] at ih; exact ih.2
  | split _ ih => unfold allSuf at ih; simp only [Bool.and_eq_true] at ih; exact ih.2
  | unpack _ ih => unfold allSuf at ih; simp only [Bool.and_eq_true] at ih; exact ih.2
  | yes _ ih => unfold allSuf at ih; simp only [Bool.and_eq_true] at ih; exact ih.2.1
  | no _ ih => unfold allSuf at ih; simp only [Bool.and_eq_true] at ih; exact ih.2.2

/-! ## The check -/

/-- **A term the frame runs handle**: a `let` of anything but a call
through a code value, a `load`, a `store` or a buffer of other than
`LanesU8` elements; a `split`, `unpack`, `ifeq`, `ret` or tail call. -/
def goodB : Expr → Bool
  | .let_ _ op _ =>
    match op with
    | .callc .. | .load .. | .store .. => false
    | .newBuf _ τ => match τ with
      | .lanes false .w8 => true
      | _ => false
    | _ => true
  | .split .. | .unpack .. | .ifeq .. | .ret _ | .tail .. => true
  | _ => false

/-- **Every suffix of the start term and of every body passes `goodB`.** -/
def ProgOk (p : Prog) : Prop :=
  allSuf goodB setupStartTerm = true ∧ ∀ d ∈ p, allSuf goodB d.body = true

/-- `hello1o` passes the check (by evaluation). -/
theorem hello1o_ok : ProgOk hello1o := by
  refine ⟨by decide, ?_⟩
  decide

/-! ## Where a local step moves -/

variable {p : Prog} {c c' : Ctl}

/-- The global context of the step below (any would do). -/
private def gO (p : Prog) : TermRun.G := { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }

/-- **A local step at an `ifeq`** moves to one of its branches. -/
theorem localStepS_ifeq_mem (h : LocalStepS p c c') {a b : At} {y n : Expr} (ht : c.term = .ifeq a b y n) :
    c'.term = y ∨ c'.term = n := by
  have := h.2 (gO p) #[] [] { term := .ifeq a b y n, env := c.env } rfl ht.symm rfl rfl
  have h2 := congrArg (fun l => l.map (·.2.2.term)) this
  simp only [TermRun.tstep, List.map_cons, List.map_nil] at h2
  repeat' split at h2
  all_goals first
    | (simp at h2; done)
    | (simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h2
       first | exact .inl h2.symm | exact .inr h2.symm)

/-! ## The controls a frame run reaches -/

/-- **A term of `p`'s runs**: a suffix of the start term or of a body. -/
def InT (p : Prog) (e : Expr) : Prop :=
  Suffix setupStartTerm e ∨ ∃ d ∈ p, Suffix d.body e

namespace InT

theorem let_ {x : String} {op : Op} {e : Expr} (h : InT p (.let_ x op e)) : InT p e :=
  h.imp (·.let_) fun ⟨d, hd, h⟩ => ⟨d, hd, h.let_⟩

theorem split {a : At} {x y : String} {e : Expr} (h : InT p (.split a x y e)) : InT p e :=
  h.imp (·.split) fun ⟨d, hd, h⟩ => ⟨d, hd, h.split⟩

theorem unpack {a : At} {i x : String} {e : Expr} (h : InT p (.unpack a i x e)) : InT p e :=
  h.imp (·.unpack) fun ⟨d, hd, h⟩ => ⟨d, hd, h.unpack⟩

theorem yes {a b : At} {y n : Expr} (h : InT p (.ifeq a b y n)) : InT p y :=
  h.imp (·.yes) fun ⟨d, hd, h⟩ => ⟨d, hd, h.yes⟩

theorem no {a b : At} {y n : Expr} (h : InT p (.ifeq a b y n)) : InT p n :=
  h.imp (·.no) fun ⟨d, hd, h⟩ => ⟨d, hd, h.no⟩

/-- The body of a declaration `find?` returns is a term of the runs. -/
theorem of_find {f : String} {d : Decl} (hd : p.find? (·.name == f) = some d) : InT p d.body :=
  .inr ⟨d, List.mem_of_find?_eq_some hd, .refl⟩

/-- **A term of the runs passes `goodB`.** -/
theorem goodB (hp : ProgOk p) {e : Expr} (h : InT p e) : Hello1oRuns.goodB e = true := by
  rcases h with h | ⟨d, hd, h⟩
  · exact allSuf_self (allSuf_of_suffix h hp.1)
  · exact allSuf_self (allSuf_of_suffix h (hp.2 d hd))

end InT

/-- **A control with frames `p`'s runs reach**: its term and every
suspended frame's body terms of the runs (`InT`). -/
def Good1Ho (p : Prog) (q : Ctl × List TermRun.Frame) : Prop :=
  InT p q.1.term ∧ ∀ f ∈ q.2, InT p f.body

/-- **A local step keeps the terms.** -/
theorem inT_localStepS (hp : ProgOk p) (hs : LocalStepS p c c') (h : InT p c.term) : InT p c'.term := by
  have hg := h.goodB hp
  cases hc : c.term with
  | let_ x op e =>
    rw [hc] at h hg
    have hcall : ∀ f is a ts, op ≠ .call f is a ts := by
      rintro f is a ts rfl; exact Spike.Lib.LocalStepS.not_call hs hc
    have hcc : ∀ f a, op ≠ .callc f a := by
      rintro f a rfl; simp [goodB] at hg
    rw [Hello1Runs.localStepS_let hs hc hcall hcc]
    exact h.let_
  | split a x y e => rw [Hello1Runs.localStepS_split hs hc]; exact (hc ▸ h).split
  | unpack a i x e => rw [Hello1Runs.localStepS_unpack hs hc]; exact (hc ▸ h).unpack
  | ifeq a b y n =>
    rcases localStepS_ifeq_mem hs hc with he | he <;> rw [he]
    · exact (hc ▸ h).yes
    · exact (hc ▸ h).no
  | tail f is a ts =>
    obtain ⟨d, hd, he⟩ := Hello1Runs.localStepS_tail hs hc
    rw [he]
    exact InT.of_find hd
  | ret a => exact (Hello1Runs.localStepS_not_ret hs a hc).elim
  | _ => rw [hc] at hg; simp [goodB] at hg

/-- **A frame step keeps `Good1Ho`.** -/
theorem good1Ho_step (hp : ProgOk p) {q q' : Ctl × List TermRun.Frame} (h : FrameStep p q q') (hg : Good1Ho p q) :
    Good1Ho p q' := by
  cases h with
  | loc hs => exact ⟨inT_localStepS hp hs hg.1, hg.2⟩
  | @call c fs x f is a e d t ws ht hd ha =>
    refine ⟨InT.of_find hd, ?_⟩
    rintro f' hf'
    rcases List.mem_cons.mp hf' with rfl | hf'
    · exact (ht ▸ hg.1).let_
    · exact hg.2 f' hf'
  | @ret c fr fs a t ws ht hσ ha =>
    exact ⟨hg.2 fr List.mem_cons_self, fun f hf => hg.2 f (List.mem_cons_of_mem _ hf)⟩

/-- **A frame run keeps `Good1Ho`.** -/
theorem good1Ho_run (hp : ProgOk p) {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q') (hg : Good1Ho p q) :
    Good1Ho p q' := by
  induction h with
  | refl => exact hg
  | step hs _ ih => exact ih (good1Ho_step hp hs hg)

/-- A `Good1Ho` control is at no load. -/
theorem Good1Ho.not_load (hp : ProgOk p) {q : Ctl × List TermRun.Frame} (h : Good1Ho p q) :
    ∀ x k a e, q.1.term ≠ .let_ x (.load k a) e := by
  intro x k a e ht
  have := h.1.goodB hp
  rw [ht] at this
  simp [goodB] at this

/-- A `Good1Ho` control is at no store. -/
theorem Good1Ho.not_store (hp : ProgOk p) {q : Ctl × List TermRun.Frame} (h : Good1Ho p q) :
    ∀ x k a b o e, q.1.term ≠ .let_ x (.store k a b o) e := by
  intro x k a b o e ht
  have := h.1.goodB hp
  rw [ht] at this
  simp [goodB] at this

/-- **A `Good1Ho` control allocates only buffers of `LanesU8` elements.** -/
theorem Good1Ho.newBuf_ty (hp : ProgOk p) {q : Ctl × List TermRun.Frame} (h : Good1Ho p q) {x : String} {a : At}
    {τ : Ty} {e : Expr} (ht : q.1.term = .let_ x (.newBuf a τ) e) : τ = .lanes false .w8 := by
  have := h.1.goodB hp
  rw [ht] at this
  simp only [goodB] at this
  split at this
  · rfl
  · cases this

/-! ## The suffixes as a list -/

/-- **The suffixes of `e`**, `e` first. -/
def sufs (e : Expr) : List Expr :=
  e :: match e with
    | .let_ _ _ e' => sufs e'
    | .split _ _ _ e' => sufs e'
    | .unpack _ _ _ e' => sufs e'
    | .ifeq _ _ y n => sufs y ++ sufs n
    | _ => []

/-- A term is among its suffixes. -/
@[simp] theorem self_mem_sufs (e : Expr) : e ∈ sufs e := by
  unfold sufs; exact List.mem_cons_self

/-- Every listed suffix is a suffix. -/
theorem suffix_of_mem_sufs : ∀ {r e : Expr}, e ∈ sufs r → Suffix r e
  | .let_ x op e', e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact .refl
    · exact suffix_trans (suffix_of_mem_sufs h) (.let_ .refl)
  | .split a x y e', e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact .refl
    · exact suffix_trans (suffix_of_mem_sufs h) (.split .refl)
  | .unpack a i x e', e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact .refl
    · exact suffix_trans (suffix_of_mem_sufs h) (.unpack .refl)
  | .ifeq a b y n, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact .refl
    · rcases List.mem_append.mp h with h | h
      · exact suffix_trans (suffix_of_mem_sufs h) (.yes .refl)
      · exact suffix_trans (suffix_of_mem_sufs h) (.no .refl)
  | .unpackT .., e, h | .region .., e, h | .openPub .., e, h | .case .., e, h | .ifnull .., e, h
  | .parity .., e, h | .cas .., e, h | .casp .., e, h | .ret _, e, h | .tail .., e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact .refl
    · simp at h
where
  /-- A suffix of a suffix is a suffix. -/
  suffix_trans {r m e : Expr} (h1 : Suffix m e) (h2 : Suffix r m) : Suffix r e := by
    induction h1 with
    | refl => exact h2
    | let_ _ ih => exact ih.let_
    | split _ ih => exact ih.split
    | unpack _ ih => exact ih.unpack
    | yes _ ih => exact ih.yes
    | no _ ih => exact ih.no

/-- **The terms of `hello1o`'s runs**: the suffixes of the start term and of
every body. -/
def hello1oTerms : List Expr :=
  sufs setupStartTerm ++ hello1o.flatMap fun d => sufs d.body

/-- A listed term is a term of `hello1o`'s runs. -/
theorem inT_of_mem {e : Expr} (h : e ∈ hello1oTerms) : InT hello1o e := by
  rcases List.mem_append.mp h with h | h
  · exact .inl (suffix_of_mem_sufs h)
  · obtain ⟨d, hd, h⟩ := List.mem_flatMap.mp h
    exact .inr ⟨d, hd, suffix_of_mem_sufs h⟩

/-- **`Good1Ho` from listed terms** (checkable by `simp` on a concrete
term). -/
theorem good1Ho_of_mem {q : Ctl × List TermRun.Frame} (ht : q.1.term ∈ hello1oTerms)
    (hfs : ∀ f ∈ q.2, f.body ∈ hello1oTerms) : Good1Ho hello1o q :=
  ⟨inT_of_mem ht, fun f hf => inT_of_mem (hfs f hf)⟩

end Spike.Lib.Hello1oRuns
