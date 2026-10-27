/-
**Frame runs with the memory lets** (`FrameRun` of `Spike/Lib/SegS.lean`
and three more steps): the ghost run of an `Accepted2` body's segments
passes its lane stores, buffer allocations and output calls, which are not
frame steps (their source steps write the memory). At the control, each
binds its name and moves to its body, its words left free: what the memory
gives is the memory side's (the node invariants' facts on the words).

- `MemLet`: `xchgAt`, `newBuf`, a call of `print`;
- `FrameStepM`, `FrameRunM`: a frame step or a memory let's step at fixed
  frames, the source not holding; `FrameRun.toM`, `FrameRunM.single`,
  `.trans`, `.ofLocal`, `.mem1`.
-/
import Spike.Lib.SegS

namespace Spike.Lib

open CoreLang CoreTerm

variable {p : Prog}

/-- **A let whose step writes the memory**: a lane store, a buffer
allocation, or a call of the output extern. -/
def MemLet : Op → Prop
  | .xchgAt _ _ _ | .newBuf _ _ => True
  | .call g _ _ _ => g = "print"
  | _ => False

/-- **One step of a thread with its frames, memory lets included**: a
frame step, or at a memory let (no hold) the binding of its name to some
words, at the same frames. -/
inductive FrameStepM (p : Prog) : Ctl × List TermRun.Frame → Ctl × List TermRun.Frame → Prop
  | frame {q q' : Ctl × List TermRun.Frame} : FrameStep p q q' → FrameStepM p q q'
  | mem {c : Ctl} {fs : List TermRun.Frame} {x : String} {op : Op} {e : Expr} {u : Ty}
      {ws : List TermRun.Word} :
      c.hold = none → c.term = .let_ x op e → MemLet op →
      FrameStepM p (c, fs) (⟨e, (x, u, ws) :: c.env, none⟩, fs)

/-- Zero or more `FrameStepM`s. -/
inductive FrameRunM (p : Prog) : Ctl × List TermRun.Frame → Ctl × List TermRun.Frame → Prop
  | refl (q : Ctl × List TermRun.Frame) : FrameRunM p q q
  | step {q q₁ q' : Ctl × List TermRun.Frame} : FrameStepM p q q₁ → FrameRunM p q₁ q' → FrameRunM p q q'

/-- **A frame run is a `FrameRunM`.** -/
theorem FrameRun.toM {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q') : FrameRunM p q q' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.frame hs) ih

namespace FrameRunM

theorem single {q q' : Ctl × List TermRun.Frame} (h : FrameStepM p q q') : FrameRunM p q q' :=
  .step h (.refl _)

theorem trans {q q₁ q' : Ctl × List TermRun.Frame} (h₁ : FrameRunM p q q₁) (h₂ : FrameRunM p q₁ q') :
    FrameRunM p q q' := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- A local run is a `FrameRunM` at any fixed frames. -/
theorem ofLocal {c c' : Ctl} (h : LocalRun p c c') (fs : List TermRun.Frame) : FrameRunM p (c, fs) (c', fs) :=
  FrameRun.toM (FrameRun.ofLocal h fs)

/-- **A memory let's step** as a run. -/
theorem mem1 {c : Ctl} {fs : List TermRun.Frame} {x : String} {op : Op} {e : Expr} {u : Ty}
    {ws : List TermRun.Word} (hh : c.hold = none) (ht : c.term = .let_ x op e) (hm : MemLet op) :
    FrameRunM p (c, fs) (⟨e, (x, u, ws) :: c.env, none⟩, fs) :=
  single (.mem hh ht hm)

end FrameRunM

end Spike.Lib
