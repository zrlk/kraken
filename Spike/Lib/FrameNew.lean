/-
**No frame step at a box allocation** (ISA-neutral): the source's `let x =
new a in e` allocates (`TermRun.alloc` moves the allocation count on), so no
local step is taken there, and a frame run from it is empty. The twin of the
consumers' `localStepS_not_newBuf` / `FrameRun.eq_of_newBuf` for boxes,
which needs no evaluation premise (a `new` that does not evaluate takes no
step at all).

- `localStepS_not_new`: no local step at `let x = new a in e`.
- `FrameRun.eq_of_new`: a frame run from there is empty.
-/
import Spike.Lib.SegS
import WeakCore.TermStep

namespace Spike.Lib.FrameNew

open CoreLang CoreTerm

variable {p : Prog}

/-- **No local step at a box allocation**: the source's step there, if any,
moves the allocation count on (`TermStep.alloc_growsP`), which a local step
keeps. -/
theorem localStepS_not_new {c c' : Ctl} (h : LocalStepS p c c') {x : String} {a : At} {T : Option Ty} {e : Expr}
    (ht : c.term = .let_ x (.new a T) e) : False := by
  obtain ⟨-, h2⟩ := h
  let g : TermRun.G := { p := p, k := default, arch := default, lbase := 0, n := 1, i := 0 }
  let th : TermRun.TTh := { term := c.term, env := c.env }
  have hs := h2 g (#[] : WeakMem.Memory) [] th rfl rfl rfl rfl
  have hm : ((#[] : WeakMem.Memory), ([] : List Nat), { th with term := c'.term, env := c'.env }) ∈
      TermRun.tstep g (#[] : WeakMem.Memory) [] th := by rw [hs]; exact List.mem_singleton_self _
  simp only [TermRun.tstep, th, ht, List.mem_map] at hm
  obtain ⟨⟨s', t, ws⟩, hev, he⟩ := hm
  simp only [TermRun.evalOp] at hev
  split at hev
  · simp at hev
  · split at hev
    · simp at hev
    · simp only [List.mem_map] at hev
      obtain ⟨r, hr, hre⟩ := hev
      have hg := (TermStep.alloc_growsP (fun t ht => by simp [TermRun.stOf] at ht) r hr).2.2.1
      obtain ⟨rfl, -, -⟩ := Prod.mk.inj hre
      have hn := congrArg (fun q => q.2.2.nalloc) he
      split at hn <;> (simp only [TermRun.withS] at hn; simp [TermRun.stOf] at hg; omega)

/-- **A frame run from a box allocation is empty.** -/
theorem FrameRun.eq_of_new {c : Ctl} {fs : List TermRun.Frame} {q' : Ctl × List TermRun.Frame}
    (hr : FrameRun p (c, fs) q') {x : String} {a : At} {T : Option Ty} {e : Expr} (ht : c.term = .let_ x (.new a T) e) :
    q' = (c, fs) := by
  cases hr with
  | refl => rfl
  | step hs _ =>
    cases hs with
    | loc hl => exact (localStepS_not_new hl ht).elim
    | call hc => rw [ht] at hc; cases hc
    | ret hc => rw [ht] at hc; cases hc

/-- info: 'Spike.Lib.FrameNew.FrameRun.eq_of_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.FrameNew.FrameRun.eq_of_new

end Spike.Lib.FrameNew
