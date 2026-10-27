/-
**The per-pair source facts at depth through a call bracket** (ISA-neutral):
the source halves of `SFactsS` (`Spike/Lib/X64SegInstS.lean`,
`Spike/Lib/A64SegInstS.lean`) at the real pairs of a call bracket and its
callee, the caller at the frames `fs` and the callee at `fr :: fs`. The
source call is `CallTo`'s (`Spike/Lib/X64CallS.lean`,
`Spike/Lib/A64CallS.lean`) body (`SrcCallTo`, the two ISAs' `CallTo` by
`id`), and `EnvSmallS` its body (`EnvSmall env ∧ ∀ f ∈ fs, EnvSmall f.env`),
so both ISAs use these facts as they are.

- `SrcCallTo`, `SrcCallTo.step`: the source call, a frame step;
- `good1_callTo`, `good1_retTo`: `Good1` (`Spike/Lib/Frames1.lean`) from the
  caller into the callee's entry and from the callee's return back into the
  caller's continuation;
- `envNum_entry`, `envSmall_entry`: the callee's entry environment, one
  argument word, a number below `2^64`, is numeric and small;
- `framesSmall_callTo`, `envSmallS_callTo`: every frame's environment small
  at the callee's entry, from the caller's and the argument's;
- `envSmall_retTo`, `framesSmall_retTo`, `envSmallS_retTo`: the same back in
  the caller after the return, the returned words small;
- `noRet_cons`, `cell_of_good1`, `noAlloc_of_good1`: `SFactsS.noRet`
  (vacuous at depth), `SFactsS.cell` and `SFactsS.noAlloc` at any frames
  from a `Good1` pair of an `Accepted1` program.
-/
import Spike.Lib.Frames1
import Spike.Lib.AbortSrc

namespace Spike.Lib

open CoreLang CoreTerm
open Spike.Lib.LowerNode (EnvNum)

variable {p : Prog}

/-! ## The source call -/

/-- **A source call** (the body of either ISA's `CallTo`): the control `c`
is at `let x = call f a in e` of a code block `f` of `p` with no type or
index arguments; the callee starts at `cE` (its body, its argument bound to
`a`'s words at its declared type) with the frame `fr` (returning into `x`
and then `e`, in `c`'s environment) pushed. -/
def SrcCallTo (p : Prog) (c cE : Ctl) (fr : TermRun.Frame) : Prop :=
  ∃ (x f : String) (a : CoreTerm.At) (e : Expr) (d : Decl) (t : Ty) (ws : List TermRun.Word),
    c.term = .let_ x (.call f [] a []) e ∧ p.find? (·.name == f) = some d ∧
    TermRun.evalAt c.env a = some (t, ws) ∧ cE = ⟨d.body, [(d.arg, d.argTy, ws)], none⟩ ∧
    fr = ⟨x, e, c.env, [], d.retTy⟩

/-- A source call is a frame step. -/
theorem SrcCallTo.step {c cE : Ctl} {fr : TermRun.Frame} (h : SrcCallTo p c cE fr) (fs : List TermRun.Frame) :
    FrameStep p (c, fs) (cE, fr :: fs) := by
  obtain ⟨x, f, a, e, d, t, ws, ht, hd, ha, rfl, rfl⟩ := h
  exact .call ht hd ha

/-- The pushed frame keeps the caller's environment. -/
theorem SrcCallTo.env {c cE : Ctl} {fr : TermRun.Frame} (h : SrcCallTo p c cE fr) : fr.env = c.env := by
  obtain ⟨x, f, a, e, d, t, ws, -, -, -, -, rfl⟩ := h
  rfl

/-- The pushed frame has no type variables. -/
theorem SrcCallTo.σs {c cE : Ctl} {fr : TermRun.Frame} (h : SrcCallTo p c cE fr) : fr.σs = [] := by
  obtain ⟨x, f, a, e, d, t, ws, -, -, -, -, rfl⟩ := h
  rfl

/-- The callee's entry holds nothing. -/
theorem SrcCallTo.hold {c cE : Ctl} {fr : TermRun.Frame} (h : SrcCallTo p c cE fr) : cE.hold = none := by
  obtain ⟨x, f, a, e, d, t, ws, -, -, -, rfl, -⟩ := h
  rfl

/-! ## `Good1` through the bracket -/

/-- **`Good1` into the callee's entry**: the callee's body and the pushed
frame's continuation are subterms of code blocks. -/
theorem good1_callTo (hp : Scc.Lower.Accepted1 p = true) {c cE : Ctl} {fr : TermRun.Frame}
    {fs : List TermRun.Frame} (hg : Good1 p (c, fs)) (h : SrcCallTo p c cE fr) : Good1 p (cE, fr :: fs) :=
  good1_step hp (h.step fs) hg

/-- **`Good1` back in the caller** after the callee's return into the top
frame. -/
theorem good1_retTo (hp : Scc.Lower.Accepted1 p = true) {c : Ctl} {fr : TermRun.Frame} {fs : List TermRun.Frame}
    {a : At} {t : Ty} {ws : List TermRun.Word} (hc : c.term = .ret a) (hσ : fr.σs = [])
    (ha : TermRun.evalAt c.env a = some (t, ws)) (hg : Good1 p (c, fr :: fs)) :
    Good1 p (⟨fr.body, (fr.x, fr.ty, ws) :: fr.env, none⟩, fs) :=
  good1_step hp (.ret hc hσ ha) hg

/-! ## Small environments through the bracket -/

/-- **The callee's entry environment is numeric**: one binding of one word,
a number below `2^64`. -/
theorem envNum_entry {x : String} {t : Ty} {w : TermRun.Word} {k : Nat} (hw : w.val = .num k) (hk : k < 2 ^ 64) :
    EnvNum [(x, t, [w])] := by
  intro b hb w' hw'
  simp only [List.mem_singleton] at hb
  subst hb
  simp only [List.mem_singleton] at hw'
  subst hw'
  exact ⟨k, hw, hk⟩

/-- **The callee's entry environment is small.** -/
theorem envSmall_entry {x : String} {t : Ty} {w : TermRun.Word} {k : Nat} (hw : w.val = .num k)
    (hk : k < 2 ^ 64) : EnvSmall [(x, t, [w])] :=
  AbortSrc.envSmall_of_envNum (envNum_entry hw hk)

/-- **Every suspended frame's environment small at the callee's entry**:
the caller's environment (the pushed frame's) and the caller's suspended
frames'. -/
theorem framesSmall_callTo {c cE : Ctl} {fr : TermRun.Frame} {fs : List TermRun.Frame} (h : SrcCallTo p c cE fr)
    (hc : EnvSmall c.env) (hfs : ∀ f ∈ fs, EnvSmall f.env) : ∀ f ∈ fr :: fs, EnvSmall f.env := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · rw [h.env]; exact hc
  · exact hfs f hf

/-- **`EnvSmallS` at the callee's entry**: the callee's entry environment
small (`hE`, e.g. `envSmall_entry`) and the caller's `EnvSmallS`. -/
theorem envSmallS_callTo {c cE : Ctl} {fr : TermRun.Frame} {fs : List TermRun.Frame} (h : SrcCallTo p c cE fr)
    (hE : EnvSmall cE.env) (hc : EnvSmall c.env ∧ ∀ f ∈ fs, EnvSmall f.env) :
    EnvSmall cE.env ∧ ∀ f ∈ fr :: fs, EnvSmall f.env :=
  ⟨hE, framesSmall_callTo h hc.1 hc.2⟩

/-- **The caller's environment small after the return**: the top frame's
environment and the returned words small. -/
theorem envSmall_retTo {fr : TermRun.Frame} {ws : List TermRun.Word} (hf : EnvSmall fr.env)
    (hw : ∀ w ∈ ws, ∀ n, w.val = .num n → n < 2 ^ 64) : EnvSmall ((fr.x, fr.ty, ws) :: fr.env) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hw
  · exact hf b hb

/-- **The remaining frames small after the return.** -/
theorem framesSmall_retTo {fr : TermRun.Frame} {fs : List TermRun.Frame} (h : ∀ f ∈ fr :: fs, EnvSmall f.env) :
    ∀ f ∈ fs, EnvSmall f.env :=
  fun f hf => h f (List.mem_cons_of_mem _ hf)

/-- **`EnvSmallS` back in the caller after the return**, the returned words
small. -/
theorem envSmallS_retTo {env : TermRun.Env} {fr : TermRun.Frame} {fs : List TermRun.Frame}
    {ws : List TermRun.Word} (h : EnvSmall env ∧ ∀ f ∈ fr :: fs, EnvSmall f.env)
    (hw : ∀ w ∈ ws, ∀ n, w.val = .num n → n < 2 ^ 64) :
    EnvSmall ((fr.x, fr.ty, ws) :: fr.env) ∧ ∀ f ∈ fs, EnvSmall f.env :=
  ⟨envSmall_retTo (h.2 fr List.mem_cons_self) hw, framesSmall_retTo h.2⟩

/-! ## `SFactsS`' source fields at any frames -/

/-- **`SFactsS.noRet` at depth**: vacuous at a pushed frame. -/
theorem noRet_cons {c : Ctl} {fr : TermRun.Frame} {fs : List TermRun.Frame} :
    fr :: fs = [] → ∀ a, c.term ≠ .ret a :=
  fun h => nomatch h

/-- **`SFactsS.cell` from `Good1`**: no frame run from a `Good1` pair of an
`Accepted1` program reaches a load or a store, at any frames. -/
theorem cell_of_good1 (hp : Scc.Lower.Accepted1 p = true) {c : Ctl} {fs : List TermRun.Frame}
    (hg : Good1 p (c, fs)) {Q : Ty → Prop} :
    ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty (w : TermRun.Word),
      (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
      TermRun.evalAt c'.env a = some (ty, [w]) → Q ty := by
  intro c' fs' hr x a e ty w hc _
  have hg' := good1_run hp hr hg
  rcases hc with hc | ⟨b, hc⟩
  · exact (hg'.not_load x true a e hc).elim
  · exact (hg'.not_store x true a b none e hc).elim

/-- **`SFactsS.noAlloc` from `Good1`**: no frame run from a `Good1` pair of
an `Accepted1` program reaches a buffer allocation, at any frames. -/
theorem noAlloc_of_good1 (hp : Scc.Lower.Accepted1 p = true) {c : Ctl} {fs : List TermRun.Frame}
    (hg : Good1 p (c, fs)) :
    ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term ≠ .let_ x (.newBuf a τ) e :=
  fun _ _ hr => (good1_run hp hr hg).not_newBuf

end Spike.Lib
