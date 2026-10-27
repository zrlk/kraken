import Spike.Lib.SegS

/-! Tests for `Spike.Lib.SegS`: frame runs and segments at depth. -/

namespace Spike.Lib.SegSTest

open CoreLang CoreTerm Spike.Lib
open Kraken.Promising

/-- `pick(n) = ret n`, called from `main` with the literal 7. -/
def pickD : Decl := { name := "pick", arg := "n", argTy := .int, retTy := .int, idx := [], body := .ret (.var "n") }

/-- **A call and its return as a frame run**: from `let r = pick(7) in ret r`
at no frame, the call pushes `main`'s frame and the return pops it, binding
`r` to the callee's result. -/
example (env : TermRun.Env) :
    FrameRun [pickD] (⟨.let_ "r" (.call "pick" [] (.lit 7) []) (.ret (.var "r")), env, none⟩, [])
      (⟨.ret (.var "r"), ("r", .int, [TermRun.cst (.num 7)]) :: env, none⟩, []) := by
  refine .step (.call (d := pickD) rfl rfl rfl) (.step (.ret (t := .int) rfl rfl ?_) (.refl _))
  simp [TermRun.evalAt, TermRun.lookupE, pickD]

/-- A local run lifts to a frame run at any frames. -/
example {p : Prog} {c c' : Ctl} (h : LocalRun p c c') (fs : List TermRun.Frame) : FrameRun p (c, fs) (c', fs) :=
  FrameRun.ofLocal h fs

/-- A segment at fixed frames, from a `SegW`. -/
example {I : ISA} {W : Frag I} {K : I.State → I.State → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide I} {P Q : Frag I} (fs : List TermRun.Frame) (h : SegW W K p lbl (ms fs) P Q) :
    SegWS (W.at fs) K p lbl ms (P.at fs) (Q.at fs) :=
  SegWS.liftS fs h fun _ _ h => ⟨h, rfl⟩

end Spike.Lib.SegSTest
