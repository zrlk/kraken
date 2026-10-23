import Scc.Lower.InvBodyA64
import Spike.Test.LowerInv

/-!
# The per-step invariants of the lowering on `ret0.w`

`Scc.Lower.InvBody`'s and `Scc.Lower.InvBodyA64`'s statements instantiated
at `ret0.w`'s code block `main` (closed form `ret0Res`, `ret0_lower0`): the
steps of its body (`let x = 40`, `let y = x + 40`… as `lower0` peels them),
`BodyInv` along them, and the facts of the context `main` is emitted in, in
any program and at any index. Each is an application of the generic
theorem to `ret0_lower0`; nothing decides over the whole program.
-/

namespace Spike.Test.LowerInvBody

open Scc Scc.IR Scc.Lower Scc.Lower.Inv Scc.Lower.InvA64 Scc.Emit.A64
open Spike.Test.LowerInv Spike.Lib.Ret0Src

/-- `main`'s function. -/
abbrev mainF : Func := func0 (Names.user "main") ret0Res

-- The instructions are all `addChk`, one per counter step.
example : (∀ i ∈ ret0Res.insts, ∃ d p q, i = .addChk d p q) ∧ ret0Res.next = 0 + ret0Res.insts.length :=
  lower0_insts_addChk _ _ _ _ ret0_lower0

-- The registers of `main` are those its instructions write: `y%0`.
example (x : Reg) : x ∈ funcRegs mainF ↔ x ∈ defsOf ret0Res.insts :=
  mem_funcRegs_func0 _ ret0_lower0 x

example : (funcRegs mainF).length ≤ 1 := funcRegs_length_func0 _ ret0_lower0

-- In any program, at any index: no outgoing area, a frame of 16-byte
-- multiples of at most 4095 bytes (one `+`), `BodyInv` at the start.
example (p : IR.Program) (fi : Nat) : (A64.ctxOf p fi mainF).out = 0 :=
  ctxOf_func0_out p fi _ (lower0_insts_addChk _ _ _ _ ret0_lower0).1

example (p : IR.Program) (fi : Nat) : (A64.ctxOf p fi mainF).frame % 16 = 0 :=
  ctxOf_frame_mod16 p fi _

example (p : IR.Program) (fi : Nat) : (A64.ctxOf p fi mainF).frame ≤ 4095 :=
  ctxOf_func0_frame_le p fi _ ret0_lower0 (by decide)

example (p : IR.Program) (fi : Nat) :
    BodyInv (A64.ctxOf p fi mainF).slots 0 [(main0.arg, .unit, [])] ∧
      (∀ d ∈ defsOf ret0Res.insts, d ∈ (A64.ctxOf p fi mainF).slots) ∧
      ∀ x ∈ ret0Res.ret.flatMap StackMap.opRegs, x ∈ (A64.ctxOf p fi mainF).slots :=
  bodyInv_func0 p fi _ ret0_lower0

/-! ## The steps of `main`'s body -/

/-- The body after its first `let` (`x = 40`). -/
def body1 : CoreTerm.Expr := match main0.body with | .let_ _ _ e => e | e => e

/-- The environment after it. -/
def env1 : Env := [("x", .intS (.lit 40), [imm 40]), (main0.arg, .unit, [])]

theorem body_eq : main0.body = .let_ "x" (.atom (.lit 40)) body1 := rfl

theorem body1_eq : body1 = .let_ "y" (.add (.var "x") (.lit 2)) (.ret (.var "y")) := rfl

-- Step 1, `let x = 40`: no instruction, `BodyInv` after it.
example (S : List Reg) : ∃ t w r', atomV [(main0.arg, .unit, [])] (.lit 40) = some (t, [w]) ∧
    scalar1 t = true ∧ lower0 ((("x" : String), t, [w]) :: [(main0.arg, .unit, [])]) 0 body1 = some r' ∧
    r'.insts = ret0Res.insts ∧ r'.ret = ret0Res.ret ∧ r'.next = ret0Res.next ∧
    (∀ y ∈ StackMap.opRegs w, y ∈ S) ∧ BodyInv S 0 (("x", t, [w]) :: [(main0.arg, .unit, [])]) :=
  bodyInv_atom (bodyInv_init S main0.arg) (body_eq ▸ ret0_lower0)

/-- The closed form of the rest of the body after step 1. -/
theorem env1_lower0 : lower0 env1 0 body1 = some ret0Res := rfl

-- Step 2, `let y = x + 2`: `addChk y%0 40 2` with `y%0` a slot, new to the
-- environment; `BodyInv` at counter 1 after it.
example (p : IR.Program) (fi : Nat)
    (hI : BodyInv (A64.ctxOf p fi mainF).slots 0 env1) :
    ∃ tp p' tq q r', atomV env1 (.var "x") = some (tp, [p']) ∧ atomV env1 (.lit 2) = some (tq, [q]) ∧
      lower0 (("y", .int, [.reg (regName "y" 0)]) :: env1) 1 (.ret (.var "y")) = some r' ∧
      ret0Res.insts = .addChk (regName "y" 0) p' q :: r'.insts ∧ r'.ret = ret0Res.ret ∧
      r'.next = ret0Res.next ∧
      (∀ y ∈ StackMap.opRegs p', y ∈ (A64.ctxOf p fi mainF).slots) ∧
      (∀ y ∈ StackMap.opRegs q, y ∈ (A64.ctxOf p fi mainF).slots) ∧
      regName "y" 0 ∈ (A64.ctxOf p fi mainF).slots ∧
      (∀ v ∈ env1, ∀ y ∈ v.2.2.flatMap StackMap.opRegs, y ≠ regName "y" 0) ∧
      (∀ d ∈ defsOf r'.insts, d ∈ (A64.ctxOf p fi mainF).slots) ∧
      BodyInv (A64.ctxOf p fi mainF).slots (0 + 1) (("y", .int, [.reg (regName "y" 0)]) :: env1) :=
  bodyInv_add hI (bodyInv_func0 p fi _ ret0_lower0).2.1 (body1_eq ▸ env1_lower0)

-- The whole-program statement at `ret0.w` (AArch64): whenever the lowering
-- and emission succeed, `main`'s context has the invariants, with the frame
-- bound (one `+`).
example (em : Scc.Lower.A64.Emitted) (h : Scc.Lower.A64.lowerAll? { arch := .arm } ret0Src = .ok em) :
    ∃ r rt, lower0 [(main0.arg, .unit, [])] 0 main0.body = some r ∧
      ∃ c : FnCtx, c = A64.ctxOf (progOf ({ arch := .arm } : Config).layout rt
        [func0 (Names.user "main") r]) rt.length (func0 (Names.user "main") r) ∧
      FrameOk c ∧ c.out = 0 ∧ c.frame % 16 = 0 ∧ c.frame ≤ 4095 ∧
      BodyInv c.slots 0 [(main0.arg, .unit, [])] := by
  rw [ret0Src_eq] at h
  obtain ⟨r, rt, hr, -, -, -, hc⟩ := main_inv_a64 { arch := .arm } main0_accepted h
  obtain ⟨hF, ho, hm, -, -, -, -, -, -, hI, -, hle⟩ := hc
  rw [ret0_lower0] at hr
  cases hr
  exact ⟨ret0Res, rt, ret0_lower0, _, rfl, hF, ho, hm, hle, hI⟩

end Spike.Test.LowerInvBody
