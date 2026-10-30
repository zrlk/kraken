import Scc.Lower.Inv
import Scc.Lower.InvA64
import Scc.Lower.SpecA64
import Spike.Lib.Ret0Src
import Scc.Test.Src

/-!
# The closed form of the lowering and its invariants on `ret0.w`

`Scc.Lower.Inv`'s statements instantiated at `ret0.w`'s code block `main`:
its hypotheses hold (`Accepted0`, the closed form exists), the closed form is
`[addChk y%0 40 2]` returning `y%0` with `x` code-free, and
`lowerDeclMarks` gives `func0`/`marks0` for it, as the generic theorems say.

`Scc.Lower.InvA64`'s hypotheses hold of the AArch64 context of `main` in
the lowered program, and its slot and `addChk` facts are instances there.
-/

namespace Spike.Test.LowerInv

open Scc Scc.IR Scc.Lower Scc.Lower.Inv
open Spike.Lib.Ret0Src

/-- `ret0.w`'s code block. -/
def main0 : CoreTerm.Decl :=
  { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int, body := ret0Body }

theorem ret0Src_eq : ret0Src = [main0] := rfl

theorem main0_accepted : Accepted0 [main0] = true := by decide

/-- The closed form of `main`'s body. -/
def ret0Res : Res :=
  { insts := [.addChk "y%0" (imm 40) (imm 2)], ret := [.reg "y%0"], next := 1,
    marked := ["y%0"],
    here := ([("y", .int, [.reg "y%0"]), ("x", .intS (.lit 40), [imm 40]), ("u", .unit, [])],
      .ret (.var "y")) }

theorem ret0_lower0 : lower0 [(main0.arg, .unit, [])] 0 main0.body = some ret0Res := by
  rfl

-- `regName` is the name `fresh` gives.
#guard regName "y" 0 == "y%0"

-- The generic closed-form theorem, instantiated at `main`.
example : lowerDeclMarks ret0Src [] main0 {} none =
    .ok (func0 (Names.user "main") ret0Res, marks0 main0) := by
  obtain ⟨r, hr, h⟩ := lowerDeclMarks_accepted0 ret0Src [] {} none main0_accepted
  rw [ret0_lower0] at hr
  cases hr
  exact h

-- The same, computed.
#guard match lowerDeclMarks ret0Src [] main0 with
  | .ok (f, ms) => f == func0 (Names.user "main") ret0Res && ms.size == 1 &&
      (ms.map (·.1)) == #[.block "entry"]
  | .error _ => false

-- The invariants, instantiated at `main`.
example : BlocksWF (func0 (Names.user "main") ret0Res).blocks ∧
    MarksIn (func0 (Names.user "main") ret0Res) (marks0 main0) ∧
    (func0 (Names.user "main") ret0Res).params = [] ∧
    (∀ b ∈ (func0 (Names.user "main") ret0Res).blocks,
      DefBefore [] b.insts b.term ∧ (defsOf b.insts).Nodup) :=
  accepted0_inv _ ret0_lower0

example : (dests_nodup _ _ 0 _ ret0_lower0).1 = (by decide : 0 ≤ 1) := rfl

/-! ## AArch64 slots of `main` -/

section A64
open Scc.Emit.A64 Scc.Lower.InvA64

/-- The lowered `ret0.w`. -/
def ret0IR : IR.Program := (Scc.Lower.A64.lowerAll { arch := .arm } ret0Src).low.ir

/-- The AArch64 context of `main` in it. -/
def mainCtx : FnCtx :=
  match ret0IR.funcs.zipIdx.find? (·.1.name == Names.user "main") with
  | some (f, fi) => fnCtx ret0IR.abortFn ret0IR.growth
      (IR.StackMap.argAreas ret0IR argRegs.length) fi f
  | none => fnCtx "" none [] 0 (func0 "" ret0Res)

-- `main` in the lowered program is `func0`.
#guard ret0IR.funcs.find? (·.name == Names.user "main") == some (func0 (Names.user "main") ret0Res)

-- Its slots are `y%0`, then nothing else; the frame is small.
#guard mainCtx.slots == ["y%0"] && mainCtx.frame ≤ 32768

theorem mainCtx_frameOk : FrameOk mainCtx := by
  unfold mainCtx; split <;> exact fnCtx_frameOk ..

theorem mainCtx_small : mainCtx.frame ≤ 32768 := by decide +kernel

theorem mainCtx_slots : mainCtx.slots = ["y%0"] := by decide +kernel

theorem mainCtx_y : mainCtx.slotOff "y%0" = .ok (8 * (mainCtx.out : Int)) := by
  simp [FnCtx.slotOff, mainCtx_slots]

-- The generic bounds, at `y%0`.
example : 0 ≤ 8 * (mainCtx.out : Int) ∧ (8 * (mainCtx.out : Int)) % 8 = 0 ∧
    8 * (mainCtx.out : Int) + 8 ≤ (mainCtx.frame : Int) - 16 :=
  slotOff_bounds mainCtx_frameOk mainCtx_y

-- The code of `main`'s `addChk`, by the generic lemma.
example : mainCtx.inst 0 (.addChk "y%0" (imm 40) (imm 2)) =
    .ok (movImm .X9 40 ++ movImm .X10 2 ++ addChecked .X9 .X9 .X10 (mainCtx.local "abort_overflow") ++
      [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 (8 * (mainCtx.out : Int)), none⟩⟩)]) :=
  inst_addChk mainCtx_frameOk mainCtx_small 0 rfl rfl mainCtx_y

-- The code of `main`'s `ret [y%0]` and the frame's exit, by the generic lemmas.
example : mainCtx.term 0 (.ret [.reg "y%0"]) =
    .ok ([ins (.LDR (rz .W64 .X0) (.addr ⟨spW64, .imm ⟨i64 (8 * (mainCtx.out : Int)), none⟩⟩))] ++
      mainCtx.leave ++ [ret]) :=
  term_ret1 0 (getReg_eq mainCtx_frameOk mainCtx_small mainCtx_y .X0)

example : mainCtx.leave =
    [ins (.LDR (rz .W64 .X29) (.addr ⟨spW64, .imm ⟨i64 ((mainCtx.frame : Int) - 16), none⟩⟩)),
      ins (.LDR (rz .W64 .X30) (.addr ⟨spW64, .imm ⟨i64 ((mainCtx.frame : Int) - 8), none⟩⟩))] ++
      addImm spW64 spW64 mainCtx.frame :=
  leave_eq mainCtx_frameOk mainCtx_small

-- The emitted frame sizes: every function's frame is at most 32 KiB, and
-- `mainCtx` is `ctxOf` of `main`.
#guard (Scc.Lower.A64.lowerAll { arch := .arm } ret0Src).frames.all (· ≤ 32768)
#guard (Scc.Lower.A64.lowerAll { arch := .arm } ret0Src).frames ==
  Scc.Lower.A64.framesOf ret0IR
#guard (ret0IR.funcs.zipIdx.find? (·.1.name == Names.user "main")).map
  (fun (f, fi) => (Scc.Lower.A64.ctxOf ret0IR fi f).frame) == some mainCtx.frame

-- The whole-program statement's hypotheses hold of `ret0.w` (AArch64).
#guard (Scc.Lower.A64.lowerAll? { arch := .arm } ret0Src).isOk
#guard match Scc.Lower.Inv.rtFuncs .arm ({ arch := .arm } : Config).layout ⟨.unit, true⟩ 0 with
  | .ok rt => ret0IR.funcs == rt ++ [func0 (Names.user "main") ret0Res]
  | .error _ => false

-- The main-thread runtime function's frame and result slot, against the
-- emitted contexts of `scc_rt_main` in `ret0.w` (entry `main(Unit) : Int`)
-- and `hello1.w` (a setup block of 4 words).
/-- `hello1.w` as the frontend reads it. -/
def hello1Src : CoreTerm.Prog :=
  match Frontend.run (w_src% "Scc/Test/hello1.w") with
  | .ok c => c.prog
  | .error _ => []

/-- The emitted context of `scc_rt_main` in a program, with the program's
entry shape. -/
def rtMainCtx (p : CoreTerm.Prog) : Option (Frontend.Entry × FnCtx) :=
  let e := Scc.Lower.A64.lowerAll { arch := .arm } p
  (e.low.ir.funcs.zipIdx.find? (·.1.name == Names.mainThread)).map fun (f, fi) =>
    (e.low.checked.entry, Scc.Lower.A64.ctxOf e.low.ir fi f)

#guard Scc.Lower.A64.mainFrame ⟨.unit, true⟩ 0 == 48 && Scc.Lower.A64.mainSpill ⟨.unit, true⟩ 0 == 8
#guard Scc.Lower.A64.mainFrame ⟨.setupTid, true⟩ 4 == 80 &&
  Scc.Lower.A64.mainSpill ⟨.setupTid, true⟩ 4 == 40

#guard match rtMainCtx ret0Src with
  | some (en, c) => en.arg == .unit && en.retInt && c.out == 0 &&
      c.frame == Scc.Lower.A64.mainFrame en 0 &&
      (match c.slotOff "v%0" with | .ok o => o == (Scc.Lower.A64.mainSpill en 0 : Int) | .error _ => false)
  | none => false

#guard match rtMainCtx hello1Src with
  | some (en, c) => en.arg == .setupTid && en.retInt && c.out == 0 &&
      c.frame == Scc.Lower.A64.mainFrame en 4 &&
      (match c.slotOff "v%4" with | .ok o => o == (Scc.Lower.A64.mainSpill en 4 : Int) | .error _ => false)
  | none => false

-- `funcItems` is the emission `emitItemsMaps` concatenates (`main`'s items).
#guard match ret0IR.funcs.zipIdx.find? (·.1.name == Names.user "main") with
  | some (f, fi) => (Scc.Lower.A64.funcItems ret0IR fi f).isOk
  | none => false

end A64

end Spike.Test.LowerInv
