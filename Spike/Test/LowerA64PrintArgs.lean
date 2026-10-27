import Spike.Lib.LowerA64.PrintArgs
import Spike.Lib.LowerA64.PrintCall
import Spike.Lib.A64Hello1Body

/-!
# `print`'s argument block at `hello1`'s frame (AArch64)

`printArgs_run` (`Spike/Lib/LowerA64/PrintArgs.lean`) instantiated at a
context with `wc_main`'s frame layout (`b`, `o`, `m`, `n` at offsets 0–24,
`lo`, `s`, `cap`, `k` at 40–64, frame 96): the emitted code of `callBlock`'s
`.print` case is `hello1`'s `.0_entry` block `wcE`
(`Spike/Lib/A64Hello1Body.lean`), and its run leaves `b + lo(o)` in `x0` and
`min(n, 8·m)` in `x1`. With `blPrintD` it is `print_block_segW`'s code
(`Spike/Lib/LowerA64/PrintCall.lean`), and at `print`'s entry `x1` is
`printN` of `n`, `m`'s values (`callSt_facts`).
-/

namespace Spike.Test.LowerA64PrintArgs

open Kraken Kraken.AArch64.Parser Scc.Emit.A64 Scc.Lower.InvA64 Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.LowerA64
open Spike.Lib.Form (opdVal)

/-- A context with `wc_main`'s frame layout (slot 4 unused by the block). -/
def ctx : FnCtx where
  fi := 19
  name := "wc_main"
  slots := ["b", "o", "m", "n", "x", "lo", "s", "cap", "k"]
  blocks := ["entry"]
  frame := 96
  abortFn := "scc_rt_abort"

theorem hf : FrameOk ctx := by unfold FrameOk; decide

/-- An emission's items, `d` on failure. -/
def okD {α : Type} (d : α) : Except String α → α
  | .ok a => a
  | .error _ => d

abbrev l1 := okD [] (ctx.inst 0 (.ext false .w32 "lo" (.reg "o")))
abbrev l2 := okD [] (ctx.inst 1 (.bin .add "s" (.reg "b") (.reg "lo")))
abbrev l3 := okD [] (ctx.inst 2 (.bin .mul "cap" (.reg "m") (Scc.Lower.imm 8)))
abbrev l4 := okD [] (ctx.inst 3 (.select .ult "k" (.reg "n") (.reg "cap") (.reg "n") (.reg "cap")))
abbrev l5 := okD [] (ctx.getArgs [.reg "s", .reg "k"])

-- The block and the call are `wcE`.
example : directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ [.instr ⟨.W64, .BL "scc_rt_print"⟩] =
    Hello1.wcE := by rfl

-- So is the emission of the five IR instructions (`inst_print_call`'s shape, no stack map).
example : (match (do
      let l1 ← ctx.inst 0 (.ext false .w32 "lo" (.reg "o"))
      let l2 ← ctx.inst 1 (.bin .add "s" (.reg "b") (.reg "lo"))
      let l3 ← ctx.inst 2 (.bin .mul "cap" (.reg "m") (Scc.Lower.imm 8))
      let l4 ← ctx.inst 3 (.select .ult "k" (.reg "n") (.reg "cap") (.reg "n") (.reg "cap"))
      let l5 ← ctx.inst 4 (.call [] Scc.Lower.Names.print [.reg "s", .reg "k"])
      return l1 ++ l2 ++ l3 ++ l4 ++ l5 : Except String (List Item)) with
    | .ok l => directives l
    | .error _ => []) = Hello1.wcE := by rfl

-- The run: `x0 = b + lo(o)`, `x1 = min(n, 8·m)`, falling through.
example (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ vb vo vm vn : BitVec 64, opdVal (rsOf ctx) σ.slot (.reg "b") = some vb.toNat ∧
      opdVal (rsOf ctx) σ.slot (.reg "o") = some vo.toNat ∧
      opdVal (rsOf ctx) σ.slot (.reg "m") = some vm.toNat ∧
      opdVal (rsOf ctx) σ.slot (.reg "n") = some vn.toNat ∧
      ∃ (rg : Reg64s) (st : StatusFlags) (sl : Int → BitVec 64),
        rg.X0.toBitVec = vb + (vo.take 32).setWidth 64 ∧
        rg.X1.toBitVec = (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64) ∧
        arun lab (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)) ⟨pc, oF ctx, σ⟩ =
          ⟨pc + Int64.ofNat (4 * (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length), oF ctx, ⟨rg, st, sl⟩⟩ :=
  have h := printArgs_run hf (by decide) (i1 := 0) (i2 := 1) (i3 := 2) (i4 := 3) (lo := "lo") (s := "s")
    (cap := "cap") (kk := "k") (b := .reg "b") (o := .reg "o") (m := .reg "m") (n := .reg "n")
    rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by decide) (by decide) lab pc σ
  let ⟨vb, vo, vm, vn, h1, h2, h3, h4, rg, st, sl, h5, h6, h7, _⟩ := h
  ⟨vb, vo, vm, vn, h1, h2, h3, h4, rg, st, sl, h5, h6, h7⟩

-- The block is covered in the frame.
example : okBlk (-(ctx.frame : Int)) 0 (oF ctx) (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)) = true :=
  okBlk_printArgs hf (by decide) (by decide) (i1 := 0) (i2 := 1) (i3 := 2) (i4 := 3) (lo := "lo") (s := "s")
    (cap := "cap") (kk := "k") (b := .reg "b") (o := .reg "o") (m := .reg "m") (n := .reg "n") rfl rfl rfl rfl rfl

-- With `bl scc_rt_print` (`blPrintD`), the block is `wcE`; its call node's code (`print_block_segW`'s `hcode`).
example : directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD = Hello1.wcE := by rfl

-- At `print`'s entry: `x1`'s count is `printN` of `n`, `m`'s values there (when `8·m < 2^63`).
example (lab : Label → Int64) (pc : Int64) (σ : AS) :
    8 * opdNat ctx (callSt lab ctx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ) (.reg "m") < 2 ^ 63 →
    (callSt lab ctx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ).regs.X1.toBitVec.toNat =
      Spike.Lib.PrintSrc.printN (opdNat ctx (callSt lab ctx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ) (.reg "n"))
        (opdNat ctx (callSt lab ctx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ) (.reg "m")) := by
  intro h8
  obtain ⟨vb, vo, vm, vn, -, -, hvm, hvn, -, -, hx1, -, hsl⟩ :=
    callSt_facts hf (by decide) (i1 := 0) (i2 := 1) (i3 := 2) (i4 := 3) (lo := "lo") (s := "s")
      (cap := "cap") (kk := "k") (b := .reg "b") (o := .reg "o") (m := .reg "m") (n := .reg "n")
      (l1 := l1) (l2 := l2) (l3 := l3) (l4 := l4) (l5 := l5)
      rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by decide) (by decide) lab pc σ
  have en : opdNat ctx (callSt lab ctx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ) (.reg "n") = vn.toNat := by
    exact congrArg (·.getD 0) ((opdVal_kept (lo := "lo") (s := "s") (cap := "cap") (kk := "k") (by simp) hsl).trans hvn)
  have em : opdNat ctx (callSt lab ctx pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ) (.reg "m") = vm.toNat := by
    exact congrArg (·.getD 0) ((opdVal_kept (lo := "lo") (s := "s") (cap := "cap") (kk := "k") (by simp) hsl).trans hvm)
  rw [em] at h8
  rw [en, em, hx1, printN_of_x1 h8]

end Spike.Test.LowerA64PrintArgs
