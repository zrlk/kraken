import Spike.Lib.LowerX64.PrintArgs
import Spike.Lib.LowerX64.PrintCall
import Spike.Lib.X64Hello1Body

/-!
# `print`'s argument block at `hello1`'s frame (x86-64)

`printArgs_runs` (`Spike/Lib/LowerX64/PrintArgs.lean`) instantiated at a
frame with `wc_main`'s layout (`b`, `o`, `m`, `n` at `-8`…`-32`, `lo`, `s`,
`cap`, `k` at `-48`…`-72`, size 80): the emitted code of `callBlock`'s
`.print` case is `hello1`'s `.entry` block, `wcE1`, the multiply `wcMul`,
then `wcE2` (`Spike/Lib/X64Hello1Body.lean`), and its run leaves `b + lo(o)`
in `%rdi` and `min(n, 8·m)` in `%rsi`. Its cells as `pblk` are
`print_block_segW`'s (`Spike/Lib/LowerX64/PrintCall.lean`).
-/

namespace Spike.Test.LowerX64PrintArgs

open Kraken Spike.Lib Spike.Lib.X64 Spike.Lib.LowerX64
open Scc.Emit.X64 (E Item emitInst)
open Spike.Lib.Form (opdVal)

/-- A function whose frame has `wc_main`'s layout (register `x` unused by
the block). -/
def wcF : Scc.IR.Func where
  name := "wc_main"
  params := ["b", "o", "m", "n", "x", "lo", "s", "cap", "k"]
  blocks := []

/-- Its frame. -/
def fr : Scc.Emit.X64.Frame := Scc.Emit.X64.frameOf [] wcF

theorem hf : FrameOk fr := ⟨[], wcF, rfl, rfl⟩

theorem h1 : fr.size ≤ 2 ^ 31 := by decide

/-- The five IR instructions of the block and the call. -/
def body : E Unit := do
  emitInst fr none (.ext false .w32 "lo" (.reg "o"))
  emitInst fr none (.bin .add "s" (.reg "b") (.reg "lo"))
  emitInst fr none (.bin .mul "cap" (.reg "m") (Scc.Lower.imm 8))
  emitInst fr none (.select .ult "k" (.reg "n") (.reg "cap") (.reg "n") (.reg "cap"))
  emitInst fr none (.call [] Scc.Lower.Names.print [.reg "s", .reg "k"])

/-- The body's directives. -/
def bodyD : List Directive := match body {} with
  | .ok (_, s) => dirs s.out.reverse
  | .error _ => []

-- The emission is `hello1`'s `.entry` block.
example : bodyD = List.map Prod.fst X64.Flow.Hello1.wcE1 ++ [FI.toDir X64.Flow.Hello1.wcMul] ++
    List.map Prod.fst X64.Flow.Hello1.wcE2 := by
  rfl

/-- An emission's items, `[]` on failure. -/
def okD : Except String (List Item) → List Item
  | .ok a => a
  | .error _ => []

abbrev lg (t : Reg64) (a : Scc.IR.Operand) : List Item := okD (getOp fr t a)

-- The block's two runs, around the multiply.
example (lab : String → Int64) (σ : AS) :
    ∃ vb vo vm vn : BitVec 64, opdVal (rsOf fr) σ.slot (.reg "b") = some vb.toNat ∧
      opdVal (rsOf fr) σ.slot (.reg "o") = some vo.toNat ∧
      opdVal (rsOf fr) σ.slot (.reg "m") = some vm.toNat ∧
      opdVal (rsOf fr) σ.slot (.reg "n") = some vn.toNat ∧
      RunsP lab (oB fr) (dirs (lg .rax (.reg "o")) ++ [ext32D, stDir (-48)] ++
          (dirs (lg .rax (.reg "b")) ++ dirs (lg .rcx (.reg "lo")) ++ [addD, stDir (-56)]) ++
          (dirs (lg .rax (.reg "m")) ++ dirs (lg .rcx (Scc.Lower.imm 8)))) σ (fun σ1 => ∀ fl : StatusFlags,
        RunsP lab (oB fr) ([stDir (-64)] ++ (dirs (lg .rdx (.reg "n")) ++ dirs (lg .rsi (.reg "cap")) ++
            dirs (lg .rax (.reg "n")) ++ dirs (lg .rcx (.reg "cap")) ++
            [cmpD, movRsiD, cmovD .c, stDir (-72)]) ++ (dirs (lg .rdi (.reg "s")) ++ dirs (lg .rsi (.reg "k"))))
          (mulFI.step σ1 fl)
          (fun σ' => σ'.regs.get64 .rdi = vb + (vo.take 32).setWidth 64 ∧
            σ'.regs.get64 .rsi = (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64) ∧
            ∀ j, (∀ q, rsOf fr q = some j → q ≠ "lo" ∧ q ≠ "s" ∧ q ≠ "cap" ∧ q ≠ "k") →
              σ'.slot j = σ.slot j)) :=
  printArgs_runs hf h1 lab (lo := "lo") (s := "s") (cap := "cap") (kk := "k") (o := .reg "o") (b := .reg "b")
    (m := .reg "m") (n := .reg "n") rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp) (by simp) (by simp) (by decide) (by decide) σ

-- The two blocks are covered in the frame's region.
example : CovP (-(fr.size : Int)) 16 (oB fr) (dirs (lg .rax (.reg "o")) ++ [ext32D, stDir (-48)] ++
      (dirs (lg .rax (.reg "b")) ++ dirs (lg .rcx (.reg "lo")) ++ [addD, stDir (-56)]) ++
      (dirs (lg .rax (.reg "m")) ++ dirs (lg .rcx (Scc.Lower.imm 8)))) ∧
    CovP (-(fr.size : Int)) 16 (oB fr) ([stDir (-64)] ++ (dirs (lg .rdx (.reg "n")) ++ dirs (lg .rsi (.reg "cap")) ++
      dirs (lg .rax (.reg "n")) ++ dirs (lg .rcx (.reg "cap")) ++ [cmpD, movRsiD, cmovD .c, stDir (-72)]) ++
      (dirs (lg .rdi (.reg "s")) ++ dirs (lg .rsi (.reg "k")))) :=
  ⟨covP_printPre hf h1 (lo := "lo") (s := "s") (o := .reg "o") (b := .reg "b") (m := .reg "m") rfl rfl rfl rfl rfl
      rfl rfl,
    covP_printPost hf h1 (cap := "cap") (kk := "k") (s := .reg "s") (n := .reg "n") rfl rfl rfl rfl rfl rfl rfl rfl⟩

/-- The block's cells at `hello1`'s sizes (`pblk`). -/
abbrev blk (pc : Int64) : PBlk :=
  pblk pc (preD (lg .rax (.reg "o")) (lg .rax (.reg "b")) (lg .rcx (.reg "lo")) (lg .rax (.reg "m"))
      (lg .rcx (Scc.Lower.imm 8)) (-48) (-56)) [4, 2, 4, 4, 4, 3, 4, 4, 7] 4
    (postD (lg .rdx (.reg "n")) (lg .rsi (.reg "cap")) (lg .rax (.reg "n")) (lg .rcx (.reg "cap"))
      (lg .rdi (.reg "s")) (lg .rsi (.reg "k")) (-64) (-72)) [4, 4, 4, 4, 4, 3, 3, 4, 4, 4, 4] 5

-- `print_block_segW`'s cells are `hello1`'s: `wcE1`, the multiply at `+36`, `wcE2` (its `call` at `+82`).
example (pc : Int64) : (blk pc).pre = X64.Flow.Hello1.wcE1 ∧
    (blk pc).post ++ [(callD, (blk pc).zc)] = X64.Flow.Hello1.wcE2 ∧
    (blk pc).pc1 = pc + 36 ∧ (blk pc).pc2 = pc + 36 + 4 ∧ (blk pc).pc3 = pc + 36 + 4 + 42 := by
  refine ⟨by rfl, by rfl, rfl, rfl, rfl⟩

end Spike.Test.LowerX64PrintArgs
