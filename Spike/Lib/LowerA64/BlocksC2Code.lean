/-
**The code of an `Accepted2` block** (AArch64): the code predicate of a
block of the closed form `lowerC2` (`Spike/Lib/LowerShapeC2.lean`) emits, the
`Accepted2` twin of `Spike/Lib/LowerA64/BlocksC1Code.lean`'s `CodeC`, and the
construct blocks of its bodies (`Kind2`, `Spike/Lib/LowerA64/Blocks1.lean`'s
`Kind1` and the `xchg`'s load and store).

- `CodeC2`: `CodeC`'s arms (a non-call instruction's code at `pc`, `Cd`; a
  one-word user call split at its `bl`, `Bl`) and two more calls, each split
  at its `bl` with the return label `spK` after it: `newBuf`'s
  (`newBufCall`: its three arguments' loads into `x0`, `x1`, `x2`, `bl
  scc_rt_alloc`, `x0`'s store into the result) and the output extern's
  (`printInsts`' last instruction: its two arguments' loads into `x0`, `x1`,
  `bl scc_rt_print`, no result). The `xchg`'s load and store and the output
  extern's first four instructions are non-call instructions.
- `BlocksCodeC2`: every block not ending in `unreachable` at its label, as
  `CodeC2` from some instruction number.
- `Kind2`: a construct's block: `Kind1`'s and a `ret` of any number of
  words (`retLoads`, each word into its argument register), as x86-64's
  `KindD2` (the `xchg`'s load and store are the lane store's, `LaneC`).
-/
import Spike.Lib.LowerA64.BlocksC1Code
import Spike.Lib.LowerShapeC2

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerShape (newBufCall)

set_option linter.unusedSimpArgs false

/-! ## The code predicate -/

/-- **The code of an `Accepted2` block's instructions `is` numbered from
`k` at `pc`, then of its terminator `tm`**: `CodeC`'s arms, and the calls of
`newBuf` (`newBufCall p h kv u`: `imm h`, `kv` and `u` loaded into `x0`,
`x1`, `x2` at `pc`, `Cd`; the `bl scc_rt_alloc` after them with the return
label `spK`, `Bl`; `x0`'s store into `p`, `Cd`) and of the output extern
(`call [] scc_rt_print [a0, a1]`: `a0`, `a1` loaded into `x0`, `x1` at `pc`,
`Cd`; the `bl scc_rt_print` after them, `Bl`; no result). -/
def CodeC2 (cx : FnCtx) (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop) :
    Nat → Int64 → List Scc.IR.Inst → Scc.IR.Term → Prop
  | k, pc, [], tm => tm = .unreachable ∨ ∃ l, cx.term k tm = .ok l ∧ Cd pc (directives l)
  | k, pc, i :: is, tm =>
    (Spike.Lib.LowerShape.isCall i = false ∧ ∃ l, cx.inst k i = .ok l ∧ Cd pc (directives l) ∧
      CodeC2 cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (directives l).length)) is tm) ∨
    (∃ d g w lw ls, i = .call [d] (Scc.Lower.Names.user g) [w] ∧ cx.getOp .X0 w = .ok lw ∧
      cx.setReg d .X0 = .ok ls ∧ Cd pc (directives lw) ∧
      Bl (pc + Int64.ofNat (4 * (directives lw).length)) (Scc.Lower.Names.user g) k ∧
      Cd (pc + Int64.ofNat (4 * (directives lw).length) + 4) (directives ls) ∧
      CodeC2 cx Cd Bl (k + 1)
        (pc + Int64.ofNat (4 * (directives lw).length) + 4 + Int64.ofNat (4 * (directives ls).length)) is tm) ∨
    (∃ p h kv u la ls, i = newBufCall p h kv u ∧
      cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la ∧ cx.setReg p .X0 = .ok ls ∧ Cd pc (directives la) ∧
      Bl (pc + Int64.ofNat (4 * (directives la).length)) Scc.Lower.Names.alloc k ∧
      Cd (pc + Int64.ofNat (4 * (directives la).length) + 4) (directives ls) ∧
      CodeC2 cx Cd Bl (k + 1)
        (pc + Int64.ofNat (4 * (directives la).length) + 4 + Int64.ofNat (4 * (directives ls).length)) is tm) ∨
    (∃ a0 a1 la, i = .call [] Scc.Lower.Names.print [a0, a1] ∧ cx.getArgs [a0, a1] = .ok la ∧
      Cd pc (directives la) ∧ Bl (pc + Int64.ofNat (4 * (directives la).length)) Scc.Lower.Names.print k ∧
      CodeC2 cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (directives la).length) + 4) is tm)

/-- **The code of instructions `is` numbered from `k` at `pc`, up to
`pc'`**: `CodeC2`'s arms without the terminator, the code ending at `pc'`
(a construct's part of a block, `CodeC2_append`). -/
def InstsC2 (cx : FnCtx) (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop) :
    Nat → Int64 → List Scc.IR.Inst → Int64 → Prop
  | _, pc, [], pc' => pc' = pc
  | k, pc, i :: is, pc' =>
    (Spike.Lib.LowerShape.isCall i = false ∧ ∃ l, cx.inst k i = .ok l ∧ Cd pc (directives l) ∧
      InstsC2 cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (directives l).length)) is pc') ∨
    (∃ d g w lw ls, i = .call [d] (Scc.Lower.Names.user g) [w] ∧ cx.getOp .X0 w = .ok lw ∧
      cx.setReg d .X0 = .ok ls ∧ Cd pc (directives lw) ∧
      Bl (pc + Int64.ofNat (4 * (directives lw).length)) (Scc.Lower.Names.user g) k ∧
      Cd (pc + Int64.ofNat (4 * (directives lw).length) + 4) (directives ls) ∧
      InstsC2 cx Cd Bl (k + 1)
        (pc + Int64.ofNat (4 * (directives lw).length) + 4 + Int64.ofNat (4 * (directives ls).length)) is pc') ∨
    (∃ p h kv u la ls, i = newBufCall p h kv u ∧
      cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la ∧ cx.setReg p .X0 = .ok ls ∧ Cd pc (directives la) ∧
      Bl (pc + Int64.ofNat (4 * (directives la).length)) Scc.Lower.Names.alloc k ∧
      Cd (pc + Int64.ofNat (4 * (directives la).length) + 4) (directives ls) ∧
      InstsC2 cx Cd Bl (k + 1)
        (pc + Int64.ofNat (4 * (directives la).length) + 4 + Int64.ofNat (4 * (directives ls).length)) is pc') ∨
    (∃ a0 a1 la, i = .call [] Scc.Lower.Names.print [a0, a1] ∧ cx.getArgs [a0, a1] = .ok la ∧
      Cd pc (directives la) ∧ Bl (pc + Int64.ofNat (4 * (directives la).length)) Scc.Lower.Names.print k ∧
      InstsC2 cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (directives la).length) + 4) is pc')

/-- **`CodeC2` of a block split after some instructions**: the code of the
instructions `is` up to some `pc'`, then `CodeC2` of the rest from `pc'`. -/
theorem CodeC2_append {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    {tm : Scc.IR.Term} (is' : List Scc.IR.Inst) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (pc : Int64),
      CodeC2 cx Cd Bl k pc (is ++ is') tm ↔ ∃ pc', InstsC2 cx Cd Bl k pc is pc' ∧
        CodeC2 cx Cd Bl (k + is.length) pc' is' tm
  | [], k, pc => by simp [InstsC2]
  | i :: is, k, pc => by
    have ih := fun k pc => CodeC2_append (cx := cx) (Cd := Cd) (Bl := Bl) (tm := tm) is' is k pc
    simp only [List.cons_append, CodeC2, InstsC2, List.length_cons, ih, show k + 1 + is.length =
      k + (is.length + 1) by omega]
    constructor
    · rintro (⟨hc, l, hl, hcd, pc', h1, h2⟩ | ⟨d, g, w, lw, ls, hi, hw, hs, h0, hb, h3, pc', h1, h2⟩ |
        ⟨p, h, kv, u, la, ls, hi, ha, hs, h0, hb, h3, pc', h1, h2⟩ | ⟨a0, a1, la, hi, ha, h0, hb, pc', h1, h2⟩)
      · exact ⟨pc', .inl ⟨hc, l, hl, hcd, h1⟩, h2⟩
      · exact ⟨pc', .inr (.inl ⟨d, g, w, lw, ls, hi, hw, hs, h0, hb, h3, h1⟩), h2⟩
      · exact ⟨pc', .inr (.inr (.inl ⟨p, h, kv, u, la, ls, hi, ha, hs, h0, hb, h3, h1⟩)), h2⟩
      · exact ⟨pc', .inr (.inr (.inr ⟨a0, a1, la, hi, ha, h0, hb, h1⟩)), h2⟩
    · rintro ⟨pc', (⟨hc, l, hl, hcd, h1⟩ | ⟨d, g, w, lw, ls, hi, hw, hs, h0, hb, h3, h1⟩ |
        ⟨p, h, kv, u, la, ls, hi, ha, hs, h0, hb, h3, h1⟩ | ⟨a0, a1, la, hi, ha, h0, hb, h1⟩), h2⟩
      · exact .inl ⟨hc, l, hl, hcd, pc', h1, h2⟩
      · exact .inr (.inl ⟨d, g, w, lw, ls, hi, hw, hs, h0, hb, h3, pc', h1, h2⟩)
      · exact .inr (.inr (.inl ⟨p, h, kv, u, la, ls, hi, ha, hs, h0, hb, h3, pc', h1, h2⟩))
      · exact .inr (.inr (.inr ⟨a0, a1, la, hi, ha, h0, hb, pc', h1, h2⟩))

/-- **The code of a function's `Accepted2` blocks**: each block not ending
in `unreachable` at its assembler label (`lab`), as `CodeC2` from some
instruction number. -/
def BlocksCodeC2 (cx : FnCtx) (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (lab : Label → Int64) (bs : List Scc.IR.Block) : Prop :=
  ∀ b ∈ bs, b.term ≠ .unreachable →
    ∃ L k, cx.blockLabel b.label = .ok L ∧ CodeC2 cx Cd Bl k (lab L) b.insts b.term

/-! ## The constructs' blocks -/

/-- **The loads of a `ret`'s words**: each word into its register. -/
def retLoads (cx : FnCtx) : List (Scc.IR.Operand × XReg) → Except String (List Item)
  | [] => .ok []
  | (v, r) :: ps => do
    let l ← cx.getOp r v
    let ls ← retLoads cx ps
    pure (l ++ ls)

/-- **A construct's block** of an `Accepted2` body: `Kind1`'s and a `ret` of
the words `vs` (at most the argument registers), each loaded into its
register (`retLoads`), then the frame's exit and `ret`. The `xchg`'s load
and store are not construct blocks: their word accesses are not covered
(`okBlk`), and their nodes come from the lane store's premise (`LaneC`). -/
def Kind2 (cx : FnCtx) (blk : List Directive) : Prop :=
  Kind1 cx blk ∨
  (∃ (vs : List Scc.IR.Operand) (ls : List Item), vs.length ≤ argRegs.length ∧
    retLoads cx (vs.zip argRegs) = .ok ls ∧ blk = directives (ls ++ cx.leave ++ [ret]))

theorem Kind2.of1 {cx : FnCtx} {blk : List Directive} (h : Kind1 cx blk) : Kind2 cx blk := .inl h

/-! ## From `CodeC` -/

/-- **`CodeC` is `CodeC2`'s first two arms.** -/
theorem CodeC.toC2 {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop} :
    ∀ {k : Nat} {pc : Int64} {is : List Scc.IR.Inst} {tm : Scc.IR.Term},
      CodeC cx Cd Bl k pc is tm → CodeC2 cx Cd Bl k pc is tm
  | _, _, [], _, h => h
  | _, _, _ :: _, _, .inl ⟨hc, l, hl, hcd, h⟩ => .inl ⟨hc, l, hl, hcd, CodeC.toC2 h⟩
  | _, _, _ :: _, _, .inr ⟨d, g, w, lw, ls, hi, hw, hs, h1, h2, h3, h⟩ =>
    .inr (.inl ⟨d, g, w, lw, ls, hi, hw, hs, h1, h2, h3, CodeC.toC2 h⟩)

end Spike.Lib.LowerA64
