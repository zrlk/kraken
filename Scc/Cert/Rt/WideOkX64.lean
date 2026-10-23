import Kraken.X64.Syntax

/-!
# The one-word fragment of x86-64, as a decidable check

The syntactic fragment of `Scc/Cert/Rt/WideX64.lean` (`certExec_w8`: the
certification semantics of a program in it writes words only), on its own
so that the compiler can import it: `scc-x64`'s `--code` refuses a program
outside it, and `Scc.Sem.TargetX64`, which `WideX64.lean` needs, brings
WeakCore's root `main` into scope. This module imports Kraken's x64 syntax
only.

**The fragment: every memory write is 8 bytes.**

- Every regular instruction at operand width `W64` is in (`mov`, `push`,
  `pop`, ALU operations to memory, `xchg`, `[lock] xadd`, `[lock] cmpxchg`,
  `lock <op>`, `movnti`, `movfs`), and so is `call` at every width (its
  return address is 8 bytes).
- A regular instruction at width 1, 2 or 4 bytes is in exactly when it has
  no memory destination (its loads are of any width): `movb`/`movw`/`movl`
  to memory, `setcc` to memory, ALU operations to memory, a narrow
  `push`, `xchg`/`xadd`/`cmpxchg` on memory, `lock <op>` and `movnti` are
  out.
- A vector instruction is in exactly when it has no memory destination: the
  vector stores (`movups`/`movaps`/`movapd`/`movdqa`/`movdqu` and their VEX
  forms, and the legacy arithmetic forms to memory) and `cmpxchg16b` are
  out.
-/

namespace Scc.Cert.WideX64

/-- A register operand (no memory access through it). -/
def noMem {w : Width} : RegOrMem w → Bool
  | .reg _ => true
  | .mem _ => false

/-- A vector register operand (no memory access through it). -/
def avxNoMem {w : AvxWidth} : AvxRegOrMem w → Bool
  | .avx _ => true
  | .mem _ => false

/-- **An operation at a width below 8 bytes in the fragment**: it writes no
memory, except `call`'s 8-byte return address. -/
def _root_.Operation.narrowOk {w : Width} : Operation w → Bool
  | .mov d _ | .movsx d _ | .movzx d _ | .pop d | .setcc _ d | .movfs d _ => noMem d
  | .add d _ | .adc d _ | .sub d _ | .sbb d _ | .and d _ | .or d _ | .xor d _ => noMem d
  | .inc d | .dec d | .neg d | .not d => noMem d
  | .shl d _ | .shr d _ | .sar d _ | .shld d _ _ | .shrd d _ _ => noMem d
  | .rol d _ | .ror d _ | .rcl d _ | .rcr d _ => noMem d
  | .imul (some d) _ _ => noMem d
  | .imul none src1 _ => noMem src1
  | .xchg _ m | .xadd _ m _ | .cmpxchg _ m _ => noMem m
  | .push _ | .lockBin .. | .lockUn .. | .movnti .. => false
  | _ => true

/-- **The one-word fragment, per regular operation**: any operation at
`W64`; at a narrower width, `Operation.narrowOk`. -/
def _root_.Operation.wideOk {w : Width} (op : Operation w) : Bool :=
  match w with
  | .W64 => true
  | _ => op.narrowOk

/-- **The one-word fragment, per vector operation**: no memory destination,
and no `cmpxchg16b`. -/
def _root_.AvxOperation.wideOk {w : AvxWidth} : AvxOperation w → Bool
  | .movups d _ | .vmovups d _ | .movaps d _ | .movapd d _ | .movdqa d _ | .movdqu d _ => avxNoMem d
  | .vmovaps d _ | .vmovapd d _ | .vmovdqa d _ | .vmovdqu d _ => avxNoMem d
  | .subps d _ | .addps d _ | .mulps d _ | .xorps d _ => avxNoMem d
  | .cmpxchg16b .. => false
  | _ => true

/-- **The one-word fragment, per instruction.** -/
def _root_.Instr.wideOk : Instr → Bool
  | .regular _ _ op => op.wideOk
  | .avx _ _ op => op.wideOk

/-- **The one-word fragment, per directive**: an instruction of the fragment
(`Instr.wideOk`); labels and data are in. -/
def _root_.Directive.wideOk : Directive → Bool
  | .instr i => i.wideOk
  | _ => true

/-- **A program of the one-word fragment**: every directive is
`Directive.wideOk`. Decidable; `scc --code` refuses a program for which it is
`false`. -/
def wideIn (prog : Program) : Bool := prog.all Directive.wideOk

end Scc.Cert.WideX64
