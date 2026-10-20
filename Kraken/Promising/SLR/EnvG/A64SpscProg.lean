/-
**Part 0: the programs of
`Examples/LockFree/AArch64/spsc_queue.kl`** (a single-producer
single-consumer ring of two slots with monotone counters, Promising-ARM
PLDI'19 §7).

The `.kl`'s `code` block is, verbatim, `spscProdA ++ spscNop ++ spscConsA`
(`A64SpscConcrete.codeMatches`): the producer's text from `prod` to the
label `pdone`, the dead `NOP` at `pdone` (the producer halts there, the
consumer never reaches it), and the consumer's text from `cons` to `cdone`.
Each thread runs its own part as its executable (the runner's threads share
the whole block; the producer halts at `pdone`, before the `NOP`).

- `spscProdA` (thread `0`, `X0 = buf`, `X1 = head`, `X2 = tail`): for
  `W3 = 1, 2, 3`: spin on `LDAR X5, [X1]` while `X4 - head = 2` (full);
  `STR W3, [X7]`; flip the slot (`EOR X7, X7, #8`); `X4 := X4 + 1`;
  `STLR X4, [X2]`.
- `spscConsA` (thread `1`): three rounds: spin on `LDAR X5, [X2]` while
  `tail = X4` (empty); `LDR W1x, [X7]` into `W10`, `W11`, `W12`; flip;
  `X4 := X4 + 1`; `STLR X4, [X1]`.
-/
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken

/-- **The producer** (`P0` of `spsc_queue.kl`, `prod` to `pdone`). -/
def spscProdA : Program := parseAArch64("
prod:
  MOV W3,#1
  MOV X4,#0
  MOV X7,X0
prod_loop:
  LDAR X5,[X1]
  SUB X6,X4,X5
  CMP X6,#2
  B.EQ prod_loop
  STR W3,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X2]
  ADD W3,W3,#1
  CMP W3,#4
  B.NE prod_loop
  B pdone
pdone:
")

/-- info: 18 -/
#guard_msgs in
#eval spscProdA.length

/-- The dead `NOP` at `pdone`. -/
def spscNop : Program := parseAArch64("
  NOP
")

/-- **The consumer** (`P1` of `spsc_queue.kl`, `cons` to `cdone`). -/
def spscConsA : Program := parseAArch64("
cons:
  MOV X4,#0
  MOV X7,X0
c1:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c1
  LDR W10,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
c2:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c2
  LDR W11,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
c3:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c3
  LDR W12,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
  B cdone
cdone:
")

/-- info: 29 -/
#guard_msgs in
#eval spscConsA.length

end Kraken.Promising.SLR.EnvG.SpscA
