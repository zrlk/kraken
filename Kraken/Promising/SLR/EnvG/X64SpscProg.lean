/-
**Part 1: the programs of
`Examples/LockFree/X64/spsc_queue.kl`** (a single-producer single-consumer
ring of two slots on x86-TSO, plain loads and stores only).

The code is the `.kl`'s verbatim except that the two index symbols are
registers (the `spinlock2` precedent, "code verbatim, symbols as
registers"): `(tail)` is `(%rdi)` and `(head)` is `(%rsi)`. As in the `.kl`,
`rbx = buf0` and slot `k` is at `buf0 + (k << 8)` (`(%rbx,%rdx,1)` with
`edx = k << 8`).

- `spscProducerX` (thread `0`): for `v` in `1, 2, 3` (in `r8d`): spin while
  `(tail + 1) & 1 = head` (full); `buf[tail] := v`; `tail := (tail + 1) & 1`.
- `spscConsumerX` (thread `1`): three rounds: spin while `head = tail`
  (empty); `v := buf[head]` into `r12d`, `r13d`, `r14d`;
  `head := (head + 1) & 1`.
-/
import Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.SpscX

open Kraken Kraken.X64.Parser

/-- **The producer** (`P0` of `spsc_queue.kl`, `(tail)` as `(%rdi)`,
`(head)` as `(%rsi)`). -/
def spscProducerX : Program := parse("
producer:
  movl $1,%r8d
produce:
  movl (%rdi),%eax
  movl %eax,%ecx
  addl $1,%ecx
  andl $1,%ecx
pfull:
  movl (%rsi),%edx
  cmpl %ecx,%edx
  je pfull
  movl %eax,%edx
  shll $8,%edx
  movl %r8d,(%rbx,%rdx,1)
  movl %ecx,(%rdi)
  addl $1,%r8d
  cmpl $4,%r8d
  jne produce
  jmp pdone
pdone:
")

/-- info: 20 -/
#guard_msgs in
#eval spscProducerX.length

/-- **The consumer** (`P1` of `spsc_queue.kl`, `(tail)` as `(%rdi)`,
`(head)` as `(%rsi)`). -/
def spscConsumerX : Program := parse("
consumer:
  movl (%rsi),%eax
cempty0:
  movl (%rdi),%ecx
  cmpl %eax,%ecx
  je cempty0
  movl %eax,%edx
  shll $8,%edx
  movl (%rbx,%rdx,1),%r12d
  addl $1,%eax
  andl $1,%eax
  movl %eax,(%rsi)
cempty1:
  movl (%rdi),%ecx
  cmpl %eax,%ecx
  je cempty1
  movl %eax,%edx
  shll $8,%edx
  movl (%rbx,%rdx,1),%r13d
  addl $1,%eax
  andl $1,%eax
  movl %eax,(%rsi)
cempty2:
  movl (%rdi),%ecx
  cmpl %eax,%ecx
  je cempty2
  movl %eax,%edx
  shll $8,%edx
  movl (%rbx,%rdx,1),%r14d
  addl $1,%eax
  andl $1,%eax
  movl %eax,(%rsi)
  jmp cdone
cdone:
")

/-- info: 34 -/
#guard_msgs in
#eval spscConsumerX.length

end Kraken.Promising.X64.EnvG.SpscX
