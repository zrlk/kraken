/-
`ReleasePrefixTests` on x64: `movups`/`vmovdqu` to memory, a release store
followed by a fresh store in one instruction.
-/
import Kraken.Litmus.X64
import Kraken.Promising.ReleasePrefixTests

namespace Kraken.Promising.ReleasePrefixTests

open Kraken.Litmus

def advanceCheckSrc (src : String) : Except String (Nat × Nat × Nat × Nat × Nat × Nat) := do
  let p ← parseProgram src
  let pr ← X64.prepareProgram p
  return advanceCheck Arch.tso pr.config

def advanceCheckNTSrc (src : String) : Except String (Nat × Nat × Nat × Nat) := do
  let p ← parseProgram src
  let pr ← X64.prepareProgram p
  return advanceCheckNT Arch.tso pr.config

/-! ## `movups` to memory: a release store, then a fresh store

x64 `movups %xmm0,(rec)` is two 8-byte TSO stores (every store a release),
low word first. Once the low store is promised, the only instruction that
fulfils it also appends the high store, so no memory-silent run fulfils the
promise: `Config.AdvanceableStrict` fails (fourth component). A run that
stops just before the `movups` exists in every case ((S1′), fifth), and one
such run serves all outstanding promises of the thread (variant (ii),
sixth). -/

def movupsOne : String := "X86_64 AdvanceableStrictMovups
{
uint64_t rec[2];
0:xmm0=0x20000000000000001;
}
threads { P0: writer done; P1: reader done; }
code {
writer:
  movups %xmm0,(rec)
  jmp done
reader:
  movups (rec),%xmm2
  jmp done
done:
}
exists (1:xmm2=0)
"

/-- info: Except.ok (35, 14, 23, 5, 0, 0) -/
#guard_msgs in #eval advanceCheckSrc movupsOne

/-- The same with `vmovdqu` and a flag written after the record. -/
def vmovdquFlag : String := "X86_64 AdvanceableStrictVmovdqu
{
uint64_t rec[2];
uint64_t flag;
0:xmm0=0x20000000000000001;
}
threads { P0: writer done; P1: reader done; }
code {
writer:
  vmovdqu %xmm0,(rec)
  movq $1,(flag)
  jmp done
reader:
  movq (flag),%rax
  vmovdqu (rec),%xmm2
  jmp done
done:
}
exists (1:xmm2=0)
"

/-- info: Except.ok (82, 42, 78, 6, 0, 0) -/
#guard_msgs in #eval advanceCheckSrc vmovdquFlag

/-! ## `movnti`: why (S2)/(S1′) assume `Thread.NoNTStores`

A non-temporal store is not in a later release store's pre-view, so the
writer may promise `y := 1` and then append its `movnti` to `x` above the
promise before fulfilling it. From such a configuration no memory-silent run
reaches the fulfilling store (the `movnti` appends), so (S1′) fails (fifth
component, non-zero): the restriction is necessary for (S1′) against the
unchanged memory. The NT generalisation lifts it by letting the run append the thread's own
messages (`Config.AdvanceableNT`, below). -/

def movntiFlag : String := "X86_64 AdvanceableMovnti
{
uint64_t x;
uint64_t y;
0:rax=1;
}
threads { P0: writer done; P1: reader done; }
code {
writer:
  movnti %rax,(x)
  movq $1,(y)
  jmp done
reader:
  movq (y),%rbx
  movq (x),%rcx
  jmp done
done:
}
exists (1:rbx=1 /\\ 1:rcx=0)
"

/-- info: Except.ok (103, 53, 73, 7, 7, 7) -/
#guard_msgs in #eval advanceCheckSrc movntiFlag

/-! With pending non-temporal stores (`Config.AdvanceableNT`, `ReleasePrefixNT.lean`): the
thread's run may append its own messages, here the `movnti`, so the
fulfilling store is reached in every case (fourth component zero); the third
is the restricted (S1′) above, the negative control. -/

/-- info: Except.ok (103, 73, 7, 0) -/
#guard_msgs in #eval advanceCheckNTSrc movntiFlag

/-- info: Except.ok (82, 78, 0, 0) -/
#guard_msgs in #eval advanceCheckNTSrc vmovdquFlag

end Kraken.Promising.ReleasePrefixTests
