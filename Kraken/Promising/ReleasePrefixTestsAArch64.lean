/-
`ReleasePrefixTests` on AArch64: `CASPAL`, two release RMW writes in one
instruction. The low word's write is promised and
fulfilled by the `CASPAL`, whose high write is fresh: `AdvanceableStrict`
fails, (S1′) and the variant-(ii) advance hold (components as in
`advanceCheck`).
-/
import Kraken.Litmus.AArch64
import Kraken.Promising.ReleasePrefixTests

namespace Kraken.Promising.ReleasePrefixTests

open Kraken.Litmus

def advanceCheckLitmus (src : String) : Except String (Nat × Nat × Nat × Nat × Nat × Nat) := do
  let t ← Litmus.parse src
  let pr ← AArch64.prepare t
  return advanceCheck Arch.armv8 pr.config

def caspalMP : String := "AArch64 MP+caspal+ldar
{
uint64_t t[2];
0:X4=t; 1:X4=t;
uint64_t 1:X0; uint64_t 1:X1;
}
P0                        | P1             ;
MOV X0,#0                 | ADD X5,X4,#0   ;
MOV X1,#0                 | ADD X6,X4,#8   ;
MOV X2,#1                 | LDAR X1,[X6]   ;
MOV X3,#1                 | LDR X0,[X5]    ;
CASPAL X0,X1,X2,X3,[X4]   |                ;
exists (1:X0=0 /\\ 1:X1=1)
"

/-- info: Except.ok (209, 150, 235, 65, 0, 0) -/
#guard_msgs in #eval advanceCheckLitmus caspalMP

end Kraken.Promising.ReleasePrefixTests
