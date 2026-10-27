import Spike.Lib.X64Flags
import Spike.Lib.X64RtNodes
import Scc.Cert.Rt.CodeX64

/-!
# `scc_rt_alloc` in an emitted x64 program

The allocator's blocks and single instructions (`Spike/Lib/X64Alloc.lean`
proves them one segment) with their cell sizes, its labels, and `allocIn
cells`: the code at its labels and offsets in the cells and the prologue's
fall-through to `.entry`, the code premise of `seg_allocW`. The text is the
runtime's, the same in every program, so A7 checks it with the rest of the
runtime's fixed code (`Scc/Cert/Rt/X64RtIn.lean`) and
`PlaceOK.X64.allocIn_of_placeOKAt` gives it from the placement check.
-/

namespace Spike.Lib.X64.Alloc

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (blockAtB labelGapB)

/-! ## The blocks -/

/-- The prologue: a frame of 144 below `%rbp`, `h`, `k`, `u` at `-8`, `-16`, `-24(%rbp)`. -/
def bPro : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $144, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)
movq %rdx, -24(%rbp)")).zip [1, 3, 7, 4, 4, 4]

/-- `k ≥ 2^28` goes to the abort. -/
def bChk : List (Directive × Nat) := (parse("movq -16(%rbp), %rax
movq $268435456, %rcx
cmpq %rcx, %rax
jae .Lscc_rt_alloc.full")).zip [4, 7, 3, 2]

/-- On to `.cnt`. -/
def bJ1 : List (Directive × Nat) := (parse("jmp .Lscc_rt_alloc.cnt")).zip [2]

/-- The add's operands: `%rcx` the counter's address (in `%rax` before), `%rax = u`. -/
def bC1 : List (Directive × Nat) := (parse("movq %rax, -32(%rbp)
movq -32(%rbp), %rcx
movq -24(%rbp), %rax")).zip [4, 4, 4]

/-- The counter's old value saved; past the cells goes to `.slow`. -/
def bC2 : List (Directive × Nat) := (parse("movq %rax, -40(%rbp)
movq -40(%rbp), %rax
movq -24(%rbp), %rcx
addq %rcx, %rax
movq %rax, -48(%rbp)
movq -48(%rbp), %rax
movq $4194304, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_alloc.slow")).zip [4, 4, 4, 3, 4, 4, 7, 3, 2]

/-- On to `.ok`. -/
def bJ2 : List (Directive × Nat) := (parse("jmp .Lscc_rt_alloc.ok")).zip [2]

/-- Past the cells before the add goes to `.spin`. -/
def bSlow : List (Directive × Nat) := (parse("movq -40(%rbp), %rax
movq $4194304, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_alloc.spin")).zip [4, 7, 3, 2]

/-- On to `.full`. -/
def bJ3 : List (Directive × Nat) := (parse("jmp .Lscc_rt_alloc.full")).zip [2]

/-- The heap abort. -/
def bFull : List (Directive × Nat) := (parse("movq $2, %rdi
call scc_rt_abort")).zip [7, 5]

/-- `h >> 22`'s operands. -/
def bO0 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $22, %rcx")).zip [4, 7]

/-- `(h >> 22) & 16383`'s operands. -/
def bO1 : List (Directive × Nat) := (parse("movq %rax, -56(%rbp)
movq -56(%rbp), %rax
movq $16383, %rcx")).zip [4, 4, 7]

/-- `m` saved. -/
def bO2 : List (Directive × Nat) := (parse("movq %rax, -64(%rbp)")).zip [4]

/-- The arena's address saved; `old << 4`'s operands. -/
def bO3 : List (Directive × Nat) := (parse("movq %rax, -72(%rbp)
movq -40(%rbp), %rax
movq $4, %rcx")).zip [4, 4, 7]

/-- The object's start `heap + 16·old` saved; `k·m`'s operands. -/
def bO4 : List (Directive × Nat) := (parse("movq %rax, -80(%rbp)
movq -72(%rbp), %rax
movq -80(%rbp), %rcx
addq %rcx, %rax
movq %rax, -88(%rbp)
movq -16(%rbp), %rax
movq -64(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 4]

/-- `8·k·m`'s operands. -/
def bO5 : List (Directive × Nat) := (parse("movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7]

/-- `8·k·m` saved; `k << 36`'s operands. -/
def bO6 : List (Directive × Nat) := (parse("movq %rax, -104(%rbp)
movq -16(%rbp), %rax
movq $36, %rcx")).zip [4, 4, 7]

/-- `h | k << 36`'s operands. -/
def bO7 : List (Directive × Nat) := (parse("movq %rax, -112(%rbp)
movq -8(%rbp), %rax
movq -112(%rbp), %rcx")).zip [4, 4, 4]

/-- The header and its address: `%rax` the header, `%rcx = heap + 16·old + 8·k·m`. -/
def bO8 : List (Directive × Nat) := (parse("movq %rax, -120(%rbp)
movq -88(%rbp), %rax
movq -104(%rbp), %rcx
addq %rcx, %rax
movq %rax, -128(%rbp)
movq -128(%rbp), %rcx
movq -120(%rbp), %rax")).zip [4, 4, 4, 3, 4, 4, 4]

/-- `%rax` one word past the header; the epilogue. -/
def bO9 : List (Directive × Nat) := (parse("movq -88(%rbp), %rax
movq -104(%rbp), %rcx
addq %rcx, %rax
movq %rax, -136(%rbp)
movq -136(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -144(%rbp)
movq -144(%rbp), %rax
movq %rbp, %rsp
popq %rbp")).zip [4, 4, 3, 7, 7, 7, 3, 7, 7, 3, 1]

/-- The single instructions: the label addresses, the counter's add, the
header store, the `ret`. -/
def iCtr : SI := .leaRip .rax "scc_rt_heap_use"
def iHeap : SI := .leaRip .rax "scc_rt_heap"
def iRmw : Directive := xaddDir .rcx 0 .rax
def iHdr : Directive := stDir .rcx 0 .rax
def iRet : AI := .ret

/-- The function's offsets inside the frame: `%rsp` at the frame's base,
`%rbp` at the saved `%rbp`. -/
abbrev oI : SO := ⟨-152, [(.rbp, -8)]⟩
/-- The offsets at entry, and before the `ret`. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets after the `ret`. -/
abbrev oR : SO := ⟨8, []⟩

block_spec bPro (-160) 8 oE bPro
block_spec bChk (-160) 8 oI bChk
block_spec bJ1 (-160) 8 oI bJ1
block_spec bC1 (-160) 8 oI bC1
block_spec bC2 (-160) 8 oI bC2
block_spec bJ2 (-160) 8 oI bJ2
block_spec bSlow (-160) 8 oI bSlow
block_spec bJ3 (-160) 8 oI bJ3
block_spec bFull (-160) 8 oI bFull
block_spec bO0 (-160) 8 oI bO0
block_spec bO1 (-160) 8 oI bO1
block_spec bO2 (-160) 8 oI bO2
block_spec bO3 (-160) 8 oI bO3
block_spec bO4 (-160) 8 oI bO4
block_spec bO5 (-160) 8 oI bO5
block_spec bO6 (-160) 8 oI bO6
block_spec bO7 (-160) 8 oI bO7
block_spec bO8 (-160) 8 oI bO8
block_spec bO9 (-160) 8 oI bO9

/-- The listing's single instructions, as Kraken's parser reads them. -/
example : parse("leaq scc_rt_heap_use(%rip), %rax
lock xaddq %rax, (%rcx)
leaq scc_rt_heap(%rip), %rax
movq %rax, (%rcx)
ret") = [iCtr.toDir, iRmw, iHeap.toDir, iHdr, iRet.toDir] := by
  decide

/-! ## The code -/

/-- `scc_rt_alloc`'s label. -/
abbrev fnL : Label := "scc_rt_alloc"
/-- Its labels: the entry, the counter's add, the slow path, the abort, the header. -/
abbrev entryL : Label := ".Lscc_rt_alloc.entry"
abbrev cntL : Label := ".Lscc_rt_alloc.cnt"
abbrev slowL : Label := ".Lscc_rt_alloc.slow"
abbrev fullL : Label := ".Lscc_rt_alloc.full"
abbrev okL : Label := ".Lscc_rt_alloc.ok"

/-- An instruction with undefined flags at `l + off`. -/
def fiAt (cells : List (Directive × Nat)) (l : Label) (off : Nat) (fi : FI) (z : Nat) : Bool :=
  blockAtB cells l off [(fi.toDir, z)]

/-- **`scc_rt_alloc`'s code in `cells`**: its blocks, its single
instructions and the fall-through into `.entry`. -/
def allocIn (cells : List (Directive × Nat)) : Bool :=
  labelGapB cells fnL entryL 23 && blockAtB cells fnL 0 bPro && blockAtB cells entryL 0 bChk &&
  blockAtB cells entryL 16 bJ1 && blockAtB cells cntL 0 [(iCtr.toDir, 7)] && blockAtB cells cntL 7 bC1 &&
  blockAtB cells cntL 19 [(iRmw, 5)] && blockAtB cells cntL 24 bC2 && blockAtB cells cntL 59 bJ2 &&
  blockAtB cells slowL 0 bSlow && blockAtB cells slowL 16 bJ3 && blockAtB cells fullL 0 bFull &&
  blockAtB cells okL 0 bO0 && fiAt cells okL 11 (.shr_cl .rax) 3 && blockAtB cells okL 14 bO1 &&
  fiAt cells okL 29 (.and_rr .rax .rcx) 3 && blockAtB cells okL 32 bO2 &&
  blockAtB cells okL 36 [(iHeap.toDir, 7)] && blockAtB cells okL 43 bO3 && fiAt cells okL 58 (.shl_cl .rax) 3 &&
  blockAtB cells okL 61 bO4 && fiAt cells okL 88 (.imul_rr .rax .rcx) 4 && blockAtB cells okL 92 bO5 &&
  fiAt cells okL 107 (.shl_cl .rax) 3 && blockAtB cells okL 110 bO6 && fiAt cells okL 125 (.shl_cl .rax) 3 &&
  blockAtB cells okL 128 bO7 && fiAt cells okL 140 (.or_rr .rax .rcx) 3 && blockAtB cells okL 143 bO8 &&
  blockAtB cells okL 170 [(iHdr, 3)] && blockAtB cells okL 173 bO9 && blockAtB cells okL 226 [(iRet.toDir, 1)]

end Spike.Lib.X64.Alloc
