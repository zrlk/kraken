/-
**The x86-64 runtime's code checks, light** (`rtCodeOk`): the groups of
fixed code the runtime's segments read (`Spike/Lib/Rt/X64RtCode.lean`),
over copies of the hand files' blocks (`Code.Tcb`, `Code.Take`, `Code.Ti`,
`Code.Start`), with `scc_rt_main`'s facts (`MainCode`, `mainUIn`), so that
the placement check (`Scc/Cert/PlaceOKX64.lean`, A11) reads them without
importing the hand proofs. `Spike/Lib/Rt/X64RtCode.lean` checks the copies
against the hand blocks (`rtCodeTab_eq`, `rfl`).
-/
import Spike.Lib.X64CodeSegs
import Spike.Lib.X64Flags
import Spike.Lib.X64Switch
import Scc.Cert.Rt.RtPassX64

namespace Spike.Lib.X64

open Kraken Kraken.Promising Kraken.Promising.X64

/-- `call fn`, five bytes (`rel32`). -/
def callB (fn : Label) : List (Directive × Nat) := [((AI.call fn).toDir, 5)]

end Spike.Lib.X64

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Kraken.X64.Parser
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (RGrp rtIn blockAtB labelGapB)

/-! ## The program's facts -/

/-- **What `scc_rt_main` reads of the program**: its frame `Z`, the spill
offset `k` of the exit value (from `%rbp`), the user function `fn`, its
labels (the prologue's check `sc`, the grow stub `grow`, the body's entry
`e0`, the call's return point `sp0`), the prologue's cell sizes (`zl zf z1
z2 zs`) and parameter stores (`ps`), and the exit tail's cell sizes (`ze0
ze1 ze2`). -/
structure MainCode where
  Z : Int64
  k : Int64
  fn : Label
  sc : Label
  grow : Label
  e0 : Label
  sp0 : Label
  zl : Nat
  zf : Nat
  z1 : Nat
  z2 : Nat
  zs : Nat
  ps : List (Reg64 × Int64 × Nat)
  ze0 : Nat
  ze1 : Nat
  ze2 : Nat

/-- **`scc_rt_main`'s code in `cells`**: the stack-checked prologue (frame
`Z`, the limit at `%fs:8`), `call fn` at the body's entry, the return point
right after it, and the `exit_group` tail there with the value spilled at
`k`. -/
def mainUIn (cells : List (Directive × Nat)) (mc : MainCode) : Bool :=
  prologueIn cells "scc_rt_main" mc.sc mc.e0 mc.Z 8 mc.grow mc.zl mc.zf mc.z1 mc.z2 mc.zs mc.ps &&
    blockAtB cells mc.e0 0 (callB mc.fn) && labelGapB cells mc.e0 mc.sp0 5 &&
    exitIn cells mc.sp0 mc.k mc.ze0 mc.ze1 mc.ze2

namespace Code

/-! ## `scc_rt_alloc_tcb` (`Ret0.AllocTcb`) -/

namespace Tcb

abbrev fnL : Label := "scc_rt_alloc_tcb"
abbrev entryL : Label := ".Lscc_rt_alloc_tcb.entry"
abbrev lenL : Label := ".Lscc_rt_alloc_tcb.len"
abbrev okL : Label := ".Lscc_rt_alloc_tcb.ok"
def atPro : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $176, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)")).zip [1, 3, 7, 4, 4]
def atChk : List (Directive × Nat) := (parse("movq -16(%rbp), %rax
movq $268435456, %rcx
cmpq %rcx, %rax
jae .Lscc_rt_alloc_tcb.full")).zip [4, 7, 3, 6]
def atJ1 : List (Directive × Nat) := (parse("jmp .Lscc_rt_alloc_tcb.len")).zip [2]
def atL0 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $8, %rcx")).zip [4, 7]
def atL1 : List (Directive × Nat) := (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $16383, %rcx")).zip [4, 4, 7]
def atL2 : List (Directive × Nat) := (parse("movq %rax, -32(%rbp)
movq -8(%rbp), %rax
movq $22, %rcx")).zip [4, 4, 7]
def atL3 : List (Directive × Nat) := (parse("movq %rax, -40(%rbp)
movq -40(%rbp), %rax
movq $16383, %rcx")).zip [4, 4, 7]
def atL4 : List (Directive × Nat) := (parse("movq %rax, -48(%rbp)
movq -32(%rbp), %rax
movq -48(%rbp), %rcx
addq %rcx, %rax
movq %rax, -56(%rbp)
movq -16(%rbp), %rax
movq -56(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 4]
def atL5 : List (Directive × Nat) := (parse("movq %rax, -64(%rbp)
movq -64(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -72(%rbp)
movq -72(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7, 3, 4, 4, 7]
def atL6 : List (Directive × Nat) := (parse("movq %rax, -80(%rbp)")).zip [4]
def atArg : List (Directive × Nat) := (parse("movq %rax, -88(%rbp)
movq -88(%rbp), %rcx
movq -80(%rbp), %rax")).zip [4, 4, 4]
def atBnd : List (Directive × Nat) := (parse("movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq -80(%rbp), %rcx
addq %rcx, %rax
movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $131072, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_alloc_tcb.full")).zip [4, 4, 4, 3, 4, 4, 7, 3, 2]
def atJ2 : List (Directive × Nat) := (parse("jmp .Lscc_rt_alloc_tcb.ok")).zip [2]
def atO1 : List (Directive × Nat) := (parse("movq %rax, -112(%rbp)
movq -112(%rbp), %rax
movq -96(%rbp), %rcx
addq %rcx, %rax
movq %rax, -120(%rbp)
movq -16(%rbp), %rax
movq -48(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 4]
def atO2 : List (Directive × Nat) := (parse("movq %rax, -128(%rbp)
movq -128(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7]
def atO3 : List (Directive × Nat) := (parse("movq %rax, -136(%rbp)
movq -16(%rbp), %rax
movq $36, %rcx")).zip [7, 4, 7]
def atO4 : List (Directive × Nat) := (parse("movq %rax, -144(%rbp)
movq -8(%rbp), %rax
movq -144(%rbp), %rcx")).zip [7, 4, 7]
def atO5 : List (Directive × Nat) := (parse("movq %rax, -152(%rbp)
movq -120(%rbp), %rax
movq -136(%rbp), %rcx
addq %rcx, %rax
movq %rax, -160(%rbp)
movq -160(%rbp), %rcx
movq -152(%rbp), %rax")).zip [7, 4, 7, 3, 7, 7, 7]
def atRet : List (Directive × Nat) := (parse("movq -120(%rbp), %rax
movq -136(%rbp), %rcx
addq %rcx, %rax
movq %rax, -168(%rbp)
movq -168(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -176(%rbp)
movq -176(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 7, 3, 7, 7, 7, 3, 7, 7, 3, 1, 1]
def rmwBlk : List (Directive × Nat) := (parse("lock xaddq %rax, (%rcx)")).zip [5]
def hdrBlk : List (Directive × Nat) := (parse("movq %rax, (%rcx)")).zip [3]

end Tcb

/-! ## `scc_rt_stack_take` (`Ret0.StackTake`) -/

namespace Take

abbrev fnL : Label := "scc_rt_stack_take"
abbrev entryL : Label := ".Lscc_rt_stack_take.entry"
abbrev clsL : Label := ".Lscc_rt_stack_take.cls5"
abbrev doneL : Label := ".Lscc_rt_stack_take.clsdone7"
abbrev spinL : Label := ".Lscc_rt_stack_take.spin14"
abbrev lockedL : Label := ".Lscc_rt_stack_take.locked15"
abbrev bumpL : Label := ".Lscc_rt_stack_take.bump"
abbrev okL : Label := ".Lscc_rt_stack_take.ok"
abbrev takenL : Label := ".Lscc_rt_stack_take.taken"
abbrev siteL : Label := "scc_rt_take_site"
def stPro : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $192, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 7, 4]
def stInit : List (Directive × Nat) := (parse("movq $16384, %rax
movq %rax, -16(%rbp)
movq $0, %rax
movq %rax, -24(%rbp)
movq $32768, %rax
movq %rax, -32(%rbp)
movq $0, %rax
movq %rax, -40(%rbp)
jmp .Lscc_rt_stack_take.cls5")).zip [7, 4, 7, 4, 7, 4, 7, 4, 2]
def stCls : List (Directive × Nat) := (parse("movq -16(%rbp), %rax
movq -8(%rbp), %rcx
cmpq %rcx, %rax
jb .Lscc_rt_stack_take.clsnext6")).zip [4, 4, 3, 2]
def stJ1 : List (Directive × Nat) := (parse("jmp .Lscc_rt_stack_take.clsdone7")).zip [2]
def stFreeN : List (Directive × Nat) := (parse("movq %rax, -56(%rbp)
movq -56(%rbp), %rax
movq -40(%rbp), %rcx
addq %rcx, %rax
movq %rax, -64(%rbp)")).zip [4, 4, 4, 3, 4]
def stFree : List (Directive × Nat) := (parse("movq %rax, -72(%rbp)
movq -72(%rbp), %rax
movq -24(%rbp), %rcx
addq %rcx, %rax
movq %rax, -80(%rbp)")).zip [4, 4, 4, 3, 4]
def stLock : List (Directive × Nat) := (parse("movq %rax, -88(%rbp)
jmp .Lscc_rt_stack_take.spin14")).zip [4, 2]
def stSwp : List (Directive × Nat) := (parse("movq -88(%rbp), %rcx
movq $1, %rax")).zip [4, 7]
def stSpin : List (Directive × Nat) := (parse("movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_stack_take.locked15")).zip [4, 4, 7, 3, 2]
def stLdN : List (Directive × Nat) := (parse("movq -64(%rbp), %rcx")).zip [4]
def stEmpty : List (Directive × Nat) := (parse("movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_stack_take.bump")).zip [4, 4, 7, 3, 2]
def stUnl : List (Directive × Nat) := (parse("movq %rax, -152(%rbp)
movq -152(%rbp), %rcx
movq $0, %rax")).zip [7, 7, 7]
def stAdd : List (Directive × Nat) := (parse("movq %rax, -160(%rbp)
movq -160(%rbp), %rcx
movq -8(%rbp), %rax")).zip [7, 7, 4]
def stBnd : List (Directive × Nat) := (parse("movq %rax, -168(%rbp)
movq -168(%rbp), %rax
movq -8(%rbp), %rcx
addq %rcx, %rax
movq %rax, -176(%rbp)
movq -176(%rbp), %rax
movq $536870912, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_stack_take.full")).zip [7, 7, 4, 3, 7, 7, 7, 3, 2]
def stJ2 : List (Directive × Nat) := (parse("jmp .Lscc_rt_stack_take.ok")).zip [2]
def stOk : List (Directive × Nat) := (parse("movq %rax, -184(%rbp)
movq -184(%rbp), %rax
movq -168(%rbp), %rcx
addq %rcx, %rax
movq %rax, -136(%rbp)
jmp .Lscc_rt_stack_take.taken")).zip [7, 7, 7, 3, 7, 2]
def stSite : List (Directive × Nat) := (parse("movq -136(%rbp), %rdi
movq -8(%rbp), %rsi")).zip [7, 4]
def stRet : List (Directive × Nat) := (parse("movq -136(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]

end Take

/-! ## `scc_rt_thread_init` (`Ret0.ThreadInit`) -/

namespace Ti

abbrev fnL : Label := "scc_rt_thread_init"
abbrev entryL : Label := ".Lscc_rt_thread_init.entry"
abbrev x7L : Label := ".Lscc_rt_thread_init.x7"
def tiPro : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 4, 4]
def tiArg : List (Directive × Nat) := (parse("movq $16384, %rdi")).zip [7]
def tiSp : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $4096, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -16(%rbp), %rax
movq $16384, %rcx
addq %rcx, %rax
movq %rax, -32(%rbp)
movq -8(%rbp), %rcx
movq -8(%rbp), %rax")).zip [4, 4, 7, 3, 4, 4, 7, 3, 4, 4, 4]
def tiF1 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq -24(%rbp), %rax")).zip [4, 4]
def tiZ : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 7]
def tiF4 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq -16(%rbp), %rax")).zip [4, 4]
def tiF5 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq -32(%rbp), %rax")).zip [4, 4]
def tiRet : List (Directive × Nat) := (parse("movq -32(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]
def callBlk : List (Directive × Nat) := (parse("call scc_rt_stack_take")).zip [5]
def storeOff : List Nat := [48, 59, 74, 89, 101, 113]
def storeBlks : List (List (Directive × Nat)) :=
  [(parse("movq %rax, (%rcx)")).zip [3], (parse("movq %rax, 8(%rcx)")).zip [4],
   (parse("movq %rax, 16(%rcx)")).zip [4], (parse("movq %rax, 24(%rcx)")).zip [4],
   (parse("movq %rax, 32(%rcx)")).zip [4], (parse("movq %rax, 40(%rcx)")).zip [4]]

end Ti

/-! ## `scc_rt_start` (`Ret0`) -/

namespace Start

def startCall : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq $2307, %rdi
movq $1, %rsi
call scc_rt_alloc_tcb")).zip [4, 7, 7, 5]
abbrev x0L : Label := ".Lscc_rt_start.x0"
def startCall2 : List (Directive × Nat) := (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rdi
call scc_rt_thread_init")).zip [4, 4, 5]
abbrev x1L : Label := ".Lscc_rt_start.x1"
def startFs : List (Directive × Nat) := (parse("movq %rax, -32(%rbp)
movq -24(%rbp), %rsi
movl $4098, %edi
movl $158, %eax")).zip [4, 4, 5, 5]
def startSw : List (Directive × Nat) := (parse("movq -32(%rbp), %rax
movq -24(%rbp), %rdi")).zip [4, 4]
def startMain : List (Directive × Nat) := (parse("call scc_rt_main")).zip [5]
/-- `_start`'s `xorl %ebp, %ebp`. -/
def entryXor : List (Directive × Nat) := [(FI.toDir (.xor_rr32_self .rbp), 2)]
/-- `_start`'s `andq $-16, %rsp`. -/
def entryAnd : List (Directive × Nat) := [(andRsp (-16), 4)]
/-- `_start`'s call of `scc_rt_start`. -/
def entryCall : List (Directive × Nat) := (parse("call scc_rt_start")).zip [5]

/-- **`_start`'s code in `cells`**: `xorl %ebp, %ebp`, `andq $-16, %rsp`,
`call scc_rt_start` (`entry_segW'`, `Spike/Lib/Rt/X64Entry.lean`). -/
def entryIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells "_start" 0 entryXor && blockAtB cells "_start" 2 entryAnd && blockAtB cells "_start" 6 entryCall

end Start

end Code

open Code.Start

/-! ## The groups -/

/-- `_start`'s and `scc_rt_start`'s groups: `_start`'s three instructions;
`scc_rt_start`'s frame's setup and the fall-through into `.entry`; the
handler, the arguments, the system call and the call of `scc_rt_alloc_tcb`
at `.entry`, `.x0` after it; the call of `scc_rt_thread_init` at `.x0`,
`.x1` after it; the tail at `.x1`. -/
def startGrps : List RGrp := [
  ⟨"_start", [(0, entryXor), (2, entryAnd), (6, entryCall)], none⟩,
  ⟨"scc_rt_start", [(0, xStart0)], some (8, startE)⟩,
  ⟨startE, [(0, [(siSig.toDir, 7)]), (7, xStartArgs), (41, [(op64 .syscall, 2)]), (43, startCall)], some (66, x0L)⟩,
  ⟨x0L, [(0, startCall2)], some (13, x1L)⟩,
  ⟨x1L, [(0, startFs), (18, [(op64 .syscall, 2)]), (20, startSw), (28, [(swDir .rax, 3)]),
    (31, [(FI.toDir (.xor_rr32_self .rbp), 2)]), (33, startMain)], none⟩]

/-- `scc_rt_main`'s groups at `mc`: the prologue's head and its
fall-through into the check, the check, the frame and the parameters'
stores and the fall-through into the body, `call fn` and the return point
after it, the `exit_group` tail there. -/
def mainUGrps (mc : MainCode) : List RGrp := [
  ⟨"scc_rt_main", [(0, xHead)], some (4, mc.sc)⟩,
  ⟨mc.sc, [(0, xLea mc.Z mc.zl), (mc.zl, [(fsDir .r11 8, mc.zf)]), (mc.zl + mc.zf, xCmp mc.grow mc.z1 mc.z2),
    (mc.zl + mc.zf + mc.z1 + mc.z2, xFr mc.Z mc.zs mc.ps)],
    some (mc.zl + mc.zf + mc.z1 + mc.z2 + mc.zs + szSum mc.ps, mc.e0)⟩,
  ⟨mc.e0, [(0, callB mc.fn)], some (5, mc.sp0)⟩,
  ⟨mc.sp0, [(0, xExit mc.k mc.ze0 mc.ze1 mc.ze2), (mc.ze0 + mc.ze1 + mc.ze2, [(op64 .syscall, 2)])], none⟩]

section Tcb

open Code.Tcb

/-- `scc_rt_alloc_tcb`'s groups (`allocTcbIn`). -/
def tcbGrps : List RGrp := [
  ⟨fnL, [(0, atPro)], some (19, entryL)⟩,
  ⟨entryL, [(0, atChk), (20, atJ1)], none⟩,
  ⟨lenL, [(0, atL0), (11, [((FI.shr_cl .rax).toDir, 3)]), (14, atL1), (29, [((FI.and_rr .rax .rcx).toDir, 3)]),
    (32, atL2), (47, [((FI.shr_cl .rax).toDir, 3)]), (50, atL3), (65, [((FI.and_rr .rax .rcx).toDir, 3)]),
    (68, atL4), (95, [((FI.imul_rr .rax .rcx).toDir, 4)]), (99, atL5), (132, [((FI.shl_cl .rax).toDir, 3)]),
    (135, atL6), (139, [((SI.leaRip .rax "scc_rt_pinned_next").toDir, 7)]), (146, atArg), (158, rmwBlk),
    (163, atBnd), (198, atJ2)], none⟩,
  ⟨okL, [(0, [((SI.leaRip .rax "scc_rt_pinned").toDir, 7)]), (7, atO1), (34, [((FI.imul_rr .rax .rcx).toDir, 4)]),
    (38, atO2), (53, [((FI.shl_cl .rax).toDir, 3)]), (56, atO3), (74, [((FI.shl_cl .rax).toDir, 3)]), (77, atO4),
    (95, [((FI.or_rr .rax .rcx).toDir, 3)]), (98, atO5), (140, hdrBlk), (143, atRet)], none⟩]

end Tcb

section Ti

open Code.Ti

/-- `scc_rt_thread_init`'s groups (`threadInitIn`). -/
def tiGrps : List RGrp := [
  ⟨fnL, [(0, tiPro)], some (12, entryL)⟩,
  ⟨entryL, [(0, tiArg), (7, callBlk)], some (12, x7L)⟩,
  ⟨x7L, [(0, tiSp), (51, tiF1), (63, tiZ), (78, tiZ), (93, tiF4), (105, tiF5), (117, tiRet)] ++
    storeOff.zip storeBlks, none⟩]

end Ti

section Take

open Code.Take

/-- `scc_rt_stack_take`'s groups (`stackTakeIn`). -/
def takeGrps : List RGrp := [
  ⟨fnL, [(0, stPro)], some (15, entryL)⟩,
  ⟨entryL, [(0, stInit)], none⟩,
  ⟨clsL, [(0, stCls), (13, stJ1)], none⟩,
  ⟨doneL, [(0, [((SI.leaRip .rax "scc_rt_stack_free_n").toDir, 7)]), (7, stFreeN),
    (26, [((SI.leaRip .rax "scc_rt_stack_free").toDir, 7)]), (33, stFree),
    (52, [((SI.leaRip .rax "scc_rt_stack_lock").toDir, 7)]), (59, stLock)], none⟩,
  ⟨spinL, [(0, stSwp), (11, (parse("xchgq %rax, (%rcx)")).zip [3]), (14, stSpin)], none⟩,
  ⟨lockedL, [(0, stLdN), (4, (parse("movq (%rcx), %rax")).zip [3]), (7, stEmpty)], none⟩,
  ⟨bumpL, [(0, [((SI.leaRip .rax "scc_rt_stack_lock").toDir, 7)]), (7, stUnl),
    (28, (parse("movq %rax, (%rcx)")).zip [3]), (31, [((SI.leaRip .rax "scc_rt_stack_next").toDir, 7)]),
    (38, stAdd), (56, (parse("lock xaddq %rax, (%rcx)")).zip [5]), (61, stBnd), (108, stJ2)], none⟩,
  ⟨okL, [(0, [((SI.leaRip .rax "scc_rt_stacks").toDir, 7)]), (7, stOk)], none⟩,
  ⟨takenL, [(0, stSite)], some (11, siteL)⟩,
  ⟨siteL, [(0, (parse("nop")).zip [1]), (1, stRet)], none⟩]

end Take

/-- **The runtime's code at `mc`**, in program order: `_start`,
`scc_rt_start`, `scc_rt_main`, `scc_rt_alloc_tcb`, `scc_rt_thread_init`,
`scc_rt_stack_take`. -/
def rtCodeTab (mc : MainCode) : List RGrp := startGrps ++ mainUGrps mc ++ tcbGrps ++ tiGrps ++ takeGrps

/-- **The runtime's code checks of `startU_segW` and `entry_segW'`, in one
pass.** -/
def rtCodeOk (cells : List (Directive × Nat)) (mc : MainCode) : Bool := rtIn cells (rtCodeTab mc)

/-- **`scc_rt_main` without a setup block**, as today's emitter writes it:
frame 32, the result spilled at `-16`, `call wc_main`, its labels and cell
sizes, `%rdi` stored at `-8(%rbp)`. -/
def bareMC : MainCode :=
  ⟨32, -16, "wc_main", ".Lscc_rt_main.chk", ".Lscc_rt_main.stk", ".Lscc_rt_main.entry", ".Lscc_rt_main.x2",
    5, 9, 3, 2, 4, [(.rdi, -8, 4)], 4, 4, 5⟩

end Spike.Lib.X64.Rt
