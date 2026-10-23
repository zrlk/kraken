/-
**The AArch64 runtime's code checks, light** (`rtCodeOk`): the code
premises of `startU_segW` (`Spike/Lib/Rt/A64Segs.lean`) and of `_start`'s
branch (`entry_segW'`) as groups of fixed code (`RGrp`) in program order
(`rtCodeTab`), checked by one pass over the program (`rtIn`,
`Scc/Cert/Rt/RtPassA64.lean`) instead of a search per label.

- The groups are over **copies of the hand files' blocks** (`Code.Tcb`,
  `Code.Take`, `Code.Ti`, `Code.Start`), so that the placement check reads
  them without importing the hand proofs; `Spike/Lib/Rt/A64RtCode.lean`
  checks the copies against the hand blocks (`rtCodeTab_eq`, `rfl`) and
  gives the checks back (`rtCodeIn_of_ok`).
- `scc_rt_main`'s facts (`MainCode`, `mainUIn`) live here for the same
  reason; `bareMC` is today's emitter's `scc_rt_main` without a setup block.
- **The labels are fixed.** scc's AArch64 emitter names a function's local
  labels `.L<i>_<fn>.<suffix>`, `i` the function's index in the program and
  the suffix numbered within the function (its block's index, `sp<k>`,
  `halt<k>`). The runtime's functions precede the user's, so their labels
  are the same in every program (`ret0.w` and `hello1.w` agree). The x86-64
  emitter numbers its return points per program instead, which is why only
  that twin needs labels read from the program.
- The pass is separate from A7's (`Scc/Cert/Rt/A64RtIn.lean`): `scc_rt_main`'s
  groups name its return point, which A7's tail group also names, and one
  pass checks each label once.
-/
import Spike.Lib.A64CodeSegs
import Spike.Lib.A64Switch
import Scc.Cert.Rt.RtPassA64

namespace Spike.Lib.A64.Flow

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64

/-- `bl fn`. -/
def blD (fn : Label) : Directive :=
  .instr { operation_size := RegWidth.W64, operation := Operation.BL fn }

end Spike.Lib.A64.Flow

namespace Spike.Lib.A64.Rt

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Scc.Cert.Rt.A64 (RGrp rtIn blockAt labelGap)

/-! ## The program's facts -/

/-- **What `scc_rt_main` reads of the program**: its frame `Z`, the spill
offset `k` of the exit value, the user function `fn`, and its labels (the
prologue's check `sc`, the grow stub `grow`, the body's entry `e0`, the
call's return point `sp0`). -/
structure MainCode where
  Z : Int64
  k : Int64
  fn : Label
  sc : Label
  grow : Label
  e0 : Label
  sp0 : Label

/-- **`scc_rt_main`'s code in `prog`**: the stack-checked prologue (frame
`Z`, the limit at `[tpidr_el0, #8]`, `x0` saved at the frame's base), `bl fn`
at the body's entry, the return point right after it, and the `exit_group`
tail there with the value spilled at `k`. -/
def mainUIn (prog : List Directive) (mc : MainCode) : Bool :=
  prologueIn prog "scc_rt_main" mc.sc mc.e0 mc.Z 8 mc.grow [(.X0, 0)] &&
    blockAt prog mc.e0 0 [blD mc.fn] && labelGap prog mc.e0 mc.sp0 1 && exitIn prog mc.sp0 mc.k

/-- **`scc_rt_main` without a setup block**, as today's emitter writes it:
frame 48, the result spilled at 8, `bl wc_main`, its labels. -/
def bareMC : MainCode :=
  ⟨48, 8, "wc_main", ".L1_scc_rt_main.stack_check", ".L1_scc_rt_main.stack_grow", ".L1_scc_rt_main.0_entry",
    ".L1_scc_rt_main.sp0"⟩

namespace Code

/-! ## Copies of the hand blocks

The blocks of `Spike/Lib/A64Ret0AllocTcb.lean`, `A64Ret0StackTake.lean`,
`A64Ret0ThreadInit.lean` and `A64Ret0.lean`, verbatim, with their labels. -/

/-! ### `scc_rt_alloc_tcb` (`Ret0.AllocTcb`) -/

namespace Tcb

abbrev fnL : Label := "scc_rt_alloc_tcb"
abbrev entryL : Label := ".L3_scc_rt_alloc_tcb.0_entry"
abbrev lenL : Label := ".L3_scc_rt_alloc_tcb.1_len"
abbrev okL : Label := ".L3_scc_rt_alloc_tcb.3_ok"

/-- The prologue: a frame of 192, `x29`/`x30` saved at 176/184, `h`/`k` at 0/8. -/
def atPro : List Directive := parseAArch64("sub sp, sp, #192
str x29, [sp, #176]
str x30, [sp, #184]
add x29, sp, #176
str x0, [sp]
str x1, [sp, #8]")

/-- `k ≥ 2^28` goes to the abort. -/
def atChk : List Directive := parseAArch64("ldr x9, [sp, #8]
movz x10, #4096, lsl #16
subs xzr, x9, x10
b.hs .L3_scc_rt_alloc_tcb.2_full")

/-- On to `.1_len`. -/
def atJ1 : List Directive := parseAArch64("b .L3_scc_rt_alloc_tcb.1_len")

/-- The TCB's length in bytes, `d = (k·(len + m) + 1)·8` (at `[sp, #72]`). -/
def atLen : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #8
lsrv x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp]
movz x10, #22
lsrv x9, x9, x10
str x9, [sp, #32]
ldr x9, [sp, #32]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #40]
ldr x9, [sp, #24]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #8]
ldr x10, [sp, #48]
madd x9, x9, x10, xzr
str x9, [sp, #56]
ldr x9, [sp, #56]
movz x10, #1
add x9, x9, x10
str x9, [sp, #64]
ldr x9, [sp, #64]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #72]")

/-- The add's operands: `x9 = d`, `x10` the counter's address. -/
def atArg : List Directive := parseAArch64("str x9, [sp, #80]
ldr x9, [sp, #72]
ldr x10, [sp, #80]")

/-- The counter's old value saved; past the pinned area (`2^17` bytes) goes to the abort. -/
def atBnd : List Directive := parseAArch64("str x11, [sp, #88]
ldr x9, [sp, #88]
ldr x10, [sp, #72]
add x9, x9, x10
str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #2, lsl #16
subs xzr, x9, x10
b.hi .L3_scc_rt_alloc_tcb.2_full")

/-- On to `.3_ok`. -/
def atJ2 : List Directive := parseAArch64("b .L3_scc_rt_alloc_tcb.3_ok")

/-- The header `h | k << 36` and its address `pinned + old + 8·k·m`. -/
def atOk : List Directive := parseAArch64("str x9, [sp, #104]
ldr x9, [sp, #104]
ldr x10, [sp, #88]
add x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #8]
ldr x10, [sp, #40]
madd x9, x9, x10, xzr
str x9, [sp, #120]
ldr x9, [sp, #120]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #128]
ldr x9, [sp, #8]
movz x10, #36
lslv x9, x9, x10
str x9, [sp, #136]
ldr x9, [sp]
ldr x10, [sp, #136]
orr x9, x9, x10
str x9, [sp, #144]
ldr x9, [sp, #112]
ldr x10, [sp, #128]
add x9, x9, x10
str x9, [sp, #152]
ldr x9, [sp, #144]
ldr x10, [sp, #152]")

/-- `x0` one word past the header; the epilogue and the return. -/
def atRet : List Directive := parseAArch64("ldr x9, [sp, #112]
ldr x10, [sp, #128]
add x9, x9, x10
str x9, [sp, #160]
ldr x9, [sp, #160]
movz x10, #8
add x9, x9, x10
str x9, [sp, #168]
ldr x0, [sp, #168]
ldr x29, [sp, #176]
ldr x30, [sp, #184]
add sp, sp, #192
ret")

end Tcb

/-! ### `scc_rt_stack_take` (`Ret0.StackTake`) -/

namespace Take

abbrev fnL : Label := "scc_rt_stack_take"
abbrev entryL : Label := ".L6_scc_rt_stack_take.0_entry"
abbrev clsL : Label := ".L6_scc_rt_stack_take.1_cls5"
abbrev doneL : Label := ".L6_scc_rt_stack_take.3_clsdone7"
abbrev spinL : Label := ".L6_scc_rt_stack_take.4_spin14"
abbrev lockedL : Label := ".L6_scc_rt_stack_take.5_locked15"
abbrev bumpL : Label := ".L6_scc_rt_stack_take.7_bump"
abbrev okL : Label := ".L6_scc_rt_stack_take.9_ok"
abbrev takenL : Label := ".L6_scc_rt_stack_take.10_taken"
abbrev siteL : Label := "scc_rt_take_site"

/-- The prologue: a frame of 208, `x29`/`x30` saved at 192/200, the size `a` at 0. -/
def stPro : List Directive := parseAArch64("sub sp, sp, #208
str x29, [sp, #192]
str x30, [sp, #200]
add x29, sp, #192
str x0, [sp]")

/-- The size classes' start: class 16384, offset 0, count 32768, index 0. -/
def stInit : List Directive := parseAArch64("movz x9, #16384
str x9, [sp, #8]
movz x9, #0
str x9, [sp, #16]
movz x9, #32768
str x9, [sp, #24]
movz x9, #0
str x9, [sp, #32]
b .L6_scc_rt_stack_take.1_cls5")

/-- A class below `a` goes on to the next. -/
def stCls : List Directive := parseAArch64("ldr x9, [sp, #8]
ldr x10, [sp]
subs xzr, x9, x10
b.lo .L6_scc_rt_stack_take.2_clsnext6")

/-- On to `.3_clsdone7`. -/
def stJ1 : List Directive := parseAArch64("b .L6_scc_rt_stack_take.3_clsdone7")

/-- The class's free count's address (the count array plus the index). -/
def stFreeN : List Directive := parseAArch64("str x9, [sp, #48]
ldr x9, [sp, #48]
ldr x10, [sp, #32]
add x9, x9, x10
str x9, [sp, #56]")

/-- The class's free list's address (the list array plus the offset). -/
def stFree : List Directive := parseAArch64("str x9, [sp, #64]
ldr x9, [sp, #64]
ldr x10, [sp, #16]
add x9, x9, x10
str x9, [sp, #72]")

/-- The lock's address saved; on to the spin. -/
def stLock : List Directive := parseAArch64("str x9, [sp, #80]
b .L6_scc_rt_stack_take.4_spin14")

/-- The swap's operands: `x9 = 1`, `x10` the lock's address. -/
def stSwp : List Directive := parseAArch64("movz x9, #1
ldr x10, [sp, #80]")

/-- The lock's old value saved; `0` goes on to `.5_locked15`. -/
def stSpin : List Directive := parseAArch64("str x11, [sp, #88]
ldr x9, [sp, #88]
movz x10, #0
subs xzr, x9, x10
b.eq .L6_scc_rt_stack_take.5_locked15")

/-- The free count's address. -/
def stLdN : List Directive := parseAArch64("ldr x10, [sp, #56]")

/-- An empty free list goes on to `.7_bump`. -/
def stEmpty : List Directive := parseAArch64("str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #0
subs xzr, x9, x10
b.eq .L6_scc_rt_stack_take.7_bump")

/-- The unlock's operands: `x9 = 0`, `x10` the lock's address. -/
def stUnl : List Directive := parseAArch64("str x9, [sp, #144]
movz x9, #0
ldr x10, [sp, #144]")

/-- The add's operands: `x9 = a`, `x10` the next offset's address. -/
def stAdd : List Directive := parseAArch64("str x9, [sp, #152]
ldr x9, [sp]
ldr x10, [sp, #152]")

/-- The old offset saved; past the stacks' area (`2^29` bytes) goes to the abort. -/
def stBnd : List Directive := parseAArch64("str x11, [sp, #160]
ldr x9, [sp, #160]
ldr x10, [sp]
add x9, x9, x10
str x9, [sp, #168]
ldr x9, [sp, #168]
movz x10, #8192, lsl #16
subs xzr, x9, x10
b.hi .L6_scc_rt_stack_take.8_full")

/-- On to `.9_ok`. -/
def stJ2 : List Directive := parseAArch64("b .L6_scc_rt_stack_take.9_ok")

/-- The stack's base: the stacks' address plus the old offset; on to `.10_taken`. -/
def stOk : List Directive := parseAArch64("str x9, [sp, #176]
ldr x9, [sp, #176]
ldr x10, [sp, #160]
add x9, x9, x10
str x9, [sp, #128]
b .L6_scc_rt_stack_take.10_taken")

/-- The site's operands: `x0` the base, `x1 = a`. -/
def stSite : List Directive := parseAArch64("ldr x0, [sp, #128]
ldr x1, [sp]")

/-- `x0` the base; the epilogue and the return. -/
def stRet : List Directive := parseAArch64("ldr x0, [sp, #128]
ldr x29, [sp, #192]
ldr x30, [sp, #200]
add sp, sp, #208
ret")

end Take

/-! ### `scc_rt_thread_init` (`Ret0.ThreadInit`) -/

namespace Ti

abbrev fnL : Label := "scc_rt_thread_init"
abbrev entryL : Label := ".L5_scc_rt_thread_init.0_entry"
abbrev spL : Label := ".L5_scc_rt_thread_init.sp0"

/-- The prologue: a frame of 48, `x29`/`x30` saved at 32/40, the TCB's address at 0. -/
def tiPro : List Directive := parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]")

/-- The stack: `scc_rt_stack_take(16384)`. -/
def tiCall : List Directive := parseAArch64("movz x0, #16384
bl scc_rt_stack_take")

/-- The stack's base, limit (`base + 4096`) and top (`base + 16384`) saved; the first field's operands. -/
def tiSp : List Directive := parseAArch64("str x0, [sp, #8]
ldr x9, [sp, #8]
movz x10, #4096
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #8]
movz x10, #16384
add x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp]
ldr x10, [sp]")

/-- The limit field's operands. -/
def tiF1 : List Directive := parseAArch64("ldr x9, [sp, #16]
ldr x10, [sp]")

/-- The third field's operands (`0`). -/
def tiF2 : List Directive := parseAArch64("movz x9, #0
ldr x10, [sp]")

/-- The fourth field's operands (`0`). -/
def tiF3 : List Directive := parseAArch64("movz x9, #0
ldr x10, [sp]")

/-- The base field's operands. -/
def tiF4 : List Directive := parseAArch64("ldr x9, [sp, #8]
ldr x10, [sp]")

/-- The top field's operands. -/
def tiF5 : List Directive := parseAArch64("ldr x9, [sp, #24]
ldr x10, [sp]")

/-- `x0` the top; the epilogue and the return. -/
def tiRet : List Directive := parseAArch64("ldr x0, [sp, #24]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

end Ti

/-! ### `scc_rt_start` and `_start` (`Ret0`) -/

namespace Start

abbrev sp2L : Label := ".L0_scc_rt_start.sp2"
abbrev sp3L : Label := ".L0_scc_rt_start.sp3"

/-- `scc_rt_start`'s call of `scc_rt_alloc_tcb` with the header and `k = 1`. -/
def startCall : List Directive := parseAArch64("str x0, [sp, #8]
movz x0, #2307
movz x1, #1
bl scc_rt_alloc_tcb")

/-- `.sp2`'s block: the TCB saved at `[sp, #16]`, the call of `scc_rt_thread_init`. -/
def startCall2 : List Directive := parseAArch64("str x0, [sp, #16]
ldr x0, [sp, #16]
bl scc_rt_thread_init")

/-- `.sp3`'s block: the top saved at `[sp, #24]`, `x9` the top, `x10` and `x0` the TCB. -/
def startSw0 : List Directive := parseAArch64("str x0, [sp, #24]
ldr x9, [sp, #24]
ldr x10, [sp, #16]
ldr x0, [sp, #16]")

/-- After the switch: `x29 = 0`, the call of `scc_rt_main`. -/
def startMain : List Directive := parseAArch64("movz x29, #0
bl scc_rt_main")

/-- `_start`: the branch to `scc_rt_start`. -/
def entryB : List Directive := parseAArch64("b scc_rt_start")

end Start

end Code

/-! ## The groups -/

section Grps

open Code

/-- An `adrp`/`add` pair of the label `L` into `x9` at `k`. -/
def labPair (k : Nat) (L : Label) : List (Nat × List Directive) :=
  [(k, [(SI.adrp .X9 L).toDir]), (k + 1, [(SI.addLo12 .X9 .X9 L).toDir])]

/-- `_start`'s and `scc_rt_start`'s groups: the branch at `_start`; the
frame's setup and the fall-through into `.0_entry`; the handler, the
arguments, the system call and the call of `scc_rt_alloc_tcb` at
`.0_entry`, `.sp2` after it; the call of `scc_rt_thread_init` at `.sp2`,
`.sp3` after it; the switch and the call of `scc_rt_main` at `.sp3`. -/
def startGrps : List RGrp := [
  ⟨"_start", [(0, Start.entryB)], none⟩,
  ⟨"scc_rt_start", [(0, Abort.b0)], some (4, startE)⟩,
  ⟨startE, labPair 0 sigign ++ [(2, startArgs), (8, [svcDir]), (9, Start.startCall)], some (13, Start.sp2L)⟩,
  ⟨Start.sp2L, [(0, Start.startCall2)], some (3, Start.sp3L)⟩,
  ⟨Start.sp3L, [(0, Start.startSw0), (4, [(SI.msr .X10).toDir]), (5, [swDir .X9]), (6, Start.startMain)], none⟩]

/-- `scc_rt_main`'s groups at `mc`: the fall-through into the check, the
check and the frame's setup and the fall-through into the body, `bl fn` and
the return point after it, the `exit_group` tail there. -/
def mainUGrps (mc : MainCode) : List RGrp := [
  ⟨"scc_rt_main", [], some (0, mc.sc)⟩,
  ⟨mc.sc, [(0, chkHead mc.Z), (2, [ldrDir .X10 .X10 8]), (3, chkBr mc.grow), (5, frameSet mc.Z [(.X0, 0)])],
    some (10, mc.e0)⟩,
  ⟨mc.e0, [(0, [blD mc.fn])], some (1, mc.sp0)⟩,
  ⟨mc.sp0, [(0, exitTail mc.k), (3, [svcDir])], none⟩]

/-- `scc_rt_alloc_tcb`'s groups (`allocTcbIn`). -/
def tcbGrps : List RGrp := [
  ⟨Tcb.fnL, [(0, Tcb.atPro)], some (6, Tcb.entryL)⟩,
  ⟨Tcb.entryL, [(0, Tcb.atChk), (4, Tcb.atJ1)], none⟩,
  ⟨Tcb.lenL, [(0, Tcb.atLen)] ++ labPair 32 "scc_rt_pinned_next" ++
    [(34, Tcb.atArg), (37, [ldopDir .ADD .acqRel .X9 .X11 .X10]), (38, Tcb.atBnd), (47, Tcb.atJ2)], none⟩,
  ⟨Tcb.okL, labPair 0 "scc_rt_pinned" ++ [(2, Tcb.atOk), (29, [strDir .X9 .X10 0]), (30, Tcb.atRet)], none⟩]

/-- `scc_rt_thread_init`'s groups (`threadInitIn`, `tiSpIn`). -/
def tiGrps : List RGrp := [
  ⟨Ti.fnL, [(0, Ti.tiPro)], some (5, Ti.entryL)⟩,
  ⟨Ti.entryL, [(0, Ti.tiCall)], some (2, Ti.spL)⟩,
  ⟨Ti.spL, [(0, Ti.tiSp), (11, parseAArch64("str x9, [x10]")), (12, Ti.tiF1),
    (14, parseAArch64("str x9, [x10, #8]")), (15, Ti.tiF2), (17, parseAArch64("str x9, [x10, #16]")),
    (18, Ti.tiF3), (20, parseAArch64("str x9, [x10, #24]")), (21, Ti.tiF4),
    (23, parseAArch64("str x9, [x10, #32]")), (24, Ti.tiF5), (26, parseAArch64("str x9, [x10, #40]")),
    (27, Ti.tiRet)], none⟩]

/-- `scc_rt_stack_take`'s groups (`stackTakeIn`). -/
def takeGrps : List RGrp := [
  ⟨Take.fnL, [(0, Take.stPro)], some (5, Take.entryL)⟩,
  ⟨Take.entryL, [(0, Take.stInit)], none⟩,
  ⟨Take.clsL, [(0, Take.stCls), (4, Take.stJ1)], none⟩,
  ⟨Take.doneL, labPair 0 "scc_rt_stack_free_n" ++ [(2, Take.stFreeN)] ++ labPair 7 "scc_rt_stack_free" ++
    [(9, Take.stFree)] ++ labPair 14 "scc_rt_stack_lock" ++ [(16, Take.stLock)], none⟩,
  ⟨Take.spinL, [(0, Take.stSwp), (2, parseAArch64("swpal x9, x11, [x10]")), (3, Take.stSpin)], none⟩,
  ⟨Take.lockedL, [(0, Take.stLdN), (1, parseAArch64("ldr x9, [x10]")), (2, Take.stEmpty)], none⟩,
  ⟨Take.bumpL, labPair 0 "scc_rt_stack_lock" ++ [(2, Take.stUnl), (5, parseAArch64("stlr x9, [x10]"))] ++
    labPair 6 "scc_rt_stack_next" ++
    [(8, Take.stAdd), (11, parseAArch64("ldaddal x9, x11, [x10]")), (12, Take.stBnd), (21, Take.stJ2)], none⟩,
  ⟨Take.okL, labPair 0 "scc_rt_stacks" ++ [(2, Take.stOk)], none⟩,
  ⟨Take.takenL, [(0, Take.stSite)], some (2, Take.siteL)⟩,
  ⟨Take.siteL, [(0, parseAArch64("nop")), (1, Take.stRet)], none⟩]

end Grps

/-- **The runtime's code at `mc`**, in program order: `_start`,
`scc_rt_start`, `scc_rt_main`, `scc_rt_alloc_tcb`, `scc_rt_thread_init`,
`scc_rt_stack_take`. -/
def rtCodeTab (mc : MainCode) : List RGrp := startGrps ++ mainUGrps mc ++ tcbGrps ++ tiGrps ++ takeGrps

/-- **The runtime's code checks of `startU_segW` and `entry_segW'`, in one
pass.** -/
def rtCodeOk (prog : List Directive) (mc : MainCode) : Bool := rtIn prog (rtCodeTab mc)

end Spike.Lib.A64.Rt
