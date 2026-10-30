import Scc.Cert.A12StageX64

/-!
# `placeOK2` for spawning programs (x86-64)

`placeOK` (`Scc/Cert/PlaceOKX64.lean`)
with three of its checks extended for a program whose `main` takes its
thread id and spawns (`wake.w`, `hello.w`), the frozen checks untouched.

* **A11'** (`a11'`): with a `.bare` tail and an IR whose `scc_rt_main` calls
  `wc_main(tcb)` (`isTidMain`), the runtime's code with `scc_rt_main`'s
  body loading the TCB from `-8(%rbp)` before the call (`mainTGrps`,
  `rtCodeOkT`) and its phase facts (`mainPhTabT`); otherwise `a11`. One
  shape, one table: the dispatch is strict.
* **A12'** (`a12'`): `a12` with two relaxations.
  - The stack need admits calls of the spawn path's runtime routines
    (`rtDepth'`: `scc_rt_park`, `scc_rt_unpark`, `scc_rt_thread_reserve`,
    `scc_rt_alloc_tcb`, `scc_rt_thread_init`, each with its depth).
  - A call of one of the reentrant runtime routines (`reent`) may enter a
    callee of another phase index if it keeps the stack lock's bit
    (`runPhB2`): the user code is in phase `0`, `scc_rt_alloc_tcb` and
    `scc_rt_thread_init` start in the start-up's phases, and neither holds
    the stack lock at its entry.
* **A13** (`a13`), for a program with a `clone`: the thread counter
  `scc_rt_nthreads` a decided word clear of the runtime's words, the second
  stack in the pool, the second TCB's allocation (up to `maxSpawnArgs`
  arguments) in clear words, and the code and phase facts of
  `scc_rt_thread_reserve`, `scc_rt_park` and `scc_rt_unpark`.

This file holds the check's definitions and `placeOK2_of` (a certificate's
combination of its decisions). The lemmas relating `placeOK2` to `placeOK`
are in `Spike/Lib/SpawnX64.lean`: `a11'_of_a11`, `a12'_of_a12` and
`a13_of_noClone` give `placeOK2` from `placeOK` on a program that neither
takes its thread id nor spawns (`placeOK2_of_placeOK`), so that `hello1.w`
and `ret0.w` re-certify without new decisions.
-/

namespace Scc.Cert.Spawn.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.X64.Parser
open Scc.Cert.PlaceOK.X64
open Spike.Lib.LowerX64 (proL ovfL ovfBlk stkHead proPhOk proLabs blkLabs raL)
open Spike.Lib.X64 (cellOff classify AI)
open Spike.Lib.X64Consumer (aiTgts)
open Scc.Emit.X64 (Frame labelOf directives)
open Scc.Cert.Rt.X64 (codeT phTabBy sitesBy inRs RGrp PhFact rtIn)
open Scc.Cert.Code1X64 (blockItems hasAddChk chkL starts callees rtDepth rtOk needOk1)
open Scc.Cert.Ph1X64 (runs runPhB runPh)

/-! ## A11': `scc_rt_main` passing the TCB -/

section Tid

open Spike.Lib.X64.Rt
open Spike.Lib.X64.Flow
open Spike.Lib.X64 (fsDir callB)
open Kraken.Promising.Lower.X64 (op64)

/-- **`scc_rt_main`'s groups when `main` takes its thread id**: the bare
shape's (`mainUGrps`) but the body's entry, `movq -8(%rbp), %rdi` (the
TCB, four bytes) then `call fn`, the return point nine bytes on. -/
def mainTGrps (mc : MainCode) : List RGrp := [
  ⟨"scc_rt_main", [(0, xHead)], some (4, mc.sc)⟩,
  ⟨mc.sc, [(0, xLea mc.Z mc.zl), (mc.zl, [(fsDir .r11 8, mc.zf)]), (mc.zl + mc.zf, xCmp mc.grow mc.z1 mc.z2),
    (mc.zl + mc.zf + mc.z1 + mc.z2, xFr mc.Z mc.zs mc.ps)],
    some (mc.zl + mc.zf + mc.z1 + mc.z2 + mc.zs + szSum mc.ps, mc.e0)⟩,
  ⟨mc.e0, [(0, [xLd (.rdi, -8, 4)] ++ callB mc.fn)], some (9, mc.sp0)⟩,
  ⟨mc.sp0, [(0, xExit mc.k mc.ze0 mc.ze1 mc.ze2), (mc.ze0 + mc.ze1 + mc.ze2, [(op64 .syscall, 2)])], none⟩]

/-- **The runtime's code when `main` takes its thread id**, in program
order (`rtCodeTab` with `mainTGrps`). -/
def rtCodeTabT (mc : MainCode) : List RGrp := startGrps ++ mainTGrps mc ++ tcbGrps ++ tiGrps ++ takeGrps

/-- The runtime's code when `main` takes its thread id, in one pass. -/
def rtCodeOkT (cells : List (Directive × Nat)) (mc : MainCode) : Bool := rtIn cells (rtCodeTabT mc)

/-- **`scc_rt_main`'s phase facts when `main` takes its thread id**
(`mainPhTab` with the body's block `mainTGrps`'). -/
def mainPhTabT (mc : MainCode) : List PhFact :=
  [.blk "scc_rt_main" 0 xHead none none, .blk mc.sc 0 (xLea mc.Z mc.zl) none none, .step mc.sc mc.zl mc.zf,
    .blk mc.sc (mc.zl + mc.zf) (xCmp mc.grow mc.z1 mc.z2) none none,
    .blk mc.sc (mc.zl + mc.zf + mc.z1 + mc.z2) (xFr mc.Z mc.zs mc.ps) none none,
    .blk mc.e0 0 ([xLd (.rdi, -8, 4)] ++ callB mc.fn) none none, .blk mc.sp0 0 (xExit mc.k mc.ze0 mc.ze1 mc.ze2) none none,
    .step mc.sp0 (mc.ze0 + mc.ze1 + mc.ze2) 2]

/-- **A11 at the thread-id shape**: the code (`rtCodeOkT`) and phase facts
(`mainPhTabT`) at today's bare frame (`bareMC`). -/
def tidOk (cells : List (Directive × Nat)) (lo : Nat) (Λ : Scc.Sem.Layout) : Bool :=
  rtCodeOkT cells bareMC && Scc.Cert.Rt.X64.rtPhOk lo cells Λ (mainPhTabT bareMC)

/-- The body's block at the thread-id shape is the parser's form of the
listing's. -/
example : [xLd (.rdi, -8, 4)] ++ callB "wc_main" = (parse("movq -8(%rbp), %rdi
call wc_main")).zip [4, 5] := by decide

end Tid

/-- **`scc_rt_main` passes the TCB to `main`**: one of its blocks calls
`wc_main` with the argument `tcb` (`Lower.mainArgs` at `.tid`). -/
def isTidMain (ir : Scc.IR.Program) : Bool :=
  ir.funcs.any fun f => f.name == "scc_rt_main" && f.blocks.any fun b => b.insts.any fun
    | .call _ g args => g == "wc_main" && args == [.reg "tcb"]
    | _ => false

/-- Whether the output's IR is of the thread-id shape. -/
def tidOf (o : Out) : Bool := (o.place.ir.map isTidMain).getD false

/-- **A11'**: at a `.bare` tail of the thread-id shape `tidOk`, otherwise
`a11`. -/
def a11' (o : Out) (t : Tables) : Bool :=
  if tidOf o && o.place.tail == .bare then tidOk o.prog t.Λ.code.lo t.Λ else a11 o t

/-! ## A12': the stack need -/

/-- **The runtime routines a stack-checked function may call, with their
depth**, on the spawn path: `rtDepth`'s, then `scc_rt_park`'s,
`scc_rt_unpark`'s, `scc_rt_thread_reserve`'s, `scc_rt_alloc_tcb`'s and
`scc_rt_thread_init`'s (its frame, then `scc_rt_stack_take`'s and
`scc_rt_abort`'s). -/
def rtDepth' : List (String × Nat) :=
  rtDepth ++ [("scc_rt_park", 64), ("scc_rt_unpark", 48), ("scc_rt_thread_reserve", 96),
    ("scc_rt_alloc_tcb", 240), ("scc_rt_thread_init", 304)]

/-- `rtOk` over `rtDepth'`. -/
def rtOk' (g : String) : Bool :=
  match rtDepth'.lookup g with
  | some d => decide (d ≤ Scc.IR.Tcb.headroom)
  | none => false

/-- `needOk1` over `rtOk'`. -/
def needOk1' (tbl : List Scc.Cert.NeedX64.Row) (name : String) (size : Nat) (f : Scc.IR.Func) : Bool :=
  match Scc.Cert.NeedX64.row? tbl name with
  | some (_, fr, nf) =>
    fr == size + 8 && decide (size + 8 ≤ nf) &&
    (callees f).1.all (fun g => match Scc.Cert.NeedX64.row? tbl g with
      | some (_, _, ng) => decide (size + 8 + 8 + ng ≤ nf)
      | none => rtOk' g) &&
    (callees f).2.all (fun g => match Scc.Cert.NeedX64.row? tbl g with
      | some (_, _, ng) => decide (ng ≤ nf)
      | none => rtOk' g)
  | none => false

/-- `fnOk1K` over `needOk1'`. -/
def fnOk1K' (T : List (Nat × Nat × List (Directive × Nat))) (tbl : List Scc.Cert.NeedX64.Row)
    (ir : Scc.IR.Program) (n : Nat) (f : Scc.IR.Func) : Bool :=
  let fr := frOfK ir f
  match f.blocks, szK T (chkL f) 0 (5 + f.params.length) with
  | b0 :: _, zl :: zf :: z1 :: z2 :: zs :: zps =>
    match spillsK (rsK (kslots fr)) f.params zps with
    | some ps =>
      ir.growth.isSome &&
      prologueInK T f.name (chkL f) (labelOf f.name b0.label) (Int64.ofInt fr.size)
        (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs ps &&
      decide (fr.size < 2 ^ 31) && decide (fr.size % 16 = 0) &&
      blocksOkK T fr n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) &&
      (!hasAddChk f || (ir.abortFn == "scc_rt_abort" && blkBK T (ovfL fr) 0 ovfBlk)) &&
      needOk1' tbl f.name fr.size f &&
      blkBK T (proL fr) 0 stkHead
    | none => false
  | _, _ => false

/-- `fnCode1OkK` over `fnOk1K'`. -/
def fnCode1OkK' (T : List (Nat × Nat × List (Directive × Nat))) (tbl : List Scc.Cert.NeedX64.Row)
    (ir : Scc.IR.Program) : Bool :=
  (starts ir 0 ir.funcs).all fun (f, n) => !f.checkStack || fnOk1K' T tbl ir n f

/-! ## A12': the phases at a reentrant call -/

/-- **The reentrant runtime routines**: those a user function may call on
the spawn path whose entry is not in the caller's phase (or may not be:
`scc_rt_park`, `scc_rt_unpark`, `scc_rt_thread_reserve` are listed with
the others), none holding the stack lock at its entry. -/
def reent : List String :=
  ["scc_rt_alloc_tcb", "scc_rt_thread_init", "scc_rt_thread_reserve", "scc_rt_park", "scc_rt_unpark"]

/-- The directive is a `call` of a reentrant runtime routine. -/
def reentCall (d : Directive) : Bool :=
  match classify d with
  | some (.call L) => reent.contains L
  | _ => false

/-- **`runPhB` with the reentrant calls' rule**: as `runPhB`, but a
target of a call of a reentrant routine (`reentCall`) is in the run's phase
or has the run's stack lock bit `lk`. -/
def runPhB2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (pc ra : Int64)
    (blk : List (Directive × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    okPc (pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat &&
    ph (pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat == ph pc.toBitVec.toNat &&
    match blk[k]? with
    | some dz =>
      (match classify dz.1 with
       | some a => aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) ra a
       | none => [pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2]).all fun t =>
        ph t.toBitVec.toNat == ph pc.toBitVec.toNat ||
          (reentCall dz.1 && lk t.toBitVec.toNat == lk pc.toBitVec.toNat)
    | none => false

/-- `runPh` over `runPhB2`. -/
def runPh2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (ra : Int64)
    (r : Label × List (Directive × Nat)) : Bool :=
  res r.1 && (blkLabs r.2).all res && runPhB2 okPc ph lk lab (lab r.1) ra r.2

/-- `blocksPhK` over `runPh2`. -/
def blocksPhK2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (T : List (Nat × Nat × List (Directive × Nat))) (fr : Frame) (ra : Int64) :
    Nat → List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) → Bool
  | _, [] => true
  | n, (b, ms) :: bs =>
    match blockItems fr n b ms with
    | .ok (code, n') =>
      (runs (labelOf fr.fn b.label)
          (segCellsK T (labelOf fr.fn b.label) (directives code).length)).all (fun r =>
            runPh2 okPc ph lk lab res ra r && ph (lab r.1).toBitVec.toNat == ph ra.toBitVec.toNat) &&
        blocksPhK2 okPc ph lk lab res T fr ra n' bs
    | .error _ => false

/-- `fnPhFK` over `blocksPhK2` (the prologue's and the overflow block's
checks unchanged: neither calls a runtime routine). -/
def fnPhFK2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (T : List (Nat × Nat × List (Directive × Nat))) (ir : Scc.IR.Program) (n : Nat) (f : Scc.IR.Func)
    (ra : Int64) : Bool :=
  let fr := frOfK ir f
  match szK T (chkL f) 0 (5 + f.params.length) with
  | zl :: zf :: z1 :: z2 :: zs :: zps =>
    match spillsK (rsK (kslots fr)) f.params zps with
    | some ps =>
      res f.name && res (chkL f) &&
      (proLabs (Int64.ofInt fr.size) (proL fr) zl z1 z2 zs ps).all res &&
      proPhOk okPc ph lab f.name (chkL f) (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs ps &&
      blocksPhK2 okPc ph lk lab res T fr ra n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) &&
      (!hasAddChk f || (res (ovfL fr) && (blkLabs ovfBlk).all res &&
        Spike.Lib.X64Consumer.blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 ovfBlk))
    | none => false
  | _ => false

/-- `fnPhAll1K` over `fnPhFK2`. -/
def fnPhAll1K2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (T : List (Nat × Nat × List (Directive × Nat))) (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  (starts ir 0 ir.funcs).all fun (f, n) => !f.checkStack || fnPhFK2 okPc ph lk lab res T ir n f ra

/-- **`fnPh1OkK` with the reentrant calls' rule**: the stack lock's bit
`lk` that of A6's phase table (`inRs P.l`). -/
def fnPh1OkK2 (T : List (Nat × Nat × List (Directive × Nat))) (lo : Nat) (Λ : Scc.Sem.Layout)
    (cells : List (Directive × Nat)) (ir : Scc.IR.Program) : Bool :=
  match phTabBy (codeT lo cells), sitesBy (codeT lo cells) Λ with
  | some P, some ss =>
    (codeT lo cells raL).isSome &&
      fnPhAll1K2 (fun pc => !ss.contains pc) P.ph (fun pc => (inRs P.l pc).toNat)
        (fun l => Int64.ofNat ((codeT lo cells l).getD 0))
        (fun l => (codeT lo cells l).isSome) T ir (Int64.ofNat ((codeT lo cells raL).getD 0))
  | _, _ => false

/-! ## A12' -/

/-- **A12''s code part** (`a12code` over `fnOk1K'`). -/
def a12code' (o : Out) : Bool :=
  match o.place.ir with
  | some ir => fnCode1OkK' (tailTab o.prog 0) o.place.need ir
  | none => false

/-- **A12''s phase part** (`a12ph` over `fnPh1OkK2`). -/
def a12ph' (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir => fnPh1OkK2 (tailTab o.prog 0) t.Λ.code.lo t.Λ o.prog ir
  | none => false

/-- **A12'**: its code part and its phase part, decided in two
declarations by a certificate. -/
def a12' (o : Out) (t : Tables) : Bool := a12code' o && a12ph' o t

/-! ## A13: the second thread -/

section A13

open Scc.Cert.Rt.X64 (rtA symLab rtWords wordOk WordSep clearB)
open Spike.Lib.X64 (fsDir SI)
open Kraken.Promising.Lower.X64 (op64)

/-- **`scc_rt_thread_reserve`'s code** (`Runtime.threadReserveF`): the
prologue, the counter's address, the `lock xadd`, the bound's check against
`maxThreads`, the abort and the return. -/
def reserveGrps : List RGrp := [
  ⟨"scc_rt_thread_reserve", [(0, (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4])], some (8, ".Lscc_rt_thread_reserve.entry")⟩,
  ⟨".Lscc_rt_thread_reserve.entry", [(0, [((SI.leaRip .rax "scc_rt_nthreads").toDir, 7)]),
    (7, (parse("movq %rax, -8(%rbp)
movq -8(%rbp), %rcx
movq $1, %rax")).zip [4, 4, 7]),
    (22, (parse("lock xaddq %rax, (%rcx)")).zip [5]),
    (27, (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $1023, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_thread_reserve.full")).zip [4, 4, 7, 3, 4, 4, 7, 3, 2]),
    (65, (parse("jmp .Lscc_rt_thread_reserve.ok")).zip [2])], none⟩,
  ⟨".Lscc_rt_thread_reserve.full", [(0, (parse("movq $5, %rdi
call scc_rt_abort")).zip [7, 5])], none⟩,
  ⟨".Lscc_rt_thread_reserve.ok", [(0, (parse("movq -24(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1])], none⟩]

/-- `xchgq %rax, 16(%rcx)` (the park word), four bytes. -/
def xchgPark : List (Directive × Nat) := (parse("xchgq %rax, 16(%rcx)")).zip [4]

/-- The `futex` call's argument block of `scc_rt_park` (`op = 128`, wait)
or `scc_rt_unpark` (`op = 129`, wake one): `op`, `val`. -/
def futexArgs (op val : Nat) : List (Directive × Nat) :=
  (parse("movq -8(%rbp), %rax
movq $16, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -24(%rbp), %rdi")).zip [4, 7, 3, 4, 4] ++
  [(op64 (.mov (.reg (.low .rsi .W64)) (.imm (.int64 (Int64.ofNat op)))), 7),
   (op64 (.mov (.reg (.low .rdx .W64)) (.imm (.int64 (Int64.ofNat val)))), 7)] ++
  (parse("movq $0, %r10
movq $0, %r8
movq $0, %r9
movl $202, %eax")).zip [7, 7, 7, 5]

/-- `futexArgs` are the listing's. -/
example : futexArgs 128 0 = (parse("movq -8(%rbp), %rax
movq $16, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -24(%rbp), %rdi
movq $128, %rsi
movq $0, %rdx
movq $0, %r10
movq $0, %r8
movq $0, %r9
movl $202, %eax")).zip [4, 7, 3, 4, 4, 7, 7, 7, 7, 7, 5] := by decide

/-- The epilogue `movq %rbp, %rsp; popq %rbp; ret`. -/
def epi : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

/-- **`scc_rt_park`'s code** (`Runtime.parkF`): the thread pointer, the
swap of the park word with `0`, the `futex` wait unless it was `1`, the
second swap. -/
def parkGrps : List RGrp := [
  ⟨"scc_rt_park", [(0, (parse("pushq %rbp
movq %rsp, %rbp
subq $48, %rsp")).zip [1, 3, 4])], some (8, ".Lscc_rt_park.entry")⟩,
  ⟨".Lscc_rt_park.entry", [(0, [(fsDir .rax 0, 9)]),
    (9, (parse("movq %rax, -8(%rbp)
movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 4, 7]),
    (24, xchgPark),
    (28, (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lscc_rt_park.done")).zip [4, 4, 7, 3, 2]),
    (48, (parse("jmp .Lscc_rt_park.wait")).zip [2])], some (50, ".Lscc_rt_park.wait")⟩,
  ⟨".Lscc_rt_park.wait", [(0, futexArgs 128 0), (62, [(op64 .syscall, 2)]),
    (64, (parse("movq %rax, -32(%rbp)
movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 4, 7]),
    (79, xchgPark),
    (83, (parse("movq %rax, -40(%rbp)")).zip [4] ++ epi)], some (92, ".Lscc_rt_park.done")⟩,
  ⟨".Lscc_rt_park.done", [(0, epi)], none⟩]

/-- **`scc_rt_unpark`'s code** (`Runtime.unparkF`): the swap of the
target's park word with `1`, the `futex` wake if it was `0`. -/
def unparkGrps : List RGrp := [
  ⟨"scc_rt_unpark", [(0, (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 4, 4])], some (12, ".Lscc_rt_unpark.entry")⟩,
  ⟨".Lscc_rt_unpark.entry", [(0, (parse("movq -8(%rbp), %rcx
movq $1, %rax")).zip [4, 7]),
    (11, xchgPark),
    (15, (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_unpark.wake")).zip [4, 4, 7, 3, 2]),
    (35, (parse("jmp .Lscc_rt_unpark.done")).zip [2])], some (37, ".Lscc_rt_unpark.wake")⟩,
  ⟨".Lscc_rt_unpark.wake", [(0, futexArgs 129 1), (62, [(op64 .syscall, 2)]),
    (64, (parse("movq %rax, -32(%rbp)")).zip [4] ++ epi)], some (73, ".Lscc_rt_unpark.done")⟩,
  ⟨".Lscc_rt_unpark.done", [(0, epi)], none⟩]

/-- **The spawn path's runtime code**, in program order. -/
def spawnGrps : List RGrp := reserveGrps ++ parkGrps ++ unparkGrps

/-- A representative return point in the user code's phase (`raL`,
`scc_rt_main`'s return point after `main`): each routine of `spawnGrps`
returns to its caller in the caller's phase. -/
def userRa : Option (String × Nat) := some (raL, 0)

/-- **The spawn path's phase facts**: each block's check (each `ret` to
`userRa`), the single steps (the thread pointer's load, the counter's
address, the system calls), the atomic accesses off the sites with their
next pcs in their phase. -/
def spawnPhTab : List PhFact :=
  let rv := ".Lscc_rt_thread_reserve.entry"
  let pk := ".Lscc_rt_park.entry"
  let pw := ".Lscc_rt_park.wait"
  let ue := ".Lscc_rt_unpark.entry"
  let uw := ".Lscc_rt_unpark.wake"
  let blks : List PhFact := (spawnGrps.flatMap fun g => g.bs.filterMap fun (o, b) =>
    if b.all (fun d => (classify d.1).isSome) then
      some (.blk g.l o b (if b.any (fun d => match classify d.1 with | some .ret => true | _ => false) then userRa else none) none)
    else none)
  blks ++ [.step rv 0 7, .step rv 22 5, .step pk 0 9, .step pk 24 4, .step pw 62 2, .step pw 79 4,
    .step ue 11 4, .step uw 62 2]

/-- Every block of `spawnGrps` but the five single instructions per
routine above is covered: the table checks them all. -/
example : (spawnGrps.flatMap fun g => g.bs.filter fun (_, b) => !b.all (fun d => (classify d.1).isSome)).length = 8 := by
  decide

/-- **The words the second thread adds**: the thread counter, and the
second allocation of `scc_rt_alloc_tcb` from `scc_rt_pinned` + 80 (after
the first TCB's ten words, `Runtime.allocF` at `2307`) up to its header,
its TCB and `maxSpawnArgs` argument words: sixteen words. -/
def spawnWords (pinA : BitVec 64) : List (BitVec 64) :=
  (List.range (1 + Scc.IR.Tcb.size / 8 + Scc.IR.maxSpawnArgs)).map fun i => pinA + BitVec.ofNat 64 (80 + 8 * i)

/-- **The words of a `scc_rt_alloc_tcb(h, k)` allocation** (`Runtime.allocF`
at the TCB layout, as `scc_rt_alloc_tcb`'s code computes them): the header,
then `k` times the `n` traced and `m` untraced words of `h`. -/
def tcbWords (h k : Nat) : Nat := k * ((h >>> 8) % 16384 + (h >>> 22) % 16384) + 1

/-- **Every TCB allocation fits `spawnWords`**: each call of
`scc_rt_alloc_tcb` has immediate arguments and at most sixteen words. -/
def allocFit (ir : Scc.IR.Program) : Bool :=
  ir.funcs.all fun f => f.blocks.all fun b => b.insts.all fun
    | .call _ g args => g != "scc_rt_alloc_tcb" || match args with
      | [.imm h, .imm k] => decide (tcbWords h.toNat k.toNat ≤ 1 + Scc.IR.Tcb.size / 8 + Scc.IR.maxSpawnArgs)
      | _ => false
    | _ => true

/-- The first TCB (`scc_rt_start`'s, `2307`) is ten words, `wake.w`'s
spawn twelve, a spawn of `maxSpawnArgs` words (`9 + 6` fields) sixteen. -/
example : (tcbWords 2307 1, tcbWords 8390915 1, tcbWords (9 * 256 + 6 * 2 ^ 22 + 3) 1,
    1 + Scc.IR.Tcb.size / 8 + Scc.IR.maxSpawnArgs) = (10, 12, 16, 16) := by decide

/-- **A13's data part**: `scc_rt_nthreads` a decided data symbol; its word
and the second allocation's passing `wordOk`, clear of the runtime's words
(`rtWords`) and of the allocator's counter, pairwise disjoint; the second
stack in the pool. -/
def a13data (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (secs : Scc.Sem.DataSecs) : Bool :=
  let pinA := rtA Λ cells secs "scc_rt_pinned"
  let ntA := rtA Λ cells secs "scc_rt_nthreads"
  let stacksA := rtA Λ cells secs "scc_rt_stacks"
  let old := rtWords pinA (rtA Λ cells secs "scc_rt_pinned_next") (rtA Λ cells secs "scc_rt_stack_next")
    (rtA Λ cells secs "scc_rt_stack_lock") (rtA Λ cells secs "scc_rt_stack_free_n")
  let new := ntA :: spawnWords pinA
  (symLab Λ.code.lo cells (Scc.Sem.loadSyms Λ secs.rodata) "scc_rt_nthreads").isSome &&
    new.all (wordOk Λ) &&
    new.all (fun a => old.all fun b => decide (WordSep a b)) &&
    new.all (fun a => decide (WordSep a (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf Λ)))) &&
    decide (new.Pairwise WordSep) &&
    decide (stacksA.toNat + 32768 ≤ Λ.stackPool.lo + Λ.stackPool.size)

/-- **A13's code part**: `spawnGrps` in the cells, its phase facts. -/
def a13code (lo : Nat) (cells : List (Directive × Nat)) (Λ : Scc.Sem.Layout) : Bool :=
  rtIn cells spawnGrps && Scc.Cert.Rt.X64.rtPhOk lo cells Λ spawnPhTab

end A13

/-- **The program spawns**: its IR has a `clone`. -/
def spawns (ir : Scc.IR.Program) : Bool :=
  ir.funcs.any fun f => f.blocks.any fun b => b.insts.any fun
    | .clone .. => true
    | _ => false

/-- Whether the output's IR spawns. -/
def spawnsOf (o : Out) : Bool := (o.place.ir.map spawns).getD false

/-- **A13**: for a program that spawns, its data part and its code part;
`true` otherwise. -/
def a13 (o : Out) (t : Tables) : Bool :=
  !spawnsOf o || ((o.place.ir.map allocFit).getD false && a13data t.Λ o.prog o.secs &&
    a13code t.Λ.code.lo o.prog t.Λ)

/-! ## `placeOK2` -/

/-- **The components of `placeOK2`** on x86-64: `checks` with A11' and
A12' ∧ A13. -/
def checks2 (cfg : Scc.Cert.PlaceOK.Config) : Scc.Cert.PlaceOK.Checks Out Tables :=
  { checks cfg with a11 := a11', a12 := fun o t => a12' o t && a13 o t }

/-- **`placeOK2` on x86-64.** -/
def placeOK2 (cfg : Scc.Cert.PlaceOK.Config) (o : Out) : Bool := (checks2 cfg).ok (tablesOf cfg) o

/-- **`placeOK2` at a given layout.** -/
def placeOK2At (cfg : Scc.Cert.PlaceOK.Config) (Λ : Scc.Sem.Layout) (o : Out) : Bool :=
  (checks2 cfg).ok (fun _ => ⟨Λ⟩) o

/-- **`placeOK2` from its components.** -/
theorem placeOK2_of {cfg : Scc.Cert.PlaceOK.Config} {o : Out}
    (h1 : a1 o (tablesOf cfg o) = true) (h2 : a2 o (tablesOf cfg o) = true)
    (h3 : a3 o (tablesOf cfg o) = true) (h4 : a4 cfg o (tablesOf cfg o) = true)
    (h5 : a5 o (tablesOf cfg o) = true) (h6 : a6 o (tablesOf cfg o) = true)
    (h7 : a7 o (tablesOf cfg o) = true) (h8 : a8 o (tablesOf cfg o) = true)
    (h9 : a9 o (tablesOf cfg o) = true) (h11 : a11' o (tablesOf cfg o) = true)
    (h12c : a12code' o = true) (h12p : a12ph' o (tablesOf cfg o) = true)
    (h13 : a13 o (tablesOf cfg o) = true) : placeOK2 cfg o = true :=
  Scc.Cert.PlaceOK.Checks.ok_of (C := checks2 cfg) h1 h2 h3 h4 h5 h6 h7 h8 h9 h11
    (by show (a12code' o && a12ph' o _) && a13 o _ = true; simp [h12c, h12p, h13])

/-- **`placeOK2At` from its components** at the layout `Λ`. -/
theorem placeOK2At_of {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Out}
    (h1 : a1 o ⟨Λ⟩ = true) (h2 : a2 o ⟨Λ⟩ = true) (h3 : a3 o ⟨Λ⟩ = true) (h4 : a4 cfg o ⟨Λ⟩ = true)
    (h5 : a5 o ⟨Λ⟩ = true) (h6 : a6 o ⟨Λ⟩ = true) (h7 : a7 o ⟨Λ⟩ = true) (h8 : a8 o ⟨Λ⟩ = true)
    (h9 : a9 o ⟨Λ⟩ = true) (h11 : a11' o ⟨Λ⟩ = true) (h12c : a12code' o = true)
    (h12p : a12ph' o ⟨Λ⟩ = true) (h13 : a13 o ⟨Λ⟩ = true) : placeOK2At cfg Λ o = true :=
  Scc.Cert.PlaceOK.Checks.ok_of (C := checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h1 h2 h3 h4 h5 h6 h7 h8 h9 h11
    (by show (a12code' o && a12ph' o _) && a13 o _ = true; simp [h12c, h12p, h13])

end Scc.Cert.Spawn.X64
