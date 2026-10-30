import Scc.Cert.A12StageA64

/-!
# `placeOK2` for spawning programs (AArch64)

The twin of `Scc/Cert/SpawnX64.lean`: `placeOK` (`Scc/Cert/PlaceOKA64.lean`) with
three of its checks extended for a program whose `main` takes its thread id
and spawns (`wake.w`, `hello.w`), the frozen checks untouched.

* **A11'** (`a11'`): with a `.bare` tail and an IR whose `scc_rt_main`
  calls `wc_main(tcb)` (`isTidMain`), the runtime's code with
  `scc_rt_main`'s body loading the TCB from `[sp]` before the `bl`
  (`mainTGrps`, `rtCodeOkT`) and its phase facts (`mainPhTabT`); otherwise
  `a11`. One shape, one table: the dispatch is strict.
* **A12'** (`a12'`): `a12` with two relaxations.
  - The stack need admits calls of the spawn path's runtime routines
    (`rtDepth'`: `scc_rt_park`, `scc_rt_unpark`, `scc_rt_thread_reserve`,
    `scc_rt_alloc_tcb`, `scc_rt_thread_init`, each with its depth).
  - A `bl` of one of the reentrant runtime routines (`reent`) may enter a
    callee of another phase index if it keeps the stack lock's bit
    (`runPhB2`).
* **A13** (`a13`), for a program with a `clone`: the thread counter
  `scc_rt_nthreads` a decided word clear of the runtime's words, the second
  stack in the pool, the second TCB's allocation (up to `maxSpawnArgs`
  arguments) in clear words, and the code and phase facts of
  `scc_rt_thread_reserve`, `scc_rt_park` and `scc_rt_unpark`.

This file holds the check's definitions and `placeOK2_of` (a certificate's
combination of its decisions). The lemmas relating `placeOK2` to `placeOK`
are in `Spike/Lib/SpawnA64.lean`: `a11'_of_a11`, `a12'_of_a12` and
`a13_of_noClone` give `placeOK2` from `placeOK` on a program that neither
takes its thread id nor spawns (`placeOK2_of_placeOK`), so that `hello1.w`
and `ret0.w` re-certify without new decisions.
-/

namespace Scc.Cert.Spawn.A64

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Flow (classify AI)
open Spike.Lib.A64Consumer (aiTgts blkPh)
open Spike.Lib.LowerA64 (proL ovfBlk stkHead proPhOk proLabs blkLabs raL)
open Scc.Emit.A64 (FnCtx directives argRegs)
open Scc.Cert.Rt.A64 (codeT phTabBy sitesBy inRs RGrp PhFact rtIn)
open Scc.Cert.Code1A64 (blockItems spills hasAddChk callees rtDepth rtOk needOk1)
open Scc.Cert.Ph1A64 (runs runPhB runPh blocksPh fnPhF)

/-! ## A11': `scc_rt_main` passing the TCB -/

section Tid

open Spike.Lib.A64.Rt
open Spike.Lib.A64.Flow

/-- **`scc_rt_main`'s groups when `main` takes its thread id**: the bare
shape's (`mainUGrps`) but the body's entry, `ldr x0, [sp]` (the TCB) then
`bl fn`, the return point two instructions on. -/
def mainTGrps (mc : MainCode) : List RGrp := [
  ⟨"scc_rt_main", [], some (0, mc.sc)⟩,
  ⟨mc.sc, [(0, chkHead mc.Z), (2, [ldrDir .X10 .X10 8]), (3, chkBr mc.grow), (5, frameSet mc.Z [(.X0, 0)])],
    some (10, mc.e0)⟩,
  ⟨mc.e0, [(0, [spLdr .X0 0, blD mc.fn])], some (2, mc.sp0)⟩,
  ⟨mc.sp0, [(0, exitTail mc.k), (3, [svcDir])], none⟩]

/-- **The runtime's code when `main` takes its thread id**, in program
order (`rtCodeTab` with `mainTGrps`). -/
def rtCodeTabT (mc : MainCode) : List RGrp := startGrps ++ mainTGrps mc ++ tcbGrps ++ tiGrps ++ takeGrps

/-- The runtime's code when `main` takes its thread id, in one pass. -/
def rtCodeOkT (prog : List Directive) (mc : MainCode) : Bool := rtIn prog (rtCodeTabT mc)

/-- **`scc_rt_main`'s phase facts when `main` takes its thread id**
(`mainPhTab` with the body's block of `mainTGrps`). -/
def mainPhTabT (mc : MainCode) : List PhFact :=
  [.blk mc.sc 0 (chkHead mc.Z) none none, .step mc.sc 2, .blk mc.sc 3 (chkBr mc.grow) none none,
    .blk mc.sc 5 (frameSet mc.Z [(.X0, 0)]) none none, .blk mc.e0 0 [spLdr .X0 0, blD mc.fn] none none,
    .blk mc.sp0 0 (exitTail mc.k) none none, .step mc.sp0 3]

/-- **A11 at the thread-id shape**: the code (`rtCodeOkT`) and phase facts
(`mainPhTabT`) at today's bare frame (`bareMC`). -/
def tidOk (prog : List Directive) (lo : Nat) (Λ : Scc.Sem.Layout) : Bool :=
  rtCodeOkT prog bareMC && Scc.Cert.Rt.A64.rtPhOk lo prog Λ (mainPhTabT bareMC)

/-- The body's block at the thread-id shape is the parser's form of the
listing's. -/
example : [spLdr .X0 0, blD "wc_main"] = parseAArch64("ldr x0, [sp]
bl wc_main") := by decide

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
depth**, on the spawn path: `rtDepth`'s, then `scc_rt_park`'s (its frame),
`scc_rt_unpark`'s (its frame), `scc_rt_thread_reserve`'s (its frame and
`scc_rt_abort`'s), `scc_rt_alloc_tcb`'s (its frame and `scc_rt_abort`'s)
and `scc_rt_thread_init`'s (its frame, then `scc_rt_stack_take`'s and
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
def needOk1' (tbl : List Scc.Cert.NeedA64.Row) (name : String) (frame : Nat) (f : Scc.IR.Func) : Bool :=
  match Scc.Cert.NeedA64.row? tbl name with
  | some (_, fr, nf) =>
    fr == frame && decide (frame ≤ nf) &&
    (callees f).1.all (fun g => match Scc.Cert.NeedA64.row? tbl g with
      | some (_, _, ng) => decide (frame + ng ≤ nf)
      | none => rtOk' g) &&
    (callees f).2.all (fun g => match Scc.Cert.NeedA64.row? tbl g with
      | some (_, _, ng) => decide (ng ≤ nf)
      | none => rtOk' g)
  | none => false

/-- `fnOk1K` over `needOk1'`. -/
def fnOk1K' (T : List (Nat × Nat × List Directive)) (tbl : List Scc.Cert.NeedA64.Row) (c : FnCtx)
    (f : Scc.IR.Func) : Bool :=
  match f.blocks, spills c f.params with
  | b0 :: _, some ps =>
    (match c.blockLabel b0.label with
     | .ok entry => prologueInK T f.name (c.local "stack_check") entry (Int64.ofInt c.frame)
         (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c) ps
     | .error _ => false) &&
    decide (c.frame ≤ 4095) && decide (c.frame % 16 = 0) &&
    blocksOkK T c 0 f.blocks &&
    (!hasAddChk f || chkK T (c.local "abort_overflow") 0 ovfBlk) &&
    needOk1' tbl f.name c.frame f &&
    chkK T (proL c) 0 (stkHead c)
  | _, _ => false

/-- `fnCode1OkK` over `fnOk1K'`. -/
def fnCode1OkK' (T : List (Nat × Nat × List Directive)) (tbl : List Scc.Cert.NeedA64.Row)
    (ir : Scc.IR.Program) : Bool :=
  let areas := Scc.IR.StackMap.argAreas ir argRegs.length
  ir.funcs.zipIdx.all fun (f, fi) => !f.checkStack || fnOk1K' T tbl (fnCtxK ir.abortFn ir.growth areas fi f) f

/-! ## A12': the phases at a reentrant call -/

/-- **The reentrant runtime routines**: those a user function may call on
the spawn path whose entry is not in the caller's phase (or may not be:
`scc_rt_park`, `scc_rt_unpark`, `scc_rt_thread_reserve` are listed with
the others), none holding the stack lock at its entry. -/
def reent : List String :=
  ["scc_rt_alloc_tcb", "scc_rt_thread_init", "scc_rt_thread_reserve", "scc_rt_park", "scc_rt_unpark"]

/-- The directive is a `bl` of a reentrant runtime routine. -/
def reentCall (d : Directive) : Bool :=
  match classify d with
  | some (.bl L) => reent.contains L
  | _ => false

/-- **`runPhB` with the reentrant calls' rule**: as `runPhB`, but a
target of a `bl` of a reentrant routine (`reentCall`) is in the run's phase
or has the run's stack lock bit `lk`. -/
def runPhB2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (pc ra : Int64)
    (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    okPc (pc + Int64.ofNat (4 * k)).toBitVec.toNat &&
    ph (pc + Int64.ofNat (4 * k)).toBitVec.toNat == ph pc.toBitVec.toNat &&
    match blk[k]? with
    | some d =>
      (match classify d with
       | some a => aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a
       | none => [pc + Int64.ofNat (4 * k) + Int64.ofNat 4]).all fun t =>
        ph t.toBitVec.toNat == ph pc.toBitVec.toNat ||
          (reentCall d && lk t.toBitVec.toNat == lk pc.toBitVec.toNat)
    | none => false

/-- `runPh` over `runPhB2`. -/
def runPh2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (ra : Int64)
    (r : Label × List Directive) : Bool :=
  res r.1 && (blkLabs r.2).all res && runPhB2 okPc ph lk lab (lab r.1) ra r.2

/-- `blocksPh` over `runPh2`. -/
def blocksPh2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (c : FnCtx)
    (ra : Int64) : Nat → List Scc.IR.Block → Bool
  | _, [] => true
  | k, b :: bs =>
    (match c.blockLabel b.label, blockItems c k b with
     | .ok l, .ok code => (runs l (directives code)).all fun r =>
        runPh2 okPc ph lk lab res ra r && ph (lab r.1).toBitVec.toNat == ph ra.toBitVec.toNat
     | _, _ => false) &&
    blocksPh2 okPc ph lk lab res c ra (k + b.insts.length + 1) bs

/-- `fnPhF` over `blocksPh2` (the prologue's and the overflow block's
checks unchanged: neither calls a runtime routine). -/
def fnPhF2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (c : FnCtx)
    (f : Scc.IR.Func) (ra : Int64) : Bool :=
  match spills c f.params with
  | some ps =>
    res f.name && res (c.local "stack_check") &&
    (proLabs (Int64.ofInt c.frame) (proL c) ps).all res &&
    proPhOk okPc ph lab (c.local "stack_check") (Int64.ofInt c.frame) (proL c) ps &&
    blocksPh2 okPc ph lk lab res c ra 0 f.blocks &&
    (!hasAddChk f || (res (c.local "abort_overflow") && (blkLabs ovfBlk).all res &&
      blkPh okPc ph (fun _ => false) lab (lab (c.local "abort_overflow") + Int64.ofNat (4 * 0)) 0 ovfBlk))
  | none => false

/-- `fnPhAll1K` over `fnPhF2`. -/
def fnPhAll1K2 (okPc : Nat → Bool) (ph lk : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  let areas := Scc.IR.StackMap.argAreas ir argRegs.length
  ir.funcs.zipIdx.all fun (f, fi) =>
    !f.checkStack || fnPhF2 okPc ph lk lab res (fnCtxK ir.abortFn ir.growth areas fi f) f ra

/-- **`fnPh1OkK` with the reentrant calls' rule**: the stack lock's bit
`lk` that of A6's phase table (`inRs P.l`). -/
def fnPh1OkK2 (lo : Nat) (Λ : Scc.Sem.Layout) (prog : Program) (ir : Scc.IR.Program) : Bool :=
  match phTabBy (codeT lo prog), sitesBy (codeT lo prog) Λ with
  | some P, some ss =>
    (codeT lo prog raL).isSome &&
      fnPhAll1K2 (fun pc => !ss.contains pc) P.ph (fun pc => (inRs P.l pc).toNat)
        (fun l => Int64.ofNat ((codeT lo prog l).getD 0))
        (fun l => (codeT lo prog l).isSome) ir (Int64.ofNat ((codeT lo prog raL).getD 0) + 4)
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
  | some ir => fnPh1OkK2 t.Λ.code.lo t.Λ o.prog ir
  | none => false

/-- **A12'**: its code part and its phase part, decided in two
declarations by a certificate. -/
def a12' (o : Out) (t : Tables) : Bool := a12code' o && a12ph' o t

/-! ## A13: the second thread -/

section A13

open Scc.Cert.Rt.A64 (rtA symLab rtWords wordOk WordSep)
open Spike.Lib.A64.Rt (labPair)

/-- The epilogue of a frame of 48 bytes, `x29`/`x30` at 32/40. -/
def epi48 : List Directive := parseAArch64("ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

/-- **`scc_rt_thread_reserve`'s code** (`Runtime.threadReserveF`): the
prologue, the counter's address, the `ldaddal`, the bound's check against
`maxThreads`, the abort and the return. -/
def reserveGrps : List RGrp := [
  ⟨"scc_rt_thread_reserve", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32"))], some (4, ".L4_scc_rt_thread_reserve.0_entry")⟩,
  ⟨".L4_scc_rt_thread_reserve.0_entry", labPair 0 "scc_rt_nthreads" ++ [(2, parseAArch64("str x9, [sp]
movz x9, #1
ldr x10, [sp]")),
    (5, parseAArch64("ldaddal x9, x11, [x10]")),
    (6, parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #1023
subs xzr, x9, x10
b.hi .L4_scc_rt_thread_reserve.1_full")),
    (15, parseAArch64("b .L4_scc_rt_thread_reserve.2_ok"))], none⟩,
  ⟨".L4_scc_rt_thread_reserve.1_full", [(0, parseAArch64("movz x0, #5
bl scc_rt_abort"))], none⟩,
  ⟨".L4_scc_rt_thread_reserve.2_ok", [(0, parseAArch64("ldr x0, [sp, #16]") ++ epi48)], none⟩]

/-- `swpal x9, x11, [x10]` (the park word's swap). -/
def swpPark : List Directive := parseAArch64("swpal x9, x11, [x10]")

/-- The `futex` call's argument block of `scc_rt_park` (`op = 128`, wait,
`val = 0`): the park word's address, `op`, `val`, the system call's number. -/
def futexWait : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #16
add x9, x9, x10
str x9, [sp, #16]
ldr x0, [sp, #16]
movz x1, #128
movz x2, #0
movz x3, #0
movz x4, #0
movz x5, #0
movz x8, #98")

/-- The `futex` call's argument block of `scc_rt_unpark` (`op = 129`, wake
one, `val = 1`). -/
def futexWake : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #16
add x9, x9, x10
str x9, [sp, #16]
ldr x0, [sp, #16]
movz x1, #129
movz x2, #1
movz x3, #0
movz x4, #0
movz x5, #0
movz x8, #98")

/-- **`scc_rt_park`'s code** (`Runtime.parkF`): the thread pointer, the
swap of the park word with `0`, the `futex` wait unless it was `1`, the
second swap. -/
def parkGrps : List RGrp := [
  ⟨"scc_rt_park", [(0, parseAArch64("sub sp, sp, #64
str x29, [sp, #48]
str x30, [sp, #56]
add x29, sp, #48"))], some (4, ".L10_scc_rt_park.0_entry")⟩,
  ⟨".L10_scc_rt_park.0_entry", [(0, parseAArch64("mrs x9, tpidr_el0
str x9, [sp]
movz x9, #0
ldr x10, [sp]
add x10, x10, #16")),
    (5, swpPark),
    (6, parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
subs xzr, x9, x10
b.eq .L10_scc_rt_park.2_done")),
    (11, parseAArch64("b .L10_scc_rt_park.1_wait"))], some (12, ".L10_scc_rt_park.1_wait")⟩,
  ⟨".L10_scc_rt_park.1_wait", [(0, futexWait), (11, [Spike.Lib.A64.Flow.svcDir]),
    (12, parseAArch64("str x0, [sp, #24]
movz x9, #0
ldr x10, [sp]
add x10, x10, #16")),
    (16, swpPark),
    (17, parseAArch64("str x11, [sp, #32]
ldr x29, [sp, #48]
ldr x30, [sp, #56]
add sp, sp, #64
ret"))], some (22, ".L10_scc_rt_park.2_done")⟩,
  ⟨".L10_scc_rt_park.2_done", [(0, parseAArch64("ldr x29, [sp, #48]
ldr x30, [sp, #56]
add sp, sp, #64
ret"))], none⟩]

/-- **`scc_rt_unpark`'s code** (`Runtime.unparkF`): the swap of the
target's park word with `1`, the `futex` wake if it was `0`. -/
def unparkGrps : List RGrp := [
  ⟨"scc_rt_unpark", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]"))], some (5, ".L11_scc_rt_unpark.0_entry")⟩,
  ⟨".L11_scc_rt_unpark.0_entry", [(0, parseAArch64("movz x9, #1
ldr x10, [sp]
add x10, x10, #16")),
    (3, swpPark),
    (4, parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #0
subs xzr, x9, x10
b.eq .L11_scc_rt_unpark.1_wake")),
    (9, parseAArch64("b .L11_scc_rt_unpark.2_done"))], some (10, ".L11_scc_rt_unpark.1_wake")⟩,
  ⟨".L11_scc_rt_unpark.1_wake", [(0, futexWake), (11, [Spike.Lib.A64.Flow.svcDir]),
    (12, parseAArch64("str x0, [sp, #24]") ++ epi48)], some (17, ".L11_scc_rt_unpark.2_done")⟩,
  ⟨".L11_scc_rt_unpark.2_done", [(0, epi48)], none⟩]

/-- **The spawn path's runtime code**, in program order. -/
def spawnGrps : List RGrp := reserveGrps ++ parkGrps ++ unparkGrps

/-- A representative return point in the user code's phase (`raL`,
`scc_rt_main`'s body): each routine of `spawnGrps` returns to its caller in
the caller's phase. -/
def userRa : Option String := some raL

/-- **The spawn path's phase facts**: each covered block's check (each
`ret` to `userRa`), the single steps (the counter's address, the system
calls, the atomic swaps and adds off the sites with their next pcs in their
phase). -/
def spawnPhTab : List PhFact :=
  let rv := ".L4_scc_rt_thread_reserve.0_entry"
  let pk := ".L10_scc_rt_park.0_entry"
  let pw := ".L10_scc_rt_park.1_wait"
  let ue := ".L11_scc_rt_unpark.0_entry"
  let uw := ".L11_scc_rt_unpark.1_wake"
  let blks : List PhFact := (spawnGrps.flatMap fun g => g.bs.filterMap fun (o, b) =>
    if b.all (fun d => (classify d).isSome) then
      some (.blk g.l o b (if b.any (fun d => match classify d with | some (.ret _) => true | _ => false) then userRa else none) none)
    else none)
  blks ++ [.step rv 0, .step rv 1, .step rv 5, .step pk 5, .step pw 11, .step pw 16, .step ue 3, .step uw 11]

/-- Every block of `spawnGrps` but the single instructions above is
covered: the table checks them all. -/
example : (spawnGrps.flatMap fun g => g.bs.filter fun (_, b) => !b.all (fun d => (classify d).isSome)).length = 8 := by
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
def a13data (Λ : Scc.Sem.Layout) (prog : Program) (secs : Scc.Sem.DataSecs) : Bool :=
  let pinA := rtA Λ prog secs "scc_rt_pinned"
  let ntA := rtA Λ prog secs "scc_rt_nthreads"
  let stacksA := rtA Λ prog secs "scc_rt_stacks"
  let old := rtWords pinA (rtA Λ prog secs "scc_rt_pinned_next") (rtA Λ prog secs "scc_rt_stack_next")
    (rtA Λ prog secs "scc_rt_stack_lock") (rtA Λ prog secs "scc_rt_stack_free_n")
  let new := ntA :: spawnWords pinA
  (symLab Λ.code.lo prog (Scc.Sem.loadSyms Λ secs.rodata) "scc_rt_nthreads").isSome &&
    new.all (wordOk Λ) &&
    new.all (fun a => old.all fun b => decide (WordSep a b)) &&
    new.all (fun a => decide (WordSep a (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf Λ)))) &&
    decide (new.Pairwise WordSep) &&
    decide (stacksA.toNat + 32768 ≤ Λ.stackPool.lo + Λ.stackPool.size)

/-- **A13's code part**: `spawnGrps` in the program, its phase facts. -/
def a13code (lo : Nat) (prog : Program) (Λ : Scc.Sem.Layout) : Bool :=
  rtIn prog spawnGrps && Scc.Cert.Rt.A64.rtPhOk lo prog Λ spawnPhTab

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

/-- **The components of `placeOK2`** on AArch64: `checks` with A11' and
A12' ∧ A13 (A7 is `placeOK`'s: its `scc_rt_print` is the fenced one for
every program, FENCE1). -/
def checks2 (cfg : Scc.Cert.PlaceOK.Config) : Scc.Cert.PlaceOK.Checks Out Tables :=
  { checks cfg with a11 := a11', a12 := fun o t => a12' o t && a13 o t }

/-- **`placeOK2` on AArch64.** -/
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

end Scc.Cert.Spawn.A64
