import Scc.Lower.Raw
import Scc.Emit.A64
import Scc.Lower.SpecA64
import Scc.Cert.MapsCheckA64
import Scc.Test.Src

/-!
# Tests of the `--host raw` emission, AArch64 (`Scc.Emit.A64.kabiItems`)

On `hello1.w` and `hello.w`, the text of the raw program
(`Lower.lowerIRHost` with `host := .raw`):

* starts with `scc_text_start`, then the kernel routine trampolines, one per slot of
  `Tcb.kabiSlots` in slot order, between `scc_kabi_start` and `scc_kabi_end`; no `_start`, and no
  system call instruction anywhere;
* re-parses with Kraken's parser (`roundTrips`);
* has the Linux text of every function the raw lowering leaves unchanged (all of `hello1.w`'s
  user functions, and `hello.w`'s but the spawning `wc_main`) and of `scc_rt_morestack`;
* passes the tables check (`MapsA64.checkTables`), and its trampolines
  precede every block entry of the tables (`scc_kabi_end` at or before the first);
* an indirect jump (`br`) is classified only between `scc_kabi_start`
  and `scc_kabi_end`: in a function body the tables refuse it.
-/

namespace Scc.Test.RawEmitA64

open Scc.IR

/-- The Linux and the raw IR of a WeakCore source for `arch`. -/
def irs (arch : Arch) (src : String) : Except String (IR.Program × IR.Program) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  let l ← Lower.lowerIRHost { arch } c.prog
  let r ← Lower.lowerIRHost { arch, host := .raw } c.prog
  pure (l.ir, r.ir)

def hello1Src : String := w_src% "Scc/Test/hello1.w"
def helloSrc : String := w_src% "Scc/Test/hello.w"

/-! ## AArch64 -/

namespace A

open Scc.Emit.A64

/-- The IR and the emitted items and safepoints of the Linux and the raw program. -/
def emitted (src : String) :
    Except String ((IR.Program × List Item × List Safepoint) × (IR.Program × List Item × List Safepoint)) := do
  let (l, r) ← irs .arm src
  let (li, lm) ← emitItemsMaps l
  let (ri, rm) ← emitItemsMaps r
  pure ((l, li, lm), (r, ri, rm))

def hello1 := emitted hello1Src
def hello := emitted helloSrc

/-- The text items: up to `scc_text_end`. -/
def textOf (its : List Item) : List Item :=
  its.takeWhile fun | .d (.label l) => l != StackMap.textEndSym | _ => true

/-- The text's items per routine: from each `.type f, %function` line up to the next. -/
def routines (its : List Item) : List (String × List Item) :=
  (textOf its).foldl (fun acc it => match it with
    | .raw s => match Scc.Cert.MapsA64.typeOf? s with
      | some f => acc ++ [(f, [it])]
      | none => match acc.getLast? with
        | some (g, xs) => acc.dropLast ++ [(g, xs ++ [it])]
        | none => acc
    | _ => match acc.getLast? with
      | some (g, xs) => acc.dropLast ++ [(g, xs ++ [it])]
      | none => acc) []

/-- The labels of the text, in order. -/
def labels (its : List Item) : List String :=
  (textOf its).filterMap fun | .d (.label l) => some l | _ => none

/-- See `X.headOk`. -/
def headOk (its : List Item) (first : String) : Bool :=
  (labels its).take (Tcb.kabiSlots.length + 4) ==
    [StackMap.textStartSym, Tcb.kabiStartSym] ++ Tcb.kabiSlots.map (·.1) ++ [Tcb.kabiEndSym, first]

/-- The entry `scc_rt_main` is global (`.globl`), the only function that is. -/
def entryGlobal (its : List Item) : Bool :=
  (its.filterMap fun | .raw s => (if s.startsWith ".globl " then some s else none) | _ => none) ==
    [".globl scc_rt_main", s!".globl {Tcb.kabiStartSym}", s!".globl {Tcb.kabiEndSym}"]

/-- No `_start` and no `svc` in the text. -/
def noStartNoSys (its : List Item) : Bool :=
  !(labels its).contains "_start" &&
    (textOf its).all fun | .d (.instr ⟨_, .SVC _⟩) => false | _ => true

/-- A rendered line with the function index of its local labels dropped (`.L<n>_<f>…` becomes
`.L#_<f>…`): the raw program has fewer functions than the Linux one, so a function's index (and
its local labels' names, not its bytes) differs. -/
def normL (s : String) : String :=
  match s.splitOn ".L" with
  | [] => s
  | h :: t => h ++ String.join (t.map fun p =>
      let cs := p.toList
      let ds := cs.takeWhile Char.isDigit
      if !ds.isEmpty && (cs.drop ds.length).head? == some '_' then
        ".L#" ++ String.ofList (cs.drop ds.length)
      else ".L" ++ p)

#guard normL "\tb.ne .L12_wc_main.b3" == "\tb.ne .L#_wc_main.b3"
#guard normL ".Lscc_x .L3x" == ".Lscc_x .L3x"

/-- See `X.differing`; local label names compared without the function index (`normL`). -/
def differing (l r : List Item) : List String :=
  let lr := routines l
  (routines r).filterMap fun (f, xs) => if Tcb.kabiSlots.any (·.1 == f) then none else
    match lr.lookup f with
    | some ys => if xs.map (normL ·.render) == ys.map (normL ·.render) then none else some f
    | none => none

/-- See `X.kabiFirst`. -/
def kabiFirst (p : IR.Program) (its : List Item) : Bool :=
  match Scc.Cert.MapsA64.itemsOf its, Scc.Cert.MapsA64.computeA64 p its with
  | .ok items, .ok t =>
    match Scc.Cert.Maps.labelAddr items Tcb.kabiEndSym,
        (t.maps.filter (·.pt.kind == .blockEntry)).head? with
    | some e, some m => e ≤ m.pt.addr
    | _, _ => false
  | _, _ => false

/-- The conjuncts of `allOk`, by name (for a failing test). -/
def failing (r : Except String ((IR.Program × List Item × List Safepoint) × (IR.Program × List Item × List Safepoint)))
    (same : List String) : List String :=
  match r with
  | .ok ((_, li, _), (rp, ri, rm)) =>
    [("head", headOk ri "scc_rt_main"), ("nosys", noStartNoSys ri), ("roundTrips", roundTrips ri),
     ("same", same.all (fun f => ((routines ri).lookup f).map (·.map (normL ·.render)) ==
        ((routines li).lookup f).map (·.map (normL ·.render)) && ((routines ri).lookup f).isSome)),
     ("tables", (Scc.Cert.MapsA64.checkTables { arch := .arm, host := .raw } rp ri rm).toOption.isSome),
     ("kabiFirst", kabiFirst rp ri)].filterMap fun (n, b) => if b then none else some n
  | .error e => [e]

/-- See `X.allOk`. -/
def allOk (r : Except String ((IR.Program × List Item × List Safepoint) × (IR.Program × List Item × List Safepoint)))
    (same : List String) : Bool :=
  match r with
  | .ok ((_, li, _), (rp, ri, rm)) =>
    headOk ri "scc_rt_main" && entryGlobal ri && noStartNoSys ri && roundTrips ri &&
      same.all (fun f => ((routines ri).lookup f).map (·.map (normL ·.render)) == ((routines li).lookup f).map (·.map (normL ·.render)) &&
        ((routines ri).lookup f).isSome) &&
      (Scc.Cert.MapsA64.checkTables { arch := .arm, host := .raw } rp ri rm).toOption.isSome &&
      kabiFirst rp ri
  | .error _ => false

end A

-- The first two trampolines (AArch64).
/--
info: scc_text_start:
scc_kabi_start:
scc_rt_alloc:
	mrs x16, tpidr_el0
	ldr x16, [x16, #96]
	ldr x16, [x16]
	br x16
scc_rt_alloc_tcb:
	mrs x16, tpidr_el0
	ldr x16, [x16, #96]
	ldr x16, [x16, #8]
	br x16
-/
#guard_msgs in
#eval match A.hello1 with
  | .ok (_, (_, ri, _)) =>
    let ds := ((A.textOf ri).filter fun (it : Scc.Emit.A64.Item) => match it with | .d _ => true | _ => false).take 12
    match Scc.Emit.A64.render ds with
    | .ok s => IO.print s
    | .error e => IO.println e
  | .error e => IO.println e

/-- info: ["scc_rt_main"] -/
#guard_msgs in
#eval match A.hello1 with
  | .ok ((_, li, _), (_, ri, _)) => A.differing li ri
  | .error e => [e]
/-- info: ["scc_rt_main", "scc_rt_thr_worker", "wc_main"] -/
#guard_msgs in
#eval match A.hello with
  | .ok ((_, li, _), (_, ri, _)) => A.differing li ri
  | .error e => [e]

-- The spawn's fence (the lowering's, `Lower.Raw.rawInsts`): `wc_main` has exactly one full fence
-- (`dmb ish`; the `dmb ishst` is the `publish`'s), and every instruction between it and
-- `bl scc_rt_spawn` is one of the call's argument moves: a load of a frame slot or an immediate
-- into `x0`–`x9`, or a store of `x9` to an outgoing argument word (`[sp]`, `[sp, #8·j]` for the
-- call's stack words). The entry's address is taken before the fence. Anything else fails.
namespace A
/-- The outgoing argument words of a call with `n` argument words: its stack words, from `[sp]`. -/
def outWords (n : Nat) : List String :=
  (List.range (n - 8)).map fun j => if j == 0 then "\tstr x9, [sp]" else s!"\tstr x9, [sp, #{8 * j}]"
/-- Whether line `l` is one of the argument moves of a spawn call with `n` argument words. -/
def argMove (n : Nat) (l : String) : Bool :=
  ((List.range 10).any fun k =>
    (l.startsWith s!"\tldr x{k}, [sp" && l.endsWith "]") ||
    l.startsWith s!"\tmovz x{k}, #" || l.startsWith s!"\tmovk x{k}, #") ||
  (outWords n).contains l
/-- The number of argument words of hello's spawn call (raw IR). -/
def spawnArgs : Nat :=
  match hello with
  | .ok (_, (rp, _, _)) =>
    (rp.funcs.flatMap fun f => f.blocks.flatMap fun b => b.insts.filterMap fun
      | .call _ g as => if g == IR.Tcb.spawnSym then some as.length else none
      | _ => none).headD 0
  | .error _ => 0
/-- The number of full fences of `ls`, the lines between the first and `bl scc_rt_spawn` that
are not argument moves, and whether the call follows. -/
def fenceGap (ls : List String) : Nat × List String × Bool :=
  let after := (ls.dropWhile (· != "\tdmb ish")).drop 1
  let gap := after.takeWhile (· != "\tbl scc_rt_spawn")
  ((ls.filter (· == "\tdmb ish")).length, gap.filter (!argMove spawnArgs ·), gap.length < after.length)
/-- The instruction lines of the raw `wc_main` of hello. -/
def mainLines : List String :=
  match hello with
  | .ok (_, (_, ri, _)) =>
    ((((routines ri).lookup "wc_main").getD []).filter fun (it : Scc.Emit.A64.Item) =>
      match it with | .d _ => true | _ => false).filterMap fun it => match Scc.Emit.A64.render [it] with
        | .ok t => if t.endsWith ":\n" then none else some (String.ofList (t.toList.filter (· != '\n')))
        | .error _ => none
  | .error e => [e]
end A

/-- info: (1, [], true) -/
#guard_msgs in
#eval A.fenceGap A.mainLines
-- hello's spawn call has 9 argument words: one stack word, `[sp]`.
#guard A.spawnArgs == 9
-- Any other instruction between the fence and the call fails: a store through a pointer, the
-- entry's address, or a store to a frame slot.
#guard ["\tstr x9, [x10]", "\tadrp x9, scc_rt_thr_worker", "\tadd x9, x9, :lo12:scc_rt_thr_worker",
    "\tstr x9, [sp, #88]"].all
  fun bad => (A.fenceGap (A.mainLines.flatMap fun l =>
    if l == "\tdmb ish" then [l, bad] else [l])).2.1 == [bad]

-- `--host raw` refuses a text with a block entry before `scc_kabi_end`
-- (`Scc.Emit.A64.kabiFirst`, checked by `Lower.A64.Emitted.listing`, so on every raw compile).
namespace A
/-- `its` with a function's block label right after `scc_kabi_start`. -/
def earlyBlock (its : List Scc.Emit.A64.Item) : List Scc.Emit.A64.Item :=
  its.flatMap fun it => match it with
    | .d (.label l) => if l == IR.Tcb.kabiStartSym then [it, .d (.label ".L0_wc_main.0_entry")] else [it]
    | _ => [it]
/-- The raw `Emitted` of hello1. -/
def hello1E : Except String Lower.A64.Emitted := do
  let c ← match Frontend.run hello1Src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  Lower.A64.emitAll (← Lower.lowerIRHost { arch := .arm, host := .raw } c.prog)
end A

#guard match A.hello1 with
  | .ok (_, (_, ri, _)) => (Scc.Emit.A64.kabiFirst ri).toOption.isSome
  | .error _ => false
/-- info: "--host raw: label .L0_wc_main.0_entry precedes scc_kabi_end" -/
#guard_msgs in
#eval match A.hello1 with
  | .ok (_, (_, ri, _)) => match Scc.Emit.A64.kabiFirst (A.earlyBlock ri) with
    | .ok _ => "accepted" | .error e => e
  | .error e => e
-- Without `scc_kabi_end` at all: refused.
#guard match A.hello1 with
  | .ok (_, (_, ri, _)) => (Scc.Emit.A64.kabiFirst (ri.filter fun it => match it with
      | .d (.label l) => l != IR.Tcb.kabiEndSym | _ => true)).toOption.isNone
  | .error _ => false
-- The listing: the raw program's is printed; with the early block label it is refused.
#guard match A.hello1E with
  | .ok e => e.listing.toOption.isSome && ({ e with items := A.earlyBlock e.items }).listing.toOption.isNone
  | .error _ => false

#guard A.allOk A.hello1 ["wc_rodata", "wc_main", IR.StackMap.morestackSym]
#guard A.allOk A.hello ["wc_rodata", "wc_worker", "wc_waitLoop", IR.StackMap.morestackSym]

-- `br x16` is classified only in `[scc_kabi_start, scc_kabi_end)`: the same branch right after
-- `scc_rt_main`'s symbol leaves the text unclassified.
open Scc.Emit.A64 in
#guard match A.hello1 with
  | .ok (_, (_, ri, _)) =>
    let ins := ri.flatMap fun it => match it with
      | .d (.label "scc_rt_main") => [it, tailReg .X16]
      | _ => [it]
    ins.length == ri.length + 1 &&
      (Scc.Cert.MapsA64.itemsOf ri).toOption.isSome &&
      (Scc.Cert.MapsA64.itemsOf ins).toOption.isNone
  | .error _ => false

end Scc.Test.RawEmitA64
