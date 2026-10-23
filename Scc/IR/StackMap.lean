import Scc.IR.Core

/-!
# Growable stacks: frame records, safepoints and stack maps

This file fixes how a thread's stack moves when it grows, and the stack-map
format that makes the move precise.  Like the rest of the IR it is not
trusted: the certificates will check the emitted maps against the
emitted code.

## Frame records

Both emitters keep a chain of **frame records**: a frame record is two
64-bit words `[fp] = ` the caller's frame-record address (the saved frame
pointer) and `[fp + 8] = ` a return address into the caller.  x64: `%rbp`
after `push %rbp; mov %rsp, %rbp`.  AArch64: `x29`, pointing at the saved
`x29`/`x30` pair at the top of the frame.  The chain of a thread ends with a
saved frame pointer of 0 (the thread entry and the start-up stack switch zero
the frame pointer before their call).  A frame record's saved frame pointer
is always a stack address and is always rewritten when the stack moves.
Return addresses point into code and are never rewritten.

## Safepoints

A **safepoint** is a place where the stack may move:

* every `Inst.call` (the stack moves while the callee runs); the safepoint's
  address is the call's return address;
* the prologue stack check of a function with `Func.checkStack`: when the
  check fails, a stub saves the argument registers in a fixed save area of
  the frame, builds the function's frame record, and calls the trampoline
  `morestackSym`; the safepoint's address is that call's return address.

At a safepoint every IR register lives in its frame slot (both emitters
spill every register), and no machine register holds a stack address except
the stack and frame pointers, which the trampoline restores from the moved
frame records.  So the frame records plus the slots and save-area words the
maps designate are all the stack addresses of the thread.

## The move

The trampoline (`morestackSym`, written by the emitter) builds its own frame
record at `fp` and calls `Growth.grow(fp, need)`, which takes a new range of
at least twice the size, copies the old `[fp, stackTop)` to the top of the
new range (`delta = newTop - oldTop`, a multiple of 16), and walks the chain
from `fp`: for each frame record `p` whose saved frame pointer `s` lies in the
old range, it stores `s + delta` at `p + delta`, looks up the return address
`[p + 8]` in the table, and for each offset `o` of the entry's stack list
rewrites the word at `s + o` (read in the old copy) to `w + delta` in the new
copy, if `w` lies in the old range.  The walk stops at the first saved frame
pointer outside the old range (0 at the thread's entry).  The trampoline then
adds `delta` to its frame pointer, moves the stack pointer onto the new
range, calls `Growth.release` on the old range, restores the moved frame
record and returns to the stub, which reloads the argument registers from
the moved save area and repeats the check.

## Table format (`tableSym`, read-only data, 8-byte aligned, 64-bit words)

```
tableSym:  N                                 -- number of entries
           N entries of 4 words, sorted by return address (ascending):
             ret, nStack, nHeap, first
           the offsets: one array of words, shared by all entries
```

Entry `e` describes the frame that its return address `ret` returns into:
its offsets are words `first, …, first + nStack - 1` (the slots holding stack
addresses) and `first + nStack, …, first + nStack + nHeap - 1` (the slots
holding heap references) of the offsets array, each a signed byte offset
from that frame's frame-record address.  The emitters write the safepoints of
all functions in code order, so the entries are sorted and the grow routine
can search them by bisection.  Every safepoint has an entry (possibly with
empty lists).

**Which slots are listed.**  At a call: the registers of `Func.stackRegs`
(stack list) and `Func.heapRegs` (heap list) that are live after the call,
other than the call's results (their slots are written only when the call
returns), plus every register whose address is taken (`Inst.slotAddr`),
which may be read through a pointer at any time.  At a prologue check: the
parameters of those kinds that are live on entry, at their save-area words
(register parameters) or in place in the caller's outgoing area (stack
parameters, `16 + 8·j` above the frame record; see `IR.Core`'s calling
convention).  No other map lists outgoing or incoming argument words: the
callee copies its stack arguments into its own slots in the prologue, right
after the check, and they are dead from then on.  They lie above the callee's
frame record and below the caller's slots, so the move copies them raw with
the rest of `[fp, stackTop)` and never takes them for frame-record words.
The grow routine also checks that a listed word lies in the old stack range
before it rewrites it, so a listed slot whose register was never written on
the path taken is harmless.

**Escape.**  The move rewrites only what the frame records and the maps
designate, so a stack address anywhere else (another thread, the heap, a
register of another kind) would dangle.  `check` enforces the rules of the
IR's "Stack addresses" section.
-/

namespace Scc.IR.StackMap

/-- The symbol of the stack-map table (defined by the emitter). -/
def tableSym : Sym := "scc_stackmap"

/-- The symbol of the emitter's trampoline between a failed prologue check
and `Growth.grow`. -/
def morestackSym : Sym := "scc_rt_morestack"

/-- Bytes of one table entry. -/
def entryBytes : Nat := 32

/-- The registers an operand reads. -/
def opRegs : Operand → List Reg
  | .reg r => [r]
  | .imm _ => []

/-- The registers an instruction reads (`slotAddr` reads none: its source
register's slot is handled as address-taken). -/
def instUses : Inst → List Reg
  | .mov _ s => opRegs s
  | .bin _ _ a b | .setc _ _ a b | .addChk _ a b | .subSat _ a b => opRegs a ++ opRegs b
  | .un _ _ a | .ext _ _ _ a => opRegs a
  | .select _ _ a b t f => opRegs a ++ opRegs b ++ opRegs t ++ opRegs f
  | .la _ _ | .getTp _ | .fence _ | .comment _ | .slotAddr _ _ => []
  | .load _ _ _ a => [a.base]
  | .store _ _ a v | .rmw _ _ a v => a.base :: opRegs v
  | .call _ _ args | .syscall _ _ args _ | .site _ args => args.flatMap opRegs
  | .clone _ s t _ a => opRegs s ++ opRegs t ++ opRegs a

/-- The registers an instruction writes. -/
def instDefs : Inst → List Reg
  | .mov d _ | .bin _ d _ _ | .un _ d _ | .ext _ _ d _ | .setc _ d _ _
  | .select _ d _ _ _ _ | .addChk d _ _ | .subSat d _ _ | .la d _ | .getTp d
  | .load _ _ d _ | .rmw _ d _ _ | .syscall d _ _ _ | .clone d _ _ _ _ | .slotAddr d _ => [d]
  | .call ds _ _ => ds
  | .store .. | .fence _ | .comment _ | .site .. => []

/-- The registers a terminator reads. -/
def termUses : Term → List Reg
  | .ret vs => vs.flatMap opRegs
  | .jmp _ | .unreachable => []
  | .br _ a b _ _ => opRegs a ++ opRegs b
  | .tail _ args => args.flatMap opRegs
  | .switchTo s t _ a => opRegs s ++ opRegs t ++ opRegs a

/-- The successor labels of a terminator. -/
def termSuccs : Term → List Label
  | .jmp l => [l]
  | .br _ _ _ t f => [t, f]
  | _ => []

/-- `a ∪ b` on lists without duplicates. -/
def union (a b : List Reg) : List Reg := b.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) a

/-- Live registers before an instruction, given those live after it. -/
def liveBefore (i : Inst) (after : List Reg) : List Reg :=
  union ((instUses i).eraseDups) (after.filter fun r => !((instDefs i).contains r))

/-- Live registers at the start of a block, given those live at its end. -/
def blockLiveIn (b : Block) (out : List Reg) : List Reg :=
  b.insts.foldr liveBefore (union (termUses b.term).eraseDups out)

/-- Live-in sets of all blocks (by label), by iteration to the fixpoint. -/
def liveIns (f : Func) : List (Label × List Reg) :=
  let find (m : List (Label × List Reg)) (l : Label) : List Reg :=
    (m.find? (·.1 == l)).map (·.2) |>.getD []
  let step (m : List (Label × List Reg)) : List (Label × List Reg) :=
    f.blocks.map fun b =>
      (b.label, blockLiveIn b ((termSuccs b.term).foldl (fun acc l => union acc (find m l)) []))
  let rec go : Nat → List (Label × List Reg) → List (Label × List Reg)
    | 0, m => m
    | n + 1, m =>
      let m' := step m
      if m'.map (fun (l, rs) => (l, rs.length)) == m.map (fun (l, rs) => (l, rs.length)) then m
      else go n m'
  -- Live sets only grow, and are bounded by the registers of the function.
  let bound := f.blocks.length * (f.blocks.foldl (fun n b => n + b.insts.length + 2) 2) + 2
  go bound (f.blocks.map fun b => (b.label, []))

/-- The registers whose slot address is taken in a function. -/
def addressTaken (f : Func) : List Reg :=
  (f.blocks.flatMap fun b => b.insts.filterMap fun | .slotAddr _ s => some s | _ => none).eraseDups

/-- The registers a safepoint's map lists: stack addresses and heap
references, in the order of `Func.stackRegs` / `Func.heapRegs`. -/
structure Entry where
  stack : List Reg
  heap : List Reg
  deriving Repr, BEq, Inhabited

/-- The entry of a safepoint whose live registers (other than results) are
`live`. -/
def entryOf (f : Func) (live : List Reg) : Entry :=
  let taken := addressTaken f
  { stack := f.stackRegs.filter fun r => live.contains r || taken.contains r,
    heap := f.heapRegs.filter fun r => live.contains r || taken.contains r }

/-- For each block (in order) and each of its instructions (in order), the
registers live after the instruction other than its results, if it is a
call (`none` otherwise): the registers the call's safepoint must preserve. -/
def callLives (f : Func) : List (List (Option (List Reg))) :=
  let ins := liveIns f
  let find (l : Label) : List Reg := (ins.find? (·.1 == l)).map (·.2) |>.getD []
  f.blocks.map fun b =>
    let out := (termSuccs b.term).foldl (fun acc l => union acc (find l)) []
    let atEnd := union (termUses b.term).eraseDups out
    -- Walk backwards, recording the live set after each instruction.
    let (_, lives) := b.insts.foldr (fun i (after, acc) =>
      let m := match i with
        | .call ds _ _ => some (after.filter fun r => !ds.contains r)
        | _ => none
      (liveBefore i after, m :: acc)) (atEnd, [])
    lives

/-- For each block (in order) and each of its instructions (in order), the
map of the instruction if it is a call (`none` otherwise). -/
def callMaps (f : Func) : List (List (Option Entry)) :=
  (callLives f).map (·.map (·.map (entryOf f)))

/-- The parameters live on entry: those the prologue check's safepoint must
preserve. -/
def entryLive (f : Func) : List Reg :=
  let live : List Reg := match f.blocks with
    | b :: _ => ((liveIns f).find? (·.1 == b.label)).map (·.2) |>.getD []
    | [] => []
  live.filter f.params.contains

/-- The map of a function's prologue check: its parameters of a listed kind
that are live on entry (to be found at their argument save-area words, or
for stack parameters at their incoming argument words). -/
def checkMap (f : Func) : Entry :=
  let live := match f.blocks with
    | b :: _ => ((liveIns f).find? (·.1 == b.label)).map (·.2) |>.getD []
    | [] => []
  let e := entryOf f live
  { stack := e.stack.filter f.params.contains, heap := e.heap.filter f.params.contains }

/-! ## Argument areas

A `tail` is a jump: it must run in constant stack whatever its argument
count.  Its stack arguments are written over the current function's own
incoming area (the words its caller put above its frame record), so that
area must be big enough for every tail call the function makes, and for the
tail calls of every function it tail-calls in turn: after the jump, the
callee owns the same area.  So the functions connected by `tail` edges (in
either direction) share one **argument area**, sized to the most stack words
any of them takes as parameters or passes in a tail call, and every `call`
of one of them reserves that much outgoing area, however few arguments it
passes.  A function in no tail edge has the area of its own parameters, so
programs without wide tail calls are laid out as before.  The emitters
compute the areas per program for their register count (`argAreas`). -/

/-- Stack words of `n` arguments on a target with `k` argument registers. -/
def stackWords (k n : Nat) : Nat := n - k

/-- The tail calls of a function: callee and argument count. -/
def tailCalls (f : Func) : List (Sym × Nat) :=
  f.blocks.filterMap fun b => match b.term with
    | .tail g args => some (g, args.length)
    | _ => none

/-- The argument area (in words) of every function of `p` on a target with
`k` argument registers: the most stack words of the parameters and tail
calls of the functions in its `tail`-connected component. -/
def argAreas (p : Program) (k : Nat) : List (Sym × Nat) :=
  let own (f : Func) : Nat :=
    (tailCalls f).foldl (fun m (_, n) => max m (stackWords k n)) (stackWords k f.params.length)
  let edges := p.funcs.flatMap fun f => (tailCalls f).filterMap fun (g, _) =>
    if p.funcs.any (·.name == g) then some (f.name, g) else none
  let get (m : List (Sym × Nat)) (s : Sym) : Nat := ((m.find? (·.1 == s)).map (·.2)).getD 0
  let step (m : List (Sym × Nat)) : List (Sym × Nat) := edges.foldl (fun m (a, b) =>
    let v := max (get m a) (get m b)
    m.map fun (s, x) => if s == a || s == b then (s, max x v) else (s, x)) m
  -- Each pass carries the maximum across every edge once, so as many passes
  -- as functions reach every member of a component.
  (List.range (p.funcs.length + 1)).foldl (fun m _ => step m) (p.funcs.map fun f => (f.name, own f))

/-- The outgoing words a call of `g` with `n` arguments reserves: the
callee's argument area if it is in the program (`areas`), else its stack
words. -/
def callWords (areas : List (Sym × Nat)) (k : Nat) (g : Sym) (n : Nat) : Nat :=
  max (stackWords k n) (((areas.find? (·.1 == g)).map (·.2)).getD 0)

/-! ## The escape check -/

/-- `StackMap.check` on one function; `callee` gives a called function's
parameters and stack registers, if it is in the program. -/
def checkFunc (callee : Sym → Option (List Reg × List Reg)) (f : Func) : Except String Unit := do
  let S := f.stackRegs
  let isS (o : Operand) : Bool := match o with | .reg r => S.contains r | .imm _ => false
  let err {α : Type} (what : String) : Except String α :=
    throw s!"{f.name}: a stack address {what}"
  for r in S do
    if f.heapRegs.contains r then throw s!"{f.name}: register {r} is both a stack and a heap register"
  let flowsTo (d : Reg) (srcs : List Operand) : Except String Unit :=
    if srcs.any isS && !S.contains d then err s!"flows into register {d}, which is not in stackRegs"
    else pure ()
  for b in f.blocks do
    for i in b.insts do
      match i with
      | .mov d s => flowsTo d [s]
      | .bin _ d a c | .addChk d a c | .subSat d a c => flowsTo d [a, c]
      | .un _ d a | .ext _ _ d a => flowsTo d [a]
      | .select _ d _ _ t e => flowsTo d [t, e]
      | .setc .. | .la .. | .getTp _ | .load .. | .fence _ | .comment _ => pure ()
      | .store _ _ _ v => if isS v then err "is stored to memory" else pure ()
      | .rmw _ _ _ v => if isS v then err "is written by a read-modify-write" else pure ()
      | .slotAddr d s =>
          if !S.contains d then throw s!"{f.name}: slotAddr into {d}, which is not in stackRegs"
          else if S.contains s then throw s!"{f.name}: slotAddr of {s}, a stack register"
          else pure ()
      | .call _ g args =>
          for (a, k) in args.zipIdx do
            if isS a then
              match callee g with
              | some (ps, gs) =>
                  match ps[k]? with
                  | some p => if !gs.contains p then
                      err s!"is passed to {g} in parameter {p}, which is not in its stackRegs"
                  | none => err s!"is passed to {g} beyond its parameters"
              | none => err s!"is passed to {g}, which is not in the program"
      | .syscall _ _ args _ => if args.any isS then err "is passed to a system call" else pure ()
      | .clone _ s t _ a => if [s, t, a].any isS then err "is passed to clone" else pure ()
      | .site _ args => if args.any isS then err "is passed to a site" else pure ()
    match b.term with
    | .ret vs => if vs.any isS then err "is returned" else pure ()
    | .tail _ args => if args.any isS then err "is passed in a tail call" else pure ()
    | .switchTo s t _ a => if [s, t, a].any isS then err "is passed to switchTo" else pure ()
    | .jmp _ | .br .. | .unreachable => pure ()

/-- The no-escape rules of the IR's "Stack addresses" section, on a whole
program.  Both emitters run it first. -/
def check (p : Program) : Except String Unit :=
  let callee (g : Sym) : Option (List Reg × List Reg) :=
    (p.funcs.find? (·.name == g)).map fun h => (h.params, h.stackRegs)
  p.funcs.forM (checkFunc callee)

end Scc.IR.StackMap
