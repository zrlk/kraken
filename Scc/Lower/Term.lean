import Scc.Frontend
import Scc.Lower.Builder

/-!
# Lowering WeakCore terms to the IR

Each code block `f` becomes the IR function `Names.user f`.  A value of a
WeakCore type is its words in `TermRun`'s order (every variable is bound to a
type, for shape only, and a list of words; products are concatenated;
existential packages and index singletons are erased), except that a
locative is two words, `(base, offset)` (`Scc.Obj`, `Scc/LAYOUT.md`): the
lowering keeps, for every variable, its shape type and one IR operand per
word.  Values: a number is its 64-bit pattern, a `Ptr` (and a `ThreadId`) is
an object's base address, a `Loc` is a base and an offset word, and `null` is
0.

Memory follows the bipartite object layout: an object made by `new` or
`newBuf` has one header word, its scalar words at non-negative offsets from
its base and its trace (reference) words at negative ones; the layout map
`Obj.slots` sends each word of a cell's value to its region and index
(`cellAddrs`).  Stores write the words in the value's order, so the model's
unit order is kept.  An address derived from a base (`cellAddrs`) is used at
once and is never live across a call, so frames and the stack maps only ever
see bases.

Arguments and results are passed flattened, one IR argument per word (at most
`maxArgs`/`maxRets`; argument words past the target's registers go on the
stack, `IR.Core`'s calling convention; every `tail` stays a jump, the
emitters size argument areas so that it fits, `IR.StackMap.argAreas`).  A
spawned block takes at most
`maxSpawnArgs` words.  The provisional externs (`print`, `park`, `unpark`) and
`spawn` call the runtime (`Scc.Lower.Runtime`).

Every register that holds a word of a typed value is recorded by kind
(`markWords`): trace words in `Func.heapRegs`, the stack maps' heap lists,
and scalar words in `Func.scalarRegs`.

`Int` `+` is always a checked addition (`Inst.addChk`, the abort edge);
`Int` `-` is the saturating subtraction,
which is exactly WeakCore's truncated `Nat` subtraction.

This lowering is not verified; the certificates check its output.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower

/-! ## Symbol names -/

namespace Names

/-- A WeakCore name as assembler-symbol characters: letters, digits and `_`
are kept, anything else (`'`, Greek letters) is `_u<hex>_`. -/
def mangle (s : String) : String :=
  String.join (s.toList.map fun c =>
    if (c.isAlphanum && c.toNat < 128) || c == '_' then c.toString
    else s!"_u{String.ofList (Nat.toDigits 16 c.toNat)}_")

/-- The IR function of code block `f`. -/
def user (f : String) : Sym := "wc_" ++ mangle f

def heap : Sym := "scc_rt_heap"
/-- The heap counter: the source units (`Frontend.words` of each object plus
one) allocated so far (`Runtime.allocF`, `Runtime.heapCells`), which is also
the arena's cursor in 16-byte cells. -/
def heapUse : Sym := "scc_rt_heap_use"
/-- The pinned region (TCBs): a separate `.bss` range, so "pinned" is a
property of the address. -/
def pinned : Sym := "scc_rt_pinned"
/-- The pinned region's bump cursor. -/
def pinnedNext : Sym := "scc_rt_pinned_next"
/-- The shared stack pool (only stack contents live there). -/
def stacks : Sym := "scc_rt_stacks"
/-- The pool's bump cursor (bytes of the pool handed out so far). -/
def stackNext : Sym := "scc_rt_stack_next"
/-- The spin lock of the pool's free arrays. -/
def stackLock : Sym := "scc_rt_stack_lock"
/-- The free counts, one word per size class. -/
def stackFreeN : Sym := "scc_rt_stack_free_n"
/-- The free arrays of all size classes, one after the other. -/
def stackFree : Sym := "scc_rt_stack_free"
def stackTake : Sym := "scc_rt_stack_take"
def stackRelease : Sym := "scc_rt_stack_release"
/-- The single exit of `stackTake`: a `nop` reached with the range's base and
size in the first two argument registers, after the range is taken. -/
def takeSite : Sym := "scc_rt_take_site"
/-- The first instruction of `stackRelease`: a `nop` reached with the range's
base and size in the first two argument registers, before the range is
given back. -/
def releaseSite : Sym := "scc_rt_release_site"
def grow : Sym := "scc_rt_grow"
/-- The number of threads spawned so far (successful or not). -/
def nthreads : Sym := "scc_rt_nthreads"
/-- `scc_rt_thread_reserve()`: count a spawn and return its thread index;
abort `threads` past `Layout.maxThreads`. -/
def threadReserve : Sym := "scc_rt_thread_reserve"
def sigign : Sym := "scc_rt_sigign"
def alloc : Sym := "scc_rt_alloc"
def threadInit : Sym := "scc_rt_thread_init"
def print : Sym := "scc_rt_print"
def park : Sym := "scc_rt_park"
def unpark : Sym := "scc_rt_unpark"
def abort : Sym := "scc_rt_abort"
def start : Sym := "scc_rt_start"
def mainThread : Sym := "scc_rt_main"
/-- The thread entry trampoline for spawns of block `f`. -/
def thread (f : String) : Sym := "scc_rt_thr_" ++ mangle f
def abortMsg (k : AbortKind) : Sym := s!"scc_rt_msg{k.code}"
/-- The abort routine of kind `k`: its message, then `exit_group(101)`. -/
def abortKind (k : AbortKind) : Sym := s!"scc_rt_abort_{k.name}"
/-- The label on the `exit_group(101)` trap instruction of `abortKind k`
(the AArch64 `svc` / x64 `syscall` itself, not the routine's entry): the
abort outcome of kind `k` is the execution reaching this instruction. -/
def abortExit (k : AbortKind) : Sym := s!"scc_rt_abort_{k.name}_exit"
/-- The allocator for thread control blocks (aborts with `AbortKind.threads`). -/
def allocTcb : Sym := "scc_rt_alloc_tcb"

end Names

/-! ## Values -/

/-- A variable: its shape type and one operand per word. -/
abbrev Env := List (String × Ty × List Operand)

/-- What the term lowering knows about the program. -/
structure Ctx where
  prog : Prog
  externs : List (String × Frontend.Extern)
  /-- The block being lowered. -/
  fn : String
  /-- The object header's configuration. -/
  obj : ObjLayout := {}
  /-- The stack depth limit (`stackBudget`): with `some n`, a call of a
  code block bumps the thread's depth counter (`Tcb.depth`) around the call
  and aborts with `AbortKind.stack` when the new depth would exceed `n`
  (`callBlock`); `none` lowers calls without the counter. -/
  frames : Option Nat := none

/-- Words of a value of type `t` (`Obj.valWords`: a locative is two). -/
def words (t : Ty) : B Nat :=
  match Obj.valWords t with
  | some n => pure n
  | none => throw s!"no runtime layout for type {repr t}"

/-- `(n, m)` of a fragment type. -/
def regOf (t : Ty) : B (Nat × Nat) :=
  match Obj.regOf t with
  | some r => pure r
  | none => throw s!"no runtime layout for type {repr t}"

/-- The header counts of an object or array element of type `t`
(`Obj.counts`: its regions with their alignment gaps, so that the size
`1 + len·(n + m)` covers the gaps).  The accesses use `regOf`'s layout, so a
type on which the two differ (one with a 16-byte pair) is refused until the
lowering places pairs. -/
def countsOf (o : ObjLayout) (t : Ty) : B (Nat × Nat) := do
  let r ← regOf t
  match Obj.counts o t with
  | some c => if c == r then pure c else
      throw s!"a type with a 16-byte pair is not lowered yet: {repr t}"
  | none => throw s!"no runtime layout for type {repr t}"

/-- The header word (length 0) of kind `k` for counts `(n, m)`. -/
def header (o : ObjLayout) (k : Obj.HeaderKind) (n m : Nat) : B Nat :=
  match Obj.header0 o k n m with
  | some h => pure h
  | none => throw s!"an object of {n} scalar and {m} trace words does not fit the header"

def lookupV (env : Env) (x : String) : B (Ty × List Operand) :=
  match env.find? (·.1 == x) with
  | some (_, t, ws) => pure (t, ws)
  | none => throw s!"unbound variable '{x}'"

def evalAt (env : Env) : At → B (Ty × List Operand)
  | .var x => lookupV env x
  | .lit n =>
      if n ≥ 2 ^ 64 then throw s!"the literal {n} does not fit in 64 bits"
      else pure (.intS (.lit n), [imm n])
  | .unit => pure (.unit, [])

def one (ws : List Operand) (what : String) : B Operand :=
  match ws with
  | [w] => pure w
  | _ => throw s!"{what}: expected one word, got {ws.length}"

def evalOne (env : Env) (a : At) (what : String) : B Operand := do
  one (← evalAt env a).2 what

/-- The element (mode, type) of a buffer type. -/
def bufElem : Ty → Option (Mode × Ty)
  | .refine (.loc μ (.array _ u)) _ => some (μ, u)
  | .loc μ (.array _ u) => some (μ, u)
  | _ => none

def needSome {α : Type} (o : Option α) (msg : String) : B α :=
  match o with
  | some a => pure a
  | none => throw msg

/-- A register holding operand `o` (a move for an immediate). -/
def inReg (o : Operand) (hint : String := "t") : B Reg :=
  match o with
  | .reg r => pure r
  | .imm _ => do let d ← fresh hint; emit (.mov d o); pure d

/-- `base + k·8` as an address. -/
def wordAddr (base : Reg) (k : Nat) (off : Int := 0) : Addr := ⟨base, off + 8 * k⟩

/-- Record the kind of every register among `ws`, the words of a value of
type `t`: those of trace words (references, locative bases, `ThreadId`s) in
`Func.heapRegs`, for the stack maps; the others (a locative's offset word,
scalars) in `Func.scalarRegs`.  Exact: the words must match `Obj.traceMask t`
one for one. -/
def markWords (t : Ty) (ws : List Operand) : B Unit := do
  let bs ← needSome (Obj.traceMask t) s!"no runtime layout for type {repr t}"
  if bs.length != ws.length then
    throw s!"{ws.length} words for a value of {bs.length} words (type {repr t})"
  for (b, w) in bs.zip ws do
    match w with
    | .reg r => if b then markHeap r else markScalar r
    | .imm _ => pure ()

/-- A reference value's `(base, offset word)`: a `Ptr` is its base (offset
0), a `Loc` its two words. -/
def refOf (ws : List Operand) (what : String) : B (Operand × Operand) :=
  match ws with
  | [p] => pure (p, imm 0)
  | [b, o] => pure (b, o)
  | _ => throw s!"{what}: expected a reference, got {ws.length} words"

/-- `a + b` on offset words, folding immediates. -/
def offAdd (a b : Operand) : B Operand :=
  match a, b with
  | .imm x, .imm y => pure (.imm (x + y))
  | .imm x, o | o, .imm x => if x == 0 then pure o else binR .add a b "off"
  | _, _ => binR .add a b "off"

/-- `i · c` on offset words, folding immediates. -/
def offMul (i : Operand) (c : Nat) : B Operand :=
  match i with
  | .imm x => pure (.imm (x * UInt64.ofNat c))
  | _ => if c == 0 then pure (imm 0) else binR .mul i (imm c) "off"

/-- The address of each word of a value of type `u` in the cell at locative
`(base, off)`, in value order (`Obj.slots`): scalar word `i` at
`base + lo(off) + 8·i`, trace word `j` at `base − hi(off) − traceBias − 8·j`.
A constant offset folds into the displacements. -/
def cellAddrs (o : ObjLayout) (base off : Operand) (u : Ty) : B (List Addr) := do
  let sl ← needSome (Obj.slots u 0 0) s!"no runtime layout for type {repr u}"
  let b ← inReg base "base"
  let bias := Obj.traceBias o
  match off with
  | .imm w =>
      let sb : Int := w.toNat % 2 ^ Obj.halfBits
      let tb : Int := w.toNat / 2 ^ Obj.halfBits
      pure (sl.map fun (tr, i) => if tr then ⟨b, -(bias + tb + 8 * i)⟩ else ⟨b, sb + 8 * i⟩)
  | .reg _ =>
      let sbase ← if sl.any (!·.1) then do
          let lo ← fresh "lo"
          emit (.ext false .w32 lo off)
          inReg (← binR .add (.reg b) (.reg lo) "sb")
        else pure b
      let tbase ← if sl.any (·.1) then do
          let hi ← binR .lshr off (imm Obj.halfBits) "hi"
          inReg (← binR .sub (.reg b) hi "tb")
        else pure b
      pure (sl.map fun (tr, i) => if tr then ⟨tbase, -(bias + 8 * i)⟩ else ⟨sbase, 8 * i⟩)

/-- Load a value at the given word addresses. -/
def loadAt (o : Order) (as : List Addr) (hint : String) : B (List Operand) :=
  as.mapM fun a => do
    let d ← fresh hint
    emit (.load o .w64 d a)
    pure (Operand.reg d)

/-- Store a value's words at the given word addresses, in value order. -/
def storeAt (o : Order) (as : List Addr) (ws : List Operand) : B Unit := do
  if as.length != ws.length then
    throw s!"store: {ws.length} words for a cell of {as.length}"
  for (a, w) in as.zip ws do
    emit (.store o .w64 a w)

/-- The locative of slot `i` of the buffer at `(base, off)` with element
type `u`: the offset advances by `i` element strides (`Obj.stride`). -/
def slotLoc (base off i : Operand) (u : Ty) : B (Operand × Operand) := do
  let (n, m) ← regOf u
  pure (base, ← offAdd off (← offMul i (Obj.stride n m)))

/-! ## Fixed-width arithmetic

A `fix sg w` value is held as its `w`-bit pattern, zero-extended to 64 bits
(`TermRun.fmask`); operations compute on 64 bits and mask back. -/

def toWidth : Wd → Width
  | .w8 => .w8 | .w16 => .w16 | .w32 => .w32 | .w64 => .w64

/-- Zero-extend the low `w` bits (`fmask`). -/
def mask (w : Wd) (a : Operand) : B Operand := do
  if w == .w64 then pure a
  else do let d ← fresh "m"; emit (.ext false (toWidth w) d a); pure (.reg d)

/-- Sign-extend the low `w` bits (`fval` as a 64-bit pattern). -/
def sext (w : Wd) (a : Operand) : B Operand := do
  if w == .w64 then pure a
  else do let d ← fresh "s"; emit (.ext true (toWidth w) d a); pure (.reg d)

/-- The value of an operand as a signed or unsigned 64-bit word. -/
def fval (sg : Bool) (w : Wd) (a : Operand) : B Operand :=
  if sg then sext w a else pure a

def fop (sg : Bool) (w : Wd) (o : FOp) (x y : Operand) : B Operand := do
  match o with
  | .add => mask w (← binR .add x y)
  | .sub => mask w (← binR .sub x y)
  | .mul => mask w (← binR .mul x y)
  | .and => binR .and x y
  | .or => binR .or x y
  | .xor => binR .xor x y
  | .div =>
      if sg then mask w (← binR .sdiv (← sext w x) (← sext w y))
      else binR .udiv x y
  | .rem =>
      if sg then mask w (← binR .srem (← sext w x) (← sext w y))
      else binR .urem x y
  | .shl =>
      let amt ← binR .and y (imm (w.bits - 1))
      mask w (← binR .shl x amt)
  | .shr =>
      let amt ← binR .and y (imm (w.bits - 1))
      if sg then mask w (← binR .ashr (← sext w x) amt)
      else binR .lshr x amt

def fcmp (sg : Bool) (w : Wd) (o : FCmp) (x y : Operand) : B Operand := do
  let x ← fval sg w x
  let y ← fval sg w y
  let c : Cond := match o, sg with
    | .eq, _ => .eq | .ne, _ => .ne
    | .lt, true => .slt | .lt, false => .ult
    | .le, true => .sle | .le, false => .ule
  let d ← fresh "c"
  emit (.setc c d x y)
  pure (.reg d)

def fop1 (w : Wd) (o : FOp1) (x : Operand) : B Operand := do
  match o with
  | .not => binR .xor x (.imm (if w == .w64 then UInt64.ofNat (2 ^ 64 - 1) else UInt64.ofNat (2 ^ w.bits - 1)))
  | .neg => do let d ← fresh "n"; emit (.un .neg d x); mask w (.reg d)

/-- `cvt`: read the source as `TermRun.srcVal` does (a `fix` by its value,
anything else by its bits) and wrap to `w` bits. -/
def cvt (src : Ty) (w : Wd) (x : Operand) : B Operand := do
  let v ← match src with
    | .fix sg w' => fval sg w' x
    | _ => pure x
  mask w v

/-- The bit position of lane `j mod lanes` of width `w`. -/
def laneShift (w : Wd) (j : Operand) : B Operand := do
  let jj ← binR .and j (imm (w.lanes - 1))
  binR .mul jj (imm w.bits)

def lane (w : Wd) (x j : Operand) : B Operand := do
  let sh ← laneShift w j
  mask w (← binR .lshr x sh)

def setLane (w : Wd) (x j v : Operand) : B Operand := do
  let sh ← laneShift w j
  let m : Operand := .imm (if w == .w64 then UInt64.ofNat (2 ^ 64 - 1) else UInt64.ofNat (2 ^ w.bits - 1))
  let hole ← binR .shl m sh
  let nhole ← fresh "nh"
  emit (.un .not nhole hole)
  let cleared ← binR .and x (.reg nhole)
  let vm ← mask w v
  let vs ← binR .shl vm sh
  binR .or cleared vs

def bitOp : BitOp → B BinOp
  | .and => pure .and | .or => pure .or | .xor => pure .xor
  | .shl => pure .shl | .shr => pure .lshr
  | .wadd => pure .add | .wsub => pure .sub | .wmul => pure .mul | .mulhi => pure .umulh
  | .msb16 => throw "bits msb16 is not supported"

def bit1Op : BitOp1 → UnOp
  | .not => .not | .ctz => .ctz | .popcnt => .popcnt

/-! ## Operations -/

/-- Call a block (or an extern) with flattened arguments; `n` result words. -/
def callBlock (cx : Ctx) (f : String) (args : List Operand) (nres : Nat) : B (List Operand) := do
  match cx.externs.find? (·.1 == f) with
  | some (_, .print) =>
      -- (((b, o), m), n): write min(n, 8·m) bytes from the slice's first
      -- byte, at b + lo(o) (bytes are scalars: element layout (1, 0)).
      match args with
      | [b, o, m, n] =>
          let s ← match o with
            | .imm w => offAdd b (.imm (w % (2 ^ 32 : Nat).toUInt64))
            | .reg _ => do
                let lo ← fresh "lo"
                emit (.ext false .w32 lo o)
                binR .add b (.reg lo) "s"
          let cap ← binR .mul m (imm 8) "cap"
          let k ← fresh "k"
          emit (.select .ult k n cap n cap)
          emit (.call [] Names.print [s, .reg k])
          pure []
      | _ => throw "print: unexpected argument shape"
  | some (_, .park) => emit (.call [] Names.park []); pure []
  | some (_, .unpark) => emit (.call [] Names.unpark args); pure []
  | none =>
      if args.length > maxArgs then
        throw s!"call of '{f}': {args.length} argument words (at most {maxArgs})"
      if nres > maxRets then
        throw s!"call of '{f}': {nres} result words (at most {maxRets})"
      let ds ← (List.range nres).mapM fun _ => fresh "r"
      match cx.frames with
      | none => emit (.call ds (Names.user f) args)
      | some fr =>
        -- The depth counter: `d + 1 > fr` aborts (stack); else the call runs
        -- at depth `d + 1` and the depth is `d` again after it.  Only the
        -- owning thread accesses its TCB's counter (plain accesses), and the
        -- thread pointer is read again after the call, so only `d` (a
        -- scalar) is live across it.
        let tp ← fresh "tp"
        emit (.getTp tp)
        let d ← fresh "depth"
        emit (.load .plain .w64 d ⟨tp, Tcb.depth⟩)
        markScalar d
        let d1 ← binR .add (.reg d) (imm 1) "depth"
        let ldeep ← freshLabel "deep"
        let lcall ← freshLabel "call"
        terminate (.br .ugt d1 (imm fr) ldeep lcall)
        startBlock ldeep
        emit (.call [] Names.abort [imm AbortKind.stack.code])
        terminate .unreachable
        startBlock lcall
        emit (.store .plain .w64 ⟨tp, Tcb.depth⟩ d1)
        emit (.call ds (Names.user f) args)
        let tp2 ← fresh "tp"
        emit (.getTp tp2)
        emit (.store .plain .w64 ⟨tp2, Tcb.depth⟩ (.reg d))
      pure (ds.map .reg)

/-- The layout of a spawned thread's TCB with argument type `T`: the TCB's
fields are its first scalar words, the argument's scalar words follow them
and its trace words form the TCB's trace region (`Obj.slots` from scalar
index `Tcb.size / 8`).  Returns the header and the argument words' slots. -/
def tcbLayout (o : ObjLayout) (T : Ty) : B (Nat × List (Bool × Nat)) := do
  let sl ← needSome (Obj.slots T (Tcb.size / 8) 0) s!"no runtime layout for type {repr T}"
  let n := Tcb.size / 8 + sl.countP (!·.1)
  let m := sl.countP (·.1)
  pure (← header o .pinned n m, sl)

/-- The address of an argument word in a TCB (`tcbLayout`). -/
def tcbArgAddr (o : ObjLayout) (tcb : Reg) : Bool × Nat → Addr
  | (true, j) => ⟨tcb, -(Obj.traceBias o + 8 * j)⟩
  | (false, i) => ⟨tcb, 8 * i⟩

/-- `spawn f a` (`f` takes `T`): a thread index (`Names.threadReserve`, which
aborts past the thread cap), a TCB in the pinned region holding the index and
the argument words (`tcbLayout`), a stack, and a `clone` into `f`'s
trampoline.  The result, the child's `ThreadId`, is its TCB's address. -/
def spawn (o : ObjLayout) (f : String) (T : Ty) (args : List Operand) : B Operand := do
  let tidx ← fresh "tidx"
  emit (.call [tidx] Names.threadReserve [])
  markScalar tidx
  let (hdr, sl) ← tcbLayout o T
  if sl.length != args.length then
    throw s!"spawn of '{f}': {args.length} argument words for a layout of {sl.length}"
  if sl.length > maxSpawnArgs then
    throw s!"spawn of '{f}': {sl.length} argument words (at most {maxSpawnArgs})"
  let tcb ← fresh "tcb"
  emit (.call [tcb] Names.allocTcb [imm hdr, imm 1])
  markHeap tcb
  emit (.store .plain .w64 ⟨tcb, Tcb.index⟩ (.reg tidx))
  for (w, s) in args.zip sl do
    emit (.store .plain .w64 (tcbArgAddr o tcb s) w)
  let top ← fresh "top"
  emit (.call [top] Names.threadInit [.reg tcb])
  let r ← fresh "clone"
  -- A spawn is a full barrier on the parent, and the child starts from the
  -- parent's views after it (`TermSpawnStep`); the fence makes that explicit
  -- rather than relying on the kernel's `clone` path.
  emit (.fence .full)
  emit (.clone r (.reg top) (.reg tcb) (Names.thread f) (.reg tcb))
  let bad ← freshLabel "spawnfail"
  let ok ← freshLabel "spawned"
  terminate (.br .slt (.reg r) (imm 0) bad ok)
  startBlock bad
  emit (.call [] Names.abort [imm AbortKind.threads.code])
  terminate .unreachable
  startBlock ok
  pure (.reg tcb)

/-- Lower one operation: its shape type and words. -/
def lowerOp (cx : Ctx) (env : Env) (x : String) : Op → B (Ty × List Operand)
  | .atom a => evalAt env a
  | .pair a b => do
      let (t, ws) ← evalAt env a
      let (u, us) ← evalAt env b
      pure (.prod t u, ws ++ us)
  | .add a b => do
      let p ← evalOne env a "+"
      let q ← evalOne env b "+"
      -- Every `Int` addition keeps its overflow check (see `Scc.Frontend`).
      let d ← fresh x
      emit (.addChk d p q)
      pure (.int, [.reg d])
  | .sub a b => do
      -- WeakCore's checker accepts `a - b` only for index-typed operands with
      -- `b ≤ a` provable (`checkOp`'s `.sub`, CoreTerm.lean:1575–1587), so the
      -- floor is never reached by a checked program.  The saturating form is
      -- exact for `TermRun.subW` (truncated `Nat` subtraction) whatever the
      -- typing, which keeps the typing invariant out of the lowering's proof.
      let p ← evalOne env a "-"
      let q ← evalOne env b "-"
      let d ← fresh x
      emit (.subSat d p q)
      pure (.int, [.reg d])
  | .new a => do
      let (t, ws) ← evalAt env a
      let (n, m) ← countsOf cx.obj t
      let h ← header cx.obj .obj n m
      let p ← fresh x
      -- the source units of the object: its words and one
      let w := (Frontend.words t).getD (n + m)
      unless n + m ≤ 2 * w do
        throw s!"new: {n + m} runtime words for {w} source words do not fit {w + 1} heap cells"
      let u := w + 1
      emit (.call [p] Names.alloc [imm h, imm 1, imm u])
      storeAt .plain (← cellAddrs cx.obj (.reg p) (imm 0) t) ws
      pure (.ptr .own t, [.reg p])
  | .publish a => do
      let (t, ws) ← evalAt env a
      emit (.fence .st)
      match t with
      | .ptr _ u => pure (.ptr .pub u, ws)
      | .refine (.loc _ (.array n u)) ψ => pure (.refine (.loc .pub (.array n u)) ψ, ws)
      | _ => throw "publish: not a pointer or buffer"
  | .newBuf n τ => do
      let k ← evalOne env n "newBuf"
      let (en, em) ← countsOf cx.obj τ
      let h ← header cx.obj .array en em
      let p ← fresh x
      -- the source units of the buffer: `k` times its element's words, and
      -- one (`scc_rt_alloc` checks `k` before it reads them, so a wrapped
      -- product is never counted)
      let ew := (Frontend.words τ).getD (en + em)
      -- the buffer's `1 + k·(en + em)` words fit its `u` 16-byte cells
      -- (`scc_rt_alloc` places it at `16·old`)
      unless en + em ≤ 2 * ew do
        throw s!"newBuf: {en + em} runtime words per element for {ew} source words do not fit the heap cells"
      let u ← match ew, k with
        | 0, _ => pure (imm 1)
        | _, .imm v => pure (imm (v.toNat * ew + 1))
        | 1, _ => binR .add k (imm 1) "u"
        | _, _ => do binR .add (← binR .mul k (imm ew) "uk") (imm 1) "u"
      -- The arena is never reused and starts zeroed: the cells are born zero
      -- (and every trace slot null).
      emit (.call [p] Names.alloc [imm h, k, u])
      pure (.refine (.loc .own (.array (.lit 0) τ)) (.ini (.lit 0)), [.reg p, imm 0])
  | .idx b i => do
      let (t, bw) ← evalAt env b
      let (base, off) ← refOf bw "b[i]"
      let iv ← evalOne env i "b[i]"
      let (μ, u) ← needSome (bufElem t) "b[i]: not a buffer"
      let (base, off) ← slotLoc base off iv u
      pure (.loc μ u, [base, off])
  | .fld i a => do
      let (t, aw) ← evalAt env a
      let (base, off) ← refOf aw "fld"
      let (μ, u) ← needSome (cellOf t) "fld: not a reference"
      match unfold1 u with
      | .prod c1 c2 =>
          if i == 0 then pure (.loc μ c1, [base, off])
          else do
            let (n, m) ← regOf c1
            pure (.loc μ c2, [base, ← offAdd off (imm (Obj.stride n m))])
      | _ => throw "fld: not a pair cell"
  | .load acq a => do
      let (t, aw) ← evalAt env a
      let (base, off) ← refOf aw "load"
      let (_, u) ← needSome (cellOf t) "load: not a reference"
      pure (u, ← loadAt (if acq then .acq else .plain) (← cellAddrs cx.obj base off u) x)
  | .loadAt b i => do
      let (t, bw) ← evalAt env b
      let (base, off) ← refOf bw "load b[i]"
      let iv ← evalOne env i "load b[i]"
      let (_, u) ← needSome (bufElem t) "load b[i]: not a buffer"
      let (base, off) ← slotLoc base off iv u
      pure (u, ← loadAt .plain (← cellAddrs cx.obj base off u) x)
  | .store rel a v _ => do
      let (t, aw) ← evalAt env a
      let (base, off) ← refOf aw "store"
      let (_, u) ← needSome (cellOf t) "store: not a reference"
      let (_, vs) ← evalAt env v
      storeAt (if rel then .rel else .plain) (← cellAddrs cx.obj base off u) vs
      pure (.unit, [])
  | .xchg a v => do
      -- On a cell this thread holds exclusively: a plain load, then a plain store.
      let (t, aw) ← evalAt env a
      let (base, off) ← refOf aw "xchg"
      let (_, u) ← needSome (cellOf t) "xchg: not a reference"
      let (_, vs) ← evalAt env v
      let as ← cellAddrs cx.obj base off u
      let old ← loadAt .plain as x
      storeAt .plain as vs
      pure (u, old)
  | .xchgAt b i v => do
      let (t, bw) ← evalAt env b
      let (base, off) ← refOf bw "xchg b[i]"
      let iv ← evalOne env i "xchg b[i]"
      let (_, u) ← needSome (bufElem t) "xchg b[i]: not a buffer"
      let (base, off) ← slotLoc base off iv u
      let (_, vs) ← evalAt env v
      let as ← cellAddrs cx.obj base off u
      let old ← loadAt .plain as x
      storeAt .plain as vs
      pure (u, old)
  | .bufInit b i v => do
      -- Initialise slot `i` (the checker's `ini`) of an own buffer: a plain
      -- store; the result is the same buffer.
      let (t, bw) ← evalAt env b
      let (base, off) ← refOf bw "bufInit"
      let iv ← evalOne env i "bufInit"
      let (_, u) ← needSome (bufElem t) "bufInit: not a buffer"
      let (sb, so) ← slotLoc base off iv u
      let (_, vs) ← evalAt env v
      storeAt .plain (← cellAddrs cx.obj sb so u) vs
      pure (t, bw)
  | .fence f => do
      emit (.fence (match f with | .ld => .ld | .st => .st | .full => .full))
      pure (.unit, [])
  | .pack a _ τ => do pure (τ, (← evalAt env a).2)
  | .packT a _ τ => do pure (τ, (← evalAt env a).2)
  | .nameI a => evalAt env a
  | .zero τ => do
      let n ← words τ
      pure (τ, List.replicate n (imm 0))
  | .call f _ a _ => do
      let d ← needSome (cx.prog.find? (·.name == f)) s!"unknown block '{f}'"
      let (_, ws) ← evalAt env a
      let n ← words d.retTy
      pure (d.retTy, ← callBlock cx f ws n)
  | .spawn f a T _ => do
      let (_, ws) ← evalAt env a
      pure (Frontend.tidTy, [← spawn cx.obj f T ws])
  | .cvt sg w a => do
      let (t, ws) ← evalAt env a
      pure (.fix sg w, [← cvt t w (← one ws "cvt")])
  | .toInt a => do pure (.int, [← evalOne env a "toInt"])
  | .asLanes sg w a => do pure (.lanes sg w, [← evalOne env a "asLanes"])
  | .fop o a b => do
      let (t, ws) ← evalAt env a
      let (sg, w) ← needSome (fixOf t) "fop: not a fixed-width value"
      pure (.fix sg w, [← fop sg w o (← one ws "fop") (← evalOne env b "fop")])
  | .fcmp o a b => do
      let (t, ws) ← evalAt env a
      let (sg, w) ← needSome (fixOf t) "fcmp: not a fixed-width value"
      pure (.int, [← fcmp sg w o (← one ws "fcmp") (← evalOne env b "fcmp")])
  | .fop1 o a => do
      let (t, ws) ← evalAt env a
      let (sg, w) ← needSome (fixOf t) "fop1: not a fixed-width value"
      pure (.fix sg w, [← fop1 w o (← one ws "fop1")])
  | .lane a j => do
      let (t, ws) ← evalAt env a
      let (sg, w) ← needSome (lanesOf t) "lane: not a lanes word"
      pure (.fix sg w, [← lane w (← one ws "lane") (← evalOne env j "lane")])
  | .setLane a j v => do
      let (t, ws) ← evalAt env a
      let (sg, w) ← needSome (lanesOf t) "setLane: not a lanes word"
      pure (.lanes sg w, [← setLane w (← one ws "setLane") (← evalOne env j "setLane")
        (← evalOne env v "setLane")])
  | .bits o a b => do
      let op ← bitOp o
      pure (.int, [← binR op (← evalOne env a "bits") (← evalOne env b "bits")])
  | .bit1 o a => do
      let d ← fresh x
      emit (.un (bit1Op o) d (← evalOne env a "bit1"))
      pure (.int, [.reg d])
  | op => throw s!"operation not in the accepted fragment: {repr op}"

/-! ## Terms -/

/-- The components of a pair type, under refinements (`let (x, y) = a`). -/
def prodOf : Ty → Option (Ty × Ty)
  | .prod u w => some (u, w)
  | .refine t _ => prodOf t
  | _ => none

/-- Lower a term. The placement trace (`BState.marks`) gets, at the start of
every block and at the return point of every call, the source point there:
at the blocks the term opens (`entry`, an `if`'s branches), those variables
and the branch; at the return of the call of a code block `let x = f(a); e`,
the variables with `x` (its words in the call's result registers) and `e`;
anywhere else inside the lowering of `let x = op; e` (a runtime call, a block
of `op`'s own), the variables before it and `let x = op; e` itself. -/
def lowerExpr (cx : Ctx) (env : Env) (ex : Expr) : B Unit := do
  setHere (env, ex)
  match ex with
  | .let_ x op e => do
      let (t, ws) ← lowerOp cx env x op
      if let .call f .. := op then
        if (cx.externs.find? (·.1 == f)).isNone then
          if let some (n@(.ret ..), _) := (← get).marks.back? then
            markAt n ((x, t, ws) :: env, e)
      markWords t ws
      lowerExpr cx ((x, t, ws) :: env) e
  | .split a x y e => do
      let (t, ws) ← evalAt env a
      let (u, w) ← needSome (prodOf t) "let (x, y): not a pair"
      let n ← words u
      lowerExpr cx ((y, w, ws.drop n) :: (x, u, ws.take n) :: env) e
  | .unpack a _ x e => do
      let (t, ws) ← evalAt env a
      match t with
      | .iex b => lowerExpr cx ((x, b, ws) :: env) e
      | _ => throw "unpack: not an index package"
  | .unpackT a _ x e => do
      let (t, ws) ← evalAt env a
      match t with
      | .tex _ b => lowerExpr cx ((x, Ty.substT 0 .unit b, ws) :: env) e
      | _ => throw "unpack: not a type package"
  | .ifeq a b yes no => do
      let p ← evalOne env a "if"
      let q ← evalOne env b "if"
      let ly ← freshLabel "then"
      let ln ← freshLabel "else"
      terminate (.br .eq p q ly ln)
      startBlock ly
      markAt (.block ly) (env, yes)
      lowerExpr cx env yes
      startBlock ln
      markAt (.block ln) (env, no)
      lowerExpr cx env no
  | .ret a => do
      let (_, ws) ← evalAt env a
      terminate (.ret ws)
  | .tail f _ a _ => do
      let (_, ws) ← evalAt env a
      if (cx.externs.find? (·.1 == f)).isSome then
        let rs ← callBlock cx f ws 0
        terminate (.ret rs)
      else
        if ws.length > maxArgs then
          throw s!"tail call of '{f}': {ws.length} argument words (at most {maxArgs})"
        terminate (.tail (Names.user f) ws)
  | _ => throw "term not in the accepted fragment"

/-- Lower one code block, with its placement trace (`lowerExpr`). -/
def lowerDeclMarks (prog : Prog) (externs : List (String × Frontend.Extern)) (d : Decl)
    (obj : ObjLayout := {}) (frames : Option Nat := none) :
    Except String (Func × Array (Node × Point)) := do
  let n ← match Obj.valWords d.argTy with
    | some n => pure n
    | none => throw s!"block '{d.name}': no runtime layout for its argument"
  if n > maxArgs then throw s!"block '{d.name}': {n} argument words (at most {maxArgs})"
  match Obj.valWords d.retTy with
  | some r => if r > maxRets then throw s!"block '{d.name}': {r} result words (at most {maxRets})"
  | none => throw s!"block '{d.name}': no runtime layout for its result"
  let params := (List.range n).map fun k => s!"{d.arg}.{k}"
  let cx : Ctx := { prog, externs, fn := d.name, obj, frames }
  buildFuncMarks (Names.user d.name) params true do
    markWords d.argTy (params.map .reg)
    markAt (.block "entry") ([(d.arg, d.argTy, params.map .reg)], d.body)
    lowerExpr cx [(d.arg, d.argTy, params.map .reg)] d.body

/-- Lower one code block. -/
def lowerDecl (prog : Prog) (externs : List (String × Frontend.Extern)) (d : Decl)
    (obj : ObjLayout := {}) (frames : Option Nat := none) : Except String Func :=
  (·.1) <$> lowerDeclMarks prog externs d obj frames

end Scc.Lower
