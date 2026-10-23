/-
The x64 instance of the Promising layer's `ISA` interface, under the TSO
profile. See `Kraken/Promising/AArch64.lean` for the shape; the differences
are the x64 `Effects` and `Width`, and that symbolic data locations are
resolved through the executable's label table.
-/
import Kraken.X64.Semantics
import Kraken.X64.Deps
import Kraken.Promising.Machine

namespace Kraken.Promising.X64

structure State where
  exe : _root_.Executable
  endPc : Int64
  st : MachineState
  /-- Source text of the instruction at an address, for traces. -/
  showPc : Int64 → String := fun pc => s!"pc={pc}"
  /-- The declared shared locations every access is resolved against
  (`Decls.resolve`); none by default, so an access is its own footprint. -/
  decls : Decls := {}

/-- The footprint of an access of `n` bytes at `addr`. -/
def loc (addr : BitVec 64) (n : Nat) : Loc := { addr, bytes := n }

/-! ### Non-atomic vector accesses

A vector access the SDM does not guarantee to be single-copy atomic is a
sequence of 8-byte pieces in address order, each an 8-byte access of its own:
two for 16 bytes, four for 32, eight for 64. The access value is
little-endian: piece `i` is bytes `[8i, 8i + 8)` of the value, so the piece
at the lowest address holds the low 64 bits.

A piece is *mapped-first*, like `MachineData.load`/`store` for a whole access:
a piece the private memory maps in full is served by it, and only the other
pieces become events. The SDM guarantees an 8-byte access only within a
cache line, so a piece that would become an event and crosses a 64-byte line
is reported unsupported. -/

/-- An 8-byte piece at `a` crosses a 64-byte cache line. -/
def crossesLine (a : BitVec 64) : Bool := 56 < a.toNat % 64

/-- The value of an 8-byte piece, from its bytes (little-endian). -/
def pieceVal (bs : List UInt8) : BitVec 64 := BitVec.ofInt 64 (Int.ofBytes bs)

/-- A load of `n` 8-byte pieces at `addr`, in address order; `k` receives the
bytes read. A piece mapped in `dmem` is read from it; any other is an 8-byte
`load` event at `addr + 8i`. -/
def loadPieces {σ : Type} (ds : Decls) (dmem : DataMem) (addr : BitVec 64) :
    Nat → (List UInt8 → EvTree σ) → EvTree σ
  | 0, k => k []
  | n + 1, k =>
    let rest (bs : List UInt8) : EvTree σ := loadPieces ds dmem (addr + 8) n fun bs' => k (bs ++ bs')
    match dmem.loadBytes addr 8 with
    | some bs => rest bs
    | none =>
      if crossesLine addr then .fault "vector piece crosses a cache line"
      else .access ds addr 8 fun l => .load .plain false l fun v => rest (Int.toBytes 8 (v.toNat : Int))

/-- A store of the bytes `bs` as `n` 8-byte pieces at `addr`, in address
order; `k` receives the private memory after it. A piece mapped in `dmem` is
written there; any other is an 8-byte `store` event at `addr + 8i`. -/
def storePieces {σ : Type} (ds : Decls) (addr : BitVec 64) :
    Nat → List UInt8 → DataMem → (DataMem → EvTree σ) → EvTree σ
  | 0, _, dmem, k => k dmem
  | n + 1, bs, dmem, k =>
    match dmem.loadBytes addr 8 with
    | some _ => storePieces ds (addr + 8) n (bs.drop 8) (dmem.storeBytes addr (bs.take 8)) k
    | none =>
      if crossesLine addr then .fault "vector piece crosses a cache line"
      else .access ds addr 8 fun l => .store .plain false l ((pieceVal (bs.take 8)).setWidth 128) fun _ =>
        storePieces ds (addr + 8) n (bs.drop 8) dmem k

/-- `Effects` to `EvTree`, resolving every access against `ds`. Values travel
zero-extended to 128 bits (`Val`); a load truncates to the access width.

Vector accesses: a guaranteed-atomic one (`atomic` at 16 bytes)
is one 16-byte event, as is `rmw16`; any other is `loadPieces`/`storePieces`,
the value read being the pieces' bytes, little-endian. The pieces are
mapped-first (a refinement of `SharedEnv.LoadPieces`/`StorePieces`, which send
every piece to the environment): a piece `dmem` maps in full is served by
`dmem`, so that the merged link holds for an access that is part private,
part shared. -/
def toEv (ds : Decls) : Effects → EvTree MachineState
  | .done a => .done a
  | .unimplemented msg => .fault msg
  | .syscall .. => .fault pendingSyscallMsg
  | .gp_unaligned _ _ => .fault "unaligned access"
  | .nonmem_load dmem addr w ret =>
    .access ds addr w.bytes fun l => .load .plain false l fun v => toEv ds (ret (v.setWidth w.bits) dmem)
  | @Effects.nonmem_store dmem addr w v ret =>
    .access ds addr w.bytes fun l => .store .plain false l (v.setWidth 128) fun _ => toEv ds (ret dmem)
  | .sync_load k xcl dmem addr w ret =>
    .access ds addr w.bytes fun l => .load k xcl l fun v => toEv ds (ret (v.setWidth w.bits) dmem)
  | @Effects.sync_store k xcl dmem addr w v ret =>
    .access ds addr w.bytes fun l => .store k xcl l (v.setWidth 128) fun ok => toEv ds (ret ok dmem)
  -- x86 has no `NoRet` atomics (herd's `NoRet` annotation is AArch64-only, and
  -- every locked RMW is a full barrier under TSO anyway): `noRet := false`.
  | .rmw k dmem addr w op ret =>
    .access ds addr w.bytes fun l =>
      .rmw k false l (fun old => (op (old.setWidth w.bits)).map (·.setWidth 128))
        fun old => toEv ds (ret (old.setWidth w.bits) dmem)
  | .fence k ok => .fence k fun _ => toEv ds (ok ())
  | @Effects.undefined _ inst ret =>
    match inst with
    | .bool => .choose 2 fun i => toEv ds (ret (i.val == 1))
    | .bitvec _ => .fault "undefined register value"
    | .avx_bitvec _ => .fault "undefined vector value"
    | .statusFlags => .fault "undefined flags"
  | .require_read_access _ _ ok => toEv ds (ok ())
  | .require_write_access _ _ ok => toEv ds (ok ())
  | .require_exec_access _ ok => toEv ds (ok ())
  | .require_read_access_avx _ _ _ ok => toEv ds (ok ())
  | .require_write_access_avx _ _ _ ok => toEv ds (ok ())
  | .nonmem_load_avx atomic dmem addr w ret =>
    if atomic && w == .W128 then
      .access ds addr 16 fun l => .load .plain false l fun v => toEv ds (ret (v.setWidth w.bits) dmem)
    else
      loadPieces ds dmem addr (w.bytes / 8) fun bs => toEv ds (ret (BitVec.ofInt w.bits (Int.ofBytes bs)) dmem)
  | @Effects.nonmem_store_avx atomic dmem addr w v ret =>
    if atomic && w == .W128 then
      .access ds addr 16 fun l => .store .plain false l (v.setWidth 128) fun _ => toEv ds (ret dmem)
    else
      storePieces ds addr (w.bytes / 8) (Int.toBytes w.bytes v.toInt) dmem fun dmem => toEv ds (ret dmem)
  | .rmw16 k dmem addr op ret =>
    .access ds addr 16 fun l => .rmw k false l op fun old => toEv ds (ret old dmem)

/-! ### Tests of the vector translation -/

/-- One run of an event tree, as text: loads and RMWs read `vals` in order
(then `0`), stores succeed, `choose` takes `0`. A leaf `unimplemented msg`
of the effect tree shows as `fault: msg`, which the tests use to print what
the continuation received. -/
def showRun {σ : Type} (vals : List Val) : EvTree σ → List String
  | .done _ => ["done"]
  | .fault m => [s!"fault: {m}"]
  | .choose 0 _ => ["choose 0"]
  | .choose (_ + 1) k => showRun vals (k 0)
  | .load _ _ l ret => s!"load 0x{l.addr.toHex}/{l.bytes} = 0x{(vals.headD 0).toHex}" :: showRun vals.tail (ret (vals.headD 0))
  | .store _ _ l v ret => s!"store 0x{l.addr.toHex}/{l.bytes} := 0x{v.toHex}" :: showRun vals (ret true)
  | .rmw _ _ l op ret =>
    s!"rmw 0x{l.addr.toHex}/{l.bytes} old 0x{(vals.headD 0).toHex} → {(op (vals.headD 0)).map (·.toHex)}" ::
      showRun vals.tail (ret (vals.headD 0))
  | .fence _ ret => "fence" :: showRun vals (ret ())

/-- `showRun`, one event per line. -/
def printRun {σ : Type} (vals : List Val) (t : EvTree σ) : IO Unit :=
  for l in showRun vals t do IO.println l

private def testVal : BitVec 256 := 0x3333333333333333_2222222222222222_1111111111111111_0000000000000000#256
private def got {n : Nat} (v : BitVec n) : Effects := .unimplemented s!"got 0x{v.toHex}"
private def stored : DataMem → Effects := fun _ => .unimplemented "stored"

-- An atomic 16-byte store, and a load reading it back: one event each.
/--
info: store 0x0000000000001000/16 := 0x11111111111111110000000000000000
fault: stored
-/
#guard_msgs in
#eval printRun [] (toEv {} (.nonmem_store_avx true ∅ 0x1000 (w := .W128) (testVal.setWidth 128) stored))
/--
info: load 0x0000000000001000/16 = 0x11111111111111110000000000000000
fault: got 0x11111111111111110000000000000000
-/
#guard_msgs in
#eval printRun [0x1111111111111111_0000000000000000] (toEv {} (.nonmem_load_avx true ∅ 0x1000 .W128 fun v _ => got v))

-- A non-atomic 16-byte store: two 8-byte events, the low half first; and the load back.
/--
info: store 0x0000000000001000/8 := 0x00000000000000000000000000000000
store 0x0000000000001008/8 := 0x00000000000000001111111111111111
fault: stored
-/
#guard_msgs in
#eval printRun [] (toEv {} (.nonmem_store_avx false ∅ 0x1000 (w := .W128) (testVal.setWidth 128) stored))
/--
info: load 0x0000000000001000/8 = 0x00000000000000000000000000000000
load 0x0000000000001008/8 = 0x00000000000000001111111111111111
fault: got 0x11111111111111110000000000000000
-/
#guard_msgs in
#eval printRun [0, 0x1111111111111111] (toEv {} (.nonmem_load_avx false ∅ 0x1000 .W128 fun v _ => got v))

-- A 32-byte store: four events in address order; `atomic` means nothing at 32 bytes.
/--
info: store 0x0000000000001000/8 := 0x00000000000000000000000000000000
store 0x0000000000001008/8 := 0x00000000000000001111111111111111
store 0x0000000000001010/8 := 0x00000000000000002222222222222222
store 0x0000000000001018/8 := 0x00000000000000003333333333333333
fault: stored
-/
#guard_msgs in
#eval printRun [] (toEv {} (.nonmem_store_avx true ∅ 0x1000 (w := .W256) testVal stored))

-- An unaligned non-atomic access: the first piece is within the line, the
-- second crosses it.
/--
info: store 0x0000000000001034/8 := 0x00000000000000000000000000000000
fault: vector piece crosses a cache line
-/
#guard_msgs in
#eval printRun [] (toEv {} (.nonmem_store_avx false ∅ 0x1034 (w := .W128) (testVal.setWidth 128) stored))

-- A piece the private memory maps is served by it (mapped-first); the other is an event.
/--
info: load 0x0000000000001008/8 = 0x00000000000000001111111111111111
fault: got 0x111111111111111100000000000000ab
-/
#guard_msgs in
#eval printRun [0x1111111111111111]
  (toEv {} (.nonmem_load_avx false (Mem.storeInt ∅ 0x1000 8 0xab) 0x1000 .W128 fun v _ => got v))

-- `rmw16`: one 16-byte event; the compare succeeds (a write) or fails (none).
/--
info: rmw 0x0000000000001000/16 old 0x00000000000000000000000000000001 → (some 00000000000000000000000000000002)
fault: got 0x00000000000000000000000000000001
-/
#guard_msgs in
#eval printRun [1] (toEv {} (.rmw16 .acqRel ∅ 0x1000 (fun old => if old == 1 then some 2 else none) fun v _ => got v))
/--
info: rmw 0x0000000000001000/16 old 0x00000000000000000000000000000005 → none
fault: got 0x00000000000000000000000000000005
-/
#guard_msgs in
#eval printRun [5] (toEv {} (.rmw16 .acqRel ∅ 0x1000 (fun old => if old == 1 then some 2 else none) fun v _ => got v))

-- A 16-byte access to an unsized declaration is reported, as by `Decls.resolve`.
/--
info: fault: mixed-size access: 16 bytes at 0x0000000000001000, declared unsized
-/
#guard_msgs in
#eval printRun [] (toEv { locs := [⟨0x1000, 0⟩] } (.nonmem_load_avx true ∅ 0x1000 .W128 fun v _ => got v))

def State.directive (s : State) : Option Directive :=
  ((s.exe.directivesFromAddress s.st.2).dropWhile (fun (d, _) => match d with | .label _ => true | _ => false))
    |>.head? |>.map (·.1)

def exec (s : State) : Option (EvTree State) :=
  if s.st.2 == s.endPc || s.directive.isNone then none
  else some <| (toEv s.decls (_root_.Executable.step s.exe s.st fun s' => .done s')).map fun st => { s with st }

/-- `toEv` for certification (`execCert`): a system call, which `toEv` makes a
fault, is a choice among `results info`, the values `rax`, `rcx` and `r11` receive, each
continuing after the instruction. The results are a parameter: Kraken knows no
system call, the client supplies an over-approximation of what each call may
return. An empty list is a dead end (`choose 0`), not a fault. -/
def toEvCert (results : SyscallInfo → List SyscallRet) (ds : Decls) : Effects → EvTree MachineState
  | .done a => .done a
  | .unimplemented msg => .fault msg
  | .syscall info ret =>
    let rs := results info
    .choose rs.length fun i => toEvCert results ds (ret rs[i])
  | .gp_unaligned _ _ => .fault "unaligned access"
  | .nonmem_load dmem addr w ret =>
    .access ds addr w.bytes fun l => .load .plain false l fun v => toEvCert results ds (ret (v.setWidth w.bits) dmem)
  | @Effects.nonmem_store dmem addr w v ret =>
    .access ds addr w.bytes fun l => .store .plain false l (v.setWidth 128) fun _ => toEvCert results ds (ret dmem)
  | .sync_load k xcl dmem addr w ret =>
    .access ds addr w.bytes fun l => .load k xcl l fun v => toEvCert results ds (ret (v.setWidth w.bits) dmem)
  | @Effects.sync_store k xcl dmem addr w v ret =>
    .access ds addr w.bytes fun l => .store k xcl l (v.setWidth 128) fun ok => toEvCert results ds (ret ok dmem)
  -- x86 has no `NoRet` atomics (herd's `NoRet` annotation is AArch64-only, and
  -- every locked RMW is a full barrier under TSO anyway): `noRet := false`.
  | .rmw k dmem addr w op ret =>
    .access ds addr w.bytes fun l =>
      .rmw k false l (fun old => (op (old.setWidth w.bits)).map (·.setWidth 128))
        fun old => toEvCert results ds (ret (old.setWidth w.bits) dmem)
  | .fence k ok => .fence k fun _ => toEvCert results ds (ok ())
  | @Effects.undefined _ inst ret =>
    match inst with
    | .bool => .choose 2 fun i => toEvCert results ds (ret (i.val == 1))
    | .bitvec _ => .fault "undefined register value"
    | .avx_bitvec _ => .fault "undefined vector value"
    | .statusFlags => .fault "undefined flags"
  | .require_read_access _ _ ok => toEvCert results ds (ok ())
  | .require_write_access _ _ ok => toEvCert results ds (ok ())
  | .require_exec_access _ ok => toEvCert results ds (ok ())
  | .require_read_access_avx _ _ _ ok => toEvCert results ds (ok ())
  | .require_write_access_avx _ _ _ ok => toEvCert results ds (ok ())
  | .nonmem_load_avx atomic dmem addr w ret =>
    if atomic && w == .W128 then
      .access ds addr 16 fun l => .load .plain false l fun v => toEvCert results ds (ret (v.setWidth w.bits) dmem)
    else
      loadPieces ds dmem addr (w.bytes / 8) fun bs => toEvCert results ds (ret (BitVec.ofInt w.bits (Int.ofBytes bs)) dmem)
  | @Effects.nonmem_store_avx atomic dmem addr w v ret =>
    if atomic && w == .W128 then
      .access ds addr 16 fun l => .store .plain false l (v.setWidth 128) fun _ => toEvCert results ds (ret dmem)
    else
      storePieces ds addr (w.bytes / 8) (Int.toBytes w.bytes v.toInt) dmem fun dmem => toEvCert results ds (ret dmem)
  | .rmw16 k dmem addr op ret =>
    .access ds addr 16 fun l => .rmw k false l op fun old => toEvCert results ds (ret old dmem)

/-- `exec` for certification only, with `toEvCert results`: same halting, and
the same tree on every instruction other than a system call. -/
def execCert (results : SyscallInfo → List SyscallRet) (s : State) : Option (EvTree State) :=
  if s.st.2 == s.endPc || s.directive.isNone then none
  else some <| (toEvCert results s.decls (_root_.Executable.step s.exe s.st fun s' => .done s')).map fun st => { s with st }

/-- A thread state for a parsed program: laid out at `0x100000 * (tid + 1)`,
one byte per instruction, halting after the last one. Symbolic data
locations named in the code are given addresses by `syms` (name, address)
through labels placed after the code. -/
def mkState (tid : Nat) (prog : Program) (regs : Reg64s) (syms : List (String × BitVec 64) := [])
    (dmem : DataMem := ∅) (texts : List String := []) (decls : Decls := {}) : State :=
  let base : Int64 := Int64.ofNat (0x100000 * (tid + 1))
  let codeCells : List (Directive × Nat) := prog.map fun d => (d, match d with | .label _ => 0 | _ => 1)
  let codeLen := (codeCells.map (·.2)).sum
  let pad (n : Nat) : Directive × Nat := (.byteArray (.mk #[]), n)
  let (cells, _) := syms.foldl (init := (codeCells, base.toBitVec.toNat + codeLen)) fun (cells, cur) (x, a) =>
    (cells ++ [pad (a.toNat - cur), (.label x, 0)], a.toNat)
  let exe : _root_.Executable := (base, cells)
  let instrs := prog.filter fun d => match d with | .label _ => false | _ => true
  { exe, endPc := base + Int64.ofNat codeLen, st := ({ regs, dmem }, base), decls,
    showPc := fun pc =>
      let i := (pc - base).toBitVec.toNat
      match texts[i]?, instrs[i]? with
      | some t, _ => t | none, some d => toString (repr d) | none, none => s!"pc={pc}" }

def deps (s : State) : InstrDeps RegId :=
  match s.directive with
  | some d => _root_.Directive.deps d
  | none => {}

def regIdx : Reg64 → Fin 17
  | .rax => 0 | .rbx => 1 | .rcx => 2 | .rdx => 3 | .rsi => 4 | .rdi => 5 | .rsp => 6 | .rbp => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

def vecIdx : RegMm → Fin 32
  | .mm0 => 0 | .mm1 => 1 | .mm2 => 2 | .mm3 => 3 | .mm4 => 4 | .mm5 => 5 | .mm6 => 6
  | .mm7 => 7 | .mm8 => 8 | .mm9 => 9 | .mm10 => 10 | .mm11 => 11 | .mm12 => 12
  | .mm13 => 13 | .mm14 => 14 | .mm15 => 15 | .mm16 => 16 | .mm17 => 17 | .mm18 => 18
  | .mm19 => 19 | .mm20 => 20 | .mm21 => 21 | .mm22 => 22 | .mm23 => 23 | .mm24 => 24
  | .mm25 => 25 | .mm26 => 26 | .mm27 => 27 | .mm28 => 28 | .mm29 => 29 | .mm30 => 30
  | .mm31 => 31

/-- The general registers, the flags, then the 32 vector registers. -/
def regIndex : RegId → Fin 49
  | .r r => (regIdx r).castLE (by decide)
  | .rflags => 16
  | .v r => (vecIdx r).natAdd 17

def isa : ISA where
  State := State
  RegId := RegId
  numRegs := 49
  regIndex := regIndex
  exec := exec
  deps := deps
  beqState a b := a.st == b.st
  hashState s := mixHash (hash s.st.1.regs) (mixHash (hash s.st.1.status) (hash s.st.2))
  showInstr s := s.showPc s.st.2

end Kraken.Promising.X64
