/-
The AArch64 instance of the Promising layer's `ISA` interface.

A thread state is Kraken's `MachineState` (registers, flags, private `dmem`,
pc) together with the thread's executable and its end address. One
instruction is `Executable.step`; its `Effects` tree is translated to an
`EvTree`, with the plain `nonmem_*` effects as plain accesses and the
`sync_*`/`rmw`/`fence` effects as what they say. The register dependencies
are `Directive.deps` of the directive at the pc.
-/
import Kraken.AArch64.Semantics
import Kraken.AArch64.LSE2
import Kraken.AArch64.Deps
import Kraken.Promising.Machine

namespace Kraken.Promising.AArch64

/-- A thread: the program, where it stops, and the machine state. -/
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

/-- Is a pair access of two `w`-sized halves at `addr` one declared location, i.e.
is there a declaration at `addr` of `2 * w.bytes` bytes (`__int128` for an `X`
pair, a 64-bit integer for a `W` pair)? Then `toEv` performs the pair as one
access of that location, single-copy atomic (see `toEv`). -/
def pairIsOneLoc (ds : Decls) (addr : BitVec 64) (w : MemWidth) : Bool :=
  ds.locs.any fun l => l.addr == addr && l.bytes == 2 * w.bytes

/-- The `CASP` event tree: the two halves are two `rmw`s of kind `k`, one per
half, each of which writes its new value iff its own half matches. herd
(`AArch64Sem.ml`, `casp`) performs the reads `R1`, `R2` and then, on a match of
both halves, the writes `W1`, `W2`, with the writes depending on both reads and
no further order among the four (the halves are not single-copy atomic as a
pair, unlike `LDXP`/`STXP`: `casp` combines them with `>>|`, not `>>||`). The
Promising thread processes an instruction's events one after the other, which
orders the first half before the second (an acquire read or an acquire-release
write orders what follows it); to stay no stronger than herd, both orders are
explored (`rev`). The outcome is chosen up front (`succ`): the success branch
writes each half on its match and is dead (`choose 0`) when a half
mismatches; the failure branch only reads (like a failed `CAS`: an `rmw` with
no write) and is dead when both halves match. -/
def caspTree {σ : Type} (ds : Decls) (k : RmwKind) (addr : BitVec 64) {w : MemWidth}
    (cmp1 cmp2 new1 new2 : w.type) (ret : w.type → w.type → EvTree σ) : EvTree σ :=
  let half (a : BitVec 64) (op : w.type → Option w.type) (r : w.type → EvTree σ) : EvTree σ :=
    .access ds a w.bytes fun l =>
      .rmw k false l (fun old => (op (old.setWidth w.bits)).map (·.setWidth 128))
        fun old => r (old.setWidth w.bits)
  let cas (cmp new : w.type) (old : w.type) : Option w.type := if old == cmp then some new else none
  let guard (b : Bool) (t : EvTree σ) : EvTree σ := if b then t else .choose 0 nofun
  .choose 2 fun succ => .choose 2 fun rev =>
    let op1 := if succ.val == 1 then cas cmp1 new1 else fun _ => none
    let op2 := if succ.val == 1 then cas cmp2 new2 else fun _ => none
    let fin (o1 o2 : w.type) : EvTree σ :=
      guard ((o1 == cmp1 && o2 == cmp2) == (succ.val == 1)) (ret o1 o2)
    if rev.val == 0 then
      half addr op1 fun o1 => half (addr + w.bytesv) op2 fun o2 => fin o1 o2
    else
      half (addr + w.bytesv) op2 fun o2 => half addr op1 fun o1 => fin o1 o2

/-- `Effects` to `EvTree`, resolving every access against `ds`. Memory values
travel zero-extended to 128 bits (`Val`); a load truncates to the access
width.

The pair effects (`LDXP`/`STXP`/`CASP`, both halves outside `dmem`): herd
performs `LDXP`/`STXP` as two accesses that form one single-copy-atomic group
(`>>||`, herd's `sca` classes). When the pair is one declared location
(`pairIsOneLoc`: a 16-byte location for an `X` pair) this is exactly one access
of that location, the value's low half being the first register's. Otherwise
(the halves are two locations, e.g. two elements of an array) the pair is two
accesses, the first carrying the exclusive; this misses herd's
single-copy atomicity of the two halves and the exclusivity of the second, so it
is weaker than herd (`Kraken/Litmus/KNOWN_GAPS.md`). `CASP` is `caspTree`. -/
def toEv (ds : Decls) : Effects → EvTree MachineState
  | .done a => .done a
  | .unimplemented msg => .fault msg
  | .unaligned_sp _ => .fault "unaligned sp"
  | .nonmem_load dmem addr w ret =>
    .access ds addr w.bytes fun l => .load .plain false l fun v => toEv ds (ret (v.setWidth w.bits) dmem)
  | @Effects.nonmem_store dmem addr w v ret =>
    .access ds addr w.bytes fun l => .store .plain false l (v.setWidth 128) fun _ => toEv ds (ret dmem)
  | .sync_load k xcl dmem addr w ret =>
    .access ds addr w.bytes fun l => .load k xcl l fun v => toEv ds (ret (v.setWidth w.bits) dmem)
  | @Effects.sync_store k xcl dmem addr w v ret =>
    .access ds addr w.bytes fun l => .store k xcl l (v.setWidth 128) fun ok => toEv ds (ret ok dmem)
  | .rmw k noRet dmem addr w op ret =>
    .access ds addr w.bytes fun l =>
      .rmw k noRet l (fun old => (op (old.setWidth w.bits)).map (·.setWidth 128))
        fun old => toEv ds (ret (old.setWidth w.bits) dmem)
  | .sync_load_pair k xcl dmem addr w ret =>
    if pairIsOneLoc ds addr w then
      .access ds addr (2 * w.bytes) fun l => .load k xcl l fun v =>
        toEv ds (ret (v.setWidth w.bits) ((v >>> w.bits).setWidth w.bits) dmem)
    else
      .access ds addr w.bytes fun l1 => .load k xcl l1 fun v1 =>
        .access ds (addr + w.bytesv) w.bytes fun l2 => .load k false l2 fun v2 =>
          toEv ds (ret (v1.setWidth w.bits) (v2.setWidth w.bits) dmem)
  | @Effects.sync_store_pair k xcl dmem addr w v1 v2 ret =>
    if pairIsOneLoc ds addr w then
      .access ds addr (2 * w.bytes) fun l =>
        .store k xcl l ((v2.setWidth 128 <<< w.bits) ||| v1.setWidth 128) fun ok => toEv ds (ret ok dmem)
    else
      .access ds addr w.bytes fun l1 => .store k xcl l1 (v1.setWidth 128) fun ok =>
        if ok then
          .access ds (addr + w.bytesv) w.bytes fun l2 => .store k false l2 (v2.setWidth 128) fun _ =>
            toEv ds (ret true dmem)
        else toEv ds (ret false dmem)
  | @Effects.rmw_pair k dmem addr _ cmp1 cmp2 new1 new2 ret =>
    caspTree ds k addr cmp1 cmp2 new1 new2 fun o1 o2 => toEv ds (ret o1 o2 dmem)
  | .fence k ok => .fence k fun _ => toEv ds (ok ())
  | @Effects.undefined _ inst ret =>
    match inst with
    | .bool => .choose 2 fun i => toEv ds (ret (i.val == 1))
    | .bitvec _ => .fault "undefined register value"
    | .statusFlags => .fault "undefined flags"
  | .require_read_access _ _ ok => toEv ds (ok ())
  | .require_write_access _ _ ok => toEv ds (ok ())
  | .require_exec_access _ ok => toEv ds (ok ())

/-- The directive at the pc, past any labels there. -/
def State.directive (s : State) : Option Directive :=
  ((s.exe.directivesFromAddress s.st.2).dropWhile (fun (d, _) => match d with | .label _ => true | _ => false))
    |>.head? |>.map (·.1)

def exec (s : State) : Option (EvTree State) :=
  if s.st.2 == s.endPc || s.directive.isNone then none
  else some <| (toEv s.decls (_root_.Executable.step s.exe s.st fun s' => .done s')).map fun st => { s with st }

/-- A thread state for a parsed program: laid out at `0x100000 * (tid + 1)`,
4 bytes per instruction, halting after the last one; `showPc` prints the
directive. -/
def mkState (tid : Nat) (prog : Program) (regs : Reg64s) (dmem : DataMem := ∅)
    (texts : List String := []) (decls : Decls := {}) : State :=
  let base : Int64 := Int64.ofNat (0x100000 * (tid + 1))
  let layout : _root_.Layout := { start := base, size i := (prog[i]?.map Directive.fakeSize).getD 0 }
  let exe : _root_.Executable := layout prog
  let endPc := base + Int64.ofNat (prog.map Directive.fakeSize).sum
  let instrs := prog.filter fun d => match d with | .label _ => false | _ => true
  { exe, endPc, st := ({ regs, dmem }, base), decls,
    showPc := fun pc =>
      let i := ((pc - base).toBitVec.toNat) / 4
      match texts[i]?, instrs[i]? with
      | some t, _ => t | none, some d => toString (repr d) | none, none => s!"pc={pc}" }

/-- The dependencies of the instruction at the pc. The `CSEL` family is a
pick: only the source the condition selects is a data dependency of the
result (`CSINC` etc. with a false condition depend on their second source).
The condition is evaluated on the current flags, which is what the
architecture's "intrinsic" dependency through the selected value amounts to.

The data registers of a store exclusive (`STXR` in all widths, `STXP`; with
or without release) are no dependency at all: herd reads them with
`read_reg_ord`, not `read_reg_data` (`AArch64Sem.ml`, `stxr` and `stxp`), so
its writes are not `data`-after the loads that produced those registers (an
`STLXR`/`STLXP` is still ordered after every earlier access by its release).
`Operation.deps` keeps them in `dataRegs`/`dataRegsPer`, where the coverage
test (`Kraken/AArch64/DepsTests.lean`) checks that they over-approximate the
registers read; only the dependencies the memory model sees drop them.
`corpus/aarch64-pairs/hand/LB+fdata-stx*`. -/
def deps (s : State) : InstrDeps RegId :=
  match s.directive with
  | some d =>
    let d0 := _root_.Directive.deps d
    match d with
    | .instr i =>
      match i.operation with
      | .CSEL _ a b c | .CSINC _ a b c | .CSINV _ a b c | .CSNEG _ a b c =>
        { d0 with dataRegs := if c.interp s.st.1.status then a.regs else b.regs }
      | .STXR .. | .STXP .. => { d0 with dataRegs := [], dataRegsPer := [] }
      | _ => d0
    | _ => d0
  | none => {}

def regIndex : RegId → Fin 33
  | .x n => ⟨n.val, by omega⟩
  | .sp => 31
  | .nzcv => 32

def isa : ISA where
  State := State
  RegId := RegId
  numRegs := 33
  regIndex := regIndex
  exec := exec
  deps := deps
  beqState a b := a.st == b.st
  hashState s := mixHash (hash s.st.1.regs) (mixHash (hash s.st.1.status) (hash s.st.2))
  showInstr s := s.showPc s.st.2

/-! ### Tests of the pair translation -/

/-- Every run of an event tree, as text, one line per event: loads and RMWs
read `vals` in order (then `0`), stores succeed, and every branch of a
`choose` is shown, prefixed `[i]`. A leaf `unimplemented msg` of the effect
tree shows as `fault: msg`, which the tests use to print what the
continuation received. -/
partial def showRuns {σ : Type} (vals : List Val) : EvTree σ → List String
  | .done _ => ["done"]
  | .fault m => [s!"fault: {m}"]
  | .choose 0 _ => ["dead"]
  | .choose n k => (List.finRange n).flatMap fun i => (showRuns vals (k i)).map (s!"[{i}] " ++ ·)
  | .load _ x l ret =>
    s!"load{if x then " xcl" else ""} 0x{l.addr.toHex}/{l.bytes} = 0x{(vals.headD 0).toHex}" ::
      showRuns vals.tail (ret (vals.headD 0))
  | .store _ x l v ret => s!"store{if x then " xcl" else ""} 0x{l.addr.toHex}/{l.bytes} := 0x{v.toHex}" ::
      showRuns vals (ret true)
  | .rmw _ _ l op ret =>
    let new := match op (vals.headD 0) with | some v => s!"0x{v.toHex}" | none => "no write"
    s!"rmw 0x{l.addr.toHex}/{l.bytes} old 0x{(vals.headD 0).toHex} → {new}" ::
      showRuns vals.tail (ret (vals.headD 0))
  | .fence _ ret => "fence" :: showRuns vals (ret ())

/-- `showRuns`, one line each. -/
def printRuns {σ : Type} (vals : List Val) (t : EvTree σ) : IO Unit :=
  for l in showRuns vals t do IO.println l

private def got2 {n : Nat} (a b : BitVec n) : Effects := .unimplemented s!"got 0x{a.toHex} 0x{b.toHex}"
private def okE (b : Bool) : Effects := .unimplemented s!"ok {b}"
private def i128 : Decls := { locs := [⟨0x1000, 16⟩] }

-- `LDXP` of two halves that are separate locations: two accesses, the
-- exclusive on the first.
/--
info: load xcl 0x0000000000001000/8 = 0x00000000000000000000000000000001
load 0x0000000000001008/8 = 0x00000000000000000000000000000002
fault: got 0x0000000000000001 0x0000000000000002
-/
#guard_msgs in
#eval printRuns [1, 2] (toEv {} (.sync_load_pair .plain true ∅ 0x1000 .W64 fun a b _ => got2 a b))

-- On a declared 16-byte location: one exclusive access, the first register
-- getting the low half.
/--
info: load xcl 0x0000000000001000/16 = 0x00000000000000020000000000000001
fault: got 0x0000000000000001 0x0000000000000002
-/
#guard_msgs in
#eval printRuns [0x2_0000000000000001] (toEv i128 (.sync_load_pair .acq true ∅ 0x1000 .W64 fun a b _ => got2 a b))

-- `STXP`: two accesses (the second plain, after the first succeeded), or one
-- 16-byte store of `v2 : v1`.
/--
info: store xcl 0x0000000000001000/8 := 0x00000000000000000000000000000001
store 0x0000000000001008/8 := 0x00000000000000000000000000000002
fault: ok true
-/
#guard_msgs in
#eval printRuns [] (toEv {} (.sync_store_pair .plain true ∅ 0x1000 (w := .W64) 1 2 fun ok _ => okE ok))
/--
info: store xcl 0x0000000000001000/16 := 0x00000000000000020000000000000001
fault: ok true
-/
#guard_msgs in
#eval printRuns [] (toEv i128 (.sync_store_pair .rel true ∅ 0x1000 (w := .W64) 1 2 fun ok _ => okE ok))

-- A `W` pair on a declared 8-byte location: one access.
/--
info: store xcl 0x0000000000001000/8 := 0x00000000000000000000000200000001
fault: ok true
-/
#guard_msgs in
#eval printRuns [] (toEv { locs := [⟨0x1000, 8⟩] } (.sync_store_pair .plain true ∅ 0x1000 (w := .W32) 1 2 fun ok _ => okE ok))

-- `CASP` with comparands `(1, 2)` and new values `(3, 4)`: branch `[1]` is
-- success, `[0]` failure, the second index the order of the halves. The reads
-- return `1` then `2` whatever the address, so in order `[0]` the success
-- branch is live and the failure branch dead, and in order `[1]` (the high
-- half first, reading `1`) the reverse: the failure branch returns the values
-- read, by register, and writes nothing.
/--
info: [0] [0] rmw 0x0000000000001000/8 old 0x00000000000000000000000000000001 → no write
[0] [0] rmw 0x0000000000001008/8 old 0x00000000000000000000000000000002 → no write
[0] [0] dead
[0] [1] rmw 0x0000000000001008/8 old 0x00000000000000000000000000000001 → no write
[0] [1] rmw 0x0000000000001000/8 old 0x00000000000000000000000000000002 → no write
[0] [1] fault: got 0x0000000000000002 0x0000000000000001
[1] [0] rmw 0x0000000000001000/8 old 0x00000000000000000000000000000001 → 0x00000000000000000000000000000003
[1] [0] rmw 0x0000000000001008/8 old 0x00000000000000000000000000000002 → 0x00000000000000000000000000000004
[1] [0] fault: got 0x0000000000000001 0x0000000000000002
[1] [1] rmw 0x0000000000001008/8 old 0x00000000000000000000000000000001 → no write
[1] [1] rmw 0x0000000000001000/8 old 0x00000000000000000000000000000002 → no write
[1] [1] dead
-/
#guard_msgs in
#eval printRuns [1, 2] (toEv {} (.rmw_pair .acqRel ∅ 0x1000 (w := .W64) 1 2 3 4 fun a b _ => got2 a b))

/-! ## FEAT_LSE2 (opt-in)

With FEAT_LSE2 (Armv8.4), an `LDP`/`STP` of two `X` registers whose access is
aligned to 16 bytes (to Normal memory) is single-copy atomic. herd7 has no such
option (its `LDP`/`STP` are always two accesses), so `isaLSE2` is a Kraken-only
model of FEAT_LSE2 hardware, stronger than herd's AArch64 model; it is off by
default (`isa` is the default ISA everywhere, and no regression corpus uses
it) and selected by `krakenlitmus_aarch64 -lse2`. `isaLSE2` performs such an
`LDP`/`STP` as `MachineData.loadPairK`/`storePairK` (`.plain`, not exclusive),
which `toEv` makes one 16-byte access exactly when the address is a declared
16-byte location (`pairIsOneLoc`) and the two plain accesses of `LDP`/`STP`
otherwise. A `CASP` of `X` registers is translated by `toEvCASP`: one 16-byte
`rmw` on a 16-aligned declared 16-byte location (Arm ARM B2.2.1 makes `CASP`
single-copy atomic at the size of the pair; gating it on `isaLSE2` is a
modelling choice that keeps `isa` herd-faithful), `caspTree` otherwise.
Every other instruction, and an unaligned `LDP`/`STP`, is `exec`.
The link theorems `SeqLinkAArch64` and `EnvWPAArch64` are about `isa`;
`isaLSE2` is linked to the FEAT_LSE2 environment logic
(`Kraken/AArch64/EnvLSE2.lean`) by `env_link_halt_lse2`
(`Kraken/Promising/EnvLSE2AArch64.lean`), for threads whose `decls` are the
shared layout's locations (`declsOf L`). -/

/-- The cell at the pc, past any labels there: the directive and its size. -/
def State.cell (s : State) : Option (Directive × Nat) :=
  ((s.exe.directivesFromAddress s.st.2).dropWhile (fun (d, _) => match d with | .label _ => true | _ => false))
    |>.head?

/-- The `Effects` of the instruction at the pc under FEAT_LSE2, if it is a
16-byte-aligned `LDP`/`STP` of two `X` registers; `none` otherwise. The
reading is `Directive.interpLSE2?` (`Kraken/AArch64/LSE2.lean`, shared with the
environment logic), run over the cell's range and continuing at the address
behind it. -/
def lse2Effects (s : State) : Option Effects :=
  letI := _root_.Executable.labels s.exe
  let (st, pc) := s.st
  match s.cell with
  | some (d, z) => d.interpLSE2? st (.mk pc (pc + .ofNat z)) fun s' => .done (s', pc + .ofNat z)
  | none => none

/-- Is the declaration that `Decls.resolve` finds at `addr` a 16-byte location?
For declarations with one location per address this is
`pairIsOneLoc ds addr .W64`. -/
def caspIsOneLoc (ds : Decls) (addr : BitVec 64) : Bool :=
  (ds.locs.find? (·.addr == addr)).any (·.bytes == 16)

/-- `toEv` under FEAT_LSE2 for the effects of a `CASP` of two `X` registers:
an `X` pair `rmw_pair` (after the fetch and access checks) whose address is 16-aligned
and a declared 16-byte location (`caspIsOneLoc`) is **one** 16-byte `rmw` of
kind `k`, single-copy atomic (Arm ARM B2.2.1): it reads 128 bits, the low half
being the first register's, and on a match of both halves writes `new2 : new1`;
on a mismatch it writes nothing (as a failed `CAS`). Everything else is
`toEv`. -/
def toEvCASP (ds : Decls) : Effects → EvTree MachineState
  | .require_read_access _ _ ok => toEvCASP ds (ok ())
  | .require_write_access _ _ ok => toEvCASP ds (ok ())
  | .require_exec_access _ ok => toEvCASP ds (ok ())
  | @Effects.rmw_pair k dmem addr .W64 cmp1 cmp2 new1 new2 ret =>
    if addr % 16 == 0 && caspIsOneLoc ds addr then
      .access ds addr 16 fun l =>
        .rmw k false l
          (fun old => if old.setWidth 64 == cmp1 && (old >>> 64).setWidth 64 == cmp2 then
            some ((new2.setWidth 128 <<< 64) ||| new1.setWidth 128) else none)
          fun old => toEv ds (ret (old.setWidth 64) ((old >>> 64).setWidth 64) dmem)
    else toEv ds (.rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret)
  | e => toEv ds e

/-- Is the directive a `CASP` of two `X` registers? -/
def _root_.Directive.isCaspX : Directive → Bool
  | .instr ⟨.W64, .CASP ..⟩ => true
  | _ => false

/-- A `CASP` of `X` registers has no `interpLSE2?` reading. -/
theorem _root_.Directive.interpLSE2?_none_of_isCaspX [Labels] {d : Directive} (hx : d.isCaspX = true)
    (s : MachineData) (p : Std.Rco Int64) (next : MachineData → Effects) : d.interpLSE2? s p next = none := by
  unfold Directive.isCaspX at hx
  split at hx
  · rfl
  · cases hx

/-- Is the directive at the pc a `CASP` of two `X` registers? -/
def State.isCaspX (s : State) : Bool :=
  match s.directive with
  | some d => d.isCaspX
  | none => false

def execLSE2 (s : State) : Option (EvTree State) :=
  if s.st.2 == s.endPc || s.directive.isNone then none
  else match lse2Effects s with
    | some e => some <| (toEv s.decls e).map fun st => { s with st }
    | none =>
      if s.isCaspX then
        some <| (toEvCASP s.decls (_root_.Executable.step s.exe s.st fun s' => .done s')).map fun st => { s with st }
      else exec s

/-- `deps`, except that an `STP` that `isaLSE2` performs as one 16-byte store
depends on both data registers in that store (no per-store split). -/
def depsLSE2 (s : State) : InstrDeps RegId :=
  let d := deps s
  letI := _root_.Executable.labels s.exe
  let (st, pc) := s.st
  match s.directive with
  | some (.instr ⟨.W64, .STP _ _ dst⟩) =>
    let addr := (dst.eval st (.mk pc (pc + 4))).1
    if addr % 16 == 0 && pairIsOneLoc s.decls addr .W64 then { d with dataRegsPer := [] } else d
  | _ => d

/-- The AArch64 ISA with FEAT_LSE2's single-copy-atomic 16-byte `LDP`/`STP`. -/
def isaLSE2 : ISA := { isa with exec := execLSE2, deps := depsLSE2 }

/-! The non-exclusive pair effects `lse2Effects` emits: one 16-byte access at
a declared 16-byte location, two 8-byte accesses otherwise. -/

/--
info: load 0x0000000000001000/16 = 0x00000000000000020000000000000001
fault: got 0x0000000000000001 0x0000000000000002
-/
#guard_msgs in
#eval printRuns [0x2_0000000000000001] (toEv i128 (.sync_load_pair .plain false ∅ 0x1000 .W64 fun a b _ => got2 a b))

/--
info: store 0x0000000000001000/16 := 0x00000000000000020000000000000001
fault: ok true
-/
#guard_msgs in
#eval printRuns [] (toEv i128 (.sync_store_pair .plain false ∅ 0x1000 (w := .W64) 1 2 fun ok _ => okE ok))

/--
info: store 0x0000000000001000/8 := 0x00000000000000000000000000000001
store 0x0000000000001008/8 := 0x00000000000000000000000000000002
fault: ok true
-/
#guard_msgs in
#eval printRuns [] (toEv {} (.sync_store_pair .plain false ∅ 0x1000 (w := .W64) 1 2 fun ok _ => okE ok))

/-! `CASP` of `X` registers under FEAT_LSE2 (`toEvCASP`), comparands `(1, 2)`,
new values `(3, 4)`: on a declared 16-byte location one 16-byte `rmw` that
writes `4 : 3` iff both halves match (success), and writes nothing otherwise
(both halves or only one mismatching); the registers get both old halves. -/

/--
info: rmw 0x0000000000001000/16 old 0x00000000000000020000000000000001 → 0x00000000000000040000000000000003
fault: got 0x0000000000000001 0x0000000000000002
-/
#guard_msgs in
#eval printRuns [0x2_0000000000000001] (toEvCASP i128 (.rmw_pair .acqRel ∅ 0x1000 (w := .W64) 1 2 3 4 fun a b _ => got2 a b))

/--
info: rmw 0x0000000000001000/16 old 0x00000000000000060000000000000005 → no write
fault: got 0x0000000000000005 0x0000000000000006
-/
#guard_msgs in
#eval printRuns [0x6_0000000000000005] (toEvCASP i128 (.rmw_pair .acqRel ∅ 0x1000 (w := .W64) 1 2 3 4 fun a b _ => got2 a b))

/--
info: rmw 0x0000000000001000/16 old 0x00000000000000060000000000000001 → no write
fault: got 0x0000000000000001 0x0000000000000006
-/
#guard_msgs in
#eval printRuns [0x6_0000000000000001] (toEvCASP i128 (.rmw_pair .plain ∅ 0x1000 (w := .W64) 1 2 3 4 fun a b _ => got2 a b))

-- Through `execLSE2`: `caspal x2, x3, x4, x5, [x1]` at `0x1000` with `(x2, x3)
-- = (1, 2)` and `(x4, x5) = (3, 4)`: one 16-byte `rmw` on the declared 16-byte
-- location, and `caspTree`'s two 8-byte halves on a 16-byte location the
-- address does not start (the low half overlaps it: a mixed-size fault).
private def caspSt (ds : Decls) : State :=
  mkState 0 [.instr ⟨.W64, .CASP .acqRel .X2 .X3 .X4 .X5 .X1⟩]
    (((((({} : Reg64s).setXReg .X1 0x1000).setXReg .X2 1).setXReg .X3 2).setXReg .X4 3).setXReg .X5 4) (decls := ds)
/--
info: rmw 0x0000000000001000/16 old 0x00000000000000020000000000000001 → 0x00000000000000040000000000000003
done
-/
#guard_msgs in
#eval (execLSE2 (caspSt i128)).forM (printRuns [0x2_0000000000000001])
/--
info: [0] [0] fault: mixed-size access: 8 bytes at 0x0000000000001000 overlaps the location of 16 bytes at 0x0000000000000ff8
[0] [1] rmw 0x0000000000001008/8 old 0x00000000000000020000000000000001 → no write
[0] [1] fault: mixed-size access: 8 bytes at 0x0000000000001000 overlaps the location of 16 bytes at 0x0000000000000ff8
[1] [0] fault: mixed-size access: 8 bytes at 0x0000000000001000 overlaps the location of 16 bytes at 0x0000000000000ff8
[1] [1] rmw 0x0000000000001008/8 old 0x00000000000000020000000000000001 → no write
[1] [1] fault: mixed-size access: 8 bytes at 0x0000000000001000 overlaps the location of 16 bytes at 0x0000000000000ff8
-/
#guard_msgs in
#eval (execLSE2 (caspSt { locs := [⟨0xff8, 16⟩] })).forM (printRuns [0x2_0000000000000001])

-- Without a 16-byte declaration, or with `W` registers, it is `caspTree`.
/--
info: true
-/
#guard_msgs in
#eval showRuns [1, 2] (toEvCASP {} (.rmw_pair .acqRel ∅ 0x1000 (w := .W64) 1 2 3 4 fun a b _ => got2 a b)) ==
  showRuns [1, 2] (toEv {} (.rmw_pair .acqRel ∅ 0x1000 (w := .W64) 1 2 3 4 fun a b _ => got2 a b))
/--
info: true
-/
#guard_msgs in
#eval showRuns [1, 2] (toEvCASP { locs := [⟨0x1000, 8⟩] } (.rmw_pair .acq ∅ 0x1000 (w := .W32) 1 2 3 4 fun a b _ => got2 a b)) ==
  showRuns [1, 2] (toEv { locs := [⟨0x1000, 8⟩] } (.rmw_pair .acq ∅ 0x1000 (w := .W32) 1 2 3 4 fun a b _ => got2 a b))

end Kraken.Promising.AArch64
