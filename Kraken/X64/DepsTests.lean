/-
Coverage test for `Operation.deps` (`Kraken/X64/Deps.lean`).

There is no lemma relating `Operation.deps` to `Operation.interp`; this file
checks by *testing* that the dependency table over-approximates what the
interpreter actually does with the registers, per operation constructor:

- **Writes.** Every register whose value differs between the input and the
  output state (the flags included) is in `loadDefs ∪ statusDefs ∪ defs`.
- **Reads.** For every register `r` not in `addrRegs ∪ dataRegs ∪ condRegs`,
  perturbing `r` in the input leaves the outcome — registers, flags, data
  memory, the branch target, and the trace of unmapped-memory events —
  unchanged. If `r` is not a declared write, it is masked in the comparison;
  if it is, the written value must not change (a write that merges the old
  value, like a 16-bit `mov`, is a read).

Each operation runs from a baseline state whose registers point into a mapped
512-byte region (so loads and stores hit `dmem`) and from a few pseudo-random
states (deterministic `StdGen`); every `undefined Bool` is resolved both ways,
other `undefined`s to a fixed value; `require_*` and `fence` are followed.
Unmapped accesses are answered with a value derived from the address and
recorded in the outcome, so a moved footprint shows up as a changed trace.

The constructor-coverage check compares the constructors reached by the
operation lists below against the constructor lists of `Operation` and
`AvxOperation` from the environment, so a new constructor fails the test until
it is added here. Vector registers are `RegId.v` of their `zmm`, and register
values are compared as 512-bit vectors (a general register or the flags is
zero-extended).
-/
import Kraken.X64.Semantics
import Kraken.X64.Deps

namespace DepsTests

open Kraken (InstrDeps)

instance : Labels where label _ := 0x8000
instance : AddressSize where address_size := .W64

/-! ## Register access by `RegId` -/

def allReg64s : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def allRegMms : List RegMm :=
  [.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7, .mm8, .mm9, .mm10, .mm11, .mm12, .mm13, .mm14,
    .mm15, .mm16, .mm17, .mm18, .mm19, .mm20, .mm21, .mm22, .mm23, .mm24, .mm25, .mm26, .mm27,
    .mm28, .mm29, .mm30, .mm31]

def allRegIds : List RegId := allReg64s.map RegId.r ++ [.rflags] ++ allRegMms.map RegId.v

/-- The registers perturbed for a general-purpose operation: every general
register, the flags, and a few vector registers (perturbing all 32 for each of
those operations would multiply the run time for little gain). -/
def gprReadIds : List RegId := allReg64s.map RegId.r ++ [.rflags, .v .mm0, .v .mm15, .v .mm31]

def flagsToUInt64 (f : StatusFlags) : UInt64 :=
  f.cf.toUInt64 ||| f.pf.toUInt64 <<< 1 ||| f.af.toUInt64 <<< 2 ||| f.zf.toUInt64 <<< 3
    ||| f.sf.toUInt64 <<< 4 ||| f.of.toUInt64 <<< 5

def flagsOfUInt64 (v : UInt64) : StatusFlags :=
  { cf := v &&& 1 != 0, pf := v &&& 2 != 0, af := v &&& 4 != 0, zf := v &&& 8 != 0,
    sf := v &&& 16 != 0, of := v &&& 32 != 0 }

/-- A register value: 512 bits, enough for a `zmm`. -/
abbrev RegVal := BitVec 512

def getReg (s : MachineData) : RegId → RegVal
  | .r r => (s.regs.get64 r).setWidth 512
  | .rflags => (flagsToUInt64 s.status).toBitVec.setWidth 512
  | .v r => s.zmms.get512 r

def setReg (s : MachineData) : RegId → RegVal → MachineData
  | .r r, v => { s with regs := s.regs.set64 r (v.setWidth 64) }
  | .rflags, v => { s with status := flagsOfUInt64 (UInt64.ofBitVec (v.setWidth 64)) }
  | .v r, v => { s with zmms := s.zmms.set512 r v }

/-! ## Running one operation to all of its outcomes -/

/-- The result of one run: the final machine data, the pc (`fallthrough` if the
operation did not jump), and the trace of effects that were not served from
`dmem`, in order. -/
structure Outcome where
  st : MachineData
  pc : Int64
  events : List String
  deriving BEq

def fallthrough : Int64 := 0x4004

/-- The value an unmapped load of `w` bytes at `addr` returns. -/
def unmappedVal (addr : BitVec 64) (w : Width) : w.type :=
  (hash addr).toBitVec.setWidth w.bits

partial def collect (e : Effects) (events : List String) : List Outcome :=
  match e with
  | .done (s, pc) => [{ st := s, pc, events := events.reverse }]
  | .unimplemented msg => [{ st := {}, pc := 0, events := (s!"unimplemented {msg}" :: events).reverse }]
  | .gp_unaligned addr w => [{ st := {}, pc := 0, events := (s!"gp_unaligned {addr.toNat} {w}" :: events).reverse }]
  | .nonmem_load dmem addr w ret =>
    collect (ret (unmappedVal addr w) dmem) (s!"load {addr.toNat} {w}" :: events)
  | @Effects.nonmem_store dmem addr w v ret =>
    collect (ret dmem) (s!"store {addr.toNat} {w} {v.toNat}" :: events)
  | .sync_load k xcl dmem addr w ret =>
    collect (ret (unmappedVal addr w) dmem) (s!"sync_load {repr k} {xcl} {addr.toNat} {w}" :: events)
  | @Effects.sync_store k xcl dmem addr w v ret =>
    let ev := s!"sync_store {repr k} {xcl} {addr.toNat} {w} {v.toNat}"
    if xcl then collect (ret false dmem) (s!"{ev} fail" :: events) ++ collect (ret true dmem) (s!"{ev} ok" :: events)
    else collect (ret true dmem) (ev :: events)
  | .rmw k dmem addr w op ret =>
    let old := unmappedVal addr w
    let new := match op old with | some n => s!"{n.toNat}" | none => "none"
    collect (ret old dmem) (s!"rmw {repr k} {addr.toNat} {w} {old.toNat} -> {new}" :: events)
  | .fence k ok => collect (ok ()) (s!"fence {repr k}" :: events)
  | .nonmem_load_avx atomic dmem addr w ret =>
    collect (ret ((hash addr).toBitVec.setWidth w.bits) dmem)
      (s!"load_avx {atomic} {addr.toNat} {w.bytes}" :: events)
  | @Effects.nonmem_store_avx atomic dmem addr w v ret =>
    collect (ret dmem) (s!"store_avx {atomic} {addr.toNat} {w.bytes} {v.toNat}" :: events)
  | .rmw16 k dmem addr op ret =>
    let old : BitVec 128 := (hash addr).toBitVec.setWidth 128
    let new := match op old with | some n => s!"{n.toNat}" | none => "none"
    collect (ret old dmem) (s!"rmw16 {repr k} {addr.toNat} {old.toNat} -> {new}" :: events)
  | .require_read_access_avx _ _ _ ok | .require_write_access_avx _ _ _ ok => collect (ok ()) events
  | .require_read_access _ _ ok | .require_write_access _ _ ok | .require_exec_access _ ok =>
    collect (ok ()) events
  | @Effects.undefined _ inst ret =>
    match inst with
    | .bool => collect (ret false) ("undefined false" :: events) ++ collect (ret true) ("undefined true" :: events)
    | .bitvec w => collect (ret (NondetSupportingType.from_hash (α := w.type) 0x5EED)) ("undefined bitvec" :: events)
    | .avx_bitvec w => collect (ret (NondetSupportingType.from_hash (α := w.type) 0x5EED)) ("undefined avx" :: events)
    | .statusFlags => collect (ret (NondetSupportingType.from_hash (α := StatusFlags) 0x5EED)) ("undefined flags" :: events)

def run {w} (op : Operation w) (s : MachineData) : List Outcome :=
  let p : Std.Rco Int64 := .mk 0x4000 fallthrough
  collect (op.interp p s (fun s => .done (s, fallthrough)) (fun pc s => .done (s, pc))) []

def runAvx {w} (op : AvxOperation w) (s : MachineData) : List Outcome :=
  let p : Std.Rco Int64 := .mk 0x4000 fallthrough
  collect (op.interp p s (fun s => .done (s, fallthrough))) []

/-! ## States -/

def regionBase : Nat := 0x10000
def regionSize : Nat := 0x200

/-- The mapped region, filled with pseudo-random bytes. -/
def initMem (g : StdGen) : DataMem × StdGen :=
  (List.range (regionSize / 8)).foldl (init := ({}, g)) fun (m, g) i =>
    let (v, g) := randNat g 0 (2^64 - 1)
    (Mem.storeInt m (BitVec.ofNat 64 (regionBase + 8 * i)) 8 v, g)

/-- Every register points into the region (8-byte aligned, with room on both
sides for the displacements the operand list uses), `rsp` in its middle, flags clear. -/
def baseline (mem : DataMem) : MachineData :=
  let regs := (allReg64s.zipIdx).foldl (init := ({} : Reg64s)) fun regs (r, i) =>
    regs.set64 r (BitVec.ofNat 64 (regionBase + 0x40 + 8 * i))
  { regs := regs.set64 .rsp (BitVec.ofNat 64 (regionBase + 0x100)),
    status := ⟨false, false, false, false, false, false⟩, dmem := mem }

/-- A pseudo-random register value: half the time a pointer into the region,
otherwise a small or an arbitrary 64-bit value. `rsp` is always a pointer. -/
def randomReg (g : StdGen) (isSp : Bool) : UInt64 × StdGen :=
  let (k, g) := randNat g 0 3
  if isSp || k < 2 then
    let (off, g) := randNat g 3 0x1B
    ((regionBase + 16 * off).toUInt64, g)
  else if k == 2 then
    let (v, g) := randNat g 0 255
    (v.toUInt64, g)
  else
    let (v, g) := randNat g 0 (2^64 - 1)
    (v.toUInt64, g)

def randomState (mem : DataMem) (g : StdGen) : MachineData × StdGen :=
  let s0 : MachineData := { dmem := mem }
  allRegIds.foldl (init := (s0, g)) fun (s, g) r =>
    match r with
    | .rflags => let (v, g) := randNat g 0 63; (setReg s r (BitVec.ofNat _ v), g)
    | .r r64 => let (v, g) := randomReg g (r64 == .rsp); (setReg s r (v.toBitVec.setWidth _), g)
    | .v _ => let (v, g) := randNat g 0 (2^512 - 1); (setReg s r (BitVec.ofNat _ v), g)

/-! ## The checks -/

def readSet (d : InstrDeps RegId) : List RegId := d.addrRegs ++ d.dataRegs ++ d.condRegs
def writeSet (d : InstrDeps RegId) : List RegId := d.loadDefs ++ d.statusDefs ++ d.defs

def maskReg (o : Outcome) (r : RegId) : Outcome := { o with st := setReg o.st r 0 }

def isFault (o : Outcome) : Bool :=
  o.events.any fun e => e.startsWith "unimplemented" || e.startsWith "gp_unaligned"

/-- The violations of `deps` for the operation `run` runs from `s`, with a
perturbation value drawn from `g` per register in addition to the complement
of its value. -/
def checkState (name : String) (run : MachineData → List Outcome) (d : InstrDeps RegId)
    (s : MachineData) (g : StdGen) (perturbed : List RegId := allRegIds) : List String × StdGen :=
  let outs := run s
  let faults := if outs.any isFault then [s!"{name}: faulted: {outs.filter isFault |>.map (·.events)}"] else []
  -- Writes.
  let writes := outs.flatMap fun o =>
    allRegIds.filterMap fun r =>
      if getReg o.st r != getReg s r && !(writeSet d).contains r
      then some s!"{name}: {repr r} written but not in defs" else none
  -- Reads.
  let (reads, g) := perturbed.foldl (init := (([] : List String), g)) fun (acc, g) r =>
    if (readSet d).contains r then (acc, g) else
    let (rnd, g) : RegVal × StdGen := match r with
      | .rflags => let (v, g) := randNat g 0 63; (BitVec.ofNat _ v, g)
      | .r _ => let (v, g) := randNat g 0 (2^64 - 1); (BitVec.ofNat _ v, g)
      | .v _ => let (v, g) := randNat g 0 (2^512 - 1); (BitVec.ofNat _ v, g)
    let flip := match r with | .rflags => getReg s r ^^^ 0x3F | _ => ~~~(getReg s r)
    let norm (os : List Outcome) := if (writeSet d).contains r then os else os.map (maskReg · r)
    let bad := [flip, rnd].any fun v => norm (run (setReg s r v)) != norm outs
    (if bad then s!"{name}: {repr r} read but not in deps" :: acc else acc, g)
  (faults ++ writes ++ reads.reverse, g)

/-- Baseline plus `n` random states. -/
def checkWith (name : String) (run : MachineData → List Outcome) (d : InstrDeps RegId)
    (mem : DataMem) (g : StdGen) (n : Nat := 3) (perturbed : List RegId := allRegIds) :
    List String × StdGen :=
  let (v, g) := checkState name run d (baseline mem) g perturbed
  (List.range n).foldl (init := (v, g)) fun (v, g) _ =>
    let (s, g) := randomState mem g
    let (v', g) := checkState name run d s g perturbed
    (v ++ v', g)

def checkOpWith (name : String) {w} (op : Operation w) (d : InstrDeps RegId) (mem : DataMem)
    (g : StdGen) (n : Nat := 3) : List String × StdGen :=
  checkWith name (run op) d mem g n gprReadIds

def ctorName {w} (op : Operation w) : Lean.Name := (Lean.toExpr op).getAppFn.constName!

/-! ## The operations

At least one instance per constructor and operand shape: register, immediate and
memory forms at each width, partial registers (including the high bytes), every
addressing form (base, base+index*scale+disp, rip-relative), `cl` and immediate
shift counts, and the `lock` variants. -/

def m (base : Reg64) (disp : Int64 := 0) : AddrExpr := { base := some (.reg base), idx := none, disp := .int64 disp }
def mi (base : Reg64) (idx : Reg64) (scale : Width := .W64) (disp : Int64 := 0) : AddrExpr :=
  { base := some (.reg base), idx := some ⟨idx, scale⟩, disp := .int64 disp }
def mrip : AddrExpr := { base := some .rip, idx := none, disp := .label "L" }
def mabs : AddrExpr := { base := none, idx := none, disp := .int64 (Int64.ofNat (regionBase + 0x100)) }
def mem {w} (a : AddrExpr) : RegOrMem w := .mem a
def R {w} (r : Reg w) : RegOrMem w := .reg r
def OR {w} (r : Reg w) : Operand w := .regOrMem (.reg r)
def OM {w} (a : AddrExpr) : Operand w := .regOrMem (.mem a)
def I {w} (i : Int64) : Operand w := .imm (.int64 i)

abbrev Op := (w : Width) × Operation w
def x {w} (op : Operation w) : Op := ⟨w, op⟩

def ops : List Op := [
  -- Data movement.
  x (.mov (R .rax) (OR .rbx)), x (.mov (R .eax) (OR .ebx)), x (.mov (R .ax) (OR .bx)), x (.mov (R .al) (OR .bl)),
  x (.mov (R .ah) (OR .bl)), x (.mov (R .al) (OR .ah)), x (.mov (R .ch) (OR .dh)),
  x (.mov (R .rax) (OM (m .rdi))), x (.mov (R .eax) (OM (mi .rdi .rcx .W32 8))), x (.mov (R .ax) (OM (m .rsi 2))),
  x (.mov (R .al) (OM (m .rsi))), x (.mov (R .bh) (OM (m .rsi))), x (.mov (R .rax) (OM mrip)), x (.mov (R .rax) (OM mabs)),
  x (.mov (mem (m .rdi)) (OR .rax)), x (.mov (mem (mi .rdi .rcx .W64 (-8))) (OR .ecx)), x (.mov (mem (m .rdi)) (OR .ah)),
  x (.mov (w := .W64) (mem (m .rdi 4)) (I 7)), x (.mov (w := .W8) (mem (m .rdi 4)) (I 7)), x (.mov (mem (m .rsp 8)) (OR .r15)),
  x (.mov (R .rax) (I 7)), x (.mov (R .eax) (I 7)), x (.mov (R .ax) (I 7)), x (.mov (R .dh) (I 7)), x (.mov (R .r8) (I (-1))),
  x (.movsx (w := .W64) (R .rax) (R .bl)), x (.movsx (w := .W32) (R .eax) (mem (w := .W16) (m .rdi))),
  x (.movsx (w := .W16) (R .ax) (R .bl)), x (.movsx (w := .W64) (R .rcx) (R .ah)), x (.movsx (w := .W64) (R .rax) (R .ebx)),
  x (.movsx (w := .W32) (mem (m .rdi)) (R .bl)),
  x (.movzx (w := .W64) (R .rax) (R .bl)), x (.movzx (w := .W32) (R .eax) (mem (w := .W16) (m .rdi))),
  x (.movzx (w := .W16) (R .ax) (R .bl)), x (.movzx (w := .W32) (R .eax) (R .ah)),
  x (.movzx (w := .W32) (mem (m .rdi)) (R .bl)),
  x (.push (OR .rax)), x (.push (w := .W64) (I 5)), x (.push (w := .W64) (OM (m .rdi))), x (.push (w := .W16) (OM (m .rdi))), x (.push (OR .ax)), x (.push (OR .rsp)),
  x (.pop (R .rax)), x (.pop (w := .W64) (mem (m .rdi))), x (.pop (w := .W16) (mem (m .rdi))), x (.pop (R .ax)), x (.pop (R .rsp)),
  x (.setcc .z (R .al)), x (.setcc .nz (w := .W8) (mem (m .rdi))), x (.setcc .g (R .ah)), x (.setcc .be (R .r9b)),
  x (.cmovcc .z .rax (R .rbx)), x (.cmovcc .nz .eax (mem (m .rdi))), x (.cmovcc .l .ax (R .bx)), x (.cmovcc .a .ecx (R .ecx)),
  -- Arithmetic.
  x (.lea .rax (mi .rbx .rcx .W64 8)), x (.lea .eax (m .rbx 4)), x (.lea .ax (m .rbx)), x (.lea .rax mrip),
  x (.lea .rsp (m .rsp (-8))),
  x (.add (R .rax) (OR .rbx)), x (.add (R .eax) (I 1)), x (.add (mem (m .rdi)) (OR .rax)), x (.add (R .rax) (OM (m .rdi))),
  x (.add (R .ah) (OR .bl)), x (.add (R .ax) (OR .bx)), x (.add (w := .W32) (mem (mi .rdi .rcx .W32)) (I 3)), x (.add (w := .W8) (mem (m .rdi)) (I 3)), x (.add (R .al) (I 1)),
  x (.adc (R .rax) (OR .rbx)), x (.adc (R .eax) (I 1)), x (.adc (mem (m .rdi)) (OR .rax)), x (.adc (R .bh) (OM (m .rdi))),
  x (.adcx .rax (R .rbx)), x (.adcx .eax (mem (m .rdi))), x (.adox .rax (R .rbx)), x (.adox .eax (mem (m .rdi))),
  x (.inc (R .rax)), x (.inc (w := .W64) (mem (m .rdi))), x (.inc (w := .W16) (mem (m .rdi))), x (.inc (R .al)), x (.inc (R .ah)), x (.inc (R .ax)),
  x (.dec (R .rax)), x (.dec (w := .W32) (mem (m .rdi))), x (.dec (R .cx)), x (.dec (R .dh)),
  x (.neg (R .rax)), x (.neg (w := .W64) (mem (m .rdi))), x (.neg (w := .W8) (mem (m .rdi))), x (.neg (R .al)), x (.neg (R .ax)),
  x (.sub (R .rax) (OR .rbx)), x (.sub (R .eax) (I 1)), x (.sub (mem (m .rdi)) (OR .rax)), x (.sub (R .rax) (OM (m .rdi))),
  x (.sub (R .al) (OR .ah)), x (.sub (R .rsp) (I 16)),
  x (.sbb (R .rax) (OR .rbx)), x (.sbb (R .eax) (I 1)), x (.sbb (mem (m .rdi)) (OR .rax)), x (.sbb (R .ax) (OM (m .rdi))),
  x (.cmp (R .rax) (OR .rbx)), x (.cmp (w := .W64) (mem (m .rdi)) (I 1)), x (.cmp (w := .W16) (mem (m .rdi)) (I 1)), x (.cmp (R .eax) (OM (m .rdi))), x (.cmp (R .al) (OR .ah)),
  x (.cmp (mem (mi .rdi .rcx .W64)) (OR .rdx)),
  x (.mul (R .rbx)), x (.mul (mem (w := .W32) (m .rdi))), x (.mul (R .bx)), x (.mul (R .bl)), x (.mul (R .ah)), x (.mul (R .rax)),
  x (.mulx .rax .rbx (R .rcx)), x (.mulx .eax .ebx (mem (m .rdi))), x (.mulx .rax .rax (R .rbx)), x (.mulx .rdx .rcx (R .rdx)),
  x (.imul1 (R .rbx)), x (.imul1 (mem (w := .W32) (m .rdi))), x (.imul1 (R .bx)), x (.imul1 (R .bl)), x (.imul1 (R .dh)),
  x (.imul none (R .rax) (OR .rbx)), x (.imul none (R .eax) (OM (m .rdi))), x (.imul none (R .ax) (OR .bx)),
  x (.imul (some (R .rax)) (R .rbx) (I 3)), x (.imul (some (R .eax)) (mem (m .rdi)) (I 3)),
  x (.imul (some (R .ax)) (R .bx) (I 3)), x (.imul (some (R .rcx)) (R .rax) (OR .rbx)),
  x (.imul (some (mem (m .rdi))) (R .rbx) (I 3)),
  -- Bitwise.
  x (.test (R .rax) (OR .rbx)), x (.test (w := .W64) (mem (m .rdi)) (I 1)), x (.test (w := .W8) (mem (m .rdi)) (I 1)), x (.test (R .al) (OR .ah)), x (.test (R .eax) (OM (m .rdi))),
  x (.and (R .rax) (OR .rbx)), x (.and (R .eax) (I 1)), x (.and (mem (m .rdi)) (OR .rax)), x (.and (R .ah) (OM (m .rdi))),
  x (.not (R .rax)), x (.not (w := .W64) (mem (m .rdi))), x (.not (w := .W16) (mem (m .rdi))), x (.not (R .al)), x (.not (R .bh)), x (.not (R .ax)),
  x (.or (R .rax) (OR .rbx)), x (.or (R .eax) (I 1)), x (.or (mem (m .rdi)) (OR .rax)), x (.or (R .bl) (OM (m .rdi))),
  x (.xor (R .rax) (OR .rbx)), x (.xor (R .eax) (OR .eax)), x (.xor (mem (m .rdi)) (OR .rax)), x (.xor (R .ax) (I 1)),
  x (.shl (R .rax) (.imm8 (.int64 3))), x (.shl (R .rax) .cl), x (.shl (w := .W64) (mem (m .rdi)) (.imm8 (.int64 1))), x (.shl (w := .W8) (mem (m .rdi)) .cl),
  x (.shl (R .al) .cl), x (.shl (R .ax) (.imm8 (.int64 17))), x (.shl (R .rcx) .cl), x (.shl (R .eax) (.imm8 (.int64 0))),
  x (.shr (R .rax) (.imm8 (.int64 3))), x (.shr (R .rax) .cl), x (.shr (w := .W32) (mem (m .rdi)) (.imm8 (.int64 1))), x (.shr (R .ah) .cl),
  x (.sar (R .rax) (.imm8 (.int64 3))), x (.sar (R .eax) .cl), x (.sar (w := .W16) (mem (m .rdi)) (.imm8 (.int64 1))), x (.sar (R .bl) .cl),
  x (.shld (R .rax) .rbx (.imm8 (.int64 3))), x (.shld (mem (m .rdi)) .rbx .cl), x (.shld (R .ax) .bx (.imm8 (.int64 1))),
  x (.shld (R .eax) .ebx .cl),
  x (.shrd (R .rax) .rbx (.imm8 (.int64 3))), x (.shrd (mem (m .rdi)) .rbx .cl), x (.shrd (R .ax) .bx (.imm8 (.int64 1))),
  x (.shrd (R .eax) .ebx .cl),
  x (.rol (R .rax) (.imm8 (.int64 3))), x (.rol (R .eax) .cl), x (.rol (w := .W64) (mem (m .rdi)) (.imm8 (.int64 1))), x (.rol (R .al) .cl),
  x (.ror (R .rax) (.imm8 (.int64 3))), x (.ror (R .eax) .cl), x (.ror (w := .W32) (mem (m .rdi)) (.imm8 (.int64 1))), x (.ror (R .ax) .cl),
  x (.rcl (R .rax) (.imm8 (.int64 3))), x (.rcl (R .eax) .cl), x (.rcl (w := .W16) (mem (m .rdi)) (.imm8 (.int64 1))), x (.rcl (R .ah) .cl),
  x (.rcr (R .rax) (.imm8 (.int64 3))), x (.rcr (R .eax) .cl), x (.rcr (w := .W8) (mem (m .rdi)) (.imm8 (.int64 1))), x (.rcr (R .al) .cl),
  x (.bswap .rax), x (.bswap .ebx), x (.bswap .ax),
  x (.tzcnt .rax (R .rbx)), x (.tzcnt .eax (mem (m .rdi))), x (.tzcnt .ax (R .bx)), x (.tzcnt .rcx (R .rcx)),
  -- Control flow.
  x (.jcc (w := .W64) .z "L"), x (.jcc (w := .W64) .le "L"), x (.jcc (w := .W64) .nc "L"),
  x (.jmp (w := .W64) (.rel (.int64 8))), x (.jmp (w := .W64) (.reg .rax)), x (.jmp (w := .W64) (.mem (m .rdi))),
  x (.jmp (w := .W64) (.mem (mi .rdi .rcx .W64))),
  x (.call (w := .W64) (.rel (.int64 8))), x (.call (w := .W64) (.reg .rax)), x (.call (w := .W64) (.mem (m .rdi))),
  x (.call (w := .W64) (.reg .rsp)),
  x (.ret (w := .W64)), x (.nop (w := .W64) 1), x (.nopalign (w := .W64) 16 none),
  -- Atomics and barriers.
  x (.lockBin .add (m .rdi) (OR .rax)), x (.lockBin .sub (w := .W64) (m .rdi) (I 1)), x (.lockBin .xor (w := .W16) (m .rdi) (I 1)), x (.lockBin .and (mi .rdi .rcx .W32) (OR .eax)),
  x (.lockBin .or (m .rdi) (OR .ax)), x (.lockBin .xor (m .rdi) (OR .ah)), x (.lockBin .add (m .rdi) (OR .bl)),
  x (.lockUn .inc (w := .W64) (m .rdi)), x (.lockUn .dec (w := .W32) (m .rdi)), x (.lockUn .neg (w := .W16) (m .rdi)),
  x (.lockUn .not (w := .W8) (m .rdi)), x (.lockUn .not (w := .W64) (mi .rdi .rcx .W64 8)),
  x (.xchg .rax (R .rbx)), x (.xchg .rax (mem (m .rdi))), x (.xchg .al (R .bh)), x (.xchg .ax (mem (m .rdi))),
  x (.xchg .ah (mem (m .rdi))), x (.xchg .ecx (R .ecx)),
  x (.xadd true (mem (m .rdi)) .rax), x (.xadd false (R .rbx) .rax), x (.xadd false (mem (m .rdi)) .eax),
  x (.xadd false (R .ax) .bx), x (.xadd true (mem (m .rdi)) .ah), x (.xadd false (R .eax) .eax),
  x (.cmpxchg true (mem (m .rdi)) .rbx), x (.cmpxchg false (R .rcx) .rbx), x (.cmpxchg false (mem (m .rdi)) .ebx),
  x (.cmpxchg true (mem (m .rdi)) .bl), x (.cmpxchg false (R .cx) .bx), x (.cmpxchg false (R .al) .ah),
  x (.cmpxchg false (R .rax) .rbx),
  x (.mfence (w := .W64)), x (.lfence (w := .W64)), x (.sfence (w := .W64)),
  x (.movnti (m .rdi) .rax), x (.movnti (mi .rdi .rcx .W32) .ebx), x (.movnti (m .rax) .eax)]

/-! ### Vector operations

The aligned forms address `rsp` (16-byte aligned in every state) or, at 32
bytes, the absolute address `mabs`; the unaligned forms use `rdi` and an
indexed form. -/

def xm (r : RegMm) : AvxReg .W128 := .xmm r
def ym (r : RegMm) : AvxReg .W256 := .ymm r
def AR {w} (r : AvxReg w) : AvxRegOrMem w := .avx r
def AM {w} (a : AddrExpr) : AvxRegOrMem w := .mem a

abbrev AvxOp := (w : AvxWidth) × AvxOperation w
def y {w} (op : AvxOperation w) : AvxOp := ⟨w, op⟩

def avxCtorName {w} (op : AvxOperation w) : Lean.Name := (Lean.toExpr op).getAppFn.constName!

def avxOps : List AvxOp := [
  -- Moves: register, load and store, legacy (merging) and VEX (zeroing).
  y (.movups (AR (xm .mm1)) (AR (xm .mm2))), y (.movups (AR (xm .mm1)) (AM (m .rdi))),
  y (.movups (AM (mi .rdi .rcx .W8 8)) (AR (xm .mm3))),
  y (.movaps (AR (xm .mm1)) (AR (xm .mm2))), y (.movaps (AR (xm .mm8)) (AM (m .rsp))),
  y (.movaps (AM (m .rsp 16)) (AR (xm .mm2))),
  y (.movapd (AR (xm .mm1)) (AR (xm .mm1))), y (.movapd (AR (xm .mm4)) (AM (m .rsp))),
  y (.movapd (AM (m .rsp (-16))) (AR (xm .mm15))),
  y (.movdqa (AR (xm .mm0)) (AR (xm .mm7))), y (.movdqa (AR (xm .mm5)) (AM (m .rsp 32))),
  y (.movdqa (AM (m .rsp)) (AR (xm .mm6))),
  y (.movdqu (AR (xm .mm1)) (AR (xm .mm2))), y (.movdqu (AR (xm .mm1)) (AM (m .rdi 3))),
  y (.movdqu (AM (mi .rdi .rcx .W8)) (AR (xm .mm9))),
  y (.vmovups (AR (ym .mm1)) (AM (m .rdi))), y (.vmovups (AM (m .rdi 1)) (AR (xm .mm2))),
  y (.vmovups (AR (ym .mm3)) (AR (ym .mm4))),
  y (.vmovaps (AR (xm .mm1)) (AM (m .rsp))), y (.vmovaps (AR (ym .mm2)) (AM mabs)),
  y (.vmovaps (AM mabs) (AR (ym .mm3))), y (.vmovaps (AR (ym .mm4)) (AR (ym .mm5))),
  y (.vmovapd (AR (xm .mm1)) (AM (m .rsp))), y (.vmovapd (AR (ym .mm2)) (AM mabs)),
  y (.vmovapd (AM (m .rsp 16)) (AR (xm .mm3))), y (.vmovapd (AR (xm .mm4)) (AR (xm .mm5))),
  y (.vmovdqa (AR (xm .mm1)) (AM (m .rsp))), y (.vmovdqa (AR (ym .mm12)) (AM mabs)),
  y (.vmovdqa (AM mabs) (AR (ym .mm3))), y (.vmovdqa (AR (xm .mm4)) (AR (xm .mm4))),
  y (.vmovdqu (AR (ym .mm1)) (AM (mi .rdi .rcx .W8))), y (.vmovdqu (AM (m .rdi 5)) (AR (ym .mm2))),
  y (.vmovdqu (AR (xm .mm3)) (AR (xm .mm4))),
  -- Legacy lane arithmetic.
  y (.subps (AR (xm .mm1)) (AR (xm .mm2))), y (.subps (AR (xm .mm1)) (AM (m .rsp))),
  y (.addps (AR (xm .mm1)) (AR (xm .mm2))), y (.addps (AR (xm .mm3)) (AM (m .rsp 16))),
  y (.mulps (AR (xm .mm1)) (AR (xm .mm2))), y (.mulps (AR (xm .mm1)) (AM (m .rsp))),
  y (.xorps (AR (xm .mm1)) (AR (xm .mm2))), y (.xorps (AR (xm .mm1)) (AR (xm .mm1))),
  y (.xorps (AR (xm .mm1)) (AM (m .rsp))),
  -- VEX three-operand forms.
  y (.vxorps (ym .mm1) (ym .mm2) (AR (ym .mm3))), y (.vxorps (xm .mm1) (xm .mm1) (AM (m .rdi))),
  y (.vaddps (ym .mm1) (ym .mm2) (AR (ym .mm3))), y (.vaddps (xm .mm4) (xm .mm5) (AM (m .rdi 4))),
  y (.vmulps (ym .mm1) (ym .mm2) (AR (ym .mm2))), y (.vmulps (xm .mm1) (xm .mm2) (AM (m .rdi))),
  y (.vfmadd231ps (ym .mm1) (ym .mm2) (AR (ym .mm3))),
  y (.vfmadd231ps (ym .mm1) (ym .mm2) (AM (mi .rdi .rcx .W8))),
  y (.vshufps (ym .mm1) (ym .mm2) (AR (ym .mm3)) 0x1B), y (.vshufps (xm .mm1) (xm .mm2) (AM (m .rdi)) 0xE4),
  -- Fixed-width register forms.
  y (.vextractf128 (w := .W256) (xm .mm1) (ym .mm2) 1), y (.vextractf128 (w := .W256) (xm .mm1) (ym .mm1) 0),
  y (.vmovhlps (w := .W128) (xm .mm1) (xm .mm2) (xm .mm3)),
  y (.vmovss (w := .W128) (xm .mm1) (xm .mm2) (xm .mm3)),
  y (.vaddss (w := .W128) (xm .mm1) (xm .mm2) (xm .mm3)), y (.vzeroupper (w := .W128)),
  -- `cmpxchg16b`, locked and not (here the compare fails; see `cas16Equal`).
  y (.cmpxchg16b (w := .W128) true (m .rsp)), y (.cmpxchg16b (w := .W128) false (m .rsp 16)),
  y (.cmpxchg16b (w := .W128) true mabs)]

/-- `cmpxchg16b` run from a state whose memory operand holds `rdx:rax`, so
that the compare succeeds and `rcx:rbx` is stored. -/
def cas16Equal (lock : Bool) (s : MachineData) : List Outcome :=
  let a := s.regs.get64 .rsp
  let acc := s.regs.get64 .rdx ++ s.regs.get64 .rax
  runAvx (.cmpxchg16b (w := .W128) lock (m .rsp)) { s with dmem := Mem.storeInt s.dmem a 16 acc.toInt }

/-! ## Results -/

/-- All violations over all operations, deduplicated and sorted. -/
def violations : List String :=
  let g := mkStdGen 20241007
  let (mem, g) := initMem g
  let (v, g) := ops.foldl (init := (([] : List String), g)) fun (acc, g) (⟨_, op⟩ : Op) =>
    let (v, g) := checkOpWith (ctorName op).toString op op.deps mem g
    (acc ++ v, g)
  let (v, g) := avxOps.foldl (init := (v, g)) fun (acc, g) (⟨_, op⟩ : AvxOp) =>
    let (v, g) := checkWith (avxCtorName op).toString (runAvx op) op.deps mem g
    (acc ++ v, g)
  let (v, _) := [true, false].foldl (init := (v, g)) fun (acc, g) lock =>
    let d := (AvxOperation.cmpxchg16b (w := .W128) lock (m .rsp)).deps
    let (v, g) := checkWith s!"cmpxchg16b {lock} (equal)" (cas16Equal lock) d mem g
    (acc ++ v, g)
  (v.eraseDups.toArray.qsort (· < ·)).toList

/-- info: [] -/
#guard_msgs in
#eval violations

-- The harness does detect omissions: with empty deps, `add %rbx, %rax` reads
-- `rax`/`rbx` and writes `rax` and the flags; `push %rbx` reads `rsp`/`rbx` and
-- writes `rsp`; `jz` reads the flags; a 16-bit `mov` merges into its destination.
/--
info: Operation.add: RegId.r (Reg64.rax) read but not in deps
Operation.add: RegId.r (Reg64.rax) written but not in defs
Operation.add: RegId.r (Reg64.rbx) read but not in deps
Operation.add: RegId.rflags written but not in defs
Operation.jcc: RegId.rflags read but not in deps
Operation.mov: RegId.r (Reg64.rax) read but not in deps
Operation.mov: RegId.r (Reg64.rbx) read but not in deps
Operation.push: RegId.r (Reg64.rbx) read but not in deps
Operation.push: RegId.r (Reg64.rsp) read but not in deps
Operation.push: RegId.r (Reg64.rsp) written but not in defs
-/
#guard_msgs in
#eval
  let g := mkStdGen 7
  let (mem, g) := initMem g
  let planted : List Op := [x (.add (R .rax) (OR .rbx)), x (.push (OR .rbx)),
    x (.jcc (w := .W64) .z "L"), x (.mov (R .ax) (OR .bx))]
  let (v, _) := planted.foldl (init := (([] : List String), g)) fun (acc, g) (⟨_, op⟩ : Op) =>
    let (v, g) := checkOpWith (ctorName op).toString op
      { defs := match op with | .mov .. => [.r .rax] | _ => [] } mem g
    (acc ++ v, g)
  IO.println (String.intercalate "\n" (v.eraseDups.toArray.qsort (· < ·)).toList)

-- Every constructor of `Operation` is reached by `ops`, and every constructor
-- of `AvxOperation` by `avxOps`.
open Lean in
/-- info: constructors not covered: [] -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let some (.inductInfo info) := env.find? ``Operation | throwError "`Operation` not found"
  let some (.inductInfo avxInfo) := env.find? ``AvxOperation | throwError "`AvxOperation` not found"
  let covered := ops.map (fun ⟨_, op⟩ => ctorName op) ++ avxOps.map (fun ⟨_, op⟩ => avxCtorName op)
  let missing := (info.ctors ++ avxInfo.ctors).filter fun c => !covered.contains c
  logInfo m!"constructors not covered: {missing}"

end DepsTests
