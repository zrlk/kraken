import Kraken.AArch64.Parser
import Kraken.Promising.AArch64

/-!
# Certification past a system call (AArch64)

The plain machine certifies with `exec`, under which `SVC` faults: a thread
can promise no write that follows a system call. The certification mode
(`certifiedPromisesWith`, `certifyWith`, `exploreWith` with
`Promising.AArch64.execCert results`) runs the system call as a choice among
`results info`, the value `x0` receives; the machine's own steps still fault
at the `SVC`.
-/

open Kraken Kraken.Promising
open Kraken.AArch64.Parser

namespace Kraken.Promising.SyscallCertTestsA64

def yAddr : BitVec 64 := 0x1000100

/-- `x0 = 41`, `x3 = &y`, `x8 = 64` (the call number). -/
def regs : Reg64s := { X0 := 41, X3 := UInt64.ofBitVec yAddr, X8 := 64 }

def prog (code : String) : Program :=
  match parse code with
  | .ok p => p
  | .error e => panic! s!"parse error: {e}"

/-- A system call, then a store of its result to `y`. -/
def p0 : Program := prog "
    SVC #0
    STR X0,[X3]"

def c0 : Config Promising.AArch64.isa := Config.init [Promising.AArch64.mkState 0 p0 regs] []

/-- The value of the newest message of each promise successor. -/
def promised (cs : List (Config Promising.AArch64.isa × TraceEv)) : List Nat :=
  cs.map fun (c, _) => (c.mem.msgs.toList.getLast?.map (·.val.toNat)).getD 999

def certMode (results : SyscallInfo → List (BitVec 64)) :=
  certifiedPromisesWith .armv8 (Promising.AArch64.execCert results) {} c0 0 8

-- The plain machine: no promise past the `SVC`, whose fault is reported.
/-- info: ([], ["pending system call: svc #0"]) -/
#guard_msgs in
#eval let (ps, r, _) := certifiedPromises .armv8 {} c0 0 8; (promised ps, r.faults)

-- Certification mode: one promise per possible result.
/-- info: ([7, 5], []) -/
#guard_msgs in
#eval let (ps, r, _) := certMode fun _ => [5, 7]; (promised ps, r.faults)

-- No possible result: a dead end, neither a promise nor a fault.
/-- info: ([], []) -/
#guard_msgs in
#eval let (ps, r, _) := certMode fun _ => []; (promised ps, r.faults)

-- The results see the call: its immediate, number and argument registers.
/-- info: [42] -/
#guard_msgs in
#eval promised (certMode fun i =>
  if i.imm == 0 && i.num == 64 then [i.args.headD 0 + 1] else []).1

/-- `c0` with `y := 5` promised by thread 0. -/
def c1 : Config Promising.AArch64.isa := ((certMode fun _ => [5]).1.headD (c0, .instr 0 "")).1

/-- Whether thread 0 of `c1` certifies, in certification mode with `results`. -/
def certifies (results : SyscallInfo → List (BitVec 64)) : Bool :=
  match c1.threads[0]? with
  | some t => (certifyWith .armv8 (Promising.AArch64.execCert results) {} t 0 c1.mem 8).1.certified
  | none => false

-- The promise must still be fulfilled: only a result of 5 does.
/-- info: (true, false, false) -/
#guard_msgs in
#eval (certifies fun _ => [5], certifies fun _ => [7], certifies fun _ => [])

-- The plain certification cannot fulfil it.
/-- info: false -/
#guard_msgs in
#eval match c1.threads[0]? with
  | some t => (certify .armv8 {} t 0 c1.mem 8).1.certified
  | none => true

-- Exploration in certification mode: the thread may promise, but its own
-- step still faults at the `SVC`, so no final state is reached.
/-- info: (0, ["pending system call: svc #0"]) -/
#guard_msgs in
#eval
  let r := exploreWith .armv8 (Promising.AArch64.execCert fun _ => [5]) c0 (fun _ => ())
  (r.finals.length, r.faults.eraseDups)

end Kraken.Promising.SyscallCertTestsA64
