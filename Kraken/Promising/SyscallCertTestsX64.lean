import Kraken.X64.Parser
import Kraken.Promising.X64

/-!
# Certification past a system call (x64)

The x64 counterpart of `SyscallCertTestsA64.lean`: under `exec`, `syscall`
faults; under `Promising.X64.execCert results` it is a choice among
`results info`, the values `rax`, `rcx` and `r11` receive.
-/

open Kraken Kraken.Promising
open Kraken.X64.Parser

namespace Kraken.Promising.SyscallCertTestsX64

def yAddr : BitVec 64 := 0x1000100
def syms : List (String × BitVec 64) := [("y", yAddr)]

def prog (code : String) : Program :=
  match parse code with
  | .ok p => p
  | .error e => panic! s!"parse error: {e}"

/-- A system call, then a store of its result to `y`. -/
def p0 : Program := prog "
    syscall
    movq %rax,(y)"

/-- `rax = 39` (the call number), `rdi = 41`. -/
def c0 : Config Promising.X64.isa :=
  Config.init [Promising.X64.mkState 0 p0 { rax := 39, rdi := 41 } syms] []

/-- The value of the newest message of each promise successor. -/
def promised (cs : List (Config Promising.X64.isa × TraceEv)) : List Nat :=
  cs.map fun (c, _) => (c.mem.msgs.toList.getLast?.map (·.val.toNat)).getD 999

def ret (v : BitVec 64) : SyscallRet := { rax := v, rcx := 0, r11 := 0 }

def certMode (results : SyscallInfo → List SyscallRet) :=
  certifiedPromisesWith .tso (Promising.X64.execCert results) {} c0 0 8

-- The plain machine: no promise past the `syscall`, whose fault is reported.
/-- info: ([], ["pending system call: syscall"]) -/
#guard_msgs in
#eval let (ps, r, _) := certifiedPromises .tso {} c0 0 8; (promised ps, r.faults)

-- Certification mode: one promise per possible result.
/-- info: ([7, 5], []) -/
#guard_msgs in
#eval let (ps, r, _) := certMode fun _ => [ret 5, ret 7]; (promised ps, r.faults)

-- No possible result: a dead end, neither a promise nor a fault.
/-- info: ([], []) -/
#guard_msgs in
#eval let (ps, r, _) := certMode fun _ => []; (promised ps, r.faults)

-- The results see the call: its number and argument registers.
/-- info: [42] -/
#guard_msgs in
#eval promised (certMode fun i => if i.num == 39 then [ret (i.args.headD 0 + 1)] else []).1

/-- `c0` with `y := 5` promised by thread 0. -/
def c1 : Config Promising.X64.isa := ((certMode fun _ => [ret 5]).1.headD (c0, .instr 0 "")).1

/-- Whether thread 0 of `c1` certifies, in certification mode with `results`. -/
def certifies (results : SyscallInfo → List SyscallRet) : Bool :=
  match c1.threads[0]? with
  | some t => (certifyWith .tso (Promising.X64.execCert results) {} t 0 c1.mem 8).1.certified
  | none => false

-- The promise must still be fulfilled: only a result of 5 does.
/-- info: (true, false, false) -/
#guard_msgs in
#eval (certifies fun _ => [ret 5], certifies fun _ => [ret 7], certifies fun _ => [])

end Kraken.Promising.SyscallCertTestsX64
