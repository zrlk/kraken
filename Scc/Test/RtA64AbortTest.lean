import Scc.Cert.Arm
import Scc.Cert.Rt.A64Abort
import Scc.Test.Src

/-!
# The never-returning runtime code in emitted AArch64 programs

`abortIn` and `mainIn` (`Scc/Cert/Rt/A64Abort.lean`) hold of the programs
scc emits for `hello1.w` and `hello.w` (a setup block), `abortIn` and
`mainIn0` of the one for `ret0` below (`main(u : Unit) : Int`), by
`decide +kernel`: `seg_stub_of`, `seg_abort_of` and `seg_main_tail_of`
(`seg_main_tail0_of`) apply to every valid layout of them.
-/

namespace Scc.Test.RtA64Abort

open Kraken.Promising.AArch64

/-- scc's AArch64 listing of `hello1.w`. -/
def hello1Asm : String :=
  match Scc.Cert.Arm.compile { arch := .arm } (w_src% "Scc/Test/hello1.w") with
  | .ok s => s
  | .error _ => ""

/-- The listing, parsed by Kraken. -/
def hello1Prog : Program := scc_arm_reparse% hello1Asm

theorem hello1_abortIn : Scc.Cert.Rt.A64.Abort.abortIn hello1Prog = true := by decide +kernel

theorem hello1_mainIn : Scc.Cert.Rt.A64.Abort.mainIn hello1Prog = true := by decide +kernel

/-- scc's AArch64 listing of `hello.w`. -/
def helloAsm : String :=
  match Scc.Cert.Arm.compile { arch := .arm } (w_src% "Scc/Test/hello.w") with
  | .ok s => s
  | .error _ => ""

/-- The listing, parsed by Kraken. -/
def helloProg : Program := scc_arm_reparse% helloAsm

theorem hello_abortIn : Scc.Cert.Rt.A64.Abort.abortIn helloProg = true := by decide +kernel

theorem hello_mainIn : Scc.Cert.Rt.A64.Abort.mainIn helloProg = true := by decide +kernel

/-- scc's AArch64 listing of a program whose `main` takes `Unit`. -/
def ret0Asm : String :=
  match Scc.Cert.Arm.compile { arch := .arm } "def main(u : Unit) : Int =
  let x = 40
  let y = x + 2
  ret y
" with
  | .ok s => s
  | .error _ => ""

/-- The listing, parsed by Kraken. -/
def ret0Prog : Program := scc_arm_reparse% ret0Asm

theorem ret0_abortIn : Scc.Cert.Rt.A64.Abort.abortIn ret0Prog = true := by decide +kernel

theorem ret0_mainIn0 : Scc.Cert.Rt.A64.Abort.mainIn0 ret0Prog = true := by decide +kernel

/-! ## The `write` system calls are checked

`stubIn` checks the stub's `svc #0` (7 instructions after its entry) and
`printIn` `scc_rt_print`'s (5 after `.2_write`, past its barrier): with `svc #1` there, the
checks fail, while the blocks around the call still match. -/

/-- `prog` with the directive `k` instructions after the label `l` replaced
by `d`. -/
def breakAt (prog : Program) (l : String) (k : Nat) (d : Directive) : Program :=
  match prog.findIdx? (· == .label l) with
  | some i => prog.set (i + 1 + k) d
  | none => prog

/-- `svc #1`, not the runtime's system call. -/
def svc1 : Directive := .instr ⟨.W64, .SVC 1⟩

open Scc.Cert.Rt.A64 Spike.Lib.A64.Abort in
example : let p := breakAt ret0Prog overflow.entry 7 svc1
    (Scc.Cert.Rt.A64.Abort.stubIn p overflow b1Overflow, Scc.Cert.Rt.A64.Abort.abortIn p,
      blockAt p overflow.entry 2 b1Overflow && blockAt p overflow.entry 8 b2) = (false, false, true) := by
  decide +kernel

open Scc.Cert.Rt.A64 in
example : let p := breakAt ret0Prog ".L9_scc_rt_print.2_write" 5 svc1
    (Scc.Cert.Rt.A64.Print.printIn p, blockAt p ".L9_scc_rt_print.2_write" 1 Spike.Lib.A64.Print.b4 &&
      blockAt p ".L9_scc_rt_print.2_write" 6 Spike.Lib.A64.Print.b5) = (false, true) := by
  decide +kernel

end Scc.Test.RtA64Abort
