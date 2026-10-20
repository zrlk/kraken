/-
**Kernel-evaluable AArch64 `exec`/`deps` for `ReachCore`**: the AArch64 counterpart of `ReachX64Core`.

`reachA64Exec`/`reachA64Deps` are `AArch64.exec`/`AArch64.deps` with
`Executable.withAddresses` replaced by the structural `reachWithAddr`;
`reachA64ExecK` is `reachA64Exec` with the private-memory lookups replaced by
the empty-map-aware `reachLoadInt`/`reachLoadBytes` (`#reach_clone`). The
equations `reachA64ExecK_eq`/`reachA64Deps_eq` make them the `ex`/`dp` of
`reachCheck` for AArch64.

Also: the runner's image (`reachA64Exe`), thread (`reachA64Thread`), the
runner comparison (`reachA64RunnerMatches`) and register observations.
-/
import Kraken.Promising.ReachCore
import Kraken.Promising.ReachClone
import Kraken.Promising.ReachMem
import Kraken.Promising.AArch64
import Kraken.Litmus.AArch64

namespace Kraken.Promising.Reach

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- `Executable.labels` (AArch64) through `reachWithAddr`. -/
@[reducible] def reachA64Labels (e : _root_.Executable) : Labels :=
  { label l := ((reachWithAddr e.1 e.2).findSome?
      (fun (p, d, _) => if d = .label l then .some p else .none)).getD (-1) }

theorem reachA64Labels_eq (e : _root_.Executable) : reachA64Labels e = _root_.Executable.labels e := by
  simp only [reachA64Labels, _root_.Executable.labels, reachWithAddr_eq']

/-- `Executable.step` (AArch64) through `reachWithAddr`. -/
def reachA64ExeStep (e : _root_.Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := reachA64Labels e
  Directives.interp
    (((reachWithAddr e.1 e.2).dropWhile (·.1 ≠ s.2)).takeWhile (·.1 = s.2) |>.map (·.2)) s.1 s.2
    (fun pc s => ret (s, pc))

theorem reachA64ExeStep_eq : reachA64ExeStep = _root_.Executable.step := by
  funext e s ret
  unfold reachA64ExeStep _root_.Executable.step Kraken.Executable.directivesAtAddress
  rw [reachA64Labels_eq, reachWithAddr_eq']

/-- `State.directive` (AArch64) through `reachWithAddr`. -/
def reachA64Directive (s : State) : Option Directive :=
  ((((reachWithAddr s.exe.1 s.exe.2).dropWhile (·.1 ≠ s.st.2)).map (·.2)).dropWhile
    (fun (d, _) => match d with | .label _ => true | _ => false)) |>.head? |>.map (·.1)

theorem reachA64Directive_eq : reachA64Directive = State.directive := by
  funext s
  simp only [reachA64Directive, State.directive, Kraken.Executable.directivesFromAddress, reachWithAddr_eq']
  rfl

/-- `AArch64.exec` through `reachWithAddr`. -/
def reachA64Exec (s : State) : Option (EvTree State) :=
  if s.st.2 == s.endPc || (reachA64Directive s).isNone then none
  else some <| (toEv s.decls (reachA64ExeStep s.exe s.st fun s' => .done s')).map fun st => { s with st }

theorem reachA64Exec_eq : (reachA64Exec : isa.State → Option (EvTree isa.State)) = isa.exec := by
  funext s
  show reachA64Exec s = AArch64.exec s
  simp only [reachA64Exec, AArch64.exec, reachA64Directive_eq, reachA64ExeStep_eq]

/- `reachA64Exec` with the private-memory lookups kernel-evaluable on an
empty map (`ReachMem`): `reachA64ExecK`, with `reachA64ExecK._reach_eq`. -/
#reach_clone reachA64Exec as reachA64ExecK using
  [Mem.loadInt := reachLoadInt by reachLoadInt_eq, Mem.loadBytes := reachLoadBytes by reachLoadBytes_eq]

theorem reachA64ExecK_eq : (reachA64ExecK : isa.State → Option (EvTree isa.State)) = isa.exec :=
  reachA64ExecK._reach_eq.trans reachA64Exec_eq

/-- `AArch64.deps` through `reachWithAddr`. -/
def reachA64Deps (s : State) : InstrDeps RegId :=
  match reachA64Directive s with
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

theorem reachA64Deps_eq : (reachA64Deps : isa.State → InstrDeps isa.RegId) = isa.deps := by
  funext s
  show reachA64Deps s = AArch64.deps s
  simp only [reachA64Deps, AArch64.deps, reachA64Directive_eq]
  rfl

/-! ## The runner's image, threads and comparison -/

/-- The runner's executable (`Litmus.AArch64.prepareProgram`): the code at
`0x100000`, each directive its `fakeSize` (4 bytes per instruction). -/
def reachA64Exe (code : Program) : _root_.Executable :=
  (0x100000, code.map fun d => (d, d.fakeSize))

/-- A thread as the runner prepares it (no stack, empty private memory):
the image `exe`, pc `pc`, end `endPc`, the `X` registers `regs` set in
order, declarations `decls`. -/
def reachA64Thread (exe : _root_.Executable) (decls : Decls) (regs : List (XReg × BitVec 64))
    (pc endPc : Int64) : AArch64.State where
  exe := exe
  endPc := endPc
  st := ({ regs := regs.foldl (fun rs (r, v) => rs.setXReg r v) {} }, pc)
  decls := decls

/-- Register `X<r>` of thread `tid` (64 bits). -/
def reachXReg (c : Config isa) (tid : Nat) (r : XReg) : Option (BitVec 64) :=
  c.threads[tid]?.map fun t => (t.st.st.1.regs.getXReg r).toBitVec

/-- The low 32 bits of register `X<r>` of thread `tid` (`W<r>`). -/
def reachWReg (c : Config isa) (tid : Nat) (r : XReg) : Option (BitVec 32) :=
  c.threads[tid]?.map fun t => (t.st.st.1.regs.getXReg r).toBitVec.setWidth 32

/-- The runner's prepared configuration agrees with `c0` in everything a
run reads: each thread's executable, end, machine state (pc, registers,
flags, private memory) and declarations, no promises, and the initial
memory (locations and values) with no messages. -/
def reachA64RunnerMatches (src : String) (c0 : Config isa) : Bool :=
  let same (t s : Thread isa) : Bool :=
    t.st.exe == s.st.exe && t.st.endPc == s.st.endPc && t.st.st == s.st.st &&
      t.st.decls == s.st.decls && t.prom.isEmpty && s.prom.isEmpty &&
      t.rview == s.rview && t.wview == s.wview
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => pr.config.threads.size == c0.threads.size &&
      (pr.config.threads.toList.zip c0.threads.toList).all (fun (t, s) => same t s) &&
      pr.config.mem.init == c0.mem.init && pr.config.mem.msgs.isEmpty && c0.mem.msgs.isEmpty

end Kraken.Promising.Reach

#print axioms Kraken.Promising.Reach.reachA64ExecK_eq
#print axioms Kraken.Promising.Reach.reachA64Deps_eq
