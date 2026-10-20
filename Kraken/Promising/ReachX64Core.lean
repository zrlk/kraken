/-
**Kernel-evaluable x64 `exec`/`deps` for `ReachCore`**.

`X64.exec` finds the next directive through `Executable.withAddresses`,
defined by well-founded recursion whose decreasing proof the kernel cannot
reduce, so `decide` gets stuck on it. `reachWithAddr` is the same function by
structural recursion; `reachExec`/`reachDeps` are `X64.exec`/`X64.deps` with
it substituted, and `reachExec_eq`/`reachDeps_eq` say they are equal. They
are the `ex`/`dp` arguments of `reachCheck` for x64.

The file also has the runner's executable layout (`reachX64Exe`) and the
runner comparison (`reachX64RunnerMatches`), shared by the `ReachX64*`
theorems.
-/
import Kraken.Promising.ReachCore
import Kraken.Promising.ReachClone
import Kraken.Promising.ReachMem
import Kraken.Promising.X64
import Kraken.Litmus.X64

namespace Kraken.Promising.Reach

open Kraken Kraken.Promising Kraken.Promising.X64

/-- `Executable.labels` through `reachWithAddr`. -/
@[reducible] def reachLabels (e : _root_.Executable) : Labels :=
  { label l := ((reachWithAddr e.1 e.2).findSome?
      (fun (p, d, _) => if d = .label l then .some p else .none)).getD (-1) }

/-- `Executable.step` through `reachWithAddr`. -/
def reachExeStep (e : _root_.Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := reachLabels e
  Directives.interp
    (((reachWithAddr e.1 e.2).dropWhile (·.1 ≠ s.2)).takeWhile (·.1 = s.2) |>.map (·.2)) s.1 s.2
    (fun pc s => ret (s, pc))

theorem reachLabels_eq (e : _root_.Executable) : reachLabels e = _root_.Executable.labels e := by
  simp only [reachLabels, _root_.Executable.labels, reachWithAddr_eq']

theorem reachExeStep_eq : reachExeStep = _root_.Executable.step := by
  funext e s ret
  unfold reachExeStep _root_.Executable.step Kraken.Executable.directivesAtAddress
  rw [reachLabels_eq, reachWithAddr_eq']

/-- `State.directive` through `reachWithAddr`. -/
def reachDirective (s : State) : Option Directive :=
  ((((reachWithAddr s.exe.1 s.exe.2).dropWhile (·.1 ≠ s.st.2)).map (·.2)).dropWhile
    (fun (d, _) => match d with | .label _ => true | _ => false)) |>.head? |>.map (·.1)

theorem reachDirective_eq : reachDirective = State.directive := by
  funext s
  simp only [reachDirective, State.directive, Kraken.Executable.directivesFromAddress, reachWithAddr_eq']
  rfl

/-- `X64.exec`, kernel-evaluable. -/
def reachExec (s : State) : Option (EvTree State) :=
  if s.st.2 == s.endPc || (reachDirective s).isNone then none
  else some <| (toEv s.decls (reachExeStep s.exe s.st fun s' => .done s')).map fun st => { s with st }

theorem reachExec_eq : (reachExec : isa.State → Option (EvTree isa.State)) = isa.exec := by
  funext s
  show reachExec s = X64.exec s
  simp only [reachExec, X64.exec, reachDirective_eq, reachExeStep_eq]

/- `reachExec` with the private-memory lookups kernel-evaluable on an
empty map (`ReachMem`): `reachExecK`, with `reachExecK._reach_eq`. -/
#reach_clone reachExec as reachExecK using
  [Mem.loadInt := reachLoadInt by reachLoadInt_eq, Mem.loadBytes := reachLoadBytes by reachLoadBytes_eq]

theorem reachExecK_eq : (reachExecK : isa.State → Option (EvTree isa.State)) = isa.exec :=
  reachExecK._reach_eq.trans reachExec_eq

/-- `X64.deps`, kernel-evaluable. -/
def reachDeps (s : State) : InstrDeps RegId :=
  match reachDirective s with
  | some d => _root_.Directive.deps d
  | none => {}

theorem reachDeps_eq : (reachDeps : isa.State → InstrDeps isa.RegId) = isa.deps := by
  funext s
  show reachDeps s = X64.deps s
  simp only [reachDeps, X64.deps, reachDirective_eq]
  rfl

/-! ## The runner's image and comparison -/

/-- The runner's executable (`Litmus.X64.prepareProgram`): the code at
`0x100000`, one byte per instruction, then for each symbol, in the
runner's order, a padding cell up to its address and its label. -/
def reachX64Exe (code : Program) (syms : List (String × Nat)) : _root_.Executable :=
  let base : Int64 := 0x100000
  let codeCells : List (Directive × Nat) := code.map fun d => (d, match d with | .label _ => 0 | _ => 1)
  let codeLen := (codeCells.map (·.2)).sum
  let (cells, _) := syms.foldl (init := (codeCells, base.toBitVec.toNat + codeLen)) fun (cells, cur) (x, a) =>
    (cells ++ [((.byteArray (.mk #[]) : Directive), a - cur), (.label x, 0)], a)
  (base, cells)

/-- A thread as the runner prepares it (no stack, empty private memory):
the image `exe`, pc `pc`, end `endPc`, the general registers `regs` and the
vector registers `xmms` set in order, declarations `decls`. -/
def reachX64Thread (exe : _root_.Executable) (decls : Decls) (regs : List (Reg64 × BitVec 64))
    (pc endPc : Int64) (xmms : List (RegMm × BitVec 512) := []) : X64.State where
  exe := exe
  endPc := endPc
  st := ({ ({} : MachineData) with
    regs := regs.foldl (fun rs (r, v) => rs.set64 r v) ({} : MachineData).regs,
    zmms := xmms.foldl (fun zs (r, v) => zs.set512 r v) ({} : MachineData).zmms }, pc)
  decls := decls

/-- The low 32 bits of register `r` of thread `tid`: a `.kl` observation
`tid:e<r>`. -/
def reachReg32 (c : Config isa) (tid : Nat) (r : Reg64) : Option (BitVec 32) :=
  c.threads[tid]?.map fun t => (t.st.st.1.regs.get64 r).setWidth 32

/-- Register `r` of thread `tid` (64 bits): a `.kl` observation `tid:r<r>`. -/
def reachReg64 (c : Config isa) (tid : Nat) (r : Reg64) : Option (BitVec 64) :=
  c.threads[tid]?.map fun t => t.st.st.1.regs.get64 r

/-- The low 128 bits of vector register `r` of thread `tid`: a `.kl`
observation `tid:xmm<r>`. -/
def reachXmm128 (c : Config isa) (tid : Nat) (r : RegMm) : Option (BitVec 128) :=
  c.threads[tid]?.map fun t => (t.st.st.1.zmms.get512 r).setWidth 128

/-- The runner's prepared configuration agrees with `c0` in everything a
run reads: each thread's executable, end, machine state (pc, registers,
flags, vector registers, private memory) and declarations, no promises, and the initial memory (locations and values)
with no messages. -/
def reachX64RunnerMatches (src : String) (c0 : Config isa) : Bool :=
  let same (t s : Thread isa) : Bool :=
    t.st.exe == s.st.exe && t.st.endPc == s.st.endPc && t.st.st == s.st.st &&
      t.st.decls == s.st.decls && t.prom.isEmpty && s.prom.isEmpty &&
      t.rview == s.rview && t.wview == s.wview
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => pr.config.threads.size == c0.threads.size &&
      (pr.config.threads.toList.zip c0.threads.toList).all (fun (t, s) => same t s) &&
      pr.config.mem.init == c0.mem.init && pr.config.mem.msgs.isEmpty && c0.mem.msgs.isEmpty

end Kraken.Promising.Reach

#print axioms Kraken.Promising.Reach.reachExecK_eq
#print axioms Kraken.Promising.Reach.reachDeps_eq
