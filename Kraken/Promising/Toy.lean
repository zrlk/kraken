/-
A toy ISA for testing the Promising core: the paper's little language, with
four registers and four locations. Tests here are the classic litmus shapes
with their known ARMv8 and x86-TSO verdicts.
-/
import Kraken.Promising.Machine

namespace Kraken.Promising.Toy

abbrev Reg := Fin 4

-- Operands: a register or an immediate.
inductive Opd | r (r : Reg) | i (v : Nat)
  deriving BEq, Hashable

def Opd.regs : Opd → List Reg | .r x => [x] | .i _ => []

inductive Instr
  /-- `dst := load [loc + depReg*0]` -/
  | ld (k : LoadKind) (xcl : Bool) (dst : Reg) (loc : Nat) (addrDep : List Reg := [])
  /-- `store [loc] src`; `status` receives 0/1 for an exclusive. -/
  | st (k : StoreKind) (xcl : Bool) (loc : Nat) (src : Opd) (addrDep : List Reg := []) (status : Option Reg := none)
  /-- `dst := old; [loc] := old + src` (an `LDADD`), or a CAS when `cmp` is given.
  `noRet`: the old value is discarded and `dst` is left alone (an AArch64
  atomic to `XZR`, herd's `NoRet`: not ordered by `fence .ld`, never an
  acquire). -/
  | rmw (k : RmwKind) (dst : Reg) (loc : Nat) (src : Opd) (cmp : Option Opd := none) (noRet : Bool := false)
  | fence (k : FenceKind)
  | mov (dst : Reg) (src : Opd)
  | add (dst : Reg) (a b : Opd)
  /-- `if r = v then goto target` -/
  | beq (r : Reg) (v : Nat) (target : Nat)
  /-- `dst := load [loc]` at `bytes` bytes, resolved against `decls`: a
  mixed-size access unless `bytes = 8`. -/
  | ldw (dst : Reg) (loc : Nat) (bytes : Nat)
  deriving BEq, Hashable

structure State where
  prog : Array Instr
  pc : Nat := 0
  regs : Array (BitVec 64) := #[0, 0, 0, 0]

/-- Locations are 8 bytes wide; values travel zero-extended to 128 bits. -/
def loc (n : Nat) : Loc := { addr := BitVec.ofNat 64 (0x1000 + 8 * n), bytes := 8 }

/-- The four locations, declared at their width. -/
def decls : Decls := { locs := (List.range 4).map loc }

def State.get (s : State) : Opd → BitVec 64
  | .r r => s.regs[r.val]!
  | .i v => BitVec.ofNat 64 v

def State.set (s : State) (r : Reg) (v : BitVec 64) : State := { s with regs := s.regs.set! r.val v }
def State.next (s : State) : State := { s with pc := s.pc + 1 }

def exec (s : State) : Option (EvTree State) := do
  let i ← s.prog[s.pc]?
  return match i with
  | .ld k xcl dst l _ => .load k xcl (loc l) fun v => .done ((s.set dst (v.setWidth 64)).next)
  | .st k xcl l src _ status => .store k xcl (loc l) ((s.get src).setWidth 128) fun ok =>
      let s := match status with | some r => s.set r (if ok then 0 else 1) | none => s
      .done s.next
  | .rmw k dst l src cmp noRet => .rmw k noRet (loc l)
      (fun old => let old := old.setWidth 64
        let new : Option (BitVec 64) := match cmp with
          | some c => if old == s.get c then some (s.get src) else none
          | none => some (old + s.get src)
        new.map (·.setWidth 128))
      fun old => .done ((if noRet then s else s.set dst (old.setWidth 64)).next)
  | .fence k => .fence k fun _ => .done s.next
  | .mov dst src => .done ((s.set dst (s.get src)).next)
  | .add dst a b => .done ((s.set dst (s.get a + s.get b)).next)
  | .beq r v target => .done (if s.regs[r.val]! == BitVec.ofNat 64 v then { s with pc := target } else s.next)
  | .ldw dst l n =>
    match decls.resolve (loc l).addr n with
    | .ok l' => .load .plain false l' fun v => .done ((s.set dst (v.setWidth 64)).next)
    | .error m => .fault m

def deps (s : State) : InstrDeps Reg :=
  match s.prog[s.pc]? with
  | none => {}
  | some i => match i with
    | .ld _ _ dst _ ad => { addrRegs := ad, loadDefs := [dst] }
    | .st _ _ _ src ad status => { addrRegs := ad, dataRegs := src.regs, statusDefs := status.toList }
    | .rmw _ dst _ src cmp noRet =>
      { dataRegs := src.regs ++ (cmp.map Opd.regs).getD [], loadDefs := if noRet then [] else [dst] }
    | .fence _ => {}
    | .mov dst src => { dataRegs := src.regs, defs := [dst] }
    | .add dst a b => { dataRegs := a.regs ++ b.regs, defs := [dst] }
    | .beq r _ _ => { condRegs := [r], isBranch := true }
    | .ldw dst _ _ => { loadDefs := [dst] }

def isa : ISA where
  State := State
  RegId := Reg
  numRegs := 4
  regIndex := id
  exec := exec
  deps := deps
  -- The program is part of the state: threads running different programs
  -- must not share certification-cache entries (`certify` is memoised on
  -- the thread and the memory).
  beqState a b := a.pc == b.pc && a.regs == b.regs && a.prog == b.prog
  hashState s := mixHash (hash s.pc) (mixHash (hash s.regs) (hash s.prog))

/-- Run a test: threads as programs, projecting the final registers of every
thread (as naturals), sorted. -/
def run (A : Arch) (progs : List (List Instr)) : List (List (List Nat)) :=
  let c0 : Config isa := Config.init (progs.map fun p => ({ prog := p.toArray } : State)) []
  let r := explore (I := isa) A c0 (fun c => c.threads.toList.map fun t => t.st.regs.toList.map (·.toNat))
  r.finals.mergeSort (fun a b => decide (a.map (·.toString) ≤ b.map (·.toString)))

/-- Final values of locations `0..n-1` in every final state, sorted. -/
def runMem (A : Arch) (progs : List (List Instr)) (n : Nat) : List (List Nat) :=
  let c0 : Config isa := Config.init (progs.map fun p => ({ prog := p.toArray } : State)) []
  let r := explore (I := isa) A c0 (fun c => (List.range n).map fun i => (c.mem.finalVal (loc i)).toNat)
  r.finals.mergeSort (fun a b => decide (a.toString ≤ b.toString))

/-- Is the outcome (thread i, register j = v) reachable? -/
def allows (A : Arch) (progs : List (List Instr)) (cond : List (Nat × Nat × Nat)) : Bool :=
  (run A progs).any fun fin => cond.all fun (i, j, v) => fin[i]![j]! == v

section Tests
open Instr

-- x = 0, y = 1
-- MP: T0: x:=1; y:=1.  T1: r0:=y; r1:=x.  r0=1 ∧ r1=0
def MP (f0 f1 : List Instr) : List (List Instr) :=
  [[st .plain false 0 (.i 1)] ++ f0 ++ [st .plain false 1 (.i 1)],
   [ld .plain false 0 1] ++ f1 ++ [ld .plain false 1 0]]
def mpCond : List (Nat × Nat × Nat) := [(1, 0, 1), (1, 1, 0)]

/-- info: true -/
#guard_msgs in #eval allows .armv8 (MP [] []) mpCond
/-- info: false -/
#guard_msgs in #eval allows .armv8 (MP [fence .sy] [fence .sy]) mpCond
/-- info: true -/
#guard_msgs in #eval allows .armv8 (MP [fence .sy] []) mpCond
/-- info: false -/
#guard_msgs in #eval allows .armv8 (MP [fence .st] [fence .ld]) mpCond
-- MP+dmb.sy+addr
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[st .plain false 0 (.i 1), fence .sy, st .plain false 1 (.i 1)],
   [ld .plain false 0 1, ld .plain false 1 0 (addrDep := [0])]] mpCond
-- MP+dmb.sy+ctrl: control dependency does not order a load
/-- info: true -/
#guard_msgs in #eval allows .armv8
  [[st .plain false 0 (.i 1), fence .sy, st .plain false 1 (.i 1)],
   [ld .plain false 0 1, beq 0 1 2, ld .plain false 1 0]] mpCond
-- MP+dmb.sy+ctrlisb
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[st .plain false 0 (.i 1), fence .sy, st .plain false 1 (.i 1)],
   [ld .plain false 0 1, beq 0 1 2, fence .isb, ld .plain false 1 0]] mpCond
-- MP+rel+acq
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[st .plain false 0 (.i 1), st .rel false 1 (.i 1)],
   [ld .acq false 0 1, ld .plain false 1 0]] mpCond
-- MP+rel+acqpc
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[st .plain false 0 (.i 1), st .rel false 1 (.i 1)],
   [ld .acqPc false 0 1, ld .plain false 1 0]] mpCond
-- MP under TSO
/-- info: false -/
#guard_msgs in #eval allows .tso (MP [] []) mpCond
-- MP with a non-temporal store (x86 `movnti`) under TSO: weakly ordered, the
-- later ordinary store may become visible first
/-- info: true -/
#guard_msgs in #eval allows .tso
  [[st .nt false 0 (.i 1), st .plain false 1 (.i 1)],
   [ld .plain false 0 1, ld .plain false 1 0]] mpCond
-- ... and an ordinary store does not order a later non-temporal one
/-- info: true -/
#guard_msgs in #eval allows .tso
  [[st .plain false 0 (.i 1), st .nt false 1 (.i 1)],
   [ld .plain false 0 1, ld .plain false 1 0]] mpCond
-- `sfence` (`fence .st`), `mfence` (`fence .sy`) and a locked RMW order it
/-- info: false -/
#guard_msgs in #eval allows .tso
  [[st .nt false 0 (.i 1), fence .st, st .plain false 1 (.i 1)],
   [ld .plain false 0 1, ld .plain false 1 0]] mpCond
/-- info: false -/
#guard_msgs in #eval allows .tso
  [[st .nt false 0 (.i 1), fence .sy, st .plain false 1 (.i 1)],
   [ld .plain false 0 1, ld .plain false 1 0]] mpCond
/-- info: false -/
#guard_msgs in #eval allows .tso
  [[st .nt false 0 (.i 1), rmw .plain 2 2 (.i 1), st .plain false 1 (.i 1)],
   [ld .plain false 0 1, ld .plain false 1 0]] mpCond
-- `lfence` (`fence .ld`) does not
/-- info: true -/
#guard_msgs in #eval allows .tso
  [[st .nt false 0 (.i 1), fence .ld, st .plain false 1 (.i 1)],
   [ld .plain false 0 1, ld .plain false 1 0]] mpCond
-- under ARMv8, `.nt` is a plain store
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[st .nt false 0 (.i 1), fence .st, st .nt false 1 (.i 1)],
   [ld .plain false 0 1, fence .ld, ld .plain false 1 0]] mpCond
-- CoWW with a non-temporal store: same-location stores stay in order
/-- info: [[2]] -/
#guard_msgs in #eval runMem .tso [[st .nt false 0 (.i 1), st .plain false 0 (.i 2)]] 1

-- SB: T0: x:=1; r0:=y.  T1: y:=1; r0:=x.  r0=0 ∧ r0=0
def SB (f0 f1 : List Instr) : List (List Instr) :=
  [[st .plain false 0 (.i 1)] ++ f0 ++ [ld .plain false 0 1],
   [st .plain false 1 (.i 1)] ++ f1 ++ [ld .plain false 0 0]]
def sbCond : List (Nat × Nat × Nat) := [(0, 0, 0), (1, 0, 0)]

/-- info: true -/
#guard_msgs in #eval allows .armv8 (SB [] []) sbCond
/-- info: false -/
#guard_msgs in #eval allows .armv8 (SB [fence .sy] [fence .sy]) sbCond
/-- info: true -/
#guard_msgs in #eval allows .tso (SB [] []) sbCond
/-- info: false -/
#guard_msgs in #eval allows .tso (SB [fence .sy] [fence .sy]) sbCond
-- SB+rel+acq: `LDAR` after `STLR` is ordered on ARMv8
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[st .rel false 0 (.i 1), ld .acq false 0 1],
   [st .rel false 1 (.i 1), ld .acq false 0 0]] sbCond
-- SB+rel+acqpc: `LDAPR` after `STLR` is not
/-- info: true -/
#guard_msgs in #eval allows .armv8
  [[st .rel false 0 (.i 1), ld .acqPc false 0 1],
   [st .rel false 1 (.i 1), ld .acqPc false 0 0]] sbCond
-- SB+rfi-pos under TSO: store forwarding, allowed
/-- info: true -/
#guard_msgs in #eval allows .tso
  [[st .plain false 0 (.i 1), ld .plain false 1 0, ld .plain false 0 1],
   [st .plain false 1 (.i 1), ld .plain false 1 1, ld .plain false 0 0]]
  [(0, 0, 0), (0, 1, 1), (1, 0, 0), (1, 1, 1)]

-- LB: T0: r0:=x; y:=1.  T1: r0:=y; x:=1.  r0=1 ∧ r0=1
def LB (f0 f1 : List Instr) : List (List Instr) :=
  [[ld .plain false 0 0] ++ f0 ++ [st .plain false 1 (.i 1)],
   [ld .plain false 0 1] ++ f1 ++ [st .plain false 0 (.i 1)]]
def lbCond : List (Nat × Nat × Nat) := [(0, 0, 1), (1, 0, 1)]

/-- info: true -/
#guard_msgs in #eval allows .armv8 (LB [] []) lbCond
/-- info: false -/
#guard_msgs in #eval allows .armv8 (LB [fence .sy] [fence .sy]) lbCond
-- LB+datas
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[ld .plain false 0 0, st .plain false 1 (.r 0)],
   [ld .plain false 0 1, st .plain false 0 (.r 0)]] lbCond
-- LB+ctrls: control dependency orders a store
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[ld .plain false 0 0, beq 0 1 2, st .plain false 1 (.i 1)],
   [ld .plain false 0 1, beq 0 1 2, st .plain false 0 (.i 1)]] lbCond
/-- info: false -/
#guard_msgs in #eval allows .tso (LB [] []) lbCond

-- CoRR: two reads of the same location in program order cannot go backwards
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[st .plain false 0 (.i 1)],
   [ld .plain false 0 0, ld .plain false 1 0]] [(1, 0, 1), (1, 1, 0)]
-- CoWW + read
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[st .plain false 0 (.i 1), st .plain false 0 (.i 2)],
   [ld .plain false 0 0, ld .plain false 1 0]] [(1, 0, 2), (1, 1, 1)]

-- IRIW+dmbs: forbidden (multi-copy atomic)
/-- info: false -/
#guard_msgs in #eval allows .armv8
  [[st .plain false 0 (.i 1)], [st .plain false 1 (.i 1)],
   [ld .plain false 0 0, fence .sy, ld .plain false 1 1],
   [ld .plain false 0 1, fence .sy, ld .plain false 1 0]]
  [(2, 0, 1), (2, 1, 0), (3, 0, 1), (3, 1, 0)]
-- IRIW under TSO: forbidden
/-- info: false -/
#guard_msgs in #eval allows .tso
  [[st .plain false 0 (.i 1)], [st .plain false 1 (.i 1)],
   [ld .plain false 0 0, ld .plain false 1 1],
   [ld .plain false 0 1, ld .plain false 1 0]]
  [(2, 0, 1), (2, 1, 0), (3, 0, 1), (3, 1, 0)]

-- Exclusives: two threads incrementing with LDXR/STXR loops; final value 2.
def incr : List Instr :=
  [ld .plain true 0 0, add 0 (.r 0) (.i 1), st .plain true 0 (.r 0) (status := some 1), beq 1 1 0, ld .plain false 2 0]
/-- info: [[2]] -/
#guard_msgs in #eval runMem .armv8 [incr, incr] 1
-- A single store exclusive without a retry loop may fail: the final value
-- can be 1 (or 2 when both succeed; never 0 since the first always can succeed
-- but may also fail: 0 when both fail).
/-- info: [[0], [1], [2]] -/
#guard_msgs in #eval runMem .armv8 [incr.take 3, incr.take 3] 1

-- Atomic RMW increments under TSO: final value 2
/-- info: [[2]] -/
#guard_msgs in #eval runMem .tso
  [[rmw .plain 0 0 (.i 1), ld .plain false 2 0],
   [rmw .plain 0 0 (.i 1), ld .plain false 2 0]] 1

-- `noRet` RMWs (herd's `NoRet`, an AArch64 `STADD`): LB where T0's RMW adds 1
-- to x and T1 writes x := 1 after reading y = 1. The outcome "the RMW read
-- T1's write" is final x = 2.
def lbRmw (rk : RmwKind) (noRet : Bool) (f0 : List Instr) (sk : StoreKind := .plain) : List (List Instr) :=
  [[rmw rk 0 0 (.i 1) (noRet := noRet)] ++ f0 ++ [st sk false 1 (.i 1)],
   [ld .plain false 0 1, fence .sy, st .plain false 0 (.i 1)]]
def allowsLbRmw (A : Arch) (progs : List (List Instr)) : Bool :=
  let c0 : Config isa := Config.init (progs.map fun p => ({ prog := p.toArray } : State)) []
  let r := explore (I := isa) A c0 (fun c =>
    ((c.threads.toList.map fun t => t.st.regs[0]!.toNat)[1]!, (c.mem.finalVal (loc 0)).toNat))
  r.finals.contains (1, 2)
-- `fence .ld` (`DMB LD`) does not order a `noRet` read ...
/-- info: true -/
#guard_msgs in #eval allowsLbRmw .armv8 (lbRmw .plain true [fence .ld])
-- ... but orders an ordinary RMW read
/-- info: false -/
#guard_msgs in #eval allowsLbRmw .armv8 (lbRmw .plain false [fence .ld])
-- `fence .sy` and a later release store order it
/-- info: false -/
#guard_msgs in #eval allowsLbRmw .armv8 (lbRmw .plain true [fence .sy])
/-- info: false -/
#guard_msgs in #eval allowsLbRmw .armv8 (lbRmw .plain true [] .rel)
-- a `noRet` read is never an acquire (`LDADDA W0,WZR`, `LDADDAL W0,WZR`)
/-- info: true -/
#guard_msgs in #eval allowsLbRmw .armv8 (lbRmw .acq true [])
/-- info: false -/
#guard_msgs in #eval allowsLbRmw .armv8 (lbRmw .acq false [])
/-- info: true -/
#guard_msgs in #eval allowsLbRmw .armv8 (lbRmw .acqRel true [])
/-- info: false -/
#guard_msgs in #eval allowsLbRmw .armv8 (lbRmw .acqRel false [])
-- a `noRet` RMW leaves its destination alone
/-- info: [[0, 0, 0, 0]] -/
#guard_msgs in #eval (run .armv8 [[rmw .plain 0 0 (.i 1) (noRet := true)]]).map (·.head!)

-- The paper's LB with a promise: T0 reads 37 from T1's store that depends
-- on T0's own later store — allowed on ARM through promising.
/-- info: true -/
#guard_msgs in #eval allows .armv8
  [[ld .plain false 0 0, st .plain false 1 (.i 37)],
   [ld .plain false 0 1, st .plain false 0 (.r 0)]] [(0, 0, 37), (1, 0, 37)]

-- Mixed-size: a 4-byte load of an 8-byte location is reported as a fault,
-- and no run that reaches it has a final state; an 8-byte one is fine.
def faultsOf (A : Arch) (progs : List (List Instr)) : List String × Nat :=
  let c0 : Config isa := Config.init (progs.map fun p => ({ prog := p.toArray } : State)) []
  let r := explore (I := isa) A c0 (fun c => c.threads.toList.map fun t => t.st.regs.toList.map (·.toNat))
  (r.faults.eraseDups, r.finals.length)
/-- info: (["mixed-size access: 4 bytes at 0x0000000000001000, declared 8 bytes"], 0) -/
#guard_msgs in #eval faultsOf .tso [[st .plain false 0 (.i 1)], [ldw 0 0 4]]
/-- info: ([], 2) -/
#guard_msgs in #eval faultsOf .tso [[st .plain false 0 (.i 1)], [ldw 0 0 8]]

end Tests

end Kraken.Promising.Toy
