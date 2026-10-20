/-
Running an AArch64 litmus test on the Promising machine.

Symbolic locations get addresses; each thread's program is parsed by the
AArch64 parser and laid out at its own base; registers are initialised from
the `{ ... }` block; shared memory is left out of every thread's `dmem`, so
each access reaches the memory model. The final states are projected onto
the test's observables and reported in herd's format.
-/
import Kraken.AArch64.Parser
import Kraken.Promising.AArch64
import Kraken.Litmus.Syntax
import Kraken.Litmus.Program
import Kraken.Litmus.Layout
import Kraken.Promising.Interactive

namespace Kraken.Litmus.AArch64

open Kraken.Promising

/-- Symbolic locations, in 256-byte slots from `0x1000` (`MemLayout`).
Untyped tests run in legacy mode: every symbol unsized, as before typed locations; a
test that types a location is sized (see `Layout.lean`). -/
def symBase : Nat := 0x1000

/-- The type a test declares for a register, if any. -/
def regType (t : Test) (r : ThreadReg) : Option String :=
  t.inits.findSome? fun | .reg r' _ ty => if r' == r then ty else none | _ => none

/-- herd prints a register with the width of the last instruction that wrote
it (`W0` ← 32-bit signed, `X0` ← 64-bit signed). Approximated syntactically:
the destination operand of the last instruction naming the register. -/
def lastWriteWidth (lines : List String) (reg : String) : Option Nat :=
  let n := String.ofList (reg.toList.drop 1)   -- "X3" → "3"
  let isDest (mnem : String) (i : Nat) : Bool :=
    let m := mnem.toUpper
    if m.startsWith "STXR" || m.startsWith "STLXR" || m.startsWith "STXP" || m.startsWith "STLXP" then i == 0
    else if m.startsWith "LDXP" || m.startsWith "LDAXP" || m.startsWith "CASP" then i ≤ 1
    else if m.startsWith "ST" || m.startsWith "CMP" || m.startsWith "CMN" || m.startsWith "TST"
         || m.startsWith "B" || m.startsWith "CB" || m.startsWith "TB" || m.startsWith "CCM" then false
    else if m.startsWith "SWP" || m.startsWith "LDADD" || m.startsWith "LDCLR" || m.startsWith "LDEOR"
         || m.startsWith "LDSET" || m.startsWith "LDSMAX" || m.startsWith "LDSMIN" || m.startsWith "LDUMAX"
         || m.startsWith "LDUMIN" then i == 1
    else if m.startsWith "LDP" || m.startsWith "STP" then i ≤ 1 && !(m.startsWith "STP")
    else i == 0
  lines.foldl (init := none) fun acc l =>
    let l := l.trimAscii.copy
    match (l.splitOn " ").filter (· ≠ "") with
    | [] => acc
    | mnem :: rest =>
      let ops := ((" ".intercalate rest).splitOn ",").map fun o =>
        (o.trimAscii.copy.splitOn "[").headD "" |>.trimAscii.copy
      let hit := (ops.zipIdx.map fun (o, i) => (i, o)).findSome? fun (i, o) =>
        let o := o.toUpper
        if isDest mnem i then
          if o == s!"W{n}" then some 32 else if o == s!"X{n}" then some 64 else none
        else none
      hit <|> acc

def regOfName (name : String) : Option XReg :=
  match Kraken.AArch64.Parser.parseXRegName name with
  | some (_, r) => some r
  | none => none

structure Prepared where
  config : Config Promising.AArch64.isa
  /-- The same configuration for the FEAT_LSE2 ISA (`Promising.AArch64.isaLSE2`,
  opt-in: `run (lse2 := true)`, `krakenlitmus_aarch64 -lse2`). -/
  configLSE2 : Config Promising.AArch64.isaLSE2
  layout : MemLayout

/-- herd prints a register by the width of its last write
(`lastWriteWidth`), signed; 64 bits if never written. -/
def regDefault (t : Test) (r : ThreadReg) : Nat × Bool :=
  ((t.threads[r.tid]?.bind fun lines => lastWriteWidth lines r.reg).getD 64, true)

/-- A register's initial value. -/
def regInit (l : MemLayout) (r : ThreadReg) (v : Value) : Except String (BitVec 64) :=
  match l.valueBits? v with
  | some b => pure (b.setWidth 64)
  | none => throw s!"bad initial value for {r.tid}:{r.reg}"

/-- Lay out and initialise the test. -/
def prepare (t : Test) : Except String Prepared := do
  -- symbolic locations: every symbol mentioned anywhere
  let syms := (t.inits.flatMap fun
      | .loc x v _ => x :: (match v with | .sym y => [y] | _ => [])
      | .reg _ v _ => (match v with | .sym y => [y] | _ => []))
    ++ t.observables.filterMap (fun | .loc x => some x | _ => none)
    ++ t.cond.obs.filterMap (fun | .loc x => some x | _ => none)
  -- layout and initial memory
  let mlayout ← MemLayout.build symBase t syms
  let initMem ← mlayout.initMem t
  let decls := mlayout.decls initMem
  -- threads
  let states ← t.threads.mapIdxM fun tid lines => do
    let prog ← match Kraken.AArch64.Parser.parse ("\n".intercalate lines) with
      | .ok p => pure p
      | .error e => throw s!"P{tid}: {e}"
    let base : Int64 := Int64.ofNat (0x100000 * (tid + 1))
    let layout : _root_.Layout := { start := base, size i := (prog[i]?.map Directive.fakeSize).getD 0 }
    let exe : _root_.Executable := layout prog
    let endPc := base + Int64.ofNat (prog.map Directive.fakeSize).sum
    let mut regs : Reg64s := {}
    for i in t.inits do
      if let .reg r v _ := i then
        if r.tid == tid then
          let some xr := regOfName r.reg | throw s!"unknown register {r.reg}"
          regs := regs.setXReg xr (← regInit mlayout r v)
    let st : MachineState := ({ regs } , base)
    -- instruction text by address: instructions are 4 bytes, labels 0
    let texts := (prog.zip lines).filterMap fun (d, l) => match d with | .label _ => none | _ => some l
    let showPc (pc : Int64) : String :=
      let i := ((pc - base).toBitVec.toNat) / 4
      texts[i]?.getD s!"pc={pc}"
    pure ({ exe, endPc, st, showPc, decls } : Promising.AArch64.State)
  return { config := Config.init states initMem, configLSE2 := Config.init states initMem, layout := mlayout }

/-- Project the final thread states and memory onto the test's observables. -/
def projectSt (t : Test) (l : MemLayout) (sts : Array Promising.AArch64.State) (mem : Memory) : FinalState :=
  t.observables.map fun o => (o, match o with
    | .reg r =>
      let v : BitVec 64 := match sts[r.tid]?, regOfName r.reg with
        | some st, some xr => st.st.1.regs.getXReg xr
        | _, _ => 0
      l.present (regType t r) (regDefault t r) (v.setWidth 128)
    | .loc x => l.finalLoc mem x)

/-- Project a final configuration onto the test's observables. -/
def project (t : Test) (l : MemLayout) (c : Config Promising.AArch64.isa) : FinalState :=
  projectSt t l (c.threads.map (·.st)) c.mem

/-- Lay out and initialise a `.kl` program: one executable shared by all
threads, each starting at its entry label and halting at its exit label,
with a private mapped stack. -/
def prepareProgram (p : Program) : Except String Prepared := do
  let t := p.toTest
  let syms := (t.inits.flatMap fun
      | .loc x v _ => x :: (match v with | .sym y => [y] | _ => [])
      | .reg _ v _ => (match v with | .sym y => [y] | _ => []))
    ++ t.observables.filterMap (fun | .loc x => some x | _ => none)
  let mlayout ← MemLayout.build symBase t syms
  let initMem ← mlayout.initMem t
  let decls := mlayout.decls initMem
  let prog ← match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok pr => pure pr
    | .error e => throw s!"code: {e}"
  let base : Int64 := Int64.ofNat 0x100000
  let layout : _root_.Layout := { start := base, size i := (prog[i]?.map Directive.fakeSize).getD 0 }
  let exe : _root_.Executable := layout prog
  let labels := _root_.Executable.labels exe
  -- one text per instruction directive, in layout order (a line may carry
  -- labels and an instruction)
  let texts := p.code.flatMap fun l => match Kraken.AArch64.Parser.parse l with
    | .ok ds => ds.filterMap fun | .label _ => none | _ => some l
    | .error _ => [l]
  let showPc (pc : Int64) : String := texts[((pc - base).toBitVec.toNat) / 4]?.getD s!"pc={pc}"
  let states ← p.threads.mapM fun th => do
    let entry := labels.label th.entry
    let exit := labels.label th.exit
    if entry == -1 then throw s!"P{th.tid}: unknown entry label {th.entry}"
    if exit == -1 then throw s!"P{th.tid}: unknown exit label {th.exit}"
    let mut regs : Reg64s := {}
    let mut dmem : DataMem := ∅
    if p.stack > 0 then
      let bottom : BitVec 64 := BitVec.ofNat 64 (0x200000 + th.tid * 0x10000)
      dmem := Mem.storeBytes dmem bottom (List.replicate p.stack 0)
      regs := { regs with SP := UInt64.ofBitVec (bottom + BitVec.ofNat 64 p.stack) }
    for i in t.inits do
      if let .reg r v _ := i then
        if r.tid == th.tid then
          if r.reg.toUpper == "SP" then
            regs := { regs with SP := UInt64.ofBitVec (← regInit mlayout r v) }
          else
            let some xr := regOfName r.reg | throw s!"unknown register {r.reg}"
            regs := regs.setXReg xr (← regInit mlayout r v)
    pure ({ exe, endPc := exit, st := ({ regs, dmem }, entry), showPc, decls } : Promising.AArch64.State)
  return { config := Config.init states initMem, configLSE2 := Config.init states initMem, layout := mlayout }

/-- Location names for traces and the stepper. -/
def locNamer (l : MemLayout) (loc : Loc) : String := l.nameAt loc.addr

structure Result where
  report : String
  /-- The test's expectation holds (`Ok`). -/
  ok : Bool
  configs : Nat
  boundHit : Bool
  faults : List String
  /-- A witness trace per final state, with whether the state satisfies the condition. -/
  witnesses : List (FinalState × Bool × String)

def runPrepared (t : Test) (p : Prepared) (kind : Option String) (o : ExploreOpts) (lse2 : Bool := false) :
    Result :=
  let r := if lse2 then
      explore (I := Promising.AArch64.isaLSE2) Arch.armv8 p.configLSE2
        (fun c => projectSt t p.layout (c.threads.map (·.st)) c.mem) o
    else explore (I := Promising.AArch64.isa) Arch.armv8 p.config (project t p.layout) o
  let norm (o : Obs) (v : Value) : Value := match o, v with
    | .reg r, .num n => p.layout.present (regType t r) (regDefault t r) ((BitVec.ofInt 64 n).setWidth 128)
    | .loc x, v => p.layout.normLoc x v
    | _, v => v
  let env (s : FinalState) (o : Obs) : Option Value := (s.find? (·.1 == o)).map (·.2)
  -- "interesting" states: witnesses of an `exists`, violations of a `forall`/`~exists`
  let witnesses := r.witnesses.map fun (st, tr) =>
    let hit := t.cond.eval (env st) norm
    (st, (if t.quant == .forall then !hit else hit), formatTrace (locNamer p.layout) tr)
  { report := report t r.finals kind norm, ok := verdict t r.finals norm,
    configs := r.configs, boundHit := r.boundHit,
    faults := r.faults.eraseDups, witnesses }

/-- Interactive stepping of a test or program. -/
def interact (p : Prepared) (o : ExploreOpts) : IO Unit :=
  interactive (I := Promising.AArch64.isa) Arch.armv8 o (locNamer p.layout) p.config

/-- A mixed-size access makes the test unsupported, as herd rejects it
("Illegal mixed-size test") unless run with `-variant mixed`. -/
def checkMixed (r : Result) : Except String Result :=
  match r.faults.find? (·.startsWith "mixed-size access") with
  | some m => throw s!"unsupported: {m}"
  | none => pure r

def prepareAny (t : Test) : Except String Prepared := prepare t

/-- Run a test. `lse2`: with FEAT_LSE2's single-copy-atomic 16-byte `LDP`/`STP`
(`Promising.AArch64.isaLSE2`), a Kraken-only option that herd does not model. -/
def run (t : Test) (kind : Option String := none) (o : ExploreOpts := {}) (lse2 : Bool := false) :
    Except String Result := do
  let p ← prepare t
  checkMixed (runPrepared t p kind o lse2)

def runProgram (p : Program) (kind : Option String := none) (o : ExploreOpts := {}) (lse2 : Bool := false) :
    Except String Result := do
  let pr ← prepareProgram p
  checkMixed (runPrepared p.toTest pr kind o lse2)

end Kraken.Litmus.AArch64
