/-
**Concrete instance of `RelayAbs.mp_relay3_xchg_envG_verbatim`**: the `.kl`
runner's own executable for `mp_relay3_xchg.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `relayCodeV`.
- `runnerMatches`: the runner's prepared threads (`Kraken.Litmus.X64.prepareProgram`)
  run exactly `relayImageV` laid out by `relayLayoutV` (text at `0x100000`,
  one byte per instruction, the symbols `0x100` bytes apart from
  `0x1000000`: `d`, `f1`, `f2`), thread `0` from `writer` to `wdone`, thread
  `1` from `relay` to `rdone`, thread `2` from `reader` to `ddone`, with the
  `.kl`'s registers and empty private memory. (Not compared: the runner's
  `decls` and initial-memory locations; the theorem assumes no declarations
  and 4-byte `f1`, `f2` at `0`.)
- `mp_relay3_xchg_envG_verbatim_concrete`: the theorem at that layout and
  those threads; every hypothesis by `decide`/`rfl`/`simp`.
-/
import Kraken.Promising.SLR.EnvG.X64RelayAbsPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.RelayAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.RelayAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG.RelayX

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `mp_relay3_xchg.kl`:
labels 0, instructions 1 (text from `0x100000` to `0x100013`: the writer's 5
instructions, so `wdone` = `0x100005`, its `nop`, the relay's 7, so `rdone` =
`0x10000d`, its `nop`, the reader's 5, so `ddone` = `0x100013`), the padding
up to `d` at `0x1000000`, and the 256-byte slots of `d`, `f1` up to `f2`. -/
def relaySizesV : List Nat :=
  [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0,
   0x1000000 - 0x100013, 0, 0x100, 0, 0x100, 0]

/-- info: 31 -/
#guard_msgs in
#eval relaySizesV.length

/-- The runner's layout of the image. -/
@[reducible] def relayLayoutV : _root_.Layout :=
  { start := 0x100000, size := fun i => relaySizesV[i]?.getD 0 }

instance relayValidV : Executable.ValidLayout (relayLayoutV relayImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- A thread as the runner prepares it: the image, pc `pc`, end `endPc`,
registers `regs`, empty private memory, no declarations. -/
def relayThreadV (pc endPc : Int64) (regs : Reg64s) : X64.State where
  exe := relayLayoutV relayImageV
  endPc := endPc
  st := ({ ({} : MachineData) with regs }, pc)

/-- The writer: from `writer` (`0x100000`) to `wdone` (`0x100005`),
`rdi = f1`, `rsi = d`. -/
def relayW0 : X64.State :=
  relayThreadV 0x100000 (0x100000 + 5) ((({} : MachineData).regs.set64 .rdi 0x1000100).set64 .rsi 0x1000000)

/-- The relay: from `relay` (`0x100006`) to `rdone` (`0x10000d`),
`rdi = f1`, `rsi = d`, `rdx = f2`. -/
def relayY1 : X64.State :=
  relayThreadV (0x100000 + 6) (0x100000 + 13)
    (((({} : MachineData).regs.set64 .rdi 0x1000100).set64 .rsi 0x1000000).set64 .rdx 0x1000200)

/-- The reader: from `reader` (`0x10000e`) to `ddone` (`0x100013`),
`rdi = f2`, `rsi = d`. -/
def relayR2 : X64.State :=
  relayThreadV (0x100000 + 14) (0x100000 + 19) ((({} : MachineData).regs.set64 .rdi 0x1000200).set64 .rsi 0x1000000)

/-- The initial memory: `d = f1 = f2 = 0` (4-byte words). -/
def relayInitMemV : List (Loc × Val) := [(⟨0x1000000, 4⟩, 0), (⟨0x1000100, 4⟩, 0), (⟨0x1000200, 4⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def relayKl : String := include_str "../../../Examples/LockFree/X64/mp_relay3_xchg.kl"

/-- The `code` block of the `.kl` parses to `relayCodeV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == relayCodeV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches relayKl

/-- The runner's threads run `relayW0`'s, `relayY1`'s and `relayR2`'s
executable, pc, end, registers and private memory. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1, t2] => same t0 relayW0 && same t1 relayY1 && same t2 relayR2
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatches relayKl

/-! ## The instance -/

section
attribute [local instance] relayLayoutV

set_option maxRecDepth 8192 in
/-- A label's address from its position in the image. -/
theorem labY_at {x : Label} (i : Nat) (hd : relayImageV.drop i = Program.fromLabel relayImageV x := by decide)
    (hne : Program.fromLabel relayImageV x ≠ [] := by decide) : labY x = (relayLayoutV relayImageV).addrOf i :=
  Program.label_addrOf_drop relayImageV_wf.nodup hd hne

set_option maxRecDepth 8192 in
theorem symY_d : symY "d" = 0x1000000 := by
  show (labY "d").toBitVec = _; rw [labY_at 26]; decide
set_option maxRecDepth 8192 in
theorem symY_f1 : symY "f1" = 0x1000100 := by
  show (labY "f1").toBitVec = _; rw [labY_at 28]; decide
set_option maxRecDepth 8192 in
theorem symY_f2 : symY "f2" = 0x1000200 := by
  show (labY "f2").toBitVec = _; rw [labY_at 30]; decide

set_option maxRecDepth 8192 in
theorem relayW0_start : StartWV relayW0 :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labY "writer"; rw [labY_at 0]; decide,
    by show (0x100000 + 5 : Int64) = labY "wdone"; rw [labY_at 6]; decide,
    by rw [symY_f1]; simp [relayW0, relayThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symY_d]; simp [relayW0, relayThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

set_option maxRecDepth 8192 in
theorem relayY1_start : StartYV relayY1 :=
  ⟨rfl, rfl, by show (0x100000 + 6 : Int64) = labY "relay"; rw [labY_at 8]; decide,
    by show (0x100000 + 13 : Int64) = labY "rdone"; rw [labY_at 16]; decide,
    by rw [symY_f1]; simp [relayY1, relayThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symY_d]; simp [relayY1, relayThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symY_f2]; simp [relayY1, relayThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

set_option maxRecDepth 8192 in
theorem relayR2_start : StartRV relayR2 :=
  ⟨rfl, rfl, by show (0x100000 + 14 : Int64) = labY "reader"; rw [labY_at 18]; decide,
    by show (0x100000 + 19 : Int64) = labY "ddone"; rw [labY_at 24]; decide,
    by rw [symY_f2]; simp [relayR2, relayThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symY_d]; simp [relayR2, relayThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

end

/-- **The x64 relay through `xchg`, `mp_relay3_xchg.kl`'s code verbatim, in
the runner's executable**: in every final configuration under `Arch.tso` the
reader's `ebx` is `43` and `[d] = 43`. -/
theorem mp_relay3_xchg_envG_verbatim_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [relayW0, relayY1, relayR2] relayInitMemV) c)
    (hf : c.final = true) :
    (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      c.mem.finalVal ⟨0x1000000, 4⟩ = 43#128 := by
  have h := mp_relay3_xchg_envG_verbatim (layout := relayLayoutV)
    ⟨by rw [symY_f1, symY_d]; decide, by rw [symY_f2, symY_d]; decide, by rw [symY_f1, symY_f2]; decide⟩
    relayW0_start relayY1_start relayR2_start
    (by rw [symY_f1]; simp only [Config.init_mem]; decide)
    (by rw [symY_f2]; simp only [Config.init_mem]; decide) hc hf
  rwa [symY_d] at h

end Kraken.Promising.X64.EnvG.RelayAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.RelayAbs.Concrete.mp_relay3_xchg_envG_verbatim_concrete
