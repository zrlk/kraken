/-
**Concrete instance of `SpscAbs.x64_spsc_envG_verbatim`**: the `.kl` runner's own executable for `spsc_queue.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `spscCodeV`.
- `runnerMatches`: the runner's prepared threads (`Kraken.Litmus.X64.prepareProgram`)
  run exactly `spscImageV` laid out by `spscLayoutV` (text at `0x100000`,
  one byte per instruction, the symbols `0x100` bytes apart from
  `0x1000000`: `buf0`, `buf1`, `head`, `tail`), thread `0` from `producer`
  to `pdone`, thread `1` from `consumer` to `cdone`, both with
  `rbx = buf0` and empty private memory. (Not compared: the runner's
  `decls` and initial-memory locations; the theorem assumes no declarations
  and 4-byte `tail`, `head` at `0`.)
- `x64_spsc_envG_verbatim_concrete`: the theorem at that layout and those
  threads; every hypothesis by `decide`/`rfl`/`simp`.
-/
import Kraken.Promising.SLR.EnvG.X64SpscAbsPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.SpscAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.SpscAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG.SpscX

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `spsc_queue.kl`: labels
0, instructions 1 (text from `0x100000` to `0x10002d`: the producer's 16
instructions, so `pdone` = `consumer` = `0x100010`, the consumer's 29, so
`cdone` = `0x10002d`), the padding up to `buf0` at `0x1000000`, and the
256-byte slots of `buf0`, `buf1`, `head` up to `tail`. -/
def spscSizesV : List Nat :=
  [0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0,
   0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0,
   0x1000000 - 0x10002d, 0, 0x100, 0, 0x100, 0, 0x100, 0]

/-- info: 62 -/
#guard_msgs in
#eval spscSizesV.length

/-- The runner's layout of the image. -/
@[reducible] def spscLayoutV : _root_.Layout :=
  { start := 0x100000, size := fun i => spscSizesV[i]?.getD 0 }

instance spscValidV : Executable.ValidLayout (spscLayoutV spscImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- A thread as the runner prepares it: the image, pc `pc`, end `endPc`,
`rbx = buf0`, empty private memory, no declarations. -/
def spscThreadV (pc endPc : Int64) : X64.State where
  exe := spscLayoutV spscImageV
  endPc := endPc
  st := ({ ({} : MachineData) with regs := (({} : MachineData).regs.set64 .rbx 0x1000000) }, pc)

/-- The producer: from `producer` (`0x100000`) to `pdone` (`0x100010`). -/
def spscP0 : X64.State := spscThreadV 0x100000 (0x100000 + 16)

/-- The consumer: from `consumer` (`0x100010`) to `cdone` (`0x10002d`). -/
def spscC1 : X64.State := spscThreadV (0x100000 + 16) (0x100000 + 45)

/-- The initial memory: `buf0 = buf1 = head = tail = 0` (4-byte words). -/
def spscInitMemV : List (Loc × Val) :=
  [(⟨0x1000000, 4⟩, 0), (⟨0x1000100, 4⟩, 0), (⟨0x1000200, 4⟩, 0), (⟨0x1000300, 4⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def spscKl : String := include_str "../../../Examples/LockFree/X64/spsc_queue.kl"

/-- The `code` block of the `.kl` parses to `spscCodeV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == spscCodeV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches spscKl

/-- The runner's threads run `spscP0`'s and `spscC1`'s executable, pc, end,
registers and private memory. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 spscP0 && same t1 spscC1
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatches spscKl

/-! ## The instance -/

section
attribute [local instance] spscLayoutV

set_option maxRecDepth 8192 in
/-- A label's address from its position in the image. -/
theorem labS_at {x : Label} (i : Nat) (hd : spscImageV.drop i = Program.fromLabel spscImageV x := by decide)
    (hne : Program.fromLabel spscImageV x ≠ [] := by decide) : labS x = (spscLayoutV spscImageV).addrOf i :=
  Program.label_addrOf_drop spscImageV_wf.nodup hd hne

set_option maxRecDepth 8192 in
theorem symS_buf0 : symS "buf0" = 0x1000000 := by
  show (labS "buf0").toBitVec = _; rw [labS_at 55]; decide
set_option maxRecDepth 8192 in
theorem symS_head : symS "head" = 0x1000200 := by
  show (labS "head").toBitVec = _; rw [labS_at 59]; decide
set_option maxRecDepth 8192 in
theorem symS_tail : symS "tail" = 0x1000300 := by
  show (labS "tail").toBitVec = _; rw [labS_at 61]; decide

set_option maxRecDepth 8192 in
theorem spscP0_start : StartPV spscP0 :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labS "producer"; rw [labS_at 0]; decide,
    by show (0x100000 + 16 : Int64) = labS "pdone"; rw [labS_at 19]; decide,
    by rw [symS_buf0]; simp [spscP0, spscThreadV, Reg64s.get64, Reg64s.set64],
    fun _ => by simp [spscP0, spscThreadV]⟩

set_option maxRecDepth 8192 in
theorem spscC1_start : StartCV spscC1 :=
  ⟨rfl, rfl, by show (0x100000 + 16 : Int64) = labS "consumer"; rw [labS_at 20]; decide,
    by show (0x100000 + 45 : Int64) = labS "cdone"; rw [labS_at 53]; decide,
    by rw [symS_buf0]; simp [spscC1, spscThreadV, Reg64s.get64, Reg64s.set64],
    fun _ => by simp [spscC1, spscThreadV]⟩

end

/-- **The x64 SPSC queue, `spsc_queue.kl`'s code verbatim, in the runner's
executable**: in every final configuration under `Arch.tso` the consumer
has `r12d = 1`, `r13d = 2`, `r14d = 3`. -/
theorem x64_spsc_envG_verbatim_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [spscP0, spscC1] spscInitMemV) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r12) = 1 ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r13) = 2 ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r14) = 3 :=
  x64_spsc_envG_verbatim (layout := spscLayoutV)
    (by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [symS_buf0, symS_head, symS_tail] <;> decide)
    spscP0_start spscC1_start
    (by rw [symS_tail]; simp only [Config.init_mem]; decide)
    (by rw [symS_head]; simp only [Config.init_mem]; decide) hc hf

end Kraken.Promising.X64.EnvG.SpscAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.SpscAbs.Concrete.x64_spsc_envG_verbatim_concrete
