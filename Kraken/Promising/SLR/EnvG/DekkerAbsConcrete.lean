/-
**Concrete instance of `DekkerAbs.x64_dekker_public_verbatim`**: the `.kl`
runner's own executable for `dekker_mfence.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `dkWorkerV`.
- `runnerMatches`: the runner's two prepared threads
  (`Kraken.Litmus.X64.prepareProgram`) run exactly `dkImageV` laid out by
  `dkLayoutV` (text at `0x100000`, one byte per instruction, the symbols at
  `0x1000000` (`flag0`), `0x1000100` (`flag1`), `0x1000200` (`counter`)),
  from the entry label with the exit label as end, with the registers `dk0`
  and `dk1` give (`%rsi`/`%rdi` the own/other flag) and empty private memory.
  (Not compared: the runner's `decls` and initial-memory locations, as for
  `SpinAbs.Concrete`.)
- `x64_dekker_public_verbatim_concrete`: the theorem at that layout and those
  threads; every hypothesis by `decide`/`rfl`.
-/
import Kraken.Promising.SLR.EnvG.DekkerAbsPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.DekkerAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.DekkerAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `dekker_mfence.kl`: labels
0, instructions 1 (text from `0x100000` to `0x10000c`), the padding up to
`flag0` at `0x1000000`, and the 256-byte slots of `flag0` and `flag1`. -/
def dkSizesV : List Nat :=
  [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0x1000000 - 0x10000c, 0, 0x100, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def dkLayoutV : _root_.Layout := { start := 0x100000, size := fun i => dkSizesV[i]?.getD 0 }

instance dkValidV : Executable.ValidLayout (dkLayoutV dkImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- A worker's initial state as the runner prepares it: the image, pc at
`worker` (`0x100000`), end at `done` (`0x10000c`), `%rsi = f`, `%rdi = o`,
empty private memory, no declarations. -/
def dkThreadV (f o : BitVec 64) : X64.State where
  exe := dkLayoutV dkImageV
  endPc := 0x100000 + 12
  st := ({ ({} : MachineData) with regs := ((({} : MachineData).regs.set64 .rsi f).set64 .rdi o) }, 0x100000)

/-- Thread `0`: own flag `flag0`. -/
def dk0 : X64.State := dkThreadV 0x1000000 0x1000100

/-- Thread `1`: own flag `flag1`. -/
def dk1 : X64.State := dkThreadV 0x1000100 0x1000000

/-- The initial memory: the three words at `0` (4-byte words). -/
def dkInitMemV : List (Loc × Val) := [(⟨0x1000000, 4⟩, 0), (⟨0x1000100, 4⟩, 0), (⟨0x1000200, 4⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def dekkerKl : String := include_str "../../../Examples/LockFree/X64/dekker_mfence.kl"

/-- The `code` block of the `.kl` parses to `dkWorkerV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == dkWorkerV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches dekkerKl

/-- The runner's threads run `dk0`'s and `dk1`'s executable, pc, end,
registers and private memory. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 dk0 && same t1 dk1
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatches dekkerKl

/-! ## The instance -/

section
attribute [local instance] dkLayoutV

/-- A label's address from its position in the image. -/
theorem labD_at {x : Label} (i : Nat) (hd : dkImageV.drop i = Program.fromLabel dkImageV x := by decide)
    (hne : Program.fromLabel dkImageV x ≠ [] := by decide) : labD x = (dkLayoutV dkImageV).addrOf i :=
  Program.label_addrOf_drop dkImageV_wf.nodup hd hne

theorem symD_flag0 : symD "flag0" = 0x1000000 := by
  show (labD "flag0").toBitVec = _; rw [labD_at 15]; decide
theorem symD_flag1 : symD "flag1" = 0x1000100 := by
  show (labD "flag1").toBitVec = _; rw [labD_at 17]; decide
theorem symD_counter : symD "counter" = 0x1000200 := by
  show (labD "counter").toBitVec = _; rw [labD_at 19]; decide

theorem dkThreadV_start (f o : BitVec 64) : StartDV f o (dkThreadV f o) :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labD "worker"; rw [labD_at 0]; decide,
    by show (0x100000 + 12 : Int64) = labD "done"; rw [labD_at 13]; decide,
    by simp [dkThreadV, Reg64s.get64, Reg64s.set64], by simp [dkThreadV, Reg64s.get64, Reg64s.set64],
    Split.empty _⟩

/-- **Dekker with `mfence`, `dekker_mfence.kl`'s code verbatim, in the
runner's executable**: no final configuration under `Arch.tso` has both
threads' `edx` at `1` and the counter at `1`. -/
theorem x64_dekker_public_verbatim_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [dk0, dk1] dkInitMemV) c) (hf : c.final = true) :
    ¬ ((∃ t, c.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      (∃ t, c.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      c.mem.finalVal ⟨0x1000200, 4⟩ = 1) := by
  have h0 : StartDV (symD "flag0") (symD "flag1") dk0 := by
    rw [symD_flag0, symD_flag1]; exact dkThreadV_start _ _
  have h1 : StartDV (symD "flag1") (symD "flag0") dk1 := by
    rw [symD_flag0, symD_flag1]; exact dkThreadV_start _ _
  have h := x64_dekker_public_verbatim
    (by rw [symD_flag0, symD_flag1, symD_counter]; exact ⟨by decide, by decide, by decide⟩) h0 h1
    (by rw [symD_flag0]; simp only [Config.init_mem]; decide)
    (by rw [symD_flag1]; simp only [Config.init_mem]; decide)
    (by rw [symD_counter]; simp only [Config.init_mem]; decide) hc hf
  rwa [symD_counter] at h

end

end Kraken.Promising.X64.EnvG.DekkerAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.DekkerAbs.Concrete.x64_dekker_public_verbatim_concrete
