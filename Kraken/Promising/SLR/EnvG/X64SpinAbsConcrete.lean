/-
**Concrete instance of `SpinAbs.x64_spin_counter_envG_verbatim`**: the `.kl`
runner's own executable for `spinlock2.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `spinWorkerV`.
- `runnerMatches`: the runner's prepared threads (`Kraken.Litmus.X64.prepareProgram`)
  run exactly `spinImageV` laid out by `spinLayoutV` (text at `0x100000`, one
  byte per instruction, the symbols at `0x1000000` (`lock`) and `0x1000100`
  (`counter`)), from the entry label with the exit label as end, with empty
  registers and private memory. (Not compared: the runner's `decls` and
  initial-memory locations, which declare the symbols as unsized locations;
  the theorem assumes no declarations and 4-byte locations, as
  `x64_spin_counter_envG`.)
- `x64_spin_counter_envG_verbatim_concreteN`/`_concrete2`: the theorem at
  that layout and those threads; every hypothesis by `decide`/`rfl`.
-/
import Kraken.Promising.SLR.EnvG.X64SpinAbsPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.SpinAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.SpinAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `spinlock2.kl`: labels 0,
instructions 1 (text from `0x100000` to `0x10000c`), the padding up to `lock`
at `0x1000000`, and the 256-byte slot of `lock` up to `counter`. -/
def spinSizesV : List Nat := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0x1000000 - 0x10000c, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def spinLayoutV : _root_.Layout := { start := 0x100000, size := fun i => spinSizesV[i]?.getD 0 }

instance spinValidV : Executable.ValidLayout (spinLayoutV spinImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- A worker's initial state as the runner prepares it: the image, pc at
`worker` (`0x100000`), end at `done` (`0x10000c`), empty registers and
private memory, no declarations. -/
def spinWorkerV0 : X64.State where
  exe := spinLayoutV spinImageV
  endPc := 0x100000 + 12
  st := ({}, 0x100000)

/-- The initial memory: `lock = 0`, `counter = 0` (4-byte words). -/
def spinInitMemV : List (Loc × Val) := [(⟨0x1000000, 4⟩, 0), (⟨0x1000100, 4⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def spinlock2Kl : String := include_str "../../../Examples/LockFree/X64/spinlock2.kl"

/-- The `code` block of the `.kl` parses to `spinWorkerV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == spinWorkerV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches spinlock2Kl

/-- The runner's threads run `spinWorkerV0`'s executable, pc, end, registers
and private memory. -/
def runnerMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => pr.config.threads.size == 2 && pr.config.threads.all fun t =>
      t.st.exe == spinWorkerV0.exe && t.st.endPc == spinWorkerV0.endPc && t.st.st.2 == spinWorkerV0.st.2 &&
      t.st.st.1.regs == spinWorkerV0.st.1.regs && t.st.st.1.dmem == spinWorkerV0.st.1.dmem

/-- info: true -/
#guard_msgs in
#eval runnerMatches spinlock2Kl

/-! ## The instance -/

section
attribute [local instance] spinLayoutV

/-- A label's address from its position in the image. -/
theorem labV_at {x : Label} (i : Nat) (hd : spinImageV.drop i = Program.fromLabel spinImageV x := by decide)
    (hne : Program.fromLabel spinImageV x ≠ [] := by decide) : labV x = (spinLayoutV spinImageV).addrOf i :=
  Program.label_addrOf_drop spinImageV_wf.nodup hd hne

theorem symV_lock : symV "lock" = 0x1000000 := by
  show (labV "lock").toBitVec = _; rw [labV_at 15]; decide
theorem symV_counter : symV "counter" = 0x1000100 := by
  show (labV "counter").toBitVec = _; rw [labV_at 17]; decide

theorem spinWorkerV0_start : StartStateV spinWorkerV0 :=
  ⟨rfl, rfl, by show _ = labV "worker"; rw [labV_at 0]; decide,
    by show _ = labV "done"; rw [labV_at 13]; decide, Split.empty _⟩

end

/-- **`counter = N`** for `N < 2 ^ 32` workers running `spinlock2.kl`'s code
verbatim in the runner's executable, under `Arch.tso`. -/
theorem x64_spin_counter_envG_verbatim_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init (List.replicate N spinWorkerV0) spinInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = BitVec.ofNat 128 N := by
  have h := x64_spin_counter_envG_verbatim (layout := spinLayoutV) N (by rw [symV_lock, symV_counter]; decide)
    hN32 (fun s hs => (List.eq_of_mem_replicate hs) ▸ spinWorkerV0_start) List.length_replicate
    (by rw [symV_counter]; simp only [Config.init_mem]; decide)
    (by rw [symV_lock]; simp only [Config.init_mem]; decide) hc hf
  rwa [symV_counter] at h

/-- **`counter = 2`** for the two workers of `spinlock2.kl`. -/
theorem x64_spin_counter_envG_verbatim_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [spinWorkerV0, spinWorkerV0] spinInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = 2 :=
  x64_spin_counter_envG_verbatim_concreteN 2 (by decide) hc hf

end Kraken.Promising.X64.EnvG.SpinAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.SpinAbs.Concrete.x64_spin_counter_envG_verbatim_concreteN
#print axioms Kraken.Promising.X64.EnvG.SpinAbs.Concrete.x64_spin_counter_envG_verbatim_concrete2
