/-
**Concrete instance of `CmpxAbs.x64_cmpx_counter_envG_verbatim`**: the `.kl`
runner's own executable for `spinlock_cmpxchg2.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `cmpxWorkerV`.
- `runnerMatches`: the runner's prepared threads (`Kraken.Litmus.X64.prepareProgram`)
  run exactly `cmpxImageV` laid out by `cmpxLayoutV` (text at `0x100000`, one
  byte per instruction, the symbols at `0x1000000` (`lock`) and `0x1000100`
  (`counter`)), from the entry label with the exit label as end, with empty
  registers and private memory. (Not compared: the runner's `decls` and
  initial-memory locations, which declare the symbols as unsized locations;
  the theorem assumes no declarations and 4-byte locations, as
  `x64_cmpx_counter_envG'`.)
- `x64_cmpx_counter_envG_verbatim_concreteN`/`_concrete2`: the theorem at
  that layout and those threads; every hypothesis by `decide`/`rfl`.
-/
import Kraken.Promising.SLR.EnvG.X64CmpxAbsPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.CmpxAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.CmpxAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `spinlock_cmpxchg2.kl`: labels 0,
instructions 1 (text from `0x100000` to `0x100009`), the padding up to `lock`
at `0x1000000`, and the 256-byte slot of `lock` up to `counter`. -/
def cmpxSizesV : List Nat := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0x1000000 - 0x100009, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def cmpxLayoutV : _root_.Layout := { start := 0x100000, size := fun i => cmpxSizesV[i]?.getD 0 }

instance cmpxValidV : Executable.ValidLayout (cmpxLayoutV cmpxImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- A worker's initial state as the runner prepares it: the image, pc at
`worker` (`0x100000`), end at `done` (`0x100009`), empty registers and
private memory, no declarations. -/
def cmpxWorkerV0 : X64.State where
  exe := cmpxLayoutV cmpxImageV
  endPc := 0x100000 + 9
  st := ({}, 0x100000)

/-- The initial memory: `lock = 0`, `counter = 0` (4-byte words). -/
def cmpxInitMemV : List (Loc × Val) := [(⟨0x1000000, 4⟩, 0), (⟨0x1000100, 4⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def spinlockCmpxchg2Kl : String := include_str "../../../Examples/LockFree/X64/spinlock_cmpxchg2.kl"

/-- The `code` block of the `.kl` parses to `cmpxWorkerV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == cmpxWorkerV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches spinlockCmpxchg2Kl

/-- The runner's threads run `cmpxWorkerV0`'s executable, pc, end, registers
and private memory. -/
def runnerMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => pr.config.threads.size == 2 && pr.config.threads.all fun t =>
      t.st.exe == cmpxWorkerV0.exe && t.st.endPc == cmpxWorkerV0.endPc && t.st.st.2 == cmpxWorkerV0.st.2 &&
      t.st.st.1.regs == cmpxWorkerV0.st.1.regs && t.st.st.1.dmem == cmpxWorkerV0.st.1.dmem

/-- info: true -/
#guard_msgs in
#eval runnerMatches spinlockCmpxchg2Kl

/-! ## The instance -/

section
attribute [local instance] cmpxLayoutV

/-- A label's address from its position in the image. -/
theorem labC_at {x : Label} (i : Nat) (hd : cmpxImageV.drop i = Program.fromLabel cmpxImageV x := by decide)
    (hne : Program.fromLabel cmpxImageV x ≠ [] := by decide) : labC x = (cmpxLayoutV cmpxImageV).addrOf i :=
  Program.label_addrOf_drop cmpxImageV_wf.nodup hd hne

theorem symC_lock : symC "lock" = 0x1000000 := by
  show (labC "lock").toBitVec = _; rw [labC_at 12]; decide
theorem symC_counter : symC "counter" = 0x1000100 := by
  show (labC "counter").toBitVec = _; rw [labC_at 14]; decide

theorem cmpxWorkerV0_start : StartStateCV cmpxWorkerV0 :=
  ⟨rfl, rfl, by show _ = labC "worker"; rw [labC_at 0]; decide,
    by show _ = labC "done"; rw [labC_at 10]; decide, Split.empty _⟩

end

/-- **`counter = N`** for `N < 2 ^ 32` workers running `spinlock_cmpxchg2.kl`'s code
verbatim in the runner's executable, under `Arch.tso`. -/
theorem x64_cmpx_counter_envG_verbatim_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init (List.replicate N cmpxWorkerV0) cmpxInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = BitVec.ofNat 128 N := by
  have h := x64_cmpx_counter_envG_verbatim (layout := cmpxLayoutV) N (by rw [symC_lock, symC_counter]; decide)
    hN32 (fun s hs => (List.eq_of_mem_replicate hs) ▸ cmpxWorkerV0_start) List.length_replicate
    (by rw [symC_counter]; simp only [Config.init_mem]; decide)
    (by rw [symC_lock]; simp only [Config.init_mem]; decide) hc hf
  rwa [symC_counter] at h

/-- **`counter = 2`** for the two workers of `spinlock_cmpxchg2.kl`. -/
theorem x64_cmpx_counter_envG_verbatim_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [cmpxWorkerV0, cmpxWorkerV0] cmpxInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = 2 :=
  x64_cmpx_counter_envG_verbatim_concreteN 2 (by decide) hc hf

end Kraken.Promising.X64.EnvG.CmpxAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.CmpxAbs.Concrete.x64_cmpx_counter_envG_verbatim_concreteN
#print axioms Kraken.Promising.X64.EnvG.CmpxAbs.Concrete.x64_cmpx_counter_envG_verbatim_concrete2
