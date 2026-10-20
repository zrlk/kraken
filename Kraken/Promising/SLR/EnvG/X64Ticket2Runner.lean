/-
**`ticketlock2.kl` from the runner's exact configuration**:
`TicketX2.ticket2_counter_envG_runner` at the `.kl`
runner's own executable, threads, declarations and initial memory.

- `codeMatchesTk2`: the `.kl`'s `code` block parses to `tk2WorkerV`.
- `runnerMatchesTk2`: the runner's prepared configuration
  (`Kraken.Litmus.X64.prepareProgram`) is `Config.init` of two copies of
  `tk2WorkerD0` and `tk2InitMemV` in everything the theorem reads
  (`runnerMatchesDN`: per thread the executable `tk2ImageV` laid out by
  `tk2LayoutV` (text at `0x100000`, one byte per instruction, `next`,
  `owner`, `counter` at `0x1000000`, `0x1000100`, `0x1000200`), end, pc,
  registers, private memory, declarations (the typed header's three 4-byte
  words, strict); the initial memory; no message).
- `ticket2_counter_envG_runner_concreteN`/`_concrete2`: the theorem at that
  configuration; every hypothesis by `decide`/`rfl`.
-/
import Kraken.Promising.SLR.EnvG.X64Ticket2Public
import Kraken.Promising.SLR.EnvG.X64RunnerCommon
import Kraken.Promising.SLR.EnvG.ConcreteCommon

namespace Kraken.Promising.X64.EnvG.TicketX2.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TicketX2 Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `ticketlock2.kl`: labels 0,
instructions 1 (text from `0x100000` to `0x10000a`), the padding up to `next`
at `0x1000000`, and the 256-byte slots of `next` and `owner`. -/
def tk2SizesV : List Nat :=
  [0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0x1000000 - 0x10000a, 0, 0x100, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def tk2LayoutV : _root_.Layout := { start := 0x100000, size := fun i => tk2SizesV[i]?.getD 0 }

instance tk2ValidV : Executable.ValidLayout (tk2LayoutV tk2ImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The runner's declarations for the typed `ticketlock2.kl`: `next`, `owner`
and `counter`, 4-byte words (strict). -/
def tk2DeclsD : Decls :=
  { locs := [⟨0x1000000, 4⟩, ⟨0x1000100, 4⟩, ⟨0x1000200, 4⟩], unsizedDefault := false }

theorem tk2DeclsD_sized : tk2DeclsD.Sized := ⟨rfl, by decide⟩

/-- A worker's initial state as the runner prepares it: the image, pc at
`worker` (`0x100000`), end at `done` (`0x10000a`), empty registers and
private memory, the runner's declarations. -/
def tk2WorkerD0 : X64.State where
  exe := tk2LayoutV tk2ImageV
  endPc := 0x100000 + 10
  st := ({}, 0x100000)
  decls := tk2DeclsD

/-- The initial memory: `next = owner = counter = 0` (4-byte words). -/
def tk2InitMemV : List (Loc × Val) := [(⟨0x1000000, 4⟩, 0), (⟨0x1000100, 4⟩, 0), (⟨0x1000200, 4⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def ticketlock2Kl : String := include_str "../../../Examples/LockFree/X64/ticketlock2.kl"

/-- The `code` block of the `.kl` parses to `tk2WorkerV`. -/
def codeMatchesTk2 (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == tk2WorkerV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatchesTk2 ticketlock2Kl

/-- The runner's configuration is `Config.init (List.replicate n tk2WorkerD0)
tk2InitMemV` in everything the theorem reads (declarations included). -/
def runnerMatchesTk2 (src : String) (n : Nat) : Bool :=
  runnerMatchesDN src n tk2WorkerD0 tk2InitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesTk2 ticketlock2Kl 2

/-! ## The instance -/

section
attribute [local instance] tk2LayoutV

/-- A label's address from its position in the image. -/
theorem labTk2_at {x : Label} (i : Nat) (hd : tk2ImageV.drop i = Program.fromLabel tk2ImageV x := by decide)
    (hne : Program.fromLabel tk2ImageV x ≠ [] := by decide) : labTk2 x = (tk2LayoutV tk2ImageV).addrOf i :=
  Program.label_addrOf_drop tk2ImageV_wf.nodup hd hne

theorem symTk2_next : symTk2 "next" = 0x1000000 := by
  show (labTk2 "next").toBitVec = _; rw [labTk2_at 14]; decide
theorem symTk2_owner : symTk2 "owner" = 0x1000100 := by
  show (labTk2 "owner").toBitVec = _; rw [labTk2_at 16]; decide
theorem symTk2_counter : symTk2 "counter" = 0x1000200 := by
  show (labTk2 "counter").toBitVec = _; rw [labTk2_at 18]; decide

theorem tk2WorkerD0_start : StartStateTk2 tk2DeclsD tk2WorkerD0 :=
  ⟨rfl, rfl, by show _ = labTk2 "worker"; rw [labTk2_at 0]; decide,
    by show _ = labTk2 "done"; rw [labTk2_at 12]; decide, Split.empty _⟩

end

/-- **`counter = N`** for `N` workers (`N + 1 < 2 ^ 32`) running
`ticketlock2.kl`'s code verbatim, from the runner's exact thread state and
initial memory (declarations included), under `Arch.tso`. -/
theorem ticket2_counter_envG_runner_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init (List.replicate N tk2WorkerD0) tk2InitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000200, 4⟩ = BitVec.ofNat 128 N := by
  have h := ticket2_counter_envG_runner (layout := tk2LayoutV) tk2DeclsD_sized N
    (by rw [symTk2_next, symTk2_owner]; decide) (by rw [symTk2_next, symTk2_counter]; decide)
    (by rw [symTk2_owner, symTk2_counter]; decide) hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ tk2WorkerD0_start) List.length_replicate
    (by rw [symTk2_next]; simp only [Config.init_mem]; decide)
    (by rw [symTk2_owner]; simp only [Config.init_mem]; decide)
    (by rw [symTk2_counter]; simp only [Config.init_mem]; decide) hc hf
  rwa [symTk2_counter] at h

/-- **`counter = 2` for the two workers of `ticketlock2.kl`, from the
runner's exact configuration** (declarations and initial memory included):
the `.kl`'s `forall [counter]=2`. -/
theorem ticket2_counter_envG_runner_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [tk2WorkerD0, tk2WorkerD0] tk2InitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000200, 4⟩ = 2 :=
  ticket2_counter_envG_runner_concreteN 2 (by decide) hc hf

end Kraken.Promising.X64.EnvG.TicketX2.Concrete

#print axioms Kraken.Promising.X64.EnvG.TicketX2.Concrete.ticket2_counter_envG_runner_concreteN
#print axioms Kraken.Promising.X64.EnvG.TicketX2.Concrete.ticket2_counter_envG_runner_concrete2
