/-
**`ticketlock3.kl` from the runner's exact configuration** (part 3):
`TicketX.ticket3_counter_envG_runner` at the
`.kl` runner's own executable, threads, declarations and initial memory.

- `codeMatchesTk3`: the `.kl`'s `code` block parses to `tk3WorkerV`.
- `runnerMatchesTk3`: the runner's prepared configuration
  (`Kraken.Litmus.X64.prepareProgram`) is `Config.init` of three copies of
  `tk3WorkerD0` and `tk3InitMemV` in everything the theorem reads
  (`runnerMatchesDN`: per thread the executable `tk3ImageV` laid out by
  `tk3LayoutV` (text at `0x100000`, one byte per instruction, `next`,
  `owner`, `counter` at `0x1000000`, `0x1000100`, `0x1000200`), end, pc,
  registers, private memory, **declarations** (the typed header's three
  4-byte words, strict); the initial memory; no message).
- `ticket3_counter_envG_runner_concreteN`/`_concrete3`: the theorem at that
  configuration; every hypothesis by `decide`/`rfl`.
-/
import Kraken.Promising.SLR.EnvG.TicketXPublic
import Kraken.Promising.SLR.EnvG.X64RunnerCommon
import Kraken.Promising.SLR.EnvG.ConcreteCommon

namespace Kraken.Promising.X64.EnvG.TicketX.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TicketX Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `ticketlock3.kl`: labels 0,
instructions 1 (text from `0x100000` to `0x10000b`), the padding up to `next`
at `0x1000000`, and the 256-byte slots of `next` and `owner`. -/
def tk3SizesV : List Nat :=
  [0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0x1000000 - 0x10000b, 0, 0x100, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def tk3LayoutV : _root_.Layout := { start := 0x100000, size := fun i => tk3SizesV[i]?.getD 0 }

instance tk3ValidV : Executable.ValidLayout (tk3LayoutV tk3ImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The runner's declarations for the typed `ticketlock3.kl`: `next`, `owner`
and `counter`, 4-byte words (strict). -/
def tk3DeclsD : Decls :=
  { locs := [⟨0x1000000, 4⟩, ⟨0x1000100, 4⟩, ⟨0x1000200, 4⟩], unsizedDefault := false }

theorem tk3DeclsD_sized : tk3DeclsD.Sized := ⟨rfl, by decide⟩

/-- A worker's initial state as the runner prepares it: the image, pc at
`worker` (`0x100000`), end at `done` (`0x10000b`), empty registers and
private memory, the runner's declarations. -/
def tk3WorkerD0 : X64.State where
  exe := tk3LayoutV tk3ImageV
  endPc := 0x100000 + 11
  st := ({}, 0x100000)
  decls := tk3DeclsD

/-- The initial memory: `next = owner = counter = 0` (4-byte words). -/
def tk3InitMemV : List (Loc × Val) := [(⟨0x1000000, 4⟩, 0), (⟨0x1000100, 4⟩, 0), (⟨0x1000200, 4⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def ticketlock3Kl : String := include_str "../../../Examples/LockFree/X64/ticketlock3.kl"

/-- The `code` block of the `.kl` parses to `tk3WorkerV`. -/
def codeMatchesTk3 (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == tk3WorkerV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatchesTk3 ticketlock3Kl

/-- The runner's configuration is `Config.init (List.replicate n tk3WorkerD0)
tk3InitMemV` in everything the theorem reads (declarations included). -/
def runnerMatchesTk3 (src : String) (n : Nat) : Bool :=
  runnerMatchesDN src n tk3WorkerD0 tk3InitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesTk3 ticketlock3Kl 3

/-! ## The instance -/

section
attribute [local instance] tk3LayoutV

/-- A label's address from its position in the image. -/
theorem labTk_at {x : Label} (i : Nat) (hd : tk3ImageV.drop i = Program.fromLabel tk3ImageV x := by decide)
    (hne : Program.fromLabel tk3ImageV x ≠ [] := by decide) : labTk x = (tk3LayoutV tk3ImageV).addrOf i :=
  Program.label_addrOf_drop tk3ImageV_wf.nodup hd hne

theorem symTk_next : symTk "next" = 0x1000000 := by
  show (labTk "next").toBitVec = _; rw [labTk_at 15]; decide
theorem symTk_owner : symTk "owner" = 0x1000100 := by
  show (labTk "owner").toBitVec = _; rw [labTk_at 17]; decide
theorem symTk_counter : symTk "counter" = 0x1000200 := by
  show (labTk "counter").toBitVec = _; rw [labTk_at 19]; decide

theorem tk3WorkerD0_start : StartStateTk tk3DeclsD tk3WorkerD0 :=
  ⟨rfl, rfl, by show _ = labTk "worker"; rw [labTk_at 0]; decide,
    by show _ = labTk "done"; rw [labTk_at 13]; decide, Split.empty _⟩

end

/-- **`counter = N`** for `N` workers (`N + 1 < 2 ^ 32`) running
`ticketlock3.kl`'s code verbatim, from the runner's exact thread state and
initial memory (declarations included), under `Arch.tso`. -/
theorem ticket3_counter_envG_runner_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init (List.replicate N tk3WorkerD0) tk3InitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000200, 4⟩ = BitVec.ofNat 128 N := by
  have h := ticket3_counter_envG_runner (layout := tk3LayoutV) tk3DeclsD_sized N
    (by rw [symTk_next, symTk_owner]; decide) (by rw [symTk_next, symTk_counter]; decide)
    (by rw [symTk_owner, symTk_counter]; decide) hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ tk3WorkerD0_start) List.length_replicate
    (by rw [symTk_next]; simp only [Config.init_mem]; decide)
    (by rw [symTk_owner]; simp only [Config.init_mem]; decide)
    (by rw [symTk_counter]; simp only [Config.init_mem]; decide) hc hf
  rwa [symTk_counter] at h

/-- **`counter = 3` for the three workers of `ticketlock3.kl`, from the
runner's exact configuration** (declarations and initial memory included). -/
theorem ticket3_counter_envG_runner_concrete3 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [tk3WorkerD0, tk3WorkerD0, tk3WorkerD0] tk3InitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000200, 4⟩ = 3 :=
  ticket3_counter_envG_runner_concreteN 3 (by decide) hc hf

end Kraken.Promising.X64.EnvG.TicketX.Concrete

#print axioms Kraken.Promising.X64.EnvG.TicketX.Concrete.ticket3_counter_envG_runner_concreteN
#print axioms Kraken.Promising.X64.EnvG.TicketX.Concrete.ticket3_counter_envG_runner_concrete3
