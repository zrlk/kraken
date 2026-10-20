/-
`swp_counter_armv8` (`SLR/SwpFinal.lean`) at a concrete instance: two
workers of `Kraken/Examples/LockFree/AArch64/spinlock_swp2.kl`, laid out as
the `.kl` runner lays them out (`Kraken.Litmus.AArch64.prepareProgram`: text
at `0x100000`, 4 bytes per instruction, labels empty; `lock` at `0x1000`,
`counter` at `0x1100`), every hypothesis discharged.
-/
import Kraken.Promising.SLR.SwpFinal
import Kraken.Litmus.AArch64
import Kraken.Promising.SLR.RunSched

namespace Kraken.Promising.SLR.SwpConcrete

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpInv
open Kraken.Promising.SLR (runSched runSched_reachable)

/-! ## The layout -/

/-- The layout of the `.kl` runner (`prepareProgram`): text at `0x100000`,
each directive its `fakeSize` (instructions 4 bytes, labels 0). -/
@[reducible] def swpLayout : _root_.Layout :=
  { start := 0x100000, size := fun i => (swpWorker[i]?.map Directive.fakeSize).getD 0 }

attribute [local instance] swpLayout

/-- The laid-out worker, cell by cell. -/
theorem swpLayout_cells :
    ((swpLayout swpWorker).2.map (·.2)) = [0, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0] := by
  decide

/-- The size check of a cell: labels 0 bytes, instructions 4, data at least 1. -/
private def cellOk : Directive × Nat → Bool
  | (.label _, z) => z == 0
  | (.instr _, z) => z == 4
  | (.byteArray _, z) => 0 < z

private theorem cells_ok : (swpLayout swpWorker).2.all cellOk = true := by decide

private theorem cellOk_of {i : Nat} {d : Directive} {z : Nat} (h : (swpLayout swpWorker).2[i]? = some (d, z)) :
    cellOk (d, z) = true :=
  List.all_eq_true.mp cells_ok _ (List.mem_of_getElem? h)

/-- The layout is valid: the `Executable.ValidLayout` hypothesis of the lock
theorems is satisfiable. -/
instance swpValid : Executable.ValidLayout (swpLayout swpWorker) where
  label_size i l z h := by simpa [cellOk] using cellOk_of h
  instr_size i ins z h := by simpa [cellOk] using cellOk_of h
  data_size i a z h := by simpa [cellOk] using cellOk_of h
  no_wrap := by decide

/-! ## The parameters and the initial configuration -/

/-- The lock word's address (`lock`, as `prepareProgram` places it). -/
def lockAddr : BitVec 64 := 0x1000
/-- The counter word's address (`counter`, as `prepareProgram` places it). -/
def counterAddr : BitVec 64 := 0x1100

/-- Two workers; the ghost locations `K j`, `F j` away from the lock, the
counter and each other. -/
def P2 : Params where
  N := 2
  l := lockAddr
  c := counterAddr
  K j := ⟨BitVec.ofNat 64 (0x10000 + 16 * j), 4⟩
  F j := ⟨BitVec.ofNat 64 (0x20000 + 16 * j), 4⟩

theorem spinLocs2 : SpinLocs P2.N P2.Lk P2.C P2.K P2.F where
  lk_c := by decide
  k_lk := by decide
  k_c := by decide
  f_lk := by decide
  f_c := by decide
  k_f := by decide
  k_inj := by decide
  f_inj := by decide

/-- A worker's initial state, as the `.kl` init block says: `X0 = lock`,
`X1 = counter`, at the start label `worker`, halting at `done` (the end of
the text, `0x100000 + 44`); no declarations, empty private memory. -/
def worker0 : State where
  exe := swpLayout swpWorker
  endPc := 0x100000 + 44
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100 } }, 0x100000)

/-- The two threads. -/
def states2 : List State := [worker0, worker0]

/-- The initial memory: `lock = 0`, `counter = 0`. -/
def initMem2 : List (Loc × Val) := [(P2.Lk, 0), (P2.C, 0)]

theorem worker0_frame : Frame P2 worker0 ∧ AtPos worker0 0 := by
  refine ⟨⟨rfl, rfl, by decide, by decide, by decide, ?_, ?_, Or.inl (by decide)⟩, by unfold AtPos; decide⟩ <;>
    simp [worker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

/-! ## The instance -/

/-- **`counter = 2`** for the two workers of `spinlock_swp2.kl` under
`Arch.armv8`: every reachable final configuration has the counter at `2`. -/
theorem swp_counter_2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init states2 initMem2) c) (hf : c.final = true) :
    c.mem.finalVal P2.C = 2 :=
  swp_counter_armv8 P2 spinLocs2 (by decide)
    (fun tid s h => by
      have : s = worker0 := by
        have := List.mem_of_getElem? h
        rcases List.mem_cons.mp this with h | h
        · exact h
        · exact List.mem_singleton.mp h
      subst this; exact worker0_frame)
    rfl (by decide) (by decide) (by decide) hc hf

/-! ## Non-vacuity: a reachable final configuration

The initial configuration reaches a final one: thread 0 runs to `done`
(`mov`, `swpa` reads `0`, `cbz`, `ldr`, `add`, `str`, `stlr`, `b`), then
thread 1 does the same, each step the first successor `succs` lists, no
promises. The machine's successor function is not kernel-reducible (the
certification cache is a `Std.HashMap` and the private memory a
`Std.ExtHashMap`, whose hashing is `opaque`), so the run is checked by
`native_decide`: **`swp_final_witness` depends on the axiom `native_decide` adds
(`sched2_final._native.native_decide.ax_1_1`).**
The theorems above do not. -/

/-- The schedule: sixteen times the first successor (thread 0's eight
instructions, then thread 1's). -/
def sched2 : List Nat := List.replicate 16 0

/-- The run along `sched2` ends in a final configuration with the counter
at `2` (checked by evaluation). -/
theorem sched2_final :
    ((runSched (I := isa) Arch.armv8 0 (Config.init states2 initMem2) sched2).map
      fun c => c.final && c.mem.finalVal P2.C == 2) = some true := by
  native_decide

/-- **Non-vacuity**: some final configuration is reachable from the initial
configuration of `swp_counter_2`, and its counter is literally `2` (by
evaluation of `finalVal`, independently of `swp_counter_2`). Depends on
the `native_decide` axiom of `sched2_final` (see above). -/
theorem swp_final_witness :
    ∃ c : Config isa, Reachable Arch.armv8 0 (Config.init states2 initMem2) c ∧ c.final = true ∧
      c.mem.finalVal P2.C = 2 := by
  have h := sched2_final
  cases hr : runSched (I := isa) Arch.armv8 0 (Config.init states2 initMem2) sched2 with
  | none => rw [hr] at h; cases h
  | some c =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨c, runSched_reachable hr, h.1, h.2⟩

/-- The initial configuration is `Config.Live` (Theorem 1′'s liveness
premise holds at the start, so its conclusion is not vacuous here). Depends
on the `native_decide` axiom, through `swp_final_witness`. -/
theorem init_live : (Config.init states2 initMem2 : Config isa).Live Arch.armv8 0 :=
  let ⟨c, hc, hf, _⟩ := swp_final_witness
  ⟨c, hc, hf⟩

/-- The witness agrees with `swp_counter_2`: the theorem, applied to the
reachable final configuration, gives the same `2` (a consistency check of
the theorem's conclusion against an actual run). -/
theorem swp_witness_consistent :
    ∃ c : Config isa, Reachable Arch.armv8 0 (Config.init states2 initMem2) c ∧ c.final = true ∧
      c.mem.finalVal P2.C = 2 :=
  let ⟨c, hc, hf, _⟩ := swp_final_witness
  ⟨c, hc, hf, swp_counter_2 hc hf⟩

/-! ## Provenance: the program and the set-up are the `.kl` file's

`swpWorker` is the `code` block of `spinlock_swp2.kl`, parsed by the `.kl`
front end (`Kraken.Litmus.parseProgram`) and the AArch64 parser; `worker0`
is the thread state `Kraken.Litmus.AArch64.prepareProgram` builds for each
of the file's two threads, except for two fields:

- `decls`: the runner declares `lock` and `counter` (typed `uint32_t` in the
  header) as the strict 4-byte locations `⟨0x1000, 4⟩`,
  `⟨0x1100, 4⟩`, the theorem's footprints; `Frame` requires `decls = {}`.
  (Before the header was typed the runner declared them *unsized*,
  `⟨0x1000, 0⟩`, `⟨0x1100, 0⟩`, legacy mode.)
- `showPc` (trace text only).

The runner's initial memory is `initMem2` (`runnerDeclsSized`). -/

/-- The `.kl` source. -/
def swpKl : String := include_str "../../Examples/LockFree/AArch64/spinlock_swp2.kl"

/-- The `code` block of the `.kl` file parses to `swpWorker`. -/
def codeMatches : Bool :=
  match Kraken.Litmus.parseProgram swpKl with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == swpWorker
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches

/-- Every thread the runner prepares is `worker0` up to `decls` and `showPc`:
same executable, end address, start address, registers, empty private
memory; and there are exactly two of them. -/
def statesMatch : Bool :=
  match Kraken.Litmus.parseProgram swpKl >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr =>
    pr.config.threads.size == 2 &&
    pr.config.threads.all fun t =>
      t.st.exe == worker0.exe && t.st.endPc == worker0.endPc && t.st.st.2 == worker0.st.2 &&
        t.st.st.1.regs == worker0.st.1.regs && t.st.st.1.status == worker0.st.1.status &&
        t.st.st.1.dmem.isEmpty

/-- info: true -/
#guard_msgs in
#eval statesMatch

/-- The runner's declarations and initial memory (the deviation above):
`lock` and `counter` unsized, legacy mode. -/
def runnerDecls : Bool :=
  match Kraken.Litmus.parseProgram swpKl >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr =>
    let ls : List Loc := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩]
    pr.config.threads.all (fun t => t.st.decls == { locs := ls, unsizedDefault := true }) &&
      pr.config.mem.init == ls.map (·, 0)

-- `false` since `spinlock_swp2.kl`'s header was typed:
-- the runner now declares the two words sized and strict;
-- see `runnerDeclsSized`.
/-- info: false -/
#guard_msgs in
#eval runnerDecls

/-- The runner's declarations and initial memory for the typed header
(`uint32_t lock`, `uint32_t counter`): the two 4-byte words, strict. The
declarations are the theorem's footprints and the initial memory is
`initMem2`; `swp_counter_2` itself still assumes no declarations. -/
def runnerDeclsSized : Bool :=
  match Kraken.Litmus.parseProgram swpKl >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr =>
    let ls : List Loc := [⟨0x1000, 4⟩, ⟨0x1100, 4⟩]
    pr.config.threads.all (fun t => t.st.decls == { locs := ls, unsizedDefault := false }) &&
      pr.config.mem.init == ls.map (·, 0) && pr.config.mem.init == initMem2

/-- info: true -/
#guard_msgs in
#eval runnerDeclsSized

/-- The explorer on the theorem's initial configuration (4-byte footprints,
no declarations): the final counters are `[2]`, as for the runner's. -/
def exploreFinals : List Nat × Bool :=
  let r := explore Arch.armv8 (Config.init states2 initMem2 : Config isa)
    (fun c => (c.mem.finalVal P2.C).toNat) { fuel := 64, symmetric := true }
  (r.finals, r.boundHit || !r.faults.isEmpty)

/-- info: ([2], false) -/
#guard_msgs in
#eval exploreFinals

end Kraken.Promising.SLR.SwpConcrete
