/-
`x64_counter_spin` (`SLR/X64SpinFinalX.lean`) at a concrete instance: two
workers of `Kraken/Examples/LockFree/X64/spinlock2.kl`, laid out as the
`.kl` runner lays out the text (`Kraken.Litmus.X64.prepareProgram`: text at
`0x100000`, 1 byte per instruction, labels empty; `lock` at `0x1000000`,
`counter` at `0x1000100`), every hypothesis discharged. The x64 twin of
`SLR/SwpConcrete.lean` (a separate file: the two ISA syntaxes cannot be
imported together).

The worker differs from the `.kl` file's in its addressing: `spinWorker`
reaches the lock and the counter through `%rdi`/`%rsi`, the `.kl` code
through the absolute operands `(lock)`/`(counter)` (see "Provenance" below).
-/
import Kraken.Promising.SLR.X64SpinFinalX
import Kraken.Litmus.X64
import Kraken.Promising.SLR.RunSched

namespace Kraken.Promising.SLR.X64SpinConcrete

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees
open Kraken.Promising.SLR.X64SpinInv
open Kraken.Promising.SLR (runSched runSched_reachable)

/-! ## The layout -/

/-- The text layout of the `.kl` runner (`prepareProgram`): text at
`0x100000`, labels 0 bytes, every other directive 1. -/
@[reducible] def spinLayout : _root_.Layout :=
  { start := 0x100000,
    size := fun i => match spinWorker[i]? with
      | some (.label _) => 0
      | some _ => 1
      | none => 0 }

attribute [local instance] spinLayout

/-- The laid-out worker, cell by cell. -/
theorem spinLayout_cells :
    ((spinLayout spinWorker).2.map (·.2)) = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] := by
  decide

/-- The size check of a cell: labels 0 bytes, everything else at least 1, no
alignment directive. -/
private def cellOk : Directive × Nat → Bool
  | (.label _, z) => z == 0
  | (.instr (.regular _ _ (.nopalign _ _)), _) => false
  | (_, z) => 0 < z

private theorem cells_ok : (spinLayout spinWorker).2.all cellOk = true := by decide

private theorem cellOk_of {i : Nat} {d : Directive} {z : Nat} (h : (spinLayout spinWorker).2[i]? = some (d, z)) :
    cellOk (d, z) = true :=
  List.all_eq_true.mp cells_ok _ (List.mem_of_getElem? h)

/-- The layout is valid: the `Executable.ValidLayout` hypothesis of the lock
theorem is satisfiable. -/
instance spinValid : Executable.ValidLayout (spinLayout spinWorker) where
  label_size i l z h := by simpa [cellOk] using cellOk_of h
  instr_size i d z h hd := by
    have := cellOk_of h
    cases d with
    | label l => exact absurd rfl (hd l)
    | instr ins =>
      cases ins with
      | regular aw w op => cases op <;> simp_all [cellOk]
      | avx => simp_all [cellOk]
    | byteArray => simp_all [cellOk]
  no_wrap := by decide
  align_addr i aw w n pad z h := by simpa [cellOk] using cellOk_of h

/-! ## The parameters and the initial configuration -/

/-- Two workers at the runner's addresses; the ghost locations `K j`, `F j`
away from the lock, the counter and each other. -/
def P2 : Params where
  N := 2
  l := 0x1000000
  c := 0x1000100
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

/-- A worker's initial state: `%rdi = lock`, `%rsi = counter` (the
register-addressed worker's arguments), at the start label `worker`,
halting at `done` (the end of the text, `0x100000 + 12`); no declarations,
empty private memory. -/
def worker0 : State where
  exe := spinLayout spinWorker
  endPc := 0x100000 + 12
  st := ({ regs := (({} : Reg64s).set64 .rdi 0x1000000).set64 .rsi 0x1000100 }, 0x100000)

/-- The two threads. -/
def states2 : List State := [worker0, worker0]

/-- The initial memory: `lock = 0`, `counter = 0`. -/
def initMem2 : List (Loc × Val) := [(P2.Lk, 0), (P2.C, 0)]

theorem worker0_frame : Frame P2 worker0 ∧ AtPos worker0 0 := by
  refine ⟨⟨rfl, rfl, by decide, by decide, by decide, ?_, ?_⟩, by unfold AtPos; decide⟩ <;>
    simp [worker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

/-! ## The instance -/

/-- **`counter = 2`** for two register-addressed workers of `spinlock2.kl`
under `Arch.tso`: every reachable final configuration has the counter at
`2`. -/
theorem x64_counter_2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init states2 initMem2) c) (hf : c.final = true) :
    c.mem.finalVal P2.C = 2 :=
  x64_counter_spin P2 spinLocs2 (by decide)
    (fun tid s h => by
      have : s = worker0 := by
        have := List.mem_of_getElem? h
        rcases List.mem_cons.mp this with h | h
        · exact h
        · exact List.mem_singleton.mp h
      subst this; exact worker0_frame)
    rfl (by decide) (by decide) (by decide) hc hf

/-! ## Non-vacuity: a reachable final configuration

Thread 0 runs to `done` (twelve instructions; `xchgl` reads `0`), then
thread 1, each step the first successor `succs` lists, no promises. As in
`SLR/SwpConcrete.lean`, `succs` is not kernel-reducible (hashing in the
certification cache and the private memory is `opaque`), so the run is
checked by `native_decide`: **`x64_final_witness` depends on the axiom
`native_decide` adds (`x64Sched2_final._native.native_decide.ax_1_1`).**
`x64_counter_2` does not. -/

/-- The schedule: twenty-four times the first successor. -/
def x64Sched2 : List Nat := List.replicate 24 0

/-- The run along `x64Sched2` ends in a final configuration with the counter
at `2` (checked by evaluation). -/
theorem x64Sched2_final :
    ((runSched (I := isa) Arch.tso 0 (Config.init states2 initMem2) x64Sched2).map
      fun c => c.final && c.mem.finalVal P2.C == 2) = some true := by
  native_decide

/-- **Non-vacuity**: some final configuration is reachable from the initial
configuration of `x64_counter_2`, and its counter is literally `2` (by
evaluation of `finalVal`). Depends on the `native_decide` axiom of
`x64Sched2_final`. -/
theorem x64_final_witness :
    ∃ c : Config isa, Reachable Arch.tso 0 (Config.init states2 initMem2) c ∧ c.final = true ∧
      c.mem.finalVal P2.C = 2 := by
  have h := x64Sched2_final
  cases hr : runSched (I := isa) Arch.tso 0 (Config.init states2 initMem2) x64Sched2 with
  | none => rw [hr] at h; cases h
  | some c =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨c, runSched_reachable hr, h.1, h.2⟩

/-- The initial configuration is `Config.Live` (Theorem 1′'s liveness
premise holds at the start, so its conclusion is not vacuous here). Depends
on the `native_decide` axiom, through `x64_final_witness`. -/
theorem init_live : (Config.init states2 initMem2 : Config isa).Live Arch.tso 0 :=
  let ⟨c, hc, hf, _⟩ := x64_final_witness
  ⟨c, hc, hf⟩

/-- The witness agrees with `x64_counter_2` (the theorem applied to it). -/
theorem x64_witness_consistent :
    ∃ c : Config isa, Reachable Arch.tso 0 (Config.init states2 initMem2) c ∧ c.final = true ∧
      c.mem.finalVal P2.C = 2 :=
  let ⟨c, hc, hf, _⟩ := x64_final_witness
  ⟨c, hc, hf, x64_counter_2 hc hf⟩

/-! ## Provenance: the program differs from the `.kl` file's in addressing

The `code` block of `spinlock2.kl` addresses the lock and the counter
absolutely, `(lock)` and `(counter)`, resolved through data labels the runner
appends to the text; `spinWorker` addresses them through `%rdi`/`%rsi`. With
`(lock)` ↦ `(%rdi)` and `(counter)` ↦ `(%rsi)` substituted in the source
text, the `.kl` code block parses to `spinWorker` exactly (`done:`
included); unsubstituted, it does not. The runner's threads
(`Kraken.Litmus.X64.prepareProgram`) and `worker0` share the text address,
start and end addresses and the cell sizes of the fourteen code cells, and
differ in:

- `exe`: the runner's executable is the absolute-address code plus four
  data cells (padding and the labels `lock`, `counter`), 18 cells;
  `Frame` requires `exe = layout spinWorker`, 14 cells;
- registers: the runner sets none (the code needs none); `worker0` sets
  `%rdi`, `%rsi`;
- `decls`: the runner declares `lock`/`counter` as 4-byte words (the `.kl`
  header is typed `uint32_t` since the declarations proofs; before, unsized in legacy mode);
  `Frame` requires `decls = {}`. -/

/-- The `.kl` source. -/
def spinKl : String := include_str "../../Examples/LockFree/X64/spinlock2.kl"

/-- The code block, parsed after substituting `(lock)`, `(counter)` with
`(%rdi)`, `(%rsi)` (`true` for the result), and as it is (`false`: the
programs differ). -/
def codeMatches : Bool × Bool :=
  match Kraken.Litmus.parseProgram spinKl with
  | .error _ => (false, true)
  | .ok p =>
    let src := "\n".intercalate p.code
    let subst := (src.replace "(lock)" "(%rdi)").replace "(counter)" "(%rsi)"
    let eqW (s : String) : Bool := match Kraken.X64.Parser.parse s with
      | .ok prog => prog == spinWorker
      | .error _ => false
    (eqW subst, eqW src)

/-- info: (true, false) -/
#guard_msgs in
#eval codeMatches

/-- The runner's threads against `worker0`: two threads, same text address,
start and end addresses, same sizes of the fourteen code cells, then the
four data cells, empty private memory, declarations of `lock` and `counter`
at `P2.l`, `P2.c` as 4-byte words (since the declarations proofs typed the `.kl` header
`uint32_t`; they were unsized), and the runner's initial memory naming
those. -/
def statesMatch : Bool :=
  match Kraken.Litmus.parseProgram spinKl >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr =>
    let ls : List Loc := [⟨P2.l, 4⟩, ⟨P2.c, 4⟩]
    pr.config.threads.size == 2 &&
    pr.config.mem.init == ls.map (·, 0) &&
    pr.config.threads.all fun t =>
      t.st.exe.1 == worker0.exe.1 && t.st.endPc == worker0.endPc && t.st.st.2 == worker0.st.2 &&
        (t.st.exe.2.take 14).map (·.2) == worker0.exe.2.map (·.2) && t.st.exe.2.length == 18 &&
        t.st.st.1.dmem.isEmpty && t.st.decls == { locs := ls, unsizedDefault := false }

/-- info: true -/
#guard_msgs in
#eval statesMatch

/-- The explorer on the theorem's initial configuration: the final counters
are `[2]`, as for the runner's. -/
def exploreFinals : List Nat × Bool :=
  let r := explore Arch.tso (Config.init states2 initMem2 : Config isa)
    (fun c => (c.mem.finalVal P2.C).toNat) { fuel := 300, symmetric := true }
  (r.finals, r.boundHit || !r.faults.isEmpty)

/-- info: ([2], false) -/
#guard_msgs in
#eval exploreFinals

end Kraken.Promising.SLR.X64SpinConcrete
