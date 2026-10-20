/-
**The `isa` ↔ `isaLSE2` transfer.**

`isaLSE2` (`Promising/AArch64.lean`) is `isa` with `exec := execLSE2`,
`deps := depsLSE2`, i.e. `isa.withExec execLSE2 depsLSE2` (`isaLSE2_eq`, by
`rfl`). The two differ only at cells that are a 64-bit `LDP`/`STP`
(`Directive.LSE2Free` is false exactly there, `AArch64/LSE2.lean`):

- **(A1), cell level.** `execLSE2_eq_exec_of_cell`: if the cell at the pc is
  `LSE2Free`, `execLSE2 s = exec s` (`lse2Effects` reads
  `Directive.interpLSE2?`, which is `none` on such a cell, whatever the
  address). `depsLSE2_eq_deps_of_directive`: if the directive at the pc is
  `LSE2Free`, `depsLSE2 s = deps s` (it differs only at a 64-bit `STP`).
  Program level: `NoLSE2Pairs e` (no cell of `e` is a 64-bit `LDP`/`STP`),
  `execLSE2_eq_exec`/`depsLSE2_eq_deps` under it, and `noLSE2Pairs_apply`,
  which reduces it for a laid-out program `layout prog` to
  `∀ d ∈ prog, d.LSE2Free`, decidable (`by decide` on a concrete program).
- **(A2), machine level.** `agreeLSE2 : Agree isa execLSE2 depsLSE2 GoodL`
  (`GoodL s := NoLSE2Pairs s.exe`; an instruction does not change `exe`), so
  the generic layer (`Lower/Variant.lean`) applies: on configurations whose
  threads all run `NoLSE2Pairs` executables (`GoodC GoodL`), `InstrSem`,
  `PromSem`, `StepSem`, their `Inf` forms and `SuccKind` agree by cast, and
  so do `ReachableSem`, `ReachableSemInf` and `ReachableK`, in both
  directions (`*_lse2` below). `Config isa` and `Config isaLSE2` are not the
  same type (the ISA is a structure parameter), but their data are:
  `castC`/`uncastC` copy the fields and are mutually inverse.
- The executable machine (`Reachable`, `succs`), which `pilot_promising`
  uses: `reachableK_of_reachable_lse2` sends a `Reachable` run of `isaLSE2`
  to a `ReachableK` run of `isa` (through `ReachableK.of_reachable`, for
  which this file gives `ISA.LawfulState isaLSE2`). The converse, and
  `Reachable isa ↔ Reachable isaLSE2` itself, are not proved: `succs` runs
  `certify`, whose hash-map caches are keyed on `Thread I`, and relating two
  caches over different key types is not attempted. Theorems on
  `Reachable isa` transfer through their `#chaink_clone` K twin
  (`Lower/PilotLSE2.lean`).
- **(A4), not done: programs with pairs that are not one 16-byte location.**
  `GoodL` is static (a property of `exe`), which is why `Agree.leaves` holds
  for free. A program may contain a 64-bit `LDP`/`STP` on which the two ISAs
  still agree (its address not 16-aligned, or aligned but no declared
  16-byte location there: `pairIsOneLoc` false, so `toEv` splits the pair
  into two 8-byte accesses and `depsLSE2` is `deps`). Covering it needs
  (1) a cell-level lemma that, on such a pair, `toEv` of the
  `interpLSE2?` effects (writeback, `SP` check, one `loadPairK`/`storePairK`)
  is the same event tree as `exec`'s (`Directive.interp`'s), which this file
  does not prove; and (2) a *dynamic* `GoodL`: the address is read from the
  registers at the pc, so "every pair the thread will execute is not one
  location" is a program invariant over thread states, not preserved by
  `Agree.leaves` without a program-specific argument. -/
import Kraken.Promising.Lower.Variant
import Kraken.Promising.CertifyAArch64

namespace Kraken.Promising.AArch64

open Kraken.Promising.Lower.Variant Kraken.Promising.Live.Bridge Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Inf

/-- `isaLSE2` is `isa` with `exec`/`deps` replaced. -/
theorem isaLSE2_eq : isaLSE2 = isa.withExec execLSE2 depsLSE2 := rfl

/-! ## (A1) Cell-level agreement -/

instance (d : Directive) : Decidable d.LSE2Free := by
  unfold Directive.LSE2Free; split <;> infer_instance

/-- **At an `LSE2Free` cell, `execLSE2` is `exec`.** -/
theorem execLSE2_eq_exec_of_cell {s : State} (h : ∀ d z, s.cell = some (d, z) → d.LSE2Free) :
    execLSE2 s = exec s := by
  have hl : lse2Effects s = none := by
    unfold lse2Effects
    cases hc : s.cell with
    | none => rfl
    | some p =>
      obtain ⟨d, z⟩ := p
      exact @Directive.interpLSE2?_none_of_free (_root_.Executable.labels s.exe) d (h d z hc) _ _ _
  have hx : s.isCaspX = false := by
    unfold State.isCaspX
    rw [show s.directive = s.cell.map (·.1) from rfl]
    cases hc : s.cell with
    | none => rfl
    | some p =>
      obtain ⟨d, z⟩ := p
      have hf := h d z hc
      simp only [Option.map_some]
      unfold Directive.isCaspX
      split
      · exact hf.elim
      · rfl
  unfold execLSE2
  rw [hl]
  split
  · unfold exec; rw [ite_eq_left ‹_›]
  · simp only [hx, Bool.false_eq_true, ite_false]

/-- **At an `LSE2Free` directive, `depsLSE2` is `deps`.** -/
theorem depsLSE2_eq_deps_of_directive {s : State} (h : ∀ d, s.directive = some d → d.LSE2Free) :
    depsLSE2 s = deps s := by
  rcases s with ⟨exe, endPc, ⟨st, pc⟩, showPc, decls⟩
  unfold depsLSE2
  dsimp only
  split
  · rename_i hd
    exact False.elim (h _ hd)
  · rfl

/-- **No cell of `e` is a 64-bit `LDP`/`STP`**: the cells where `isa` and
`isaLSE2` may differ. -/
def NoLSE2Pairs (e : _root_.Executable) : Prop := ∀ p ∈ e.2, p.1.LSE2Free

theorem mem_of_mem_directivesFromAddress {e : _root_.Executable} {a : Int64} {x : Directive × Nat}
    (h : x ∈ e.directivesFromAddress a) : x ∈ e.2 := by
  unfold Kraken.Executable.directivesFromAddress at h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
  have hy' := (List.dropWhile_suffix _).subset hy
  rw [← Kraken.Executable.withAddresses_map_snd e.2 e.1]
  exact List.mem_map_of_mem hy'

theorem mem_of_cell {s : State} {d : Directive} {z : Nat} (h : s.cell = some (d, z)) : (d, z) ∈ s.exe.2 := by
  unfold State.cell at h
  exact mem_of_mem_directivesFromAddress ((List.dropWhile_suffix _).subset (List.mem_of_mem_head? h))

theorem mem_of_directive {s : State} {d : Directive} (h : s.directive = some d) : ∃ z, (d, z) ∈ s.exe.2 := by
  unfold State.directive at h
  obtain ⟨⟨d', z⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨z, mem_of_mem_directivesFromAddress ((List.dropWhile_suffix _).subset (List.mem_of_mem_head? hp))⟩

theorem execLSE2_eq_exec {s : State} (h : NoLSE2Pairs s.exe) : execLSE2 s = exec s :=
  execLSE2_eq_exec_of_cell fun _ _ hc => h _ (mem_of_cell hc)

theorem depsLSE2_eq_deps {s : State} (h : NoLSE2Pairs s.exe) : depsLSE2 s = deps s :=
  depsLSE2_eq_deps_of_directive fun _ hd => by
    obtain ⟨z, hz⟩ := mem_of_directive hd
    exact h _ hz

/-- **A laid-out program has no LSE2 pair iff none of its directives is
one**; the right-hand side is decidable. -/
theorem noLSE2Pairs_apply (l : _root_.Layout) {prog : Program} (h : ∀ d ∈ prog, d.LSE2Free) :
    NoLSE2Pairs (l prog) := by
  intro p hp
  change p ∈ prog.mapIdx (fun i d => (d, l.size i)) at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hp
  exact h _ (List.getElem_mem hi)

/-! ## (A2) Machine-level transfer -/

/-- The thread states on which `isa` and `isaLSE2` agree: the executable has
no LSE2 pair. -/
abbrev GoodL (s : isa.State) : Prop := NoLSE2Pairs s.exe

/-- **`isaLSE2` agrees with `isa` on `GoodL`**, which instructions preserve. -/
theorem agreeLSE2 : Agree isa execLSE2 depsLSE2 GoodL where
  exec _ h := execLSE2_eq_exec h
  deps _ h := depsLSE2_eq_deps h
  leaves s h tree hex := by
    change exec s = some tree at hex
    unfold exec at hex
    split at hex
    · cases hex
    · cases hex
      exact EvTree.All.map (P := GoodL) (fun st => { s with st }) (fun _ => h) _

/-- `isaLSE2`'s state comparison is `isa`'s, and its instructions also keep
the static part (the `LDP`/`STP` branch replaces only the machine state). -/
instance : ISA.LawfulState isaLSE2 where
  static := static
  beq_refl := ISA.LawfulState.beq_refl (I := isa)
  beq_symm := ISA.LawfulState.beq_symm (I := isa)
  beq_trans := ISA.LawfulState.beq_trans (I := isa)
  hash_eq := ISA.LawfulState.hash_eq (I := isa)
  eq_of_beq := ISA.LawfulState.eq_of_beq (I := isa)
  exec_static a tree h := by
    change execLSE2 a = some tree at h
    unfold execLSE2 at h
    split at h
    · cases h
    · split at h
      · cases h
        exact EvTree.All.map (P := fun s => static s = static a) (fun st => { a with st }) (fun _ => rfl) _
      · split at h
        · cases h
          exact EvTree.All.map (P := fun s => static s = static a) (fun st => { a with st }) (fun _ => rfl) _
        · exact ISA.LawfulState.exec_static (I := isa) a tree h

/-- `isa → isaLSE2` on configurations. -/
abbrev toL (c : Config isa) : Config isaLSE2 := castC (I := isa) (ex := execLSE2) (dp := depsLSE2) c

/-- `isaLSE2 → isa` on configurations. -/
abbrev ofL (c : Config isaLSE2) : Config isa := uncastC (I := isa) (ex := execLSE2) (dp := depsLSE2) c

/-- The initial configuration is its own cast. -/
theorem toL_init (states : List isa.State) (initMem : List (Loc × Val)) :
    toL (Config.init states initMem) = (Config.init states initMem : Config isaLSE2) :=
  castC_init states initMem

section Transfer

variable {A : Arch} {c : Config isa} (hc : GoodC GoodL c)
include hc

theorem instrSem_lse2_iff {fuel tid : Nat} {c' : Config isa} :
    InstrSem A fuel tid (toL c) (toL c') ↔ InstrSem A fuel tid c c' :=
  instrSem_castC_iff agreeLSE2 hc

theorem promSem_lse2_iff {fuel tid : Nat} {c' : Config isa} :
    PromSem A fuel tid (toL c) (toL c') ↔ PromSem A fuel tid c c' :=
  promSem_castC_iff agreeLSE2 hc

theorem stepSem_lse2_iff {fuel tid : Nat} {c' : Config isa} :
    StepSem A fuel tid (toL c) (toL c') ↔ StepSem A fuel tid c c' :=
  stepSem_castC_iff agreeLSE2 hc

theorem instrSemInf_lse2_iff {tid : Nat} {c' : Config isa} :
    InstrSemInf A tid (toL c) (toL c') ↔ InstrSemInf A tid c c' :=
  instrSemInf_castC_iff agreeLSE2 hc

theorem promSemInf_lse2_iff {tid : Nat} {c' : Config isa} :
    PromSemInf A tid (toL c) (toL c') ↔ PromSemInf A tid c c' :=
  promSemInf_castC_iff agreeLSE2 hc

theorem stepSemInf_lse2_iff {tid : Nat} {c' : Config isa} :
    StepSemInf A tid (toL c) (toL c') ↔ StepSemInf A tid c c' :=
  stepSemInf_castC_iff agreeLSE2 hc

theorem succKind_lse2_iff {c' : Config isa} : SuccKind A (toL c) (toL c') ↔ SuccKind A c c' :=
  succKind_castC_iff agreeLSE2 hc

/-- **`ReachableSem` of `isa` is `ReachableSem` of `isaLSE2`**, both ways. -/
theorem reachableSem_lse2_iff {fuel : Nat} {c' : Config isa} :
    ReachableSem A fuel (toL c) (toL c') ↔ ReachableSem A fuel c c' :=
  ⟨fun h => (congrArg _ (uncastC_castC c')).mp (reachableSem_uncastC agreeLSE2 h hc), fun h => reachableSem_castC agreeLSE2 h hc⟩

theorem reachableSemInf_lse2_iff {c' : Config isa} :
    ReachableSemInf A (toL c) (toL c') ↔ ReachableSemInf A c c' :=
  ⟨fun h => (congrArg _ (uncastC_castC c')).mp (reachableSemInf_uncastC agreeLSE2 h hc), fun h => reachableSemInf_castC agreeLSE2 h hc⟩

theorem reachableK_lse2_iff {c' : Config isa} : ReachableK A (toL c) (toL c') ↔ ReachableK A c c' :=
  ⟨fun h => (congrArg _ (uncastC_castC c')).mp (reachableK_uncastC agreeLSE2 h hc), fun h => reachableK_castC agreeLSE2 h hc⟩

/-- Every `isaLSE2` configuration reachable (semantic machine) from `toL c`
is the cast of one reachable from `c` under `isa`. -/
theorem reachableSem_ofL {fuel : Nat} {x : Config isaLSE2} (h : ReachableSem A fuel (toL c) x) :
    ReachableSem A fuel c (ofL x) :=
  reachableSem_uncastC agreeLSE2 h hc

/-- **The executable machine of `isaLSE2` is inside the K world of `isa`.** -/
theorem reachableK_of_reachable_lse2 {fuel : Nat} {x : Config isaLSE2} (h : Reachable A fuel (toL c) x) :
    ReachableK A c (ofL x) :=
  reachableK_uncastC agreeLSE2 (ReachableK.of_reachable (I := isaLSE2) h) hc

/-- A final configuration reached from `toL c` is final as an `isa`
configuration. -/
theorem final_ofL_of_reachableK {x : Config isaLSE2} (h : ReachableK A (toL c) x) (hf : x.final = true) :
    (ofL x).final = true := by
  have hg := goodC_of_reachableK agreeLSE2 (reachableK_uncastC agreeLSE2 h hc) hc
  rw [← final_castC agreeLSE2 hg]
  exact (congrArg Config.final (castC_uncastC x)).trans hf

end Transfer

end Kraken.Promising.AArch64
