/-
**Smoke test of the x64 `EnvGLR` link**:
an unlocked read-modify-write of a shared location, `incl (%rdi)` (a plain
4-byte load, then a plain 4-byte store of the incremented value to the same
address, `MachineData.rmwPlain`; under `Arch.tso` the store is a release).

- Shape: `incl (%rdi)` and `addl $1, (%rdi)` fail `dirs_phase2X` (a
  release-kind write after a load) and pass `dirs_lrX` (load-then-store).
  `lock incl (%rdi)` (one release-kind RMW) fails `dirs_lrX`: it stays on
  `ofSafelyEnvGRX`.
- The env rule `inc32_shared` (`LRX64VCGen.lean`): `incl d(%b)` on a
  location outside `dmem`, any environment.
- The VC (`incRelX_tripleEnv`): from `IncPre` (the location outside `dmem`
  and in `S`, a positive write permission, a non-releasing plan for it and a
  pure release predicate), `incl (%rdi)` runs in `EnvGLRX`: its store is
  permitted at the `EnvGLR` state after its load (the load keeps the
  resource and the ghost's release predicates). The same VC by `vcgen`:
  `incRelX_vcgen` (`vcgen [inc32_shared_spec]`, at `CodeEnv := layout incRelX`).
- The rule: `incRelX_rule` (`ThreadRuleRX.ofSafelyEnvGLRX`, the shape from
  `dirs_lrX`), `incRelX_noFault` (`noFaultRule_ofSafelyEnvGLRX_struct`,
  `dirs_no_fault`), and `incRelX_inv_init` (the rule's invariant at the
  initial configuration from the VC, `invGLRX_init`).

What is shown: the load-then-release tree is accepted by the rule link, and
the env-side VC of the store after the load holds in `EnvGLRX`. The
postcondition handed to `B` is trivial (`B := fun _ _ _ => True`); the
program's effect on the shared counter is not tracked (no plan for it).
-/
import Kraken.Promising.SLR.EnvG.LRX64VCGen
import Kraken.Promising.EnvLinkTermX64
import Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.LRSmoke

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser MachineWP

/-! ## The programs and their shapes -/

/-- An unlocked increment of a shared counter. -/
def incRelX : Program := parse("
  incl (%rdi)
")

/-- A scalar load, then an unlocked add to a shared location. -/
def addRelX : Program := parse("
  movl (%rsi), %eax
  addl $1, (%rdi)
")

/-- The locked increment (one release-kind RMW). -/
def lockIncX : Program := parse("
  lock incl (%rdi)
")

variable [layout : _root_.Layout]

/-- The unlocked increment is not phase-2 (a release-kind write after a load). -/
example : True := by
  fail_if_success (have : DirsPhase2X Arch.tso (layout incRelX) := by dirs_phase2X incRelX)
  trivial

example : True := by
  fail_if_success (have : DirsPhase2X Arch.tso (layout addRelX) := by dirs_phase2X addRelX)
  trivial

/-- **The unlocked increment is a load-then-store tree.** -/
theorem incRelX_lr : DirsLRX Arch.tso (layout incRelX) := by dirs_lrX incRelX

/-- **`movl` then `addl $1, (m)`**: phase-1, then load-then-store. -/
theorem addRelX_lr : DirsLRX Arch.tso (layout addRelX) := by dirs_lrX addRelX

/-- The locked increment is not (a release-kind RMW: `ofSafelyEnvGRX`). -/
example : True := by
  fail_if_success (have : DirsLRX Arch.tso (layout lockIncX) := by dirs_lrX lockIncX)
  trivial

/-- The unlocked increment is fault-free. -/
theorem incRelX_noFaultDirs : DirsNoFault (layout incRelX) := by dirs_no_fault incRelX

/-! ## The VC in `EnvGLRX` -/

section VC

variable {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- The address of `incl (%rdi)`. -/
abbrev incAddr (s : MachineData) : BitVec 64 := s.regs.get64 .rdi + (0 : Int64).toBitVec

/-- **The precondition of the increment**: the location outside `dmem` and
in `S`, a positive write permission for it, a plan under which no store to
it is a planned release, and a pure release predicate for it. -/
def IncPre (pl : Plan) (S : SharedEnv.Layout) (s : MachineData) (σ : EStateX) : Prop :=
  Mem.loadInt s.dmem (incAddr s) 4 = none ∧ (incAddr s, 4) ∈ S ∧ 0 < (σ.r.wr ⟨incAddr s, 4⟩).q ∧
    (∀ v, pl.rel ⟨incAddr s, 4⟩ v = false) ∧ ∀ v, Pred.Pure (σ.g.rel ⟨incAddr s, 4⟩) v

omit layout in
/-- **The store after the load is permitted in `EnvGLRX`**: the `EnvGLR`
load keeps the resource and the ghost's release predicates. -/
theorem incStore_ok {s : MachineData} {σ σ' : EStateX} (h : IncPre pl S s σ) {v : Val}
    (hs : (EnvGLRX Arch.tso tid pl S).step (.load .plain false (incAddr s) 4) σ v σ') (v' : Val) :
    (EnvGLRX Arch.tso tid pl S).ok (.store .plain false (incAddr s) 4 v') σ' := by
  obtain ⟨-, hS, hq, hrel, hpure⟩ := h
  obtain ⟨hanc, hr, -⟩ := step_loadFactsLR (I := isa) (pl := pl) hs
  have hg : σ'.g.rel = σ.g.rel := hanc.ghost.rel
  exact ⟨⟨rfl, by rw [hr]; exact hq, fun _ => by rw [hg]; exact hpure _,
    fun h => absurd h (by rw [hrel]; decide)⟩, hS⟩

omit layout in
/-- **The VC of the increment in `EnvGLRX`**: from `IncPre`, the increment
runs to its end. -/
theorem incRelX_tripleEnv [CodeEnv] {E : Int64 → MachineData → EStateX → Prop} :
    TripleEnv (EnvGLRX Arch.tso tid pl S) (IncPre pl S) incRelX (fun _ _ => True) E :=
  fun s g h => inc32_shared (EnvGLRX Arch.tso tid pl S) .rdi 0 (p := []) s g
    ⟨h.1, ⟨trivial, h.2.1⟩, fun _ _ hs => ⟨incStore_ok h hs _,
      fun _ _ _ _ _ _ => Eventually.done _ (Or.inl ⟨rfl, trivial⟩)⟩⟩

end VC

/-! ## The rule -/

section Rule

variable [Kraken.Executable.ValidLayout (layout incRelX)] {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- The increment's postcondition: the end of its text. -/
abbrev incPost : MachineState × EStateX → Prop := postOfX incRelX fun _ _ => True

/-- **The unlocked increment's rule on `EnvGLR`** (`Arch.tso`). -/
def incRelX_rule (hpl : pl.Valid) (hS : Le16 S) :
    ThreadRuleRX (I := isa) Arch.tso (fun _ _ _ => True) tid :=
  ThreadRuleRX.ofSafelyEnvGLRX (S := S) (post := incPost) hpl hS (lrTreeX_of_dirs incRelX_lr)
    postOfX_end (not_instrStepEnv_of_end_labels _ 0) (fun _ _ _ _ _ _ _ _ _ _ => trivial)

/-- **The increment's rule excludes faults.** -/
theorem incRelX_noFault (hpl : pl.Valid) (hS : Le16 S) :
    NoFaultRule (incRelX_rule (tid := tid) hpl hS) :=
  noFaultRule_ofSafelyEnvGLRX_struct _ _ _ _ _ _ incRelX_noFaultDirs

/-- **The rule's invariant at the initial configuration**, from the VC. -/
theorem incRelX_inv_init [CodeEnv] (henv : cenv = layout incRelX) {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    (he : s.exe = layout incRelX) (hds : s.decls = {}) (hend : s.endPc = (layout incRelX).addrOf incRelX.length)
    (hpc : s.st.2 = (layout incRelX).addrOf 0) (hsplit : Split S s.st.1.dmem)
    (hP : IncPre pl S s.st.1 (σInitX (Config.init ss m) r g)) :
    InvGLR (I := isa) Arch.tso tid pl
      (QX64LR Arch.tso tid pl S (layout incRelX) ((layout incRelX).addrOf incRelX.length) incPost)
      True (Config.init ss m) r g :=
  invGLRX_init hs hpend
    (qx64LR_of_partialTripleEnv (E := fun _ _ _ => False) incRelX_tripleEnv.partial henv he hds hend hpc hsplit hP)

end Rule

section VCGen

open Std.WP Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

variable {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

local instance incRelX.env : CodeEnv := ⟨layout incRelX⟩

/-- **The same VC by `vcgen`** (`inc32_shared_spec`). -/
theorem incRelX_vcgen :
    TripleEnv (EnvGLRX Arch.tso tid pl S) (fun s σ => IncPre pl S s σ) incRelX (fun _ _ => True)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold incRelX IncPre
  vcgen [inc32_shared_spec]
  case vc1 s σ h => exact h.1
  case vc2 s σ h => exact ⟨trivial, h.2.1⟩
  case vc3 s σ h v σ' hs =>
    exact ⟨incStore_ok h hs _, fun _ _ _ _ _ _ => Eventually.done _ (Or.inl ⟨rfl, trivial⟩)⟩

end VCGen

#print axioms incRelX_lr
#print axioms addRelX_lr
#print axioms incRelX_tripleEnv
#print axioms incRelX_vcgen
#print axioms incRelX_rule
#print axioms incRelX_noFault
#print axioms incRelX_inv_init

end Kraken.Promising.X64.EnvG.LRSmoke
