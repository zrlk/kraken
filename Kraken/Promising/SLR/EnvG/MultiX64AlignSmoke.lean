/-
**The load-then-release design's `movups` smoke, fault-free under alignment**:
`movupsLoad` (`movups (%rdi), %xmm0; movl (%rsi), %eax`,
`MultiX64Smoke.lean`) is not statically fault-free (`dirs_no_fault` fails: a
piece crossing a cache line faults), but it is fault-free wherever an
environment fitting an `Al8` layout runs it (`movupsLoad_noFaultEnv`), so its
phase-2 rule `movupsLoadRule` excludes faults (`movupsLoadRule_noFault`).

`Al8 S` is decidable on a concrete layout (`al8_example`: a 16-aligned
buffer's two halves and a 4-byte flag).
-/
import Kraken.Promising.SLR.EnvG.MultiX64Align
import Kraken.Promising.SLR.EnvG.MultiX64Smoke

namespace Kraken.Promising.X64.EnvG.MultiSmoke

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

/-- `Al8` of a concrete layout, by `decide`. -/
theorem al8_example : Al8 [(0x1000, 8), (0x1008, 8), (0x2000, 4)] := by
  intro a ha
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ha
  rcases ha with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, h⟩
  · decide
  · decide
  · cases h

variable [layout : _root_.Layout]

/-- **`movupsLoad` is fault-free where an environment fitting an `Al8`
layout runs it**: `movups` reads its first piece from the environment, so its
address is 8-aligned and no piece crosses a line; `movl` is statically
fault-free. -/
theorem movupsLoad_noFaultEnv {S : SharedEnv.Layout} (hal : Al8 S) : DirsNoFaultEnvX S (layout movupsLoad) := by
  refine dirsNoFaultEnvX_layout ?_
  intro d hd e z
  simp only [movupsLoad, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · intro E hF s pc g P₁ P₂ h
    simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.AvxOperation.interp, _root_.AvxRegOrMem.interp,
      _root_.MachineData.loadAvx, _root_.MachineData.setAvxLegacy] at h ⊢
    simp only [Effects.AllEnv, Kraken.Promising.X64.toEv, Bool.false_and, Bool.false_eq_true, ite_false] at h ⊢
    split
    · simp [Kraken.Promising.X64.toEv, EvTree.NoFault]
    · rename_i hnone
      simp only [hnone, Effects.AllEnv, AvxWidth.bytes] at h
      -- the environment's first piece is a location of `S`, hence 8-aligned
      have hA := hal _ (hF.load (h.elim (fun h => h.1) (fun h => h.1)))
      exact loadPieces_noFault_al8 _ _ _ hA fun _ => trivial
  · exact DirNoFault.toEnvX (by
      intro s pc
      simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
        Kraken.Promising.X64.toEv, _root_.MachineData.load, _root_.RegOrMem.interp, _root_.Operand.interp,
        _root_.MachineData.set]
      repeat' (first | split | simp [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault,
        Kraken.Promising.EvTree.access_empty]))

section Rule

variable [Kraken.Executable.ValidLayout (layout movupsLoad)] {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}
  {post : MachineState × EStateX → Prop} {B : Config isa → (model isa).R → (model isa).Ghost → Prop}

/-- **The vector load's phase-2 rule excludes faults**, for an `Al8` layout. -/
theorem movupsLoadRule_noFault (hal : Al8 S) (hpl : pl.Valid) (hS : Le16 S)
    (hpost : ∀ y, post y → y.1.2 = (layout movupsLoad).1)
    (hstuck : ∀ x R, x.1.2 = (layout movupsLoad).1 →
      ¬ Kraken.Executable.instrStepEnv (layout movupsLoad) (EnvGX Arch.tso tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    NoFaultRule (movupsLoadRule hpl hS hpost hstuck hB) :=
  noFaultRule_ofSafelyEnvG2X_env _ _ _ _ _ _ (movupsLoad_noFaultEnv hal)

end Rule

#print axioms al8_example
#print axioms movupsLoad_noFaultEnv
#print axioms movupsLoadRule_noFault

end Kraken.Promising.X64.EnvG.MultiSmoke
