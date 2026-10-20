/-
Whole-thread environment: **no fault for x64 vector
loads read in pieces, under an alignment hypothesis on the shared layout**.

A non-atomic vector access outside `dmem` is read in 8-byte pieces
(`loadPieces`/`storePieces`, `Promising/X64.lean`); a piece that becomes an
event and crosses a 64-byte cache line (`crossesLine a := 56 < a % 64`) is a
`.fault`. So `dirs_no_fault` rejects every vector load from memory (the load-then-release design's
`movups` smoke), and `noFaultRule_ofSafelyEnvG2X_struct` does not apply.

**The fault condition.** An 8-aligned piece never crosses a line, and the
pieces of an access at an 8-aligned address are 8-aligned
(`crossesLine_of_al8`, `al8_add8`, `loadPieces_noFault_al8`). The address is
known from the `Safely` judgment: the environment's side of the access
(`Effects.AllEnv`, `SharedEnv.LoadPieces`) asks the environment for the
*first* piece, whatever the private memory, and an environment fitting `S`
(`X64Fit`) permits only locations of `S`. So the hypothesis is static, on the
layout: **`Al8 S`**, every 8-byte location of `S` is 8-aligned (for a
16-byte `movups` of a 16-aligned buffer: `S` holds its two 8-aligned
halves). (Whether later pieces are asked depends on the environment's
answers; the first piece's alignment covers them all.)

- `DirNoFaultEnvX S e d z`: the directive's tree is fault-free at every
  machine state at which some environment fitting `S` runs it
  (either `stepAtEnv` disjunct); `DirNoFault.toEnvX` (static no-fault
  directives qualify), `dirsNoFaultEnvX_layout`.
- `noFault_of_instrStepEnvX`: the plumbing of `exec_treeJ_of_instrStepEnv`
  with the per-directive hypothesis in place of `directive_jsim`.
- `noFault_QX64_env`, `noFaultRule_ofSafelyEnvG2X_env` (phase 2),
  `noFaultRule_ofSafelyEnvGX_env` (phase 1), `noFaultRule_ofSafelyEnvGLRX_env`
  (`EnvGLR`).
- `movups_noFaultEnvX`: `movups d(%b), %x` qualifies under `Al8 S`.

Instance on the load-then-release design's smoke: `MultiX64AlignSmoke.lean`.
-/
import Kraken.Promising.SLR.EnvG.LRX64
import Kraken.Promising.EnvLinkTermX64

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Aligned pieces do not fault -/

/-- **Every 8-byte location of the layout is 8-aligned.** -/
def Al8 (S : SharedEnv.Layout) : Prop := ∀ a : BitVec 64, (a, 8) ∈ S → a.toNat % 8 = 0

/-- An 8-aligned piece does not cross a cache line. -/
theorem crossesLine_of_al8 {a : BitVec 64} (h : a.toNat % 8 = 0) : crossesLine a = false := by
  have : a.toNat % 64 % 8 = 0 := by rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 64)]; exact h
  have : a.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [crossesLine, decide_eq_false_iff_not, Nat.not_lt]
  omega

/-- The next piece of an 8-aligned access is 8-aligned. -/
theorem al8_add8 {a : BitVec 64} (h : a.toNat % 8 = 0) : (a + 8).toNat % 8 = 0 := by
  rw [BitVec.toNat_add]
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [h8, Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2 ^ 64)]
  omega

/-- **The pieces of a load at an 8-aligned address do not fault.** -/
theorem loadPieces_noFault_al8 {σ : Type} {dmem : DataMem} :
    ∀ (n : Nat) (addr : BitVec 64) (k : List UInt8 → EvTree σ), addr.toNat % 8 = 0 →
      (∀ bs, (k bs).NoFault) → (loadPieces {} dmem addr n k).NoFault
  | 0, _, _, _, hk => hk []
  | n + 1, addr, k, ha, hk => by
    unfold loadPieces
    simp only
    split
    · exact loadPieces_noFault_al8 n (addr + 8) _ (al8_add8 ha) fun _ => hk _
    · rw [crossesLine_of_al8 ha]
      simp only [Bool.false_eq_true, ite_false, EvTree.access_empty, EvTree.NoFault]
      exact fun _ => loadPieces_noFault_al8 n (addr + 8) _ (al8_add8 ha) fun _ => hk _

/-- **The pieces of a store at an 8-aligned address do not fault.** -/
theorem storePieces_noFault_al8 {σ : Type} :
    ∀ (n : Nat) (addr : BitVec 64) (bs : List UInt8) (dmem : DataMem) (k : DataMem → EvTree σ),
      addr.toNat % 8 = 0 → (∀ d, (k d).NoFault) → (storePieces {} addr n bs dmem k).NoFault
  | 0, _, _, _, _, _, hk => hk _
  | n + 1, addr, bs, dmem, k, ha, hk => by
    unfold storePieces
    split
    · exact storePieces_noFault_al8 n (addr + 8) _ _ _ (al8_add8 ha) hk
    · rw [crossesLine_of_al8 ha]
      simp only [Bool.false_eq_true, ite_false, EvTree.access_empty, EvTree.NoFault]
      exact fun _ => storePieces_noFault_al8 n (addr + 8) _ _ _ (al8_add8 ha) hk

/-! ## No fault at the environment's states, per directive -/

/-- **The directive's tree is fault-free wherever an environment fitting `S`
runs it**: at every machine state at which some `E` with `X64Fit S E` answers
the directive's effects (`Effects.AllEnv`, either disjunct of `stepAtEnv`),
the adapter's tree has no fault. -/
def DirNoFaultEnvX (S : SharedEnv.Layout) (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (E : SharedEnv), X64Fit S E → ∀ (s : MachineData) (pc : Int64) (g : E.State)
    (P₁ P₂ : MachineState → E.State → Prop),
    ((@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).AllEnv E g P₁ ∨
      (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
        (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).AllEnv E g P₂) →
    (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))).NoFault

/-- Every directive of the text is fault-free where the environment runs it. -/
def DirsNoFaultEnvX (S : SharedEnv.Layout) (e : _root_.Executable) : Prop :=
  ∀ d z, (d, z) ∈ e.2 → DirNoFaultEnvX S e d z

/-- A statically fault-free directive qualifies. -/
theorem DirNoFault.toEnvX {S : SharedEnv.Layout} {e : _root_.Executable} {d : Directive} {z : Nat}
    (h : DirNoFault e d z) : DirNoFaultEnvX S e d z :=
  fun _ _ s pc _ _ _ _ => h s pc

/-- Statically fault-free code qualifies. -/
theorem DirsNoFault.toEnvX {S : SharedEnv.Layout} {e : _root_.Executable} (h : DirsNoFault e) :
    DirsNoFaultEnvX S e :=
  fun d z hm => DirNoFault.toEnvX (h d z hm)

/-- The directives of a laid-out program are the program's. -/
theorem dirsNoFaultEnvX_layout [layout : _root_.Layout] {S : SharedEnv.Layout} {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirNoFaultEnvX S e d z) : DirsNoFaultEnvX S (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

/-- **One instruction: no fault at an environment step** (the plumbing of
`exec_treeJ_of_instrStepEnv`, with `DirsNoFaultEnvX` in place of
`directive_jsim`). -/
theorem noFault_of_instrStepEnvX {E : SharedEnv} {S : SharedEnv.Layout} (hF : X64Fit S E)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hds : st.decls = {}) (hnf : DirsNoFaultEnvX S e)
    (h : e.instrStepEnv E (st.st, g) R) : ∀ tree, isa.exec st = some tree → tree.NoFault := by
  intro tree htree
  obtain ⟨d, sz, rest, hcode, hstep⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  have hmem := mem_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat hstep hmem ⊢
  subst he hds
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls := {} } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  simp only [isa, exec, hdir, Option.isNone_some, Bool.or_false] at htree
  split at htree
  · cases htree
  · cases htree
    refine (EvTree.noFault_map _ _).mpr ?_
    unfold Executable.step
    letI := Executable.labels exe
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]
    unfold Kraken.Executable.stepAtEnv at hstep
    exact hnf d sz hmem E hF s pc g _ _ hstep

/-! ## The no-fault rules -/

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **Every tree from a `QX64`-state is fault-free**, for code fault-free
where the environment runs it (`noFault_QX64` with `DirsNoFaultEnvX`). -/
theorem noFault_QX64_env (hnf : DirsNoFaultEnvX S e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64 A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_instrStepEnvX (within_fit _ S) he hds hnf hR tree hex

/-- `noFault_QX64_env` at `QX64LR`. -/
theorem noFault_QX64LR_env (hnf : DirsNoFaultEnvX S e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64LR A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_instrStepEnvX (within_fit _ S) he hds hnf hR tree hex

/-- **The x64 phase-1 no-fault rule, environment form.** -/
theorem noFaultRule_ofSafelyEnvGX_env {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultEnvX S e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGX hpl hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG_struct _ _ (noFault_QX64_env hnf hpost)

/-- **The x64 phase-2 no-fault rule, environment form** (vector loads in
pieces, with `Al8 S` through `movups_noFaultEnvX`). -/
theorem noFaultRule_ofSafelyEnvG2X_env {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase2TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultEnvX S e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvG2X hpl hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG2_structX _ _ (noFault_QX64_env hnf hpost)

/-- **The x64 `EnvGLR` no-fault rule, environment form.** -/
theorem noFaultRule_ofSafelyEnvGLRX_env {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : LRTreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGLRX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultEnvX S e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGLRX hpl hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvGLR_struct _ _ (noFault_QX64LR_env hnf hpost)

end Rule

end Kraken.Promising.X64.EnvG
