/-
Whole-thread environment (`EnvG`): **the AArch64 link
`ThreadRuleRX.ofSafelyEnvG`**.

A thread proved by a `Safely` judgment of `instrStepEnv (EnvG isa A tid pl)`
(code `e`, end address `endPc`, postcondition `post` only at `endPc`) gives
a `ThreadRuleRX`, so `NPSafe.of_ruleRX` applies unchanged
(`npSafe_of_safelyEnvG`). It is the rule link (`EnvG/RuleLink.lean`) at

  `QA64 st σ := st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧
    Safely (e.instrStepEnv (EnvG isa A tid pl)) post (st.st, σ)`;

`LinkHyps` from `exec_treeJLive_of_instrStepEnv'` (`A64Live.lean`; a
`Safely` state at an instruction steps, since `post` is only at `endPc`,
where the thread's tree is `none`), the static check `e.rmwLive`, and the
phase-1 shape of the code's trees (`Phase1Tree`, a stated hypothesis:
deterministic single access, **releases are stores**; `KNOWN_GAPS.md`).
`done` reads `post` off a halted thread (`hstuck`: no step at `endPc`, e.g.
`not_instrStepEnv_of_end_labels`; elsewhere a halted thread has no
instruction).

Also a sample `Plan.Valid` by `decide`.
-/
import Kraken.Promising.SLR.EnvG.RuleLink
import Kraken.Promising.SLR.EnvG.A64Live

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- `EnvG` for AArch64. -/
abbrev EnvGA (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv := Kraken.Promising.SLR.EnvG isa A tid pl

/-- `EnvG`'s state for AArch64. -/
abbrev EStateA : Type := Kraken.Promising.SLR.EnvG.State isa

/-- **The phase-1 shape of the code** (stated hypothesis): every tree of a
thread state running `e` with no declarations is a deterministic single
access with no release-kind RMW. -/
def Phase1Tree (A : Arch) (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree → Phase1Shape A tree

/-- **The thread-local invariant**: the code, no declarations, the end
address, and the `Safely` judgment of `EnvG` at the machine state. -/
def QA64 (A : Arch) (tid : Nat) (pl : Plan) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGA A tid pl)) post (st.st, σ)

/-- An instruction step at a thread state's pc finds its directive. -/
theorem directive_isSome_of_instrStepEnv {E : SharedEnv} {e : Kraken.Executable Directive} {st : State}
    {g : E.State} {R : MachineState × E.State → Prop} (he : st.exe = e) (h : e.instrStepEnv E (st.st, g) R) :
    st.directive.isSome := by
  obtain ⟨d, z, rest, hcode, -⟩ := h
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hcode
  subst he
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  rw [hdir]; rfl

/-- At the end address the thread has no instruction. -/
theorem exec_eq_none_of_end {st : State} (h : st.st.2 = st.endPc) : isa.exec st = none := by
  show exec st = none
  unfold exec
  simp [h]

/-- **`done` from a `Safely` judgment, for any environment**: a halted
thread whose `Safely` state allows no step at `endPc` (`hstuck`) is at its
postcondition (elsewhere a halted thread has no directive). The shared body
of the `post_of_halted_Q…` lemmas. -/
theorem post_of_halted_env {E : SharedEnv} {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × E.State → Prop} (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv E x R)
    {t : Thread isa} {σ : E.State} (he : t.st.exe = e) (hend : t.st.endPc = endPc)
    (hsafe : Safely (e.instrStepEnv E) post (t.st.st, σ)) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  refine hsafe.post_of_stuck fun R hR => ?_
  have hdir := directive_isSome_of_instrStepEnv he hR
  have hh' : (exec t.st).isNone = true := hh
  unfold exec at hh'
  split at hh'
  · next hc =>
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with hc | hc
    · exact hstuck _ R (by rw [← hend]; exact hc) hR
    · rw [Option.isNone_iff_eq_none] at hc
      rw [hc] at hdir; cases hdir
  · cases hh'

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses at `QA64`**: from `exec_treeJLive_of_instrStepEnv'`
(`post` only at `endPc`, where the thread has no tree). -/
theorem linkHyps_QA64 (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHyps (I := isa) A tid pl (QA64 A tid pl e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnv' J he hds hR (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive
        tree hex

omit [Kraken.Executable.ValidLayout e] in
/-- **`done` at `QA64`**: a halted thread's `Safely` state is at its
postcondition (no step at `endPc`, `hstuck`; elsewhere no directive). -/
theorem post_of_halted_QA64 (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    {t : Thread isa} {σ : EStateA} (hQ : QA64 A tid pl e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRX.ofSafelyEnvG`**: the AArch64 rule link. A thread whose
code `e` passes the static check and has phase-1 trees, proved by a `Safely`
judgment of `EnvG` with postcondition `post` only at `endPc` (and no step at
`endPc`), satisfies `ThreadRuleRX A B tid` for every `B` that `post` gives at
a halted thread with no promise (`hB`, with `EnvRel` and the clean flag). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvG {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG (linkHyps_QA64 (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64 hstuck hQ hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvG`** (`NPSafe.of_ruleRX` at
`ofSafelyEnvG`), from any configuration where the rule's invariant holds:
the core (`CoreAt`: `EnvRel`, pending marks below `|M|`, in-flight facts)
and `QA64` at some env state. -/
theorem npSafe_of_safelyEnvG {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QA64 A tid pl e endPc post) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvG hpl hlive hshape hpost hstuck hB) n m cl c r g h

end Link

/-! ## A sample plan -/

/-- A spinlock release plan: a store of `0` to the lock word gives away the
protected counter. -/
def sampleLockPlan : Plan := ⟨[{ loc := ⟨0x1000, 4⟩, val := some 0, gives := [⟨0x2000, 4⟩] }]⟩

theorem sampleLockPlan_valid : sampleLockPlan.Valid := by decide

/-- An invalid plan (the release gives away its own location). -/
theorem not_valid_selfGive : ¬ (⟨[{ loc := ⟨0x1000, 4⟩, gives := [⟨0x1000, 4⟩] }]⟩ : Plan).Valid := by decide

end Kraken.Promising.AArch64.EnvG
