/-
**Calls in the environment wp, AArch64.** The environment-wp (`wpEnv`)
counterparts of the call rules of
`Kraken/AArch64/WP/RulesCF.lean`, for a callee whose own run consults the
environment (it touches shared memory), so that its specification is a
`TripleEnv` or a `ProcSpecEnv` rather than a sequential triple.

`MachineWP.wpEnv_of_triple` and `env_lift_spec` lift a call whose callee is
sequential (`call_spec` first, then lifting); a callee with a shared access
has no sequential triple, and needs these.

## Contents

- `bl_cellEnv`, `blr_cellEnv`: the `BL`/`BLR` cells under `AllEnv`. Neither
  accesses memory, so the environment state is passed through unchanged.
- `MachineWP.call_specEnv`: **the call rule**, `call_spec` over `wpEnv`. The
  callee's run (text `body` at label `l`) is a `TripleEnv` premise, for every
  return address `ra`. Its exit at `ra` continues the caller's `wpEnv` of the
  cells behind the `BL`, at the environment state the callee left; any other
  exit is the caller's own.
- `MachineWP.fun_specEnv_from_label`: the same with the callee's
  `Pre`/`Post` not mentioning `ra` (the form of `fun_spec_from_label`). The
  tail and channels are left open, so one `have` serves every call site.
- `MachineWP.call_proc_specEnv`, `MachineWP.blr_proc_specEnv`: `BL`/`BLR`
  through a callee's `ProcSpecEnv` (`call_proc_spec`, `blr_proc_spec`).
- `TripleEnv.mono`: consequence for `TripleEnv`.
- Example (`CallLdar`): a caller `bl f; add x2, x0, #1` whose callee
  `f: ldar x0, [x1]; ret` performs one shared acquire load. The caller's
  `TripleEnv` in `SharedEnv.lastWrite` is proved from the callee's
  `TripleEnv` (`callee_envSpec`, by `vcgen`) through
  `fun_specEnv_from_label`.
-/
import Kraken.AArch64.EnvVCGen
import Kraken.AArch64.Parser
import Kraken.AArch64.WP.Cfg
import Kraken.AArch64.WP.RulesCF

open Kraken
open Std.WP
open Lean.Order

section Rules

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- The cell of `BL l` under the environment: `X30` gets the address behind
it, control goes to the label, and the environment state is unchanged. -/
theorem bl_cellEnv (l : Label) (s : MachineData) (pc : Int64) (z : Nat) (g : env.State)
    (post : MachineState → env.State → Prop) :
    (@Directive.interp (_root_.Executable.labels cenv)
        (Directive.instr ⟨.W64, .BL (.label l)⟩) s (.mk pc (pc + .ofNat z))
        (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).AllEnv env g post
      = post (s.setLr (pc + .ofNat z), (_root_.Executable.labels cenv).label l) g := by
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, MachineData.setRegOrZr, Effects.AllEnv, BitVec.ofInt_toInt_int64]
  rfl

/-- The cell of `BLR Xn` under the environment: `X30` gets the address behind
it, control goes to the address `Xn` held before, and the environment state
is unchanged. -/
theorem blr_cellEnv (r : RegOrZr .W64) (s : MachineData) (pc : Int64) (z : Nat) (g : env.State)
    (post : MachineState → env.State → Prop) :
    (@Directive.interp (_root_.Executable.labels cenv)
        (Directive.instr ⟨.W64, .BLR r⟩) s (.mk pc (pc + .ofNat z))
        (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).AllEnv env g post
      = post (s.setLr (pc + .ofNat z), Int64.ofBitVec (s.regs.getRegOrZr r)) g := by
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setRegOrZr, Effects.AllEnv,
    BitVec.ofInt_toInt_int64, Int64.ofInt_signed]
  rfl

/-- The fall-through address past one instruction cell. -/
private theorem after_instrEnv {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

/-- **Consequence for `TripleEnv`.** -/
theorem TripleEnv.mono {P P' : MachineData → env.State → Prop} {q : Program}
    {Q' : MachineData → env.State → Prop} {E' : Int64 → MachineData → env.State → Prop}
    (hP : ∀ s g, P s g → P' s g) (hQ : ∀ s g, Q' s g → Q s g) (hE : ∀ a s g, E' a s g → E a s g)
    (h : TripleEnv env P' q Q' E') : TripleEnv env P q Q E :=
  fun s g hp => Executable.wpEnv_mono hQ hE (h s g (hP s g hp))

/-- **The call rule in the environment wp** (`call_spec` over `wpEnv`). `P ra`
is the callee's assertion at its entry, for a run that returns to `ra`; the
callee's run is a `TripleEnv` premise, so it may consult the environment. The
conclusion rolls `P` back over the write of `X30`, for every address the
machine may write, at the caller's environment state (`BL` does not touch
it). The callee's exit at `ra` continues the caller's `wpEnv` of the cells
behind the call, at the environment state the callee left; an exit anywhere
else is the caller's own. -/
theorem MachineWP.call_specEnv {P : Int64 → MachineData → env.State → Prop} (l : Label)
    (body : Program) (hplace : cenv.sits ((_root_.Executable.labels cenv).label l) body)
    (hbody : ∀ ra : Int64,
      TripleEnv env (P ra) body (fun _ _ => False)
        (fun a s' g' => if a = ra then cenv.wpEnv env p Q E s' g' else E a s' g')) :
    TripleEnv env (fun s g => ∀ ra : Int64, P ra (s.setLr ra) g)
      (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p) Q E := by
  intro s g hP pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  refine .step _ _ ⟨_, _, _, hseg, Or.inr ?_⟩ (fun _ h => h)
  rw [bl_cellEnv]
  have hrun := hbody (pc + Int64.ofNat z) (s.setLr (pc + Int64.ofNat z)) g (hP (pc + Int64.ofNat z))
    ((_root_.Executable.labels cenv).label l) hplace
  refine eventually_trans _ _ _ _ hrun ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨-, hbot⟩ | hexit)
  · exact hbot.elim
  · dsimp only at hexit
    by_cases ha : a = pc + Int64.ofNat z
    · subst ha
      simp only [↓reduceIte] at hexit
      rw [after_instrEnv hseg]
      exact hexit _ hpl'
    · simp only [ha, ↓reduceIte] at hexit
      exact .done _ (Or.inr hexit)

/-- **The call rule with the callee's `Pre`/`Post`** (`fun_spec_from_label`
over `wpEnv`): the callee's `TripleEnv`, from the state `s.setLr ra` and the
environment state `g` its caller left, returns to `ra` with `Post s g`. The
tail and the channels stay open. -/
theorem MachineWP.fun_specEnv_from_label {Pre : MachineData → env.State → Prop}
    {Post : MachineData → env.State → MachineData → env.State → Prop} {l : Label} {body : Program}
    (hplace : cenv.sits ((_root_.Executable.labels cenv).label l) body)
    (hbody : ∀ (ra : Int64) (s : MachineData) (g : env.State),
      TripleEnv env (fun t g' => t = s.setLr ra ∧ g' = g ∧ Pre s g) body
        (fun _ _ => False) (fun a s' g' => a = ra ∧ Post s g s' g')) :
    ∀ ⦃p : Program⦄ ⦃Q : MachineData → env.State → Prop⦄ ⦃E : Int64 → MachineData → env.State → Prop⦄,
      TripleEnv env (fun s g => Pre s g ∧ ∀ s' g', Post s g s' g' → cenv.wpEnv env p Q E s' g')
        (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p) Q E := by
  intro p Q E s g ⟨hpre, hcont⟩
  refine MachineWP.call_specEnv
    (P := fun ra t h => ∃ s0 g0, t = s0.setLr ra ∧ h = g0 ∧ Pre s0 g0 ∧
      ∀ s1 g1, Post s0 g0 s1 g1 → cenv.wpEnv env p Q E s1 g1)
    l body hplace (fun ra => ?_) s g (fun ra => ⟨s, g, rfl, rfl, hpre, hcont⟩)
  rintro t h ⟨s0, g0, rfl, rfl, hpre0, hcont0⟩
  refine Executable.wpEnv_mono (fun _ _ h => h) ?_ (hbody ra s0 _ _ _ ⟨rfl, rfl, hpre0⟩)
  rintro a s1 g1 ⟨rfl, hpost⟩
  simp only [↓reduceIte]
  exact hcont0 s1 g1 hpost

/-- **`BL l` through the callee's `ProcSpecEnv`** (`call_proc_spec` over
`wpEnv`). -/
theorem MachineWP.call_proc_specEnv {α : Type} {Pre : α → Int64 → MachineData → env.State → Prop}
    {Post : α → Int64 → MachineData → env.State → MachineData → env.State → Prop} (x : α) (l : Label)
    (hproc : cenv.ProcSpecEnv env ((_root_.Executable.labels cenv).label l) Pre Post) :
    TripleEnv env (fun s g => ∀ ra : Int64, Pre x ra (s.setLr ra) g ∧
        ∀ s' g', Post x ra (s.setLr ra) g s' g' → cenv.wpEnv env p Q E s' g')
      (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p) Q E := by
  intro s g hP pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  refine .step _ _ ⟨_, _, _, hseg, Or.inr ?_⟩ (fun _ h => h)
  rw [bl_cellEnv]
  refine eventually_trans _ _ _ _
    (hproc x (pc + Int64.ofNat z) (s.setLr (pc + Int64.ofNat z)) g (hP _).1) ?_
  rintro ⟨⟨s', a⟩, g'⟩ ⟨rfl, hpost⟩
  rw [after_instrEnv hseg]
  exact (hP _).2 s' g' hpost _ hpl'

/-- **`BLR Xn` through the callee's `ProcSpecEnv`** at the address `f` the
register holds (`blr_proc_spec` over `wpEnv`); the target is read before the
write of `X30`. -/
theorem MachineWP.blr_proc_specEnv {α : Type} {Pre : α → Int64 → MachineData → env.State → Prop}
    {Post : α → Int64 → MachineData → env.State → MachineData → env.State → Prop} (x : α)
    (r : RegOrZr .W64) (f : Int64) (hproc : cenv.ProcSpecEnv env f Pre Post) :
    TripleEnv env (fun s g => Int64.ofBitVec (s.regs.getRegOrZr r) = f ∧ ∀ ra : Int64,
        Pre x ra (s.setLr ra) g ∧ ∀ s' g', Post x ra (s.setLr ra) g s' g' → cenv.wpEnv env p Q E s' g')
      (Directive.instr ⟨.W64, .BLR r⟩ :: p) Q E := by
  intro s g ⟨hf, hP⟩ pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  refine .step _ _ ⟨_, _, _, hseg, Or.inr ?_⟩ (fun _ h => h)
  rw [blr_cellEnv, hf]
  refine eventually_trans _ _ _ _
    (hproc x (pc + Int64.ofNat z) (s.setLr (pc + Int64.ofNat z)) g (hP _).1) ?_
  rintro ⟨⟨s', a⟩, g'⟩ ⟨rfl, hpost⟩
  rw [after_instrEnv hseg]
  exact (hP _).2 s' g' hpost _ hpl'

end Rules
