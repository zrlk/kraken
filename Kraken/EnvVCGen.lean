/-
`vcgen` over the environment-aware wp, x64 (design note
`Kraken/Promising/EnvWP.md` §8).

`vcgen` finds a rule by the program alone (a discrimination tree over the
program term; the candidates are tried by priority, and a rule whose instance
arguments cannot be synthesised gives way). `Program` already carries
`MachineWP.instWP`, whose predicates are `MachineData → Prop`, so the
environment wp gets a program type of its own:

- `EnvProgram env`: a `Program` run in the environment `env`, with the `WP`
  instance `MachineWP.instWPEnv` (predicates `MachineData → env.State → Prop`,
  `wp := cenv.wpEnv env`). Its triple is `TripleEnv` (`TripleEnv.of_triple`,
  `TripleEnv.triple`).
- **The generic rule** `env_lift_spec` (`@[spec low]`, keyed on `⟨d :: p⟩`,
  instance argument `[env.Skips]`): the precondition is the `Program` wp of
  `[d]` with the tail's environment wp, at the same environment state, as its
  postcondition. `vcgen` steps `[d]` by the existing `MachineWP` rule for `d`
  and comes back to the tail by `MachineWP.nil_spec`. So every `MachineWP` rule
  (registers, flags, branches, mapped memory, stack) serves the environment wp
  unchanged, and the environment state passes through untouched.
- The shared-location rules of `Kraken/EnvWPRules.lean`, restated over
  `EnvProgram` (`*_shared_spec`, derived from the `TripleEnv` theorems):
  * the atomic read-modify-writes (`xchg`, `lock cmpxchg`, `lock xadd`,
    `lock op` with two operands and with one (`lock_un_shared_spec`: `inc`,
    `dec`, `neg`, `not`), `lock cmpxchg16b`) are `@[spec]` at the default
    priority, above
    the generic rule. On a location in `dmem` the generic rule is the one
    wanted: erase the shared rule for that call (`vcgen [-xchg_shared_spec]`);
  * the fences are `@[spec 50]`, below the generic rule: with `Skips` the
    generic rule steps them as no-ops, and they fire only where no `Skips`
    instance exists;
  * the vector moves (`movdqa`, `movapd`, `movaps` (also with an index
    register), `movdqu`, `movups`; the VEX `vmovdqa`/`vmovapd`/`vmovdqu` of
    every width and `vmovaps`/`vmovups` with an index register), the packed
    arithmetic with a memory source (`mulps`, `xorps`, `vmulps`,
    `vfmadd231ps`) and the other plain accesses (`movb` loads and stores, `movslq (%b,%i,s)`,
    `cmpl $i, d(%b)`) are not registered: pass them to the `vcgen` call that
    needs them (`vcgen [mov8_store_imm_shared_spec]`). The vector rules leave
    the environment's side as `SharedEnv.AvxLoad`/`AvxStore`/`LoadPieces`/
    `StorePieces` around the tail's wp; `vcgen_env [rules]` (end of file)
    goes through them piece by piece and on into the tail.
- **Combined rules** for the plain general-purpose moves (`movq`/`movl` to and
  from `d(%b)`, `*_env_spec`, `@[spec]`): one rule per instruction for both
  cases, the location in `dmem` or shared. The outcome is one disjunction
  (`dmem` read or written, environment state unchanged; or the environment
  accessed, `dmem` unchanged) and one continuation, so `vcgen` does not branch
  and a program may mix mapped and shared moves of the same shape. They need
  no `Skips`.
  The stack and the indirect jump have combined rules of the same form
  (`push_reg_env_spec`, `pop_reg_env_spec`, `ret_env_spec`,
  `jmp_mem_base_disp_env_spec`, `@[spec]`; `ret` and `jmp *d(%b)` end in the
  exit `E` at the loaded address), and `call_env_spec` is `call_spec` over the
  environment wp (not `@[spec]`, the callee's run as its premise).
  `call_proc_env_spec` (and `_at`, for `vcgen [hc]`) is `call_proc_spec`
  over the environment wp: a call through the callee's
  `Executable.ProcSpecEnv`.

A program defined by name must be unfolded first (`unfold prog; vcgen`):
`vcgen [prog]` unfolds a program at the head of the goal, and here the head is
`EnvProgram.mk`.
-/
import Kraken.EnvWPRules

open Kraken
open Std.WP
open Lean.Order

/-- A `Program` run in the environment `env`: the program type of the
environment wp's `WP` instance (`MachineWP.instWPEnv`). -/
structure EnvProgram (env : SharedEnv) where
  prog : Program

namespace MachineWP

/-- A triple on an `EnvProgram` is the environment wp of the ambient code. -/
scoped instance instWPEnv [CodeEnv] (env : SharedEnv) :
    WP (EnvProgram env) Unit (MachineData → env.State → Prop)
      (Int64 → MachineData → env.State → Prop) where
  wpTrans q := ⟨fun Q E s g => cenv.wpEnv env q.prog (Q ()) E s g⟩
  wp_trans_monotone _ _ _ _ _ hE hQ := fun _ _ h =>
    Executable.wpEnv_mono (fun s' g' => hQ () s' g') hE h

/-- Unfold an `EnvProgram` triple's wp into the environment wp. -/
theorem wpEnv_eq [CodeEnv] {env : SharedEnv} (q : EnvProgram env)
    (Q : Unit → MachineData → env.State → Prop) (E : Int64 → MachineData → env.State → Prop)
    (s : MachineData) (g : env.State) :
    WP.wp q Q E s g = cenv.wpEnv env q.prog (Q ()) E s g := rfl

/-- A triple on `⟨q⟩` is a `TripleEnv` on `q`. -/
theorem TripleEnv.of_triple [CodeEnv] {env : SharedEnv} {P : MachineData → env.State → Prop}
    {q : Program} {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    (h : ⦃ P ⦄ (⟨q⟩ : EnvProgram env) ⦃ fun _ => Q; E ⦄) : TripleEnv env P q Q E :=
  fun s g hp => h.le_wp s g hp

/-- A `TripleEnv` on `q` is a triple on `⟨q⟩`, from any stronger
precondition. -/
theorem TripleEnv.triple [CodeEnv] {env : SharedEnv} {P P' : MachineData → env.State → Prop}
    {q : Program} {Q : Unit → MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop}
    (hP : ∀ s g, P s g → P' s g) (h : TripleEnv env P' q (Q ()) E) :
    ⦃ P ⦄ (⟨q⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g hp => h s g (hP s g hp)

end MachineWP

/-! ## The structural rules and the generic rule -/

section Specs

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

@[spec] theorem MachineWP.env_nil_spec :
    ⦃ fun s g => Q () s g ⦄ (⟨[]⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => fun _ _ => Eventually.done _ (Or.inl ⟨rfl, h⟩)

/-- **The generic rule.** Any cell, in an environment whose fences skip: run
it by the `MachineWP` rules (the `Program` wp of `[d]`), with the tail's
environment wp at the same environment state as its postcondition. Lifting
(`Executable.wpEnv_of_wp`) with the invariant `(· = g)`. -/
@[spec low] theorem MachineWP.env_lift_spec [env.Skips] (d : Directive) :
    ⦃ fun s g => WP.wp ([d] : Program) (fun _ s' => WP.wp (⟨p⟩ : EnvProgram env) Q E s' g)
        (fun a s' => E a s' g) s ⦄
      (⟨d :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    apply Executable.wpEnv_cons
    have hI := (SharedEnv.Skips.fencesSkip (env := env)).fenceInv_eq g
    exact Executable.wpEnv_mono (fun _ _ ⟨h1, h2⟩ => h2 ▸ h1) (fun _ _ _ ⟨h1, h2⟩ => h2 ▸ h1)
      (Executable.wpEnv_of_wp (Q := fun s' => cenv.wpEnv env p (Q ()) E s' g)
        (E := fun a s' => E a s' g) hI h g rfl)

end Specs

/-! ## The shared-location rules over `EnvProgram`

Each is its `Kraken/EnvWPRules.lean` theorem with `⊓` for `∧` and the tail
as an `EnvProgram` wp, so that `vcgen` continues into it. -/

section SharedSpecs

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- `xchgq %r, d(%b)` on a shared location (`xchg_shared`). -/
@[spec] theorem MachineWP.xchg_shared_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let acc := SharedAccess.rmw .acqRel a 8 (rmwOp128 .W64 (fun _ => some (s.regs.get64 r)))
        (Mem.loadInt s.dmem a 8 = none) ⊓ env.ok acc g ⊓
          (∀ old g', env.step acc g old g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.set64 r (old.setWidth 64) } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.xchg (.low r .W64) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (xchg_shared env r b d p (Q ()) E)

/-- `lock cmpxchgq %r, d(%b)` on a shared location (`lock_cmpxchg_shared`). -/
@[spec] theorem MachineWP.lock_cmpxchg_shared_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let acc := s.regs.get64 .rax
        let op := rmwOp128 .W64 (fun x => if x == acc then some (s.regs.get64 r) else none)
        (Mem.loadInt s.dmem a 8 = none) ⊓ env.ok (.rmw .acqRel a 8 op) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 8 op) g v g' →
            let old := v.setWidth 64
            let dv := acc - old
            let status := StatusFlags.from_result dv
              { cf := dv.unsigned != acc.unsigned - old.unsigned,
                af := (dv.take 4).unsigned != (acc.take 4).unsigned - (old.take 4).unsigned,
                of := dv.signed != acc.signed - old.signed }
            (old = acc → WP.wp (⟨p⟩ : EnvProgram env) Q E { s with status } g')
            ⊓ (old ≠ acc → WP.wp (⟨p⟩ : EnvProgram env) Q E
                { s with regs := s.regs.set64 .rax old, status } g')) ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.cmpxchg true (.mem ⟨some (.reg b), none, .int64 d⟩) (.low r .W64))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (lock_cmpxchg_shared env b d r)

/-- `lock xaddq %r, d(%b)` on a shared location (`lock_xadd_shared`). -/
@[spec] theorem MachineWP.lock_xadd_shared_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let src := s.regs.get64 r
        let op := rmwOp128 .W64 (fun x => some (x + src))
        (Mem.loadInt s.dmem a 8 = none) ⊓ env.ok (.rmw .acqRel a 8 op) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 8 op) g v g' →
            let old := v.setWidth 64
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with
              regs := s.regs.set64 r old,
              status := LockBinOp.add.status old src (old + src) false } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.xadd true (.mem ⟨some (.reg b), none, .int64 d⟩) (.low r .W64))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (lock_xadd_shared env b d r)

/-- `lock op $i, d(%b)` on a shared location (`lock_bin_imm_shared`). -/
@[spec] theorem MachineWP.lock_bin_imm_shared_spec (op : LockBinOp) (b : Reg64) (d i : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let src := BitVec.setWidth 64 i.toBitVec
        let f := rmwOp128 .W64 (fun x => some (op.eval x src))
        (Mem.loadInt s.dmem a 8 = none) ⊓ env.ok (.rmw .acqRel a 8 f) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 8 f) g v g' → ∀ af : Bool,
            let old := v.setWidth 64
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with status := op.status old src (op.eval old src) af } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.lockBin op ⟨some (.reg b), none, .int64 d⟩ (.imm (.int64 i)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (lock_bin_imm_shared env op b d i)

/-- `lock op %r, d(%b)` on a shared location (`lock_bin_reg_shared`). -/
@[spec] theorem MachineWP.lock_bin_reg_shared_spec (op : LockBinOp) (b : Reg64) (d : Int64)
    (r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let src := s.regs.get64 r
        let f := rmwOp128 .W64 (fun x => some (op.eval x src))
        (Mem.loadInt s.dmem a 8 = none) ⊓ env.ok (.rmw .acqRel a 8 f) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 8 f) g v g' → ∀ af : Bool,
            let old := v.setWidth 64
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with status := op.status old src (op.eval old src) af } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.lockBin op ⟨some (.reg b), none, .int64 d⟩ (.regOrMem (.reg (.low r .W64))))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (lock_bin_reg_shared env op b d r)

/-- `lock op d(%b)` (`inc dec neg not`) on a shared location (`lock_un_shared`). -/
@[spec] theorem MachineWP.lock_un_shared_spec (op : LockUnOp) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let f := rmwOp128 .W64 (fun x => some (op.eval x))
        (Mem.loadInt s.dmem a 8 = none) ⊓ env.ok (.rmw .acqRel a 8 f) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 8 f) g v g' →
            let old := v.setWidth 64
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with status := op.status old (op.eval old) s.status } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64 (.lockUn op ⟨some (.reg b), none, .int64 d⟩)) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (lock_un_shared env op b d)

/-- `lock cmpxchg16b d(%b)` on a shared location (`lock_cmpxchg16b_shared`). -/
@[spec] theorem MachineWP.lock_cmpxchg16b_shared_spec (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let acc := s.regs.get64 .rdx ++ s.regs.get64 .rax
        let op := fun old : BitVec 128 =>
          if old == acc then some (s.regs.get64 .rcx ++ s.regs.get64 .rbx) else none
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓ env.ok (.rmw .acqRel a 16 op) g ⊓
          (∀ old g', env.step (.rmw .acqRel a 16 op) g old g' →
            (old = acc → WP.wp (⟨p⟩ : EnvProgram env) Q E
                { s with status := { s.status with zf := true } } g')
            ⊓ (old ≠ acc → WP.wp (⟨p⟩ : EnvProgram env) Q E
                { s with
                    regs := (s.regs.set64 .rax (old.extractLsb' 0 64)).set64 .rdx (old.extractLsb' 64 64),
                    status := { s.status with zf := false } } g')) ⦄
      (⟨Directive.instr (.avx .W64 .W128 (.cmpxchg16b true ⟨some (.reg b), none, .int64 d⟩)) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (lock_cmpxchg16b_shared env b d)

/-- `mfence` asking the environment (`mfence_shared`). Below the generic rule:
it fires only where `env` has no `Skips` instance. -/
@[spec 50] theorem MachineWP.mfence_shared_spec (asz osz : Width) :
    ⦃ fun s g => env.ok (.fence .sy) g ⊓
        (∀ g', env.step (.fence .sy) g () g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.regular asz osz .mfence) :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h)
    (mfence_shared env asz osz)

/-- `lfence` asking the environment (`lfence_shared`), as `mfence_shared_spec`. -/
@[spec 50] theorem MachineWP.lfence_shared_spec (asz osz : Width) :
    ⦃ fun s g => env.ok (.fence .ld) g ⊓
        (∀ g', env.step (.fence .ld) g () g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.regular asz osz .lfence) :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h)
    (lfence_shared env asz osz)

/-- `sfence` asking the environment (`sfence_shared`), as `mfence_shared_spec`. -/
@[spec 50] theorem MachineWP.sfence_shared_spec (asz osz : Width) :
    ⦃ fun s g => env.ok (.fence .st) g ⊓
        (∀ g', env.step (.fence .st) g () g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.regular asz osz .sfence) :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h)
    (sfence_shared env asz osz)

/-! The vector moves: not `@[spec]` (a location in `dmem` is the common case
and is the generic rule's); pass them to the `vcgen` call that accesses a
shared location with one. -/

/-- `movdqa d(%b), %xmm` on a shared location (`movdqa_load_shared`). -/
theorem MachineWP.movdqa_load_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.load .plain false a 16) g ⊓
          (∀ v g', env.step (.load .plain false a 16) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movdqa (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movdqa_load_shared env x b d)

/-- `movdqa %xmm, d(%b)` on a shared location (`movdqa_store_shared`). -/
theorem MachineWP.movdqa_store_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := s.zmms.get (.xmm x)
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.store .plain false a 16 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 16 v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movdqa (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movdqa_store_shared env x b d)

/-- `movapd d(%b), %xmm` on a shared location (`movapd_load_shared`). -/
theorem MachineWP.movapd_load_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.load .plain false a 16) g ⊓
          (∀ v g', env.step (.load .plain false a 16) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movapd (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movapd_load_shared env x b d)

/-- `movapd %xmm, d(%b)` on a shared location (`movapd_store_shared`). -/
theorem MachineWP.movapd_store_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := s.zmms.get (.xmm x)
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.store .plain false a 16 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 16 v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movapd (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movapd_store_shared env x b d)

/-- `movdqu d(%b), %xmm` on a shared location (`movdqu_load_shared`). -/
theorem MachineWP.movdqu_load_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a 16 = none) ⊓
          env.LoadPieces a 2 g (fun vs g' => WP.wp (⟨p⟩ : EnvProgram env) Q E
            { s with zmms := s.zmms.setLegacy (.xmm x) (ofPieces 128 vs) } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movdqu (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h)
    (movdqu_load_shared env x b d)

/-- `movdqu %xmm, d(%b)` on a shared location (`movdqu_store_shared`). -/
theorem MachineWP.movdqu_store_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a 16 = none) ⊓
          env.StorePieces a (toPieces (s.zmms.get (.xmm x)) 2) g
            (fun g' => WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movdqu (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h)
    (movdqu_store_shared env x b d)

/-- `movups d(%b), %xmm` on a shared location (`movups_load_shared`). -/
theorem MachineWP.movups_load_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a 16 = none) ⊓
          env.LoadPieces a 2 g (fun vs g' => WP.wp (⟨p⟩ : EnvProgram env) Q E
            { s with zmms := s.zmms.setLegacy (.xmm x) (ofPieces 128 vs) } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movups (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h)
    (movups_load_shared env x b d)

/-- `movups %xmm, d(%b)` on a shared location (`movups_store_shared`). -/
theorem MachineWP.movups_store_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a 16 = none) ⊓
          env.StorePieces a (toPieces (s.zmms.get (.xmm x)) 2) g
            (fun g' => WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movups (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h)
    (movups_store_shared env x b d)

/-- `movaps d(%b), %xmm` on a shared location (`movaps_load_shared`). -/
theorem MachineWP.movaps_load_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.load .plain false a 16) g ⊓
          (∀ v g', env.step (.load .plain false a 16) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movaps_load_shared env x b d)

/-- `movaps %xmm, d(%b)` on a shared location (`movaps_store_shared`). -/
theorem MachineWP.movaps_store_shared_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := s.zmms.get (.xmm x)
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.store .plain false a 16 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 16 v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movaps_store_shared env x b d)

/-! The other plain accesses with a `MachineWP` rule: not `@[spec]`, as
the vector moves; pass them to the `vcgen` call that needs them. -/

/-- `movb d(%b), %r8` on a shared location (`mov8_load_shared`). -/
theorem MachineWP.mov8_load_shared_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a 1 = none) ⊓ env.ok (.load .plain false a 1) g ⊓
          (∀ v g', env.step (.load .plain false a 1) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (v.setWidth 8)) } g') ⦄
      (⟨Directive.instr (.regular .W64 .W8
          (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (mov8_load_shared env r b d)

/-- `movb $i, d(%b)` on a shared location (`mov8_store_imm_shared`). -/
theorem MachineWP.mov8_store_imm_shared_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := (i.toBitVec.truncate 8).setWidth 128
        (Mem.loadInt s.dmem a 1 = none) ⊓ env.ok (.store .plain false a 1 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 1 v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (mov8_store_imm_shared env b d i)

/-- `movb %r8, d(%b)` on a shared location (`mov8_store_reg_shared`). -/
theorem MachineWP.mov8_store_reg_shared_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := ((s.regs.get64 r).setWidth 8).setWidth 128
        (Mem.loadInt s.dmem a 1 = none) ⊓ env.ok (.store .plain false a 1 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 1 v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (mov8_store_reg_shared env b d r)

/-- `movslq (%b,%i,s), %r` on a shared location (`movsxd_load_sib_shared`). -/
theorem MachineWP.movsxd_load_sib_shared_spec (r b i : Reg64) (c : Width) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i * BitVec.ofNat 64 c.bytes
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok (.load .plain false a 4) g ⊓
          (∀ v g', env.step (.load .plain false a 4) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.set64 r ((v.setWidth 32).signExtend 64) } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.movsx (w' := .W32) (.reg (.low r .W64))
            (.mem ⟨some (.reg b), some ⟨i, c⟩, .int64 0⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (movsxd_load_sib_shared env r b i c)

/-- `cmpl $i, d(%b)` on a shared location (`cmp32_mem_imm_shared`). -/
theorem MachineWP.cmp32_mem_imm_shared_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s g =>
        let addr := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem addr 4 = none) ⊓ env.ok (.load .plain false addr 4) g ⊓
          (∀ m g', env.step (.load .plain false addr 4) g m g' →
            let a := m.setWidth 32
            let c := i.toBitVec.truncate 32
            let v := a - c
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned - c.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned - (c.take 4).unsigned,
                  of := v.signed != a.signed - c.signed } } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (cmp32_mem_imm_shared env b d i)

/-! The VEX moves and the SIB and memory-source forms: not `@[spec]`, as
the SSE moves; pass them to the `vcgen` call that accesses a shared location
with one. -/

/-- `vmovdqa d(%b), %xmm/%ymm/%zmm` on a shared location (`vmovdqa_load_shared`). -/
theorem MachineWP.vmovdqa_load_shared_spec {w : AvxWidth} (x : AvxReg w) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (isAligned w.bytes a = true) ⊓
          (Mem.loadInt s.dmem a w.bytes = none) ⊓
          env.AvxLoad (w == .W128) a w g (fun v g' =>
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.set x v } g') ⦄
      (⟨Directive.instr (.avx .W64 w
          (.vmovdqa (.avx x) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (vmovdqa_load_shared env x b d)

/-- `vmovapd d(%b), %xmm/%ymm/%zmm` on a shared location (`vmovapd_load_shared`). -/
theorem MachineWP.vmovapd_load_shared_spec {w : AvxWidth} (x : AvxReg w) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (isAligned w.bytes a = true) ⊓
          (Mem.loadInt s.dmem a w.bytes = none) ⊓
          env.AvxLoad (w == .W128) a w g (fun v g' =>
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.set x v } g') ⦄
      (⟨Directive.instr (.avx .W64 w
          (.vmovapd (.avx x) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (vmovapd_load_shared env x b d)

/-- `vmovdqu d(%b), %xmm/%ymm/%zmm` on a shared location (`vmovdqu_load_shared`). -/
theorem MachineWP.vmovdqu_load_shared_spec {w : AvxWidth} (x : AvxReg w) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a w.bytes = none) ⊓
          env.AvxLoad false a w g (fun v g' =>
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.set x v } g') ⦄
      (⟨Directive.instr (.avx .W64 w
          (.vmovdqu (.avx x) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1, h.2⟩)
    (vmovdqu_load_shared env x b d)

/-- `vmovdqa %xmm/%ymm/%zmm, d(%b)` on a shared location (`vmovdqa_store_shared`). -/
theorem MachineWP.vmovdqa_store_shared_spec {w : AvxWidth} (x : AvxReg w) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (isAligned w.bytes a = true) ⊓
          (Mem.loadInt s.dmem a w.bytes = none) ⊓
          env.AvxStore (w == .W128) a (s.zmms.get x) g (fun g' => WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 w
          (.vmovdqa (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx x))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (vmovdqa_store_shared env x b d)

/-- `vmovapd %xmm/%ymm/%zmm, d(%b)` on a shared location (`vmovapd_store_shared`). -/
theorem MachineWP.vmovapd_store_shared_spec {w : AvxWidth} (x : AvxReg w) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (isAligned w.bytes a = true) ⊓
          (Mem.loadInt s.dmem a w.bytes = none) ⊓
          env.AvxStore (w == .W128) a (s.zmms.get x) g (fun g' => WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 w
          (.vmovapd (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx x))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (vmovapd_store_shared env x b d)

/-- `vmovdqu %xmm/%ymm/%zmm, d(%b)` on a shared location (`vmovdqu_store_shared`). -/
theorem MachineWP.vmovdqu_store_shared_spec {w : AvxWidth} (x : AvxReg w) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a w.bytes = none) ⊓
          env.AvxStore false a (s.zmms.get x) g (fun g' => WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 w
          (.vmovdqu (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx x))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1, h.2⟩)
    (vmovdqu_store_shared env x b d)

/-- `movaps (%b,%i,1), %xmm` on a shared location (`movaps_load_sib1_shared`). -/
theorem MachineWP.movaps_load_sib1_shared_spec (x : RegMm) (b i : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i
        (isAligned 16 a = true) ⊓
          (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.load .plain false a 16) g ⊓
          (∀ v g', env.step (.load .plain false a 16) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 0⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movaps_load_sib1_shared env x b i)

/-- `movaps %xmm, (%b,%i,1)` on a shared location (`movaps_store_sib1_shared`). -/
theorem MachineWP.movaps_store_sib1_shared_spec (x : RegMm) (b i : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i
        let v := s.zmms.get (.xmm x)
        (isAligned 16 a = true) ⊓
          (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.store .plain false a 16 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 16 v) g ok g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 0⟩) (.avx (.xmm x)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movaps_store_sib1_shared env x b i)

/-- `movaps d(%b,%i,1), %xmm` on a shared location (`movaps_load_sib1_disp_shared`). -/
theorem MachineWP.movaps_load_sib1_disp_shared_spec (x : RegMm) (b i : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (isAligned 16 a = true) ⊓
          (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.load .plain false a 16) g ⊓
          (∀ v g', env.step (.load .plain false a 16) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movaps_load_sib1_disp_shared env x b i d)

/-- `movaps %xmm, d(%b,%i,1)` on a shared location (`movaps_store_sib1_disp_shared`). -/
theorem MachineWP.movaps_store_sib1_disp_shared_spec (x : RegMm) (b i : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        let v := s.zmms.get (.xmm x)
        (isAligned 16 a = true) ⊓
          (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.store .plain false a 16 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 16 v) g ok g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.avx (.xmm x)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (movaps_store_sib1_disp_shared env x b i d)

/-- `vmovaps d(%b,%i,1), %xmm` on a shared location (`vmovaps_load_sib1_disp_shared`). -/
theorem MachineWP.vmovaps_load_sib1_disp_shared_spec (x : AvxReg .W128) (b i : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (isAligned 16 a = true) ⊓
          (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.load .plain false a 16) g ⊓
          (∀ v g', env.step (.load .plain false a 16) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.set x v } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.vmovaps (.avx x) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (vmovaps_load_sib1_disp_shared env x b i d)

/-- `vmovups d(%b,%i,1), %ymm` on a shared location (`vmovups_load_sib1_disp_shared`). -/
theorem MachineWP.vmovups_load_sib1_disp_shared_spec (y : AvxReg .W256) (b i : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (Mem.loadInt s.dmem a 32 = none) ⊓
          env.LoadPieces a 4 g (fun vs g' =>
            let m := ofPieces 256 vs
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.set y m } g') ⦄
      (⟨Directive.instr (.avx .W64 .W256
          (.vmovups (.avx y) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1, h.2⟩)
    (vmovups_load_sib1_disp_shared env y b i d)

/-- `mulps d(%b,%i,1), %xmm` on a shared location (`mulps_load_sib1_disp_shared`). -/
theorem MachineWP.mulps_load_sib1_disp_shared_spec (x : RegMm) (b i : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (isAligned 16 a = true) ⊓
          (Mem.loadInt s.dmem a 16 = none) ⊓
          env.LoadPieces a 2 g (fun vs g' =>
            let m := ofPieces 128 vs
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := (s.zmms.setLegacy (.xmm x)
              (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get (.xmm x)) m)) } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.mulps (.avx (.xmm x)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (mulps_load_sib1_disp_shared env x b i d)

/-- `xorps sym(%rip), %xmm` on a shared location (`xorps_load_rip_shared`). -/
theorem MachineWP.xorps_load_rip_shared_spec (x : RegMm) (l : Label) :
    ⦃ fun s g =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        (isAligned 16 a = true) ⊓
          (Mem.loadInt s.dmem a 16 = none) ⊓
          env.LoadPieces a 2 g (fun vs g' =>
            let m := ofPieces 128 vs
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.setLegacy (.xmm x) (s.zmms.get (.xmm x) ^^^ m) } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.xorps (.avx (.xmm x))
            (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (xorps_load_rip_shared env x l)

/-- `vmulps d(%b,%i,1), %xmm1, %xmm0` on a shared location (`vmulps_load_sib1_disp_shared`). -/
theorem MachineWP.vmulps_load_sib1_disp_shared_spec (dst src1 : AvxReg .W128) (b i : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (Mem.loadInt s.dmem a 16 = none) ⊓
          env.LoadPieces a 2 g (fun vs g' =>
            let m := ofPieces 128 vs
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get src1) m) } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.vmulps dst src1 (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1, h.2⟩)
    (vmulps_load_sib1_disp_shared env dst src1 b i d)

/-- `vfmadd231ps d(%b,%i,1), %ymm1, %ymm0` on a shared location (`vfmadd231ps_load_sib1_disp_shared`). -/
theorem MachineWP.vfmadd231ps_load_sib1_disp_shared_spec (dst src1 : AvxReg .W256) (b i : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (Mem.loadInt s.dmem a 32 = none) ⊓
          env.LoadPieces a 4 g (fun vs g' =>
            let m := ofPieces 256 vs
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := (s.zmms.set dst
              (BitVec.packedTernOp 32 BitVec.f32fma (s.zmms.get src1) m (s.zmms.get dst))) } g') ⦄
      (⟨Directive.instr (.avx .W64 .W256
          (.vfmadd231ps dst src1 (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1, h.2⟩)
    (vfmadd231ps_load_sib1_disp_shared env dst src1 b i d)

end SharedSpecs

/-! ## Combined rules for the plain general-purpose moves

Mapped or shared, in one rule: the location's bytes are in `dmem`
(`(Mem.loadInt s.dmem a n).isSome`), and the move reads or writes them with
the environment state unchanged; or they are not (`= none`), and the move is a
plain access the environment must permit, with `dmem` unchanged. The two
outcomes are one disjunction in front of one continuation, so `vcgen` does
not branch at the move. Proved from the interpreter directly, for every
environment. -/

section CombinedSpecs

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

set_option hygiene false in
/-- One cell: place it, step it, and leave the `AllEnv` goal of its
fall-through tree, with the placement of the tail as `hpl'`. -/
local macro "env_step" : tactic =>
  `(tactic| (
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩))

/-- `movq %r, d(%b)`, mapped or shared. -/
@[spec] theorem MachineWP.mov_store_env_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := (s.regs.get64 r).setWidth 128
        (Mem.loadInt s.dmem a 8 = none → env.ok (.store .plain false a 8 v) g) ⊓
          (∀ m g',
            ((Mem.loadInt s.dmem a 8).isSome = true ∧
                m = Mem.storeInt s.dmem a 8 (s.regs.get64 r).toInt ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧ m = s.dmem ∧
                ∃ ok, env.step (.store .plain false a 8 v) g ok g') →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with dmem := m } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (s.regs.get64 b + d.toBitVec) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun ok g' hs => hk s.dmem g' (.inr ⟨hl, rfl, ok, hs⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨by rw [hl]; rfl, rfl, rfl⟩) _ hpl'

/-- `movl %r32, d(%b)`, mapped or shared. -/
@[spec] theorem MachineWP.mov32_store_env_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := ((s.regs.get64 r).setWidth 32).setWidth 128
        (Mem.loadInt s.dmem a 4 = none → env.ok (.store .plain false a 4 v) g) ⊓
          (∀ m g',
            ((Mem.loadInt s.dmem a 4).isSome = true ∧
                m = Mem.storeInt s.dmem a 4 ((s.regs.get64 r).setWidth 32).toInt ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 4 = none ∧ m = s.dmem ∧
                ∃ ok, env.step (.store .plain false a 4 v) g ok g') →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with dmem := m } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (s.regs.get64 b + d.toBitVec) 4 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun ok g' hs => hk s.dmem g' (.inr ⟨hl, rfl, ok, hs⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨by rw [hl]; rfl, rfl, rfl⟩) _ hpl'

/-- `movq d(%b), %r`, mapped or shared: the register gets the `dmem` bytes, or
any value the environment allows. -/
@[spec] theorem MachineWP.mov_load_env_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a 8 = none → env.ok (.load .plain false a 8) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧
                ∃ v, env.step (.load .plain false a 8) g v g' ∧ x = v.setWidth 64) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.set64 r x } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (s.regs.get64 b + d.toBitVec) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.set_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun v g' hs => hk _ g' (.inr ⟨hl, v, hs, rfl⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.set_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨w, hl, rfl, rfl⟩) _ hpl'

/-- `movl d(%b), %r32`, mapped or shared: the register gets the 4 bytes
zero-extended. -/
@[spec] theorem MachineWP.mov32_load_env_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a 4 = none → env.ok (.load .plain false a 4) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem a 4 = some v ∧ x = BitVec.ofInt 32 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 4 = none ∧
                ∃ v, env.step (.load .plain false a 4) g v g' ∧ x = v.setWidth 32) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.set64 r (x.setWidth 64) } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (s.regs.get64 b + d.toBitVec) 4 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.set_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun v g' hs => hk _ g' (.inr ⟨hl, v, hs, rfl⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.set_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨w, hl, rfl, rfl⟩) _ hpl'

/-! ### The stack and the indirect jump

`push`/`pop` of a register, `ret` and `jmp *d(%b)`, mapped or shared, in the
same form; `ret` and `jmp *d(%b)` end in the exit `E` at the loaded address.
`call_env_spec` is `call_spec` over the environment wp, with the callee's
run as its premise (not `@[spec]`). -/

set_option hygiene false in
/-- One jumping cell: place it and leave the `AllEnv` goal of its jump tree. -/
local macro "env_step_jmp" : tactic =>
  `(tactic| (
    intro pc hpl
    obtain ⟨z, rest, hseg, -⟩ := hpl
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inr ?_⟩))

/-- `push %r`, mapped or shared: the 8 bytes below the stack pointer get the
register, in `dmem` or by a plain store the environment must permit, and the
stack pointer drops by 8. -/
@[spec] theorem MachineWP.push_reg_env_spec (asz : Width) (r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 .rsp - Width.W64.bytesv
        let v := (s.regs.get64 r).setWidth 128
        (Mem.loadInt s.dmem a 8 = none → env.ok (.store .plain false a 8 v) g) ⊓
          (∀ m g',
            ((Mem.loadInt s.dmem a 8).isSome = true ∧
                m = Mem.storeInt s.dmem a 8 (s.regs.get64 r).toInt ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧ m = s.dmem ∧
                ∃ ok, env.step (.store .plain false a 8 v) g ok g') →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.set64 .rsp a, dmem := m } g') ⦄
      (⟨Directive.instr (.regular asz .W64 (.push (.regOrMem (.reg (.low r .W64))))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.store, Reg64s.get_low64, Width.bytes, hl, Effects.AllEnv]
      exact ⟨hok hl, fun ok g' hs => hk s.dmem g' (.inr ⟨hl, rfl, ok, hs⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.store, Reg64s.get_low64, Width.bytes, hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨by rw [hl]; rfl, rfl, rfl⟩) _ hpl'

/-- `pop %r`, mapped or shared: the register gets the 8 bytes at the stack
pointer, from `dmem` or any value the environment allows, and the stack
pointer rises by 8. -/
@[spec] theorem MachineWP.pop_reg_env_spec (asz : Width) (r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 .rsp
        (Mem.loadInt s.dmem a 8 = none → env.ok (.load .plain false a 8) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧
                ∃ v, env.step (.load .plain false a 8) g v g' ∧ x = v.setWidth 64) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := (s.regs.set64 .rsp (a + Width.W64.bytesv)).set64 r x } g') ⦄
      (⟨Directive.instr (.regular asz .W64 (.pop (.reg (.low r .W64)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.set,
        MachineData.setReg, MachineData.load, Reg64s.set_low64, Width.bytes, hl, Effects.AllEnv]
      exact ⟨hok hl, fun v g' hs => hk _ g' (.inr ⟨hl, v, hs, rfl⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.set,
        MachineData.setReg, MachineData.load, Reg64s.set_low64, Width.bytes, hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨w, hl, rfl, rfl⟩) _ hpl'

/-- `ret`, mapped or shared: the run exits to the address the 8 bytes at the
stack pointer hold, from `dmem` or any value the environment allows, with the
stack pointer raised by 8. -/
@[spec] theorem MachineWP.ret_env_spec (asz osz : Width) :
    ⦃ fun s g =>
        let a := s.regs.get64 .rsp
        (Mem.loadInt s.dmem a 8 = none → env.ok (.load .plain false a 8) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧
                ∃ v, env.step (.load .plain false a 8) g v g' ∧ x = v.setWidth 64) →
            E (Int64.ofBitVec x) { s with regs := s.regs.set64 .rsp (a + Width.W64.bytesv) } g') ⦄
      (⟨Directive.instr (.regular asz osz .ret) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step_jmp
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load,
        Width.bytes, hl, Effects.AllEnv]
      exact ⟨hok hl, fun v g' hs => .done _ (Or.inr (hk _ g' (.inr ⟨hl, v, hs, rfl⟩)))⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load,
        Width.bytes, hl, Effects.AllEnv]
      exact .done _ (Or.inr (hk _ g (.inl ⟨w, hl, rfl, rfl⟩)))

/-- `jmp *d(%b)`, mapped or shared: the run exits to the address the 8 bytes at
`b + d` hold, from `dmem` or any value the environment allows. -/
@[spec] theorem MachineWP.jmp_mem_base_disp_env_spec (osz : Width) (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a 8 = none → env.ok (.load .plain false a 8) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧
                ∃ v, env.step (.load .plain false a 8) g v g' ∧ x = v.setWidth 64) →
            E (Int64.ofBitVec x) s g') ⦄
      (⟨Directive.instr (.regular .W64 osz (.jmp (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step_jmp
    cases hl : Mem.loadInt s.dmem (s.regs.get64 b + d.toBitVec) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        MachineData.load, AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64,
        Width.bytes, hl, Effects.AllEnv]
      exact ⟨hok hl, fun v g' hs => .done _ (Or.inr (hk _ g' (.inr ⟨hl, v, hs, rfl⟩)))⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        MachineData.load, AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64,
        Width.bytes, hl, Effects.AllEnv]
      exact .done _ (Or.inr (hk _ g (.inl ⟨w, hl, rfl, rfl⟩)))

/-- One call, mapped or shared, with the callee's run as its premise, as
`MachineWP.call_spec` over the environment wp: the return address goes to the
8 bytes below the stack pointer, in `dmem` or by a plain store the environment
must permit, and `P ra` holds of every state and environment state the push
may leave. Not `@[spec]`, like `call_spec`. -/
theorem MachineWP.call_env_spec {P : Int64 → MachineData → env.State → Prop} (asz osz : Width)
    (l : Label) (body : Program)
    (hplace : cenv.sits ((_root_.Executable.labels cenv).label l) body)
    (hbody : ∀ ra : Int64,
      TripleEnv env (P ra) body (fun _ _ => False)
        (fun a s' g' => if a = ra then WP.wp (⟨p⟩ : EnvProgram env) Q E s' g' else E a s' g')) :
    ⦃ fun s g =>
        let a := s.regs.get64 .rsp - Width.W64.bytesv
        (Mem.loadInt s.dmem a 8 = none →
            ∀ ra : Int64, env.ok (.store .plain false a 8 (ra.toBitVec.setWidth 128)) g) ∧
          (∀ ra m g',
            ((Mem.loadInt s.dmem a 8).isSome = true ∧
                m = Mem.storeInt s.dmem a 8 ra.toBitVec.toInt ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧ m = s.dmem ∧
                ∃ ok, env.step (.store .plain false a 8 (ra.toBitVec.setWidth 128)) g ok g') →
            P ra { s with regs := s.regs.set64 .rsp a, dmem := m } g') ⦄
      (⟨Directive.instr (.regular asz osz
          (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    obtain ⟨hok, hP⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    have hcancel : Int64.ofBitVec
        (pc + Int64.ofNat z +
          ((_root_.Executable.labels cenv).label l - (pc + Int64.ofNat z))).toBitVec
        = (_root_.Executable.labels cenv).label l := by
      rw [Int64.ofBitVec_toBitVec]
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    -- the callee's run from the state behind the push, then the caller's tail
    have hcont : ∀ s' g', P (pc + Int64.ofNat z) s' g' →
        Eventually (cenv.instrStepEnv env)
          (fun x => (x.1.2 = cenv.after pc (Directive.instr (.regular asz osz
              (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p) ∧ Q () x.1.1 x.2)
            ∨ E x.1.2 x.1.1 x.2)
          ((s', (_root_.Executable.labels cenv).label l), g') := by
      intro s' g' hp
      refine eventually_trans _ _ _ _ (hbody _ _ _ hp _ hplace) ?_
      rintro ⟨⟨s', a⟩, g''⟩ (⟨-, hbot⟩ | hexit)
      · exact hbot.elim
      · dsimp only at hexit
        by_cases ha : a = pc + Int64.ofNat z
        · subst ha
          simp only [↓reduceIte] at hexit
          rw [after_instr hseg]
          exact hexit _ hpl'
        · simp only [ha, ↓reduceIte] at hexit
          exact Eventually.done _ (Or.inr hexit)
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inr ?_⟩
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        ConstExpr.interp, MachineData.store, Width.bytes, hl, Effects.AllEnv, hcancel]
      exact ⟨hok hl _, fun ok g' hs => hcont _ _ (hP _ _ _ (.inr ⟨hl, rfl, ok, hs⟩))⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        ConstExpr.interp, MachineData.store, Width.bytes, hl, Effects.AllEnv, hcancel]
      exact hcont _ _ (hP _ _ _ (.inl ⟨by rw [hl]; rfl, rfl, rfl⟩))

/-- `xchgl %r32, d(%b)` on a shared location: one `rmw .acqRel` of 4 bytes
writing the low word of `r`; `r` gets the old word, zero-extended. -/
@[spec] theorem MachineWP.xchg32_shared_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let acc := SharedAccess.rmw .acqRel a 4 (rmwOp128 .W32 (fun _ => some ((s.regs.get64 r).setWidth 32)))
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok acc g ⊓
          (∀ old g', env.step acc g old g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.set64 r ((old.setWidth 32).setWidth 64) } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.xchg (.low r .W32) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hnone, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    simp only [Directive.interp, Instr.interp, Operation.interp,
      RegOrMem.rmw, MachineData.rmwK, MachineData.setReg,
      AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low32,
      Reg64s.set_low32, Width.bytes, hnone, Effects.AllEnv, ite_true]
    exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movl $i, d(%b)` on a shared location: one `store .plain` of 4 bytes of
the immediate's low word. -/
@[spec] theorem MachineWP.mov32_store_imm_shared_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := (i.toBitVec.truncate 32).setWidth 128
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok (.store .plain false a 4 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 4 v) g ok g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hnone, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, ConstExpr.interp,
      MachineData.set, MachineData.store,
      AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Width.bytes,
      hnone, Effects.AllEnv]
    exact ⟨hok, fun ok g' hs => hk ok g' hs _ hpl'⟩

/-- `lock cmpxchgl %r32, d(%b)` on a shared location: one `rmw .acqRel` of 4
bytes that writes the low word of `r` if the old low word equals `eax` (the
32-bit `MachineWP.lock_cmpxchg_shared_spec`). The flags are those of `cmpl` of
`eax` with the old word; on a mismatch the old word lands in `eax`
(zero-extended). Both outcomes are VCs. -/
@[spec] theorem MachineWP.lock_cmpxchg32_shared_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let acc := (s.regs.get64 .rax).setWidth 32
        let op := rmwOp128 .W32 (fun x => if x == acc then some ((s.regs.get64 r).setWidth 32) else none)
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok (.rmw .acqRel a 4 op) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 4 op) g v g' →
            let old := v.setWidth 32
            let dv := acc - old
            let status := StatusFlags.from_result dv
              { cf := dv.unsigned != acc.unsigned - old.unsigned,
                af := (dv.take 4).unsigned != (acc.take 4).unsigned - (old.take 4).unsigned,
                of := dv.signed != acc.signed - old.signed }
            (old = acc → WP.wp (⟨p⟩ : EnvProgram env) Q E { s with status } g')
            ⊓ (old ≠ acc → WP.wp (⟨p⟩ : EnvProgram env) Q E
                { s with regs := s.regs.set64 .rax (old.setWidth 64), status } g')) ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.cmpxchg true (.mem ⟨some (.reg b), none, .int64 d⟩) (.low r .W32))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hnone, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    simp only [Directive.interp, Instr.interp, Operation.interp,
      RegOrMem.rmw, MachineData.rmwK, MachineData.setReg,
      AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low32,
      Reg64s.set_low32, Width.bytes, hnone, Effects.AllEnv, ite_true]
    refine ⟨hok, fun v g' hs => ?_⟩
    obtain ⟨heq, hne⟩ := hk v g' hs
    by_cases h : v.setWidth 32 = (s.regs.get64 .rax).setWidth 32
    · have hb : (v.setWidth 32 == (s.regs.get64 .rax).setWidth 32) = true := by simpa using h
      simp only [hb, ite_true]
      exact heq h _ hpl'
    · have hb : (v.setWidth 32 == (s.regs.get64 .rax).setWidth 32) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false]
      exact hne h _ hpl'

end CombinedSpecs

/-! ## Procedure specifications in the environment

`Executable.ProcSpecEnv` (`Kraken.EnvWP`) is `Executable.ProcSpec` over the
environment judgment: a run entered at `entry` with `Pre x ra t g` reaches
`ra` with `Post x ra t g s' g'`, the environment state threaded through.
`call_proc_env_spec` steps a `call` through such a spec, as
`MachineWP.call_proc_spec` does for `ProcSpec`; the return address is pushed
as by `call_env_spec` (into `dmem`, or by a plain store the environment must
permit). `ProcSpecEnv.of_tripleEnv` establishes a spec from a `TripleEnv` on
the procedure's body that ends in the exit channel at `ra` (its `ret`). -/

section ProcSpecEnv

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- A procedure's spec from a `TripleEnv` on its body, placed at its label:
from the entry state, every run leaves the body by the exit channel at `ra`
(the body's `ret`), with the postcondition; it never falls through. -/
theorem Kraken.Executable.ProcSpecEnv.of_tripleEnv {α : Type}
    {Pre : α → Int64 → MachineData → env.State → Prop}
    {Post : α → Int64 → MachineData → env.State → MachineData → env.State → Prop}
    {l : Label} {body : Program}
    (hplace : cenv.sits ((_root_.Executable.labels cenv).label l) body)
    (h : ∀ x ra t g, Pre x ra t g →
      TripleEnv env (fun s g' => s = t ∧ g' = g) body (fun _ _ => False)
        (fun a s' g' => a = ra ∧ Post x ra t g s' g')) :
    cenv.ProcSpecEnv env ((_root_.Executable.labels cenv).label l) Pre Post := by
  intro x ra t g hpre
  refine eventually_weaken _ _ _ _ ?_ (h x ra t g hpre t g ⟨rfl, rfl⟩ _ hplace)
  rintro _ (⟨-, hf⟩ | hexit)
  · exact hf.elim
  · exact hexit

/-- **A call through a procedure's environment spec.** The caller fixes the
logical variable `x`; for every return address and every outcome of the push
(into `dmem` where the slot is mapped, else a plain store the environment
must permit, as in `call_env_spec`), the callee's precondition holds of the
pushed state, and its postcondition continues the caller's tail. -/
theorem MachineWP.call_proc_env_spec {α : Type}
    {Pre : α → Int64 → MachineData → env.State → Prop}
    {Post : α → Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (x : α) (asz osz : Width) (l : Label)
    (hproc : cenv.ProcSpecEnv env ((_root_.Executable.labels cenv).label l) Pre Post) :
    ⦃ fun s g =>
        let a := s.regs.get64 .rsp - Width.W64.bytesv
        (Mem.loadInt s.dmem a 8 = none →
            ∀ ra : Int64, env.ok (.store .plain false a 8 (ra.toBitVec.setWidth 128)) g) ⊓
          (∀ ra m g',
            ((Mem.loadInt s.dmem a 8).isSome = true ∧
                m = Mem.storeInt s.dmem a 8 ra.toBitVec.toInt ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧ m = s.dmem ∧
                ∃ ok, env.step (.store .plain false a 8 (ra.toBitVec.setWidth 128)) g ok g') →
            Pre x ra { s with regs := s.regs.set64 .rsp a, dmem := m } g' ⊓
              ∀ s'' g'', Post x ra { s with regs := s.regs.set64 .rsp a, dmem := m } g' s'' g'' →
                WP.wp (⟨p⟩ : EnvProgram env) Q E s'' g'') ⦄
      (⟨Directive.instr (.regular asz osz
          (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hP⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    have hcancel : Int64.ofBitVec
        (pc + Int64.ofNat z +
          ((_root_.Executable.labels cenv).label l - (pc + Int64.ofNat z))).toBitVec
        = (_root_.Executable.labels cenv).label l := by
      rw [Int64.ofBitVec_toBitVec]
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    -- the callee's run from the state behind the push, then the caller's tail
    have hcont : ∀ m g',
        ((Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true ∧
            m = Mem.storeInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8
              (pc + Int64.ofNat z).toBitVec.toInt ∧ g' = g)
          ∨ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8 = none ∧ m = s.dmem ∧
            ∃ ok, env.step (.store .plain false (s.regs.get64 .rsp - Width.W64.bytesv) 8
              ((pc + Int64.ofNat z).toBitVec.setWidth 128)) g ok g') →
        Eventually (cenv.instrStepEnv env)
          (fun x => (x.1.2 = cenv.after pc (Directive.instr (.regular asz osz
              (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p) ∧ Q () x.1.1 x.2)
            ∨ E x.1.2 x.1.1 x.2)
          (({ s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - Width.W64.bytesv), dmem := m },
            (_root_.Executable.labels cenv).label l), g') := by
      intro m g' halt
      obtain ⟨hpre, hpost⟩ := hP _ m g' halt
      refine eventually_trans _ _ _ _ (hproc x _ _ _ hpre) ?_
      rintro ⟨⟨s'', a⟩, g''⟩ ⟨ha, hq⟩
      dsimp only at ha hq
      subst ha
      rw [after_instr hseg]
      exact hpost _ _ hq _ hpl'
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inr ?_⟩
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        ConstExpr.interp, MachineData.store, Width.bytes, hl, Effects.AllEnv, hcancel]
      exact ⟨hok hl _, fun ok g' hs => hcont _ _ (.inr ⟨hl, rfl, ok, hs⟩)⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        ConstExpr.interp, MachineData.store, Width.bytes, hl, Effects.AllEnv, hcancel]
      exact hcont _ _ (.inl ⟨by rw [hl]; rfl, rfl, rfl⟩)

/-- `call_proc_env_spec` with the widths, the tail and the channels open, in
the form `vcgen [hc]` steps a call with: `have hc := call_proc_env_spec_at x l
hproc` at the call site. -/
theorem MachineWP.call_proc_env_spec_at {α : Type}
    {Pre : α → Int64 → MachineData → env.State → Prop}
    {Post : α → Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (x : α) (l : Label)
    (hproc : cenv.ProcSpecEnv env ((_root_.Executable.labels cenv).label l) Pre Post) :
    ∀ ⦃asz osz : Width⦄ ⦃p : Program⦄ ⦃Q : Unit → MachineData → env.State → Prop⦄
      ⦃E : Int64 → MachineData → env.State → Prop⦄,
      ⦃ fun s g =>
          let a := s.regs.get64 .rsp - Width.W64.bytesv
          (Mem.loadInt s.dmem a 8 = none →
              ∀ ra : Int64, env.ok (.store .plain false a 8 (ra.toBitVec.setWidth 128)) g) ⊓
            (∀ ra m g',
              ((Mem.loadInt s.dmem a 8).isSome = true ∧
                  m = Mem.storeInt s.dmem a 8 ra.toBitVec.toInt ∧ g' = g)
                ∨ (Mem.loadInt s.dmem a 8 = none ∧ m = s.dmem ∧
                  ∃ ok, env.step (.store .plain false a 8 (ra.toBitVec.setWidth 128)) g ok g') →
              Pre x ra { s with regs := s.regs.set64 .rsp a, dmem := m } g' ⊓
                ∀ s'' g'', Post x ra { s with regs := s.regs.set64 .rsp a, dmem := m } g' s'' g'' →
                  WP.wp (⟨p⟩ : EnvProgram env) Q E s'' g'') ⦄
        (⟨Directive.instr (.regular asz osz
            (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p⟩ : EnvProgram env)
      ⦃ Q; E ⦄ :=
  fun asz osz _ _ _ => MachineWP.call_proc_env_spec x asz osz l hproc

end ProcSpecEnv

/-! ## Piece-aware `vcgen`

The shared vector rules leave the environment's side of the access as
`SharedEnv.AvxLoad`/`AvxStore`, `LoadPieces`/`StorePieces` with the tail's
wp inside the continuation, and `vcgen` does not enter it (it is a recursive
definition, not a wp). The introduction rules below take one piece at a time,
the obligation on the piece apart and the continuation under the binders of
the step; `vcgen_env` interleaves them with `vcgen`, so that one call goes
through the pieces into the tail. `vcgen` itself is unchanged. -/

namespace SharedEnv

variable {env : SharedEnv} {addr : BitVec 64} {g : env.State}

theorem StorePieces.intro_nil {k : env.State → Prop} (h : k g) : env.StorePieces addr [] g k := h

theorem StorePieces.intro_cons {p : BitVec 64} {ps : List (BitVec 64)} {k : env.State → Prop}
    (hok : env.ok (.store .plain false addr 8 (p.setWidth 128)) g)
    (hk : ∀ b g', env.step (.store .plain false addr 8 (p.setWidth 128)) g b g' →
      env.StorePieces (addr + 8) ps g' k) :
    env.StorePieces addr (p :: ps) g k := ⟨hok, hk⟩

theorem LoadPieces.intro_zero {k : List (BitVec 64) → env.State → Prop} (h : k [] g) :
    env.LoadPieces addr 0 g k := h

theorem LoadPieces.intro_succ {n : Nat} {k : List (BitVec 64) → env.State → Prop}
    (hok : env.ok (.load .plain false addr 8) g)
    (hk : ∀ v g', env.step (.load .plain false addr 8) g v g' →
      env.LoadPieces (addr + 8) n g' (fun vs g'' => k (v.setWidth 64 :: vs) g'')) :
    env.LoadPieces addr (n + 1) g k := ⟨hok, hk⟩

theorem AvxLoad.intro_atomic {w : AvxWidth} {k : BitVec w.bits → env.State → Prop}
    (hok : env.ok (.load .plain false addr w.bytes) g)
    (hk : ∀ v g', env.step (.load .plain false addr w.bytes) g v g' → k (v.setWidth w.bits) g') :
    env.AvxLoad true addr w g k := ⟨hok, hk⟩

theorem AvxLoad.intro_pieces {w : AvxWidth} {k : BitVec w.bits → env.State → Prop}
    (h : env.LoadPieces addr (w.bytes / 8) g (fun vs g' => k (ofPieces w.bits vs) g')) :
    env.AvxLoad false addr w g k := h

/-- `AvxLoad.intro_pieces` with the piece count of each width as a literal
(the count `w.bytes / 8` does not unify with `n + 1`). -/
theorem AvxLoad.intro_pieces_W128 {k : BitVec AvxWidth.W128.bits → env.State → Prop}
    (h : env.LoadPieces addr 2 g (fun vs g' => k (ofPieces AvxWidth.W128.bits vs) g')) :
    env.AvxLoad false addr .W128 g k := h

theorem AvxLoad.intro_pieces_W256 {k : BitVec AvxWidth.W256.bits → env.State → Prop}
    (h : env.LoadPieces addr 4 g (fun vs g' => k (ofPieces AvxWidth.W256.bits vs) g')) :
    env.AvxLoad false addr .W256 g k := h

theorem AvxLoad.intro_pieces_W512 {k : BitVec AvxWidth.W512.bits → env.State → Prop}
    (h : env.LoadPieces addr 8 g (fun vs g' => k (ofPieces AvxWidth.W512.bits vs) g')) :
    env.AvxLoad false addr .W512 g k := h

theorem AvxStore.intro_atomic {w : AvxWidth} {v : BitVec w.bits} {k : env.State → Prop}
    (hok : env.ok (.store .plain false addr w.bytes (v.setWidth 128)) g)
    (hk : ∀ b g', env.step (.store .plain false addr w.bytes (v.setWidth 128)) g b g' → k g') :
    env.AvxStore true addr v g k := ⟨hok, hk⟩

theorem AvxStore.intro_pieces {w : AvxWidth} {v : BitVec w.bits} {k : env.State → Prop}
    (h : env.StorePieces addr (toPieces v (w.bytes / 8)) g k) :
    env.AvxStore false addr v g k := h

end SharedEnv

/-- `vcgen_env [rules]` is `vcgen [rules]` that also goes through the
environment's side of the shared vector accesses: wherever `vcgen` leaves an
`AvxLoad`/`AvxStore`/`LoadPieces`/`StorePieces` goal, one introduction rule
per access or piece (the `ok` obligation stays a goal, the step's binders are
introduced), then `vcgen [rules]` again on the tail's wp, once the last piece
is taken (`vcgen` is called on the tail only, never on a side goal). The atomicity flag,
the piece list and the piece count are computed by unification at the width
literal. Every goal it does not recognise is left as `vcgen` leaves it. -/
syntax (name := vcgenEnv) "vcgen_env"
  (" [" withoutPosition((Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,?) "] ")? : tactic

macro_rules
  | `(tactic| vcgen_env) => `(tactic| vcgen_env [])
  | `(tactic| vcgen_env [$ts,*]) => `(tactic| (
      vcgen [$ts,*]
      all_goals (repeat' (first
        | (refine SharedEnv.AvxStore.intro_atomic ?_ (fun _ _ _ => ?_); rotate_left; vcgen [$ts,*])
        | refine SharedEnv.AvxStore.intro_pieces ?_
        | (refine SharedEnv.AvxLoad.intro_atomic ?_ (fun _ _ _ => ?_); rotate_left; vcgen [$ts,*])
        | refine SharedEnv.AvxLoad.intro_pieces_W128 ?_
        | refine SharedEnv.AvxLoad.intro_pieces_W256 ?_
        | refine SharedEnv.AvxLoad.intro_pieces_W512 ?_
        | refine SharedEnv.AvxLoad.intro_pieces ?_
        | refine SharedEnv.StorePieces.intro_cons ?_ (fun _ _ _ => ?_)
        | (refine SharedEnv.StorePieces.intro_nil ?_; vcgen [$ts,*])
        | refine SharedEnv.LoadPieces.intro_succ ?_ (fun _ _ _ => ?_)
        | (refine SharedEnv.LoadPieces.intro_zero ?_; vcgen [$ts,*])))))
