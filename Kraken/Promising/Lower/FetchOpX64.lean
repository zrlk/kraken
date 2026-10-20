/-
**x64 `fetch or/and/xor` as a `lock cmpxchg`
retry loop, as a fragment specification.** ISA: x64;
machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness, as `FragSpecEnv`
(`Lower/FragSpecX64.lean`).

x64 has no locked instruction that applies `or`/`and`/`xor` and returns the
old value (`lock orq`, `Lower/EventsX64LockBin.lean`, only when the result is
dead). The lowering is `fetchOpFragX op`: a load,
then `movq %rax,%rcx; op %rsi,%rcx; lock cmpxchgq %rcx,(%rdi); jne`, then
`jmp *%r11` (the register-link convention).

`fetchOpFragX_spec`: for **any** environment `E` whose fences skip
(`[E.Skips]`, needed by `vcgen`'s generic lift `MachineWP.env_lift_spec`; the
loop has no fence), counted, and any rely `J` on `E`'s state that survives the
loop's loads and failed `cmpxchg`s (`FetchRely`): from `rdi = a`, `rsi = v`,
`r11 = ra`, `a` not in `dmem`, `J`, every run returns to `ra` with the x64 pilot's
callee-saved `Saved` (so `dmem` too) and **the final environment state is
the result of one successful `lock cmpxchg` step** at `a`, from a `J` state,
with comparand `o` and new value `op.eval o v`, returning `o`, and `rax = o`
(`FetchPost`). A pure environment is the instance `J = ⊤`. A protocol-level
use supplies `J` and reads `o op v` off the step through `E.step`.

Not here: an EnvG (`FenceMono`, not `Skips`) instance, which would go
through `envMonoX_lift_spec`; a bit-set protocol for a two-thread demo (no
EnvG protocol for an or-shaped shared word exists; the x64 counter protocols
are `xadd`-shaped). `or_reg_reg_spec`/`and_reg_reg_spec` are new `@[spec]`
rules (`MachineWP` had only `xor`).
-/
import Kraken.Promising.Lower.FragSpecX64
import Kraken.Promising.Lower.PilotXRSpecs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.X64

namespace Kraken.Promising.Lower.FetchOpX

open Kraken.Promising.Lower.PilotX (Saved Saved.refl)
open Kraken.Promising.Lower.PilotXR (ofBitVec_reg)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## `or`/`and` of two registers

`MachineWP` has `xor_reg_reg_spec` but no `or`/`and` twin; its rule
plumbing (`after_instr`, `step_here`, `fallthrough_nondet_spec`, `wp_step`) is
private or local, so it is repeated here (verbatim). -/

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

private theorem fallthrough_nondet_spec {α : Type} [NondetSupportingType α] {i : Instr}
    {f : MachineData → α → MachineData}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop),
      (∀ v : α, P (f s v, 0)) → (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => ∀ v : α, WP.wp p Q E (f s v) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    exact step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl (hcell s _ _ (fun v => h v _ hpl'))⟩

/-- `or %rs, %rd` (64-bit). -/
@[spec] theorem or_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ||| s.regs.get64 rs
        ∀ af : Bool, WP.wp p Q E
          { s with regs := s.regs.set64 rd v, status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64 (.or (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_nondet_spec (fun s rng P hP => by wp_step; exact hP)

/-- `and %rs, %rd` (64-bit). -/
@[spec] theorem and_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd &&& s.regs.get64 rs
        ∀ af : Bool, WP.wp p Q E
          { s with regs := s.regs.set64 rd v, status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64 (.and (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_nondet_spec (fun s rng P hP => by wp_step; exact hP)

end Specs

/-- The operation of a WeakCore `fetch or/and/xor`. -/
inductive FetchOp | or | and | xor

/-- The value `fetch op` writes, from the old value `o` and the operand `v`. -/
def FetchOp.eval : FetchOp → BitVec 64 → BitVec 64 → BitVec 64
  | .or, o, v => o ||| v | .and, o, v => o &&& v | .xor, o, v => o ^^^ v

/-- **`fetch op` on x64**: `rax := [rdi]`, then `[rdi] := rax op rsi` by a
`lock cmpxchg` retry loop; returns to the link `r11` with the old value in
`rax`. Clobbers `rcx` and the flags. -/
def fetchOpFragX : FetchOp → Program
  | .or => parse("
fetch_op:
    movq (%rdi), %rax
fetch_op_loop:
    movq %rax, %rcx
    orq %rsi, %rcx
    lock cmpxchgq %rcx, (%rdi)
    jne fetch_op_loop
    jmp *%r11
")
  | .and => parse("
fetch_op:
    movq (%rdi), %rax
fetch_op_loop:
    movq %rax, %rcx
    andq %rsi, %rcx
    lock cmpxchgq %rcx, (%rdi)
    jne fetch_op_loop
    jmp *%r11
")
  | .xor => parse("
fetch_op:
    movq (%rdi), %rax
fetch_op_loop:
    movq %rax, %rcx
    xorq %rsi, %rcx
    lock cmpxchgq %rcx, (%rdi)
    jne fetch_op_loop
    jmp *%r11
")

/-- `fetch or`, a row of the lowering specification. -/
abbrev fetchOrFragX : Program := fetchOpFragX .or

/-- The `lock cmpxchgq` at `a` with comparand `o` and new value `op.eval o v`
(the loop's only write), as the environment sees it. -/
abbrev casAcc (op : FetchOp) (a v o : BitVec 64) : SharedAccess :=
  .rmw .acqRel a 8 (rmwOp128 .W64 fun x => if x == o then some (op.eval o v) else none)

/-- The environment's rely for the loop at `a`: `J` holds on entry, survives
every load of `a` and every failed `cmpxchg`, and every access is allowed. -/
structure FetchRely (op : FetchOp) (E : SharedEnv) (a v : BitVec 64) (J : E.State → Prop) : Prop where
  ld_ok : ∀ g, J g → E.ok (.load .plain false a 8) g
  ld : ∀ g x g', J g → E.step (.load .plain false a 8) g x g' → J g'
  cas_ok : ∀ g o, J g → E.ok (casAcc op a v o) g
  fail : ∀ g o x g', J g → E.step (casAcc op a v o) g x g' → x.setWidth 64 ≠ o → J g'

/-- The precondition: link `r11 = ra`, `rdi = a`, `rsi = v`, `a` not in
`dmem`, the rely `J`. -/
def FetchPre (E : SharedEnv) (a v : BitVec 64) (J : E.State → Prop) (ra : Int64) (t : MachineData)
    (g : (SharedEnv.counted E).State) : Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ t.regs.get64 .rdi = a ∧ t.regs.get64 .rsi = v ∧
    Mem.loadInt t.dmem a 8 = none ∧ J g.1

/-- The postcondition: `Saved`, and the last environment step is the
successful `lock cmpxchg` (comparand `o = x`, new `op.eval o v`) from a `J`
state, with `rax = o`. -/
def FetchPost (op : FetchOp) (E : SharedEnv) (a v : BitVec 64) (J : E.State → Prop) (_ : Int64) (t : MachineData)
    (_ : (SharedEnv.counted E).State) (t' : MachineData) (g' : (SharedEnv.counted E).State) : Prop :=
  Saved t t' ∧ ∃ g0 x, J g0 ∧ E.step (casAcc op a v (x.setWidth 64)) g0 x g'.1 ∧
    t'.regs.get64 .rax = x.setWidth 64

private theorem step_rmw_congr {E : SharedEnv} {k : RmwKind} {a a' : BitVec 64} {n : Nat}
    {op op' : BitVec 128 → Option (BitVec 128)} {g g' : E.State} {x : BitVec 128} (ha : a = a') (hop : op = op')
    (h : E.step (.rmw k a n op) g x g') : E.step (.rmw k a' n op') g x g' := by
  subst ha hop; exact h

private theorem step_load_congr {E : SharedEnv} {k : LoadKind} {xcl : Bool} {a a' : BitVec 64} {n : Nat}
    {g g' : E.State} {x : BitVec 128} (ha : a = a') (h : E.step (.load k xcl a n) g x g') :
    E.step (.load k xcl a' n) g x g' := by
  subst ha; exact h

private theorem ea0 (x : BitVec 64) : x + Int64.toBitVec 0 = x := by simp

/-- **The CAS-loop `fetch op` fragment specification.** -/
theorem fetchOpFragX_spec (op : FetchOp) (E : SharedEnv) [E.Skips] (a v : BitVec 64) (J : E.State → Prop)
    (hR : FetchRely op E a v J) :
    FragSpecEnv (SharedEnv.counted E) (fetchOpFragX op) "fetch_op" (FetchPre E a v J) (FetchPost op E a v J) := by
  cases op <;> (
    refine FragSpecEnv.of_cfg (fun ra t _ lb s g => s.regs.get64 .r11 = ra.toBitVec ∧ s.regs.get64 .rdi = a ∧
        s.regs.get64 .rsi = v ∧ Mem.loadInt s.dmem a 8 = none ∧ Saved t s ∧ J g.1 ∧
        (lb = "fetch_op" ∨ lb = "fetch_op_loop")) rfl (by decide)
      (fun ra t g ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, Saved.refl t, h5, .inl rfl⟩) ?_
    intro _ ra t g _
    cfg_cases_env [fetchOpFragX]
    all_goals intro s₀ g₀
    all_goals vcgen
    all_goals obtain ⟨⟨h11, hdi, hsi, hdm, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hJ, -⟩, rfl, rfl⟩ :=
      ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
    all_goals subst hdi hsi
    all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, Reg64s.get64_set64, reduceCtorEq,
      ↓reduceIte, ea0] at *
    -- `fetch_op`: the first load
    case vc1 => exact hR.ld_ok _ hJ
    case vc2 =>
      rename_i s g x g1 _ hld _
      rcases hld with ⟨_, h, -⟩ | ⟨-, _, ⟨h, -⟩, -⟩
      · rw [hdm] at h; cases h
      refine ⟨?_, trivial, trivial, hdm, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hR.ld _ _ _ hJ (step_load_congr (ea0 _) h),
        .inr trivial⟩
      all_goals first | assumption | (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption)
    -- `fetch_op_loop`
    case vc1 => exact hdm
    case vc2 => exact hR.cas_ok _ _ hJ
    case vc3 =>
      rename_i s g af old g1 _ hst heq hz _
      simp [CondCode.interp, StatusFlags.from_result, heq] at hz
    case vc4 =>
      rename_i s g af old g1 _ hst heq hz _
      refine .inr ⟨ofBitVec_reg h11, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, _, old, hJ,
        step_rmw_congr (ea0 _) (by simp [heq, FetchOp.eval]) hst.1, ?_⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | assumption | exact heq.symm
    case vc5 =>
      rename_i s g af old g1 _ hst hne hz _
      refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ?_, hdm, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩,
        hR.fail _ _ _ _ hJ (step_rmw_congr (ea0 _) (by simp [FetchOp.eval]) hst.1) hne, .inr rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      rotate_left 9
      · subst hg; have := hst.2; simp only [SharedAccess.tick] at this; omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try assumption
    case vc6 =>
      rename_i s g af old g1 _ hst hne hz _
      simp [CondCode.interp, StatusFlags.from_result] at hz
      exact (hne (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm).elim)

/-- **`fetch or`**: `fetchOpFragX_spec` at `.or`. -/
theorem fetchOrFragX_spec (E : SharedEnv) [E.Skips] (a v : BitVec 64) (J : E.State → Prop)
    (hR : FetchRely .or E a v J) :
    FragSpecEnv (SharedEnv.counted E) fetchOrFragX "fetch_op" (FetchPre E a v J) (FetchPost .or E a v J) :=
  fetchOpFragX_spec .or E a v J hR

end Kraken.Promising.Lower.FetchOpX
