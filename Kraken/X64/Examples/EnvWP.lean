/-
The environment-aware wp (`Kraken.EnvWP`) on a two-instruction program with
one shared load:

    movl (%rdi), %eax     -- a 4-byte shared location, outside `dmem`
    addq $1, %rax

The load is answered by an environment `bounded loc`: other threads only
ever leave values below 10 at `loc`. Its rule (`mov32_load_shared_env`) is a
prototype of the shared-location rules of `Kraken/EnvWPRules.lean`, proved by
unfolding one cell. The
`addq` is not re-proved: its `MachineWP` triple, obtained by `vcgen`, is
lifted by `MachineWP.wpEnv_of_triple`.
-/
import Kraken.EnvWP
import Kraken.X64.Parser

open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace EnvWPExample

open MachineWP

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr [CodeEnv] {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

/-- `movl d(%b), %r32` on a location outside `dmem`: the access must be
permitted, and the tail runs from every value and environment state the
environment allows, the value zero-extended in the register. -/
theorem mov32_load_shared_env [CodeEnv] (env : SharedEnv) (r b : Reg64) (d : Int64) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a 4 = none ∧ env.ok (.load .plain false a 4) g ∧
          ∀ v g', env.step (.load .plain false a 4) g v g' →
            cenv.wpEnv env p Q E { s with regs := s.regs.set64 r ((v.setWidth 32).setWidth 64) } g')
      (Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩ pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [after_instr hseg]
  refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.set_low32, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-! ## The environment -/

/-- A 4-byte location at `loc` that the other threads only ever set to values
below 10, and that this thread may read but not write. No other location is
shared; fences are permitted and change nothing. -/
def bounded (loc : BitVec 64) : SharedEnv where
  State := Unit
  ok a _ := match a with
    | .load _ _ addr n => addr = loc ∧ n = 4
    | .fence _ => True
    | _ => False
  step a _ r _ := match a, r with
    | .load .., v => v.toNat < 10
    | .fence _, _ => True
    | _, _ => False

theorem bounded_fencesSkip (loc : BitVec 64) : (bounded loc).FencesSkip :=
  fun _ _ => ⟨trivial, fun _ _ => rfl⟩

/-! ## The program -/

section Program

open Kraken.X64.Parser

variable [layout : _root_.Layout]

def loadIncr : Program := parse("
  movl (%rdi), %eax
  addq $1, %rax
")

def incr : Program := parse("
  addq $1, %rax
")

local instance loadIncr.env : CodeEnv := ⟨layout loadIncr⟩

/-- The existing judgment about the tail, in the `MachineWP` logic. -/
theorem incr_correct (x : BitVec 64) :
    ⦃ fun s => s.regs.get64 .rax = x ⦄ incr ⦃ fun _ s => s.regs.get64 .rax = x + 1; fun _ _ => False ⦄ := by
  vcgen [incr]
  all_goals grind

/-- The environment version: whatever value below 10 the other threads left
at `loc`, `rax` ends at most 10. The load is the shared-location rule; the
`addq` is `incr_correct`, lifted. -/
theorem loadIncr_env (s : MachineData) (loc : BitVec 64)
    (hloc : s.regs.get64 .rdi = loc) (hnone : Mem.loadInt s.dmem loc 4 = none) :
    TripleEnv (bounded loc) (fun s' _ => s' = s) loadIncr
      (fun s' _ => (s'.regs.get64 .rax).toNat ≤ 10) (fun _ _ _ => False) := by
  intro s' g hs
  subst hs
  show cenv.wpEnv _ (_ :: incr) _ _ s' g
  apply Executable.wpEnv_cons
  have ha : s'.regs.get64 .rdi + (0 : Int64).toBitVec = loc := by simp [hloc]
  refine mov32_load_shared_env (bounded loc) .rax .rdi 0 (p := []) s' g
    ⟨by rw [ha]; exact hnone, by rw [ha]; exact ⟨rfl, rfl⟩, fun v g' hs => ?_⟩
  intro pc _
  refine .done _ (.inl ⟨rfl, ?_⟩)
  have hv : v.toNat < 10 := hs
  have hlift := wpEnv_of_triple (bounded_fencesSkip loc).fenceInv_true
    (incr_correct ((v.setWidth 32).setWidth 64))
  refine Executable.wpEnv_mono (fun s'' _ h => ?_) (fun _ _ _ h => h.1)
    (hlift _ g' ⟨by simp, trivial⟩)
  rw [h.1]
  bv_omega

end Program

end EnvWPExample
