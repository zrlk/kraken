/-
**`vcgen` over `EnvGLR`**: `EnvGLR`'s fences are
`EnvG`'s, so it has `EnvG`'s fence order (`FenceLe`) and `vcgen`'s generic
rule for monotone-fence environments (`envMonoX_lift_spec`, `X64VCGen.lean`)
applies in `EnvGLRX` (through the `within` instance).

- `fenceInv_fenceLe_LR`, the `FenceMonoX` instance `instFenceMonoXEnvGLR`,
  `@[simp]` `fenceMonoX_le_envGLR`; `@[simp]` `envGLR_ok_store`, `envGLR_step_load`.
- `inc32_shared` (unlocked `incl d(%b)` on a location outside `dmem`, any
  environment: a load, then a store at the env state after the load; the
  flags left arbitrary; `EnvWPRules.lean` lists non-locked read-modify-writes
  as having no rule) and its `vcgen` form `inc32_shared_spec`.
- Smoke: a `vcgen` triple in `EnvGLRX` (`movl $1, %eax` then `mfence`).
-/
import Kraken.Promising.SLR.EnvG.LRX64
import Kraken.Promising.SLR.EnvG.X64VCGen
import Kraken.X64.Parser

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- Every `EnvGLR` fence is permitted and stays in `FenceLe σ`
(`fenceInv_fenceLe`: the fences are `EnvG`'s). -/
theorem fenceInv_fenceLe_LR (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) :
    (EnvGLR I A tid pl).FenceInv (FenceLe σ) :=
  fenceInv_fenceLe A tid pl σ

/-- `EnvGLR`'s fence order (the class under its x64 name `FenceMonoX`, the
one `envMonoX_lift_spec` and the `within` instance ask for). -/
instance instFenceMonoXEnvGLR (A : Arch) (tid : Nat) (pl : Plan) : (EnvGLR I A tid pl).FenceMonoX :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLe_LR A tid pl⟩

@[simp] theorem fenceMonoX_le_envGLR (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMonoX.le (env := EnvGLR I A tid pl)) = FenceLe := rfl

@[simp] theorem envGLR_ok_store (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : StoreKind) (xcl : Bool)
    (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGLR I A tid pl).ok (.store k xcl addr n v) σ = StoreOk A tid pl σ k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGLR_step_load (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : LoadKind) (xcl : Bool)
    (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGLR I A tid pl).step (.load k xcl addr n) σ v σ' = LoadOutLR A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising MachineWP Std.WP Lean.Order

/-! ## The env rule of `incl d(%b)` on a shared location -/

/-- **`incl d(%b)` on a location outside `dmem`**, any environment: a plain
4-byte load, then a plain 4-byte store of the old value plus one at the env
state after the load; the tail runs with every flag value. -/
theorem inc32_shared [CodeEnv] (env : SharedEnv) (b : Reg64) (d : Int64) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a 4 = none ∧ env.ok (.load .plain false a 4) g ∧
          ∀ v g', env.step (.load .plain false a 4) g v g' →
            env.ok (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) g' ∧
            ∀ ok g'', env.step (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) g' ok g'' →
              ∀ st : StatusFlags, cenv.wpEnv env p Q E { s with status := st } g'')
      (Directive.instr (.regular .W64 .W32 (.inc (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩ pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [show cenv.after pc (Directive.instr (.regular .W64 .W32 (.inc (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      = cenv.after (pc + .ofNat z) p by simp only [Executable.after, hseg]]
  refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.load, MachineData.store, Effects.AllEnv]
  simp only [AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Width.bytes, hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => ⟨(hk v g' hs).1, fun ok g'' hs' => (hk v g' hs).2 ok g'' hs' _ _ hpl'⟩⟩

/-- `inc32_shared` as a `vcgen` rule (not global: `vcgen [inc32_shared_spec]`),
the form of `MachineWP.lock_un_shared_spec`. -/
theorem inc32_shared_spec [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {p : Program} (b : Reg64) (d : Int64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok (.load .plain false a 4) g ⊓
          (∀ v g', env.step (.load .plain false a 4) g v g' →
            env.ok (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) g' ∧
            ∀ ok g'', env.step (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) g' ok g'' →
              ∀ st : StatusFlags, WP.wp (⟨p⟩ : EnvProgram env) Q E { s with status := st } g'') ⦄
      (⟨Directive.instr (.regular .W64 .W32 (.inc (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (inc32_shared env b d)

end Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.LRVCGenSmoke

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The instance reaches `EnvGLRX` through `within`. -/
example (pl : Plan) (S : SharedEnv.Layout) : (EnvGLRX Arch.tso 0 pl S).FenceMonoX := inferInstance

def movFence : Program := parse("
  movl $1, %eax
  mfence
")

variable [layout : _root_.Layout]

local instance movFence.env : CodeEnv := ⟨layout movFence⟩

/-- **`vcgen` runs in `EnvGLRX`**: a silent instruction and a fence, the
resource framed through `FenceLe`. -/
theorem movFence_envGLRX (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (r₀ : Res) :
    TripleEnv (EnvGLRX Arch.tso tid pl S) (fun _ σ => σ.r = r₀) movFence
      (fun s σ => (s.regs.get64 .rax).setWidth 32 = 1 ∧ σ.r = r₀) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold movFence
  vcgen
  all_goals simp only [fenceMonoX_le_within, fenceMonoX_le_envGLR] at *
  case vc1 => simp; trivial
  case vc2 s σ0 hpre σ1 σ2 hst hf =>
    have h12 : FenceLe σ1 σ2 := (fenceInv_fenceLe_LR Arch.tso tid pl σ1 .sy σ1 (FenceLe.refl σ1)).2 σ2 hst
    exact ⟨by simp, h12.r.trans (hf.r.trans hpre)⟩

#print axioms movFence_envGLRX

end Kraken.Promising.X64.EnvG.LRVCGenSmoke
