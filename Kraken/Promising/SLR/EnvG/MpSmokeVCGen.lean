/-
**The MP smoke test, whole threads by `vcgen`**: the per-thread proofs a program author
writes on `EnvG`, discharged by `vcgen` and the isolated VCs of
`EnvG/MpSmoke.lean`.

- `mpWriter_envG`: the writer (`mov; str; mov; stlr`), a `TripleEnv` in
  `EnvG` from `W1` to `W3`. One `vcgen` call; six goals.
- `mpReader_envG`: the reader (`spin: ldar; cbz; ldr`), a `PartialTripleEnv`
  in the counted `EnvG` by `cfgEnv_partial` with a two-label table; under the
  clean flag at the end, `W4 = 1`. `mpReader_envG'` projects the counter away.

What `vcgen` needed beyond `EnvG/Simp.lean` is `EnvG/A64VCGen.lean`
(`SharedEnv.FenceMono`, `envMono_lift_spec`): the generic rule for `MOV`/`CBZ`
needs `Skips`, which `EnvG` is not. After a silent instruction a goal is at
every `σ'` with `FenceLe σ σ'`; the table predicates are monotone in it
(`W1.fence`, …, `R3.fence`).

Not linked to `ThreadRuleRX` here: that is `ofSafelyEnvG`.
-/
import Kraken.Promising.SLR.EnvG.MpSmoke
import Kraken.Promising.SLR.EnvG.A64VCGen
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees

namespace Kraken.Promising.SLR.EnvG.MpSmoke

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The table predicates are monotone under fences -/

theorem W1.fence {P : Params} {σ σ' : State isa} (h : W1 P σ) (hf : FenceLe σ σ') : W1 P σ' := by
  unfold W1; rw [hf.g, hf.r]; exact h

theorem W2.fence {P : Params} {σ σ' : State isa} (h : W2 P σ) (hf : FenceLe σ σ') : W2 P σ' := by
  unfold W2 Own1; rw [hf.g, hf.r, hf.vwOld]; exact h

theorem W3.fence {P : Params} {σ σ' : State isa} (h : W3 P σ) (hf : FenceLe σ σ') : W3 P σ' := by
  unfold W3; rw [hf.g, hf.r]; exact h

theorem R1.fence {P : Params} {σ σ' : State isa} (h : R1 P σ) (hf : FenceLe σ σ') : R1 P σ' := by
  unfold R1; rw [hf.g, hf.r, hf.getFwd]; exact h

theorem R3.fence {P : Params} {σ σ' : State isa} (h : R3 P σ) (hf : FenceLe σ σ') : R3 P σ' := by
  obtain ⟨hw, tsF, vF, h1, h2, h3⟩ := h
  exact ⟨by rw [hf.g, hf.r]; exact hw, tsF, vF, by rw [hf.snap]; exact h1, h2, Nat.le_trans h3 hf.vrNew⟩

variable [layout : _root_.Layout]

/-! ## The writer -/

section Writer

local instance mpWriter.env : CodeEnv := ⟨layout mpWriter⟩

/-- **The MP writer on `EnvG`**: from `W1` (all of `Dt`, the token, a share of
`Fl`) the writer ends in `W3` (the token), its release accounted by the plan. -/
theorem mpWriter_envG (P : Params) (hL : MpLocs P) (tid : Nat) :
    TripleEnv (E P tid)
      (fun s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
        Mem.loadInt s.dmem P.d 4 = none ∧ W1 P σ)
      mpWriter (fun _ σ => W3 P σ) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold mpWriter
  vcgen
  all_goals simp only [fenceMono_le_envG] at *
  case vc1 => simp
  case vc3 => simp
  case vc2 s σ0 hpre σ1 hf1 rng _ =>
    obtain ⟨-, hx1, -, -, hW⟩ := hpre
    simpa [hx1] using (vc_w1 hL tid σ1 (W1.fence hW hf1)).1
  case vc4 s σ0 hpre σ1 hf1 rng dm σ2 hd σ3 hf2 =>
    obtain ⟨hx0, hx1, hdf, hdd, -⟩ := hpre
    simp [hx1, hdd] at hd
    simp [hx0, hd.1, hdf]
  case vc5 s σ0 hpre σ1 hf1 rng dm σ2 hd σ3 hf2 =>
    obtain ⟨hx0, hx1, -, hdd, hW⟩ := hpre
    simp [hx0, hx1, hdd] at hd ⊢
    have hW2 : W2 P σ2 := by
      rcases hd.2 with hst | hst <;> exact (vc_w1 hL tid σ1 (W1.fence hW hf1)).2 _ σ2 hst
    exact (vc_w2 hL tid σ3 (W2.fence hW2 hf2)).1
  case vc6 s σ0 hpre σ1 hf1 rng dm σ2 hd σ3 hf2 b σ4 hst4 σ5 hf4 =>
    obtain ⟨hx0, hx1, -, hdd, hW⟩ := hpre
    simp [hx0, hx1, hdd] at hd hst4
    have hW2 : W2 P σ2 := by
      rcases hd.2 with hst | hst <;> exact (vc_w1 hL tid σ1 (W1.fence hW hf1)).2 _ σ2 hst
    exact W3.fence ((vc_w2 hL tid σ3 (W2.fence hW2 hf2)).2 _ σ4 hst4) hf4

end Writer

/-! ## The reader -/

section Reader

variable [Executable.ValidLayout (layout mpReader)]

local instance mpReader.env : CodeEnv := ⟨layout mpReader⟩

/-- The reader's table: `R1` at `spin`; at `done_r`, under the clean flag,
`W4 = 1`. -/
abbrev readerTable (P : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (E P tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
    Mem.loadInt s.dmem P.d 4 = none ∧
    ((lb = "spin" ∧ R1 P σ.1) ∨ (lb = "done_r" ∧ (σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 1)))

/-- The reader's table with its end facts: `R1` at `spin`; at `done_r`, `R4`
and, under the clean flag, `W4 = 1`. -/
abbrev readerTableP (P : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (E P tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
    Mem.loadInt s.dmem P.d 4 = none ∧
    ((lb = "spin" ∧ R1 P σ.1) ∨ (lb = "done_r" ∧ R4 P σ.1 ∧ (σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 1)))

/-- **The MP reader on `EnvG`, with its end facts** (counted, partial): every
run that reaches the end has the world and a seen flag message (`R4`), and
`W4 = 1` under the clean flag. -/
theorem mpReader_envGP (P : Params) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (E P tid))
      (fun s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
        Mem.loadInt s.dmem P.d 4 = none ∧ R1 P σ.1)
      mpReader (fun s σ => R4 P σ.1 ∧ (σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 1)) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTableP P tid) (hP := by funext s g; simp [readerTableP])
  cfg_cases_env [mpReader]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdf, hdd, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  case vc1 => simp
  case vc2 => simp [hx0, hdf]
  case vc3 => simp
  case vc5 => simp
  case vc6 => simp
  case vc4 =>
    -- the back edge (`cbz` taken): `R1` again; the counter moved
    rename_i s σ0 b σ1 hst1 hcbz σ2 hf _
    simp only [fenceMono_le_counted, fenceMono_le_envG, SharedEnv.counted_step, envG_step_load] at hst1 hf
    simp [hx0] at hst1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdf], by simp [hdd],
      .inl ⟨rfl, R1.fence ((vc_r1 tid σ0.1 hT) _ σ1.1 hst1.1).1 hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  case vc7 =>
    -- `cbz` not taken, then the data load
    rename_i s σ0 b σ1 hst1 hcbz σ2 hf rng v σ3 hld _
    simp only [fenceMono_le_counted, fenceMono_le_envG, SharedEnv.counted_step, envG_step_load] at hst1 hf
    simp [hx0] at hst1
    have hR3 : R3 P σ2.1 := R3.fence (((vc_r1 tid σ0.1 hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf.1
    simp [hx1, hdd] at hld
    obtain ⟨w, ⟨hst3, -⟩, rfl⟩ := hld
    refine ⟨by simp [hx0], by simp [hx1], by simp [hdf], by simp [hdd], .inr ⟨rfl, vc_r3_world tid σ2.1 hR3 w σ3.1 hst3,
      fun hcl => ?_⟩⟩
    rw [vc_r3 tid σ2.1 hR3 w σ3.1 hst3 hcl]
    simp
  case vc1 => exact hT

/-- **The MP reader on `EnvG`** (counted, partial): every run that reaches
the end has `W4 = 1` under the clean flag (`mpReader_envGP`, weakened). -/
theorem mpReader_envG (P : Params) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (E P tid))
      (fun s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
        Mem.loadInt s.dmem P.d 4 = none ∧ R1 P σ.1)
      mpReader (fun s σ => σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 1) (fun _ _ _ => False) :=
  fun s g hp pc hpl => (mpReader_envGP P tid s g hp pc hpl).mono fun _ h => h.imp (And.imp_right And.right) id

/-- The reader without the counter. -/
theorem mpReader_envG' (P : Params) (tid : Nat) :
    PartialTripleEnv (E P tid)
      (fun s σ => ∃ _ : Nat, s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧
        Mem.loadInt s.dmem P.f 4 = none ∧ Mem.loadInt s.dmem P.d 4 = none ∧ R1 P σ)
      mpReader (fun s σ => ∃ _ : Nat, σ.cl → s.regs.X4.toBitVec.setWidth 32 = 1) (fun _ _ _ => ∃ _ : Nat, False) :=
  (mpReader_envG P tid).uncount

end Reader

end Kraken.Promising.SLR.EnvG.MpSmoke
