/-
**The x64 MP smoke test, whole threads by `vcgen`**: the programs and the per-thread
proofs on `EnvGX` (`EnvG` restricted to `[(f, 4), (d, 4)]`, `Arch.tso`).

- `mpWriterX`: `movl $42, %eax; movl %eax, (%rsi); movl $1, %ecx;
  movl %ecx, (%rdi)` (`rdi = f`, `rsi = d`). `mpWriterX_envG`: a `TripleEnv`
  from `W1` to `W3`, one `vcgen` call.
- `mpReaderX`: `spin: movl (%rdi), %eax; cmpl $0, %eax; je spin;
  movl (%rsi), %ebx; done_r:`. `mpReaderX_envGP`: a `PartialTripleEnv` in the
  counted `EnvGX` by `cfgEnv_partial` with a two-label table; at `done_r`,
  `R4` and, under the clean flag, `ebx = 42`.

`vcgen` steps the silent instructions by `envMonoX_lift_spec`
(`EnvG/X64VCGen.lean`); the table predicates are monotone under `FenceLe`.
-/
import Kraken.Promising.SLR.EnvG.X64MpSmoke
import Kraken.Promising.SLR.EnvG.X64VCGen
import Kraken.X64.Parser

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.MpSmoke

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The programs -/

/-- The x64 MP writer: data `42` to `(%rsi)`, then flag `1` to `(%rdi)`. -/
def mpWriterX : Program := parse("
  movl $42, %eax
  movl %eax, (%rsi)
  movl $1, %ecx
  movl %ecx, (%rdi)
")

/-- The x64 MP reader: spin until the flag at `(%rdi)` is non-zero, then load
the data at `(%rsi)` into `ebx`. -/
def mpReaderX : Program := parse("
spin:
  movl (%rdi), %eax
  cmpl $0, %eax
  je spin
  movl (%rsi), %ebx
done_r:
")

/-! ## The table predicates are monotone under fences -/

theorem W1.fence {P : Params} {σ σ' : EStateX} (h : W1 P σ) (hf : FenceLe σ σ') : W1 P σ' := by
  unfold W1; rw [hf.g, hf.r]; exact h

theorem W2.fence {P : Params} {σ σ' : EStateX} (h : W2 P σ) (hf : FenceLe σ σ') : W2 P σ' := by
  unfold W2 Own1; rw [hf.g, hf.r, hf.vwOld]; exact h

theorem W3.fence {P : Params} {σ σ' : EStateX} (h : W3 P σ) (hf : FenceLe σ σ') : W3 P σ' := by
  unfold W3; rw [hf.g, hf.r]; exact h

theorem R1G.fence {P : Params} {φ : Pred} {σ σ' : EStateX} (h : R1G P φ σ) (hf : FenceLe σ σ') : R1G P φ σ' := by
  unfold R1G; rw [hf.g, hf.r, hf.getFwd]; exact h

theorem R3G.fence {P : Params} {φ : Pred} {σ σ' : EStateX} (h : R3G P φ σ) (hf : FenceLe σ σ') : R3G P φ σ' := by
  obtain ⟨hw, tsF, vF, h1, h2, h3⟩ := h
  exact ⟨by rw [hf.g, hf.r]; exact hw, tsF, vF, by rw [hf.snap]; exact h1, h2, Nat.le_trans h3 hf.vrNew⟩

theorem R1.fence {P : Params} {σ σ' : EStateX} (h : R1 P σ) (hf : FenceLe σ σ') : R1 P σ' :=
  R1G.fence (φ := P.φ) h hf

theorem R3.fence {P : Params} {σ σ' : EStateX} (h : R3 P σ) (hf : FenceLe σ σ') : R3 P σ' :=
  R3G.fence (φ := P.φ) h hf

/-! ## The VCs at an address and value given by equations

`vcgen`'s goals state the address and value as register expressions; a step
hypothesis cannot be rewritten by `simp` (the outcome's type depends on the
access), so the VCs are restated at any `a = …`, `v = …`. -/

theorem vc_w1_ok {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W1 P σ) {a : BitVec 64} {v : Val}
    (ha : a = P.d) (hv : v = dataVal) : (E P tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; exact (vc_w1 hL tid σ h).1

theorem vc_w1_step {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W1 P σ) {a : BitVec 64} {v : Val}
    (ha : a = P.d) (hv : v = dataVal) :
    ∀ b (σ' : EStateX), (E P tid).step (.store .plain false a 4 v) σ b σ' → W2 P σ' := by
  subst ha hv; exact (vc_w1 hL tid σ h).2

theorem vc_w2_ok {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W2 P σ) {a : BitVec 64} {v : Val}
    (ha : a = P.f) (hv : v = 1#128) : (E P tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; exact (vc_w2 hL tid σ h).1

theorem vc_w2_step {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W2 P σ) {a : BitVec 64} {v : Val}
    (ha : a = P.f) (hv : v = 1#128) :
    ∀ b (σ' : EStateX), (E P tid).step (.store .plain false a 4 v) σ b σ' → W3 P σ' := by
  subst ha hv; exact (vc_w2 hL tid σ h).2

theorem vc_r1G_step {P : Params} {φ : Pred} (tid : Nat) (σ : EStateX) (h : R1G P φ σ) {a : BitVec 64}
    (ha : a = P.f) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false a 4) σ v σ' →
      R1G P φ σ' ∧ (BitVec.setWidth 32 v ≠ 0 → R3G P φ σ') := by
  subst ha; exact vc_r1G tid σ h

theorem vc_r3G_step {P : Params} {φ : Pred} (hφ : FlagLaw P.Dt φ) (tid : Nat) (σ : EStateX) (h : R3G P φ σ)
    {a : BitVec 64} (ha : a = P.d) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false a 4) σ v σ' → R4G P φ σ' ∧ (σ'.cl → v = dataVal) := by
  subst ha; exact fun v σ' hs => ⟨vc_r3_worldG tid σ h v σ' hs, vc_r3G hφ tid σ h v σ' hs⟩

theorem vc_r1_step {P : Params} (tid : Nat) (σ : EStateX) (h : R1 P σ) {a : BitVec 64} (ha : a = P.f) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false a 4) σ v σ' →
      R1 P σ' ∧ (BitVec.setWidth 32 v ≠ 0 → R3 P σ') :=
  vc_r1G_step (φ := P.φ) tid σ h ha

theorem vc_r3_step {P : Params} (tid : Nat) (σ : EStateX) (h : R3 P σ) {a : BitVec 64} (ha : a = P.d) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false a 4) σ v σ' → R4 P σ' ∧ (σ'.cl → v = dataVal) :=
  vc_r3G_step (flagPred_law _) tid σ h ha

variable [layout : _root_.Layout]

/-! ## The writer -/

section Writer

local instance mpWriterX.env : CodeEnv := ⟨layout mpWriterX⟩

/-- **The x64 MP writer on `EnvG`**: from `W1` the writer ends in `W3`. -/
theorem mpWriterX_envG (P : Params) (hL : MpLocs P) (tid : Nat) :
    TripleEnv (E P tid)
      (fun s σ => s.regs.get64 .rdi = P.f ∧ s.regs.get64 .rsi = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
        Mem.loadInt s.dmem P.d 4 = none ∧ W1 P σ)
      mpWriterX (fun _ σ => W3 P σ) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold mpWriterX
  vcgen
  all_goals simp only [fenceMonoX_le_within, fenceMonoX_le_envG] at *
  case vc1 s σ0 hpre σ1 hl hf =>
    obtain ⟨-, hx1, -, -, hW⟩ := hpre
    simp at hx1
    exact vc_w1_ok hL tid σ1 (W1.fence hW hf) (by simp [hx1]) (by simp [dataVal])
  case vc2 s σ0 hpre σ1 dm σ2 hd σ3 hl2 hf1 hf2 =>
    obtain ⟨hx0, hx1, -, hdd, hW⟩ := hpre
    simp at hx0 hx1
    rcases hd with ⟨hsome, -, -⟩ | ⟨-, -, b, hst⟩
    · simp [hx1, hdd] at hsome
    · have hW2 := vc_w1_step hL tid σ1 (W1.fence hW hf1) (by simp [hx1]) (by simp [dataVal]) b σ2 hst
      exact vc_w2_ok hL tid σ3 (W2.fence hW2 hf2) (by simp [hx0]) (by simp)
  case vc3 s σ0 hpre σ1 dm σ2 hd σ3 dm' σ4 hd' hf1 hf2 =>
    obtain ⟨hx0, hx1, hdf, hdd, hW⟩ := hpre
    simp at hx0 hx1
    rcases hd with ⟨hsome, -, -⟩ | ⟨-, rfl, b, hst⟩
    · simp [hx1, hdd] at hsome
    · have hW2 := vc_w1_step hL tid σ1 (W1.fence hW hf1) (by simp [hx1]) (by simp [dataVal]) b σ2 hst
      rcases hd' with ⟨hsome, -, -⟩ | ⟨-, -, b', hst'⟩
      · simp [hx0, hdf] at hsome
      · exact vc_w2_step hL tid σ3 (W2.fence hW2 hf2) (by simp [hx0]) (by simp) b' σ4 hst'

end Writer

/-! ## The reader -/

section Reader

variable [Executable.ValidLayout (layout mpReaderX)]

local instance mpReaderX.env : CodeEnv := ⟨layout mpReaderX⟩

/-- The reader's precondition (and frame): `rdi = f`, `rsi = d`, neither word
in `dmem`. -/
abbrev FrameRX (P : Params) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = P.f ∧ s.regs.get64 .rsi = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
    Mem.loadInt s.dmem P.d 4 = none

/-- The reader's table for the flag predicate `φ`: `R1G` at `spin`;
at `done_r`, `R4G` and, under the clean flag, `ebx = 42`. -/
abbrev readerTablePG (P : Params) (φ : Pred) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (E P tid)).State → Prop :=
  fun lb s σ => FrameRX P s ∧
    ((lb = "spin" ∧ R1G P φ σ.1) ∨
      (lb = "done_r" ∧ R4G P φ σ.1 ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 42)))

/-- **The x64 MP reader on `EnvG`, with its end facts**, for any flag
predicate `φ` with `FlagLaw` (counted, partial). -/
theorem mpReaderX_envGPG (P : Params) (φ : Pred) (hφ : FlagLaw P.Dt φ) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (E P tid))
      (fun s σ => FrameRX P s ∧ R1G P φ σ.1)
      mpReaderX (fun s σ => R4G P φ σ.1 ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 42))
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTablePG P φ tid) (hP := by funext s g; simp [readerTablePG])
  cfg_cases_env [mpReaderX]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre hl =>
    obtain ⟨⟨⟨hx0, -, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx0
    simp [hx0] <;> trivial
  case vc2 s σ pre x σ1 hld σ2 hf1 hz σ3 hf2 =>
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envG] at hf1 hf2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hR := vc_r1G_step tid σ.1 hT (by simp [hx0]) v σ1.1 hst.1
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
        by simpa using hdd⟩, .inl ⟨rfl, R1G.fence (R1G.fence hR.1 hf1.1) hf2.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 s σ pre x σ1 hld σ2 hf1 hz σ3 hf2 hl =>
    obtain ⟨⟨⟨-, hx1, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1] <;> trivial
  case vc4 s σ pre x σ1 hld σ2 hf1 hz σ3 hf2 y σ4 hld2 =>
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envG] at hf1 hf2
    simp at hz
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hR3 : R3G P φ σ3.1 := R3G.fence (R3G.fence
        ((vc_r1G_step tid σ.1 hT (by simp [hx0]) v σ1.1 hst.1).2 hz) hf1.1) hf2.1
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
      · simp [hx1, hdd] at hm
      · have h4 := vc_r3G_step hφ tid σ3.1 hR3 (by simp [hx1]) w σ4.1 hst2.1
        refine ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf, by simpa using hdd⟩,
          .inr ⟨rfl, h4.1, fun hcl => ?_⟩⟩
        obtain rfl := h4.2 hcl
        simp [dataVal]
  case vc1 s σ pre =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    exact hT

/-- The reader's table: `R1` at `spin`; at `done_r`, `R4` and, under the
clean flag, `ebx = 42`. -/
abbrev readerTableP (P : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (E P tid)).State → Prop :=
  fun lb s σ => FrameRX P s ∧
    ((lb = "spin" ∧ R1 P σ.1) ∨
      (lb = "done_r" ∧ R4 P σ.1 ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 42)))

/-- **The x64 MP reader on `EnvG`, with its end facts** (counted, partial). -/
theorem mpReaderX_envGP (P : Params) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (E P tid))
      (fun s σ => FrameRX P s ∧ R1 P σ.1)
      mpReaderX (fun s σ => R4 P σ.1 ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 42))
      (fun _ _ _ => False) :=
  mpReaderX_envGPG P P.φ (flagPred_law _) tid

end Reader

end Kraken.Promising.X64.EnvG.MpSmoke
