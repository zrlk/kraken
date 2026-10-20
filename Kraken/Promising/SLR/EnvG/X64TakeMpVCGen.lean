/-
**Part 5: the x64 writing reader by `vcgen`
on `EnvGTX`** (the `X64MpVCGen.mpReaderX_envGP` / `TakeMpVCGen` pattern).

- `takeReaderX_envGT`: the reader (`spin: movl; cmpl; je; movl $43; movl`),
  a `PartialTripleEnv` in the counted `EnvGTX` by `cfgEnv_partial` with a
  two-label table: `K1` at `spin`; at `done_t`, `Own43` (all of `Dt`, maximal
  write `(43, tw)`) and, under the clean flag, `ebx = 43`. One `vcgen` call
  per cut; the goals are discharged by the isolated VCs of
  `EnvG/X64TakeMp.lean`, restated at an address given by an equation.
-/
import Kraken.Promising.SLR.EnvG.X64TakeMp
import Kraken.EnvCfg

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp
open Kraken.Promising.X64.EnvG.MpSmoke

namespace Kraken.Promising.X64.EnvG.TakeMp

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The VCs at an address and value given by equations -/

theorem vc_k1_step {P : Params} (tid : Nat) (σ : EStateX) (h : K1 P σ) {a : BitVec 64} (ha : a = P.f) :
    ∀ v (σ' : EStateX), (ETX P tid).step (.load .plain false a 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → K1 P σ') ∧ (BitVec.setWidth 32 v ≠ 0 → K2 P σ') := by
  subst ha; exact vc_k1 tid σ h

theorem vc_k2_ok {P : Params} (tid : Nat) (σ : EStateX) (h : K2 P σ) {a : BitVec 64} {v : Val}
    (ha : a = P.d) (hv : v = 43#128) : (ETX P tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; exact (vc_k2 tid σ h).1

theorem vc_k2_step {P : Params} (tid : Nat) (σ : EStateX) (h : K2 P σ) {a : BitVec 64} {v : Val}
    (ha : a = P.d) (hv : v = 43#128) :
    ∀ b (σ' : EStateX), (ETX P tid).step (.store .plain false a 4 v) σ b σ' → K3 P σ' := by
  subst ha hv; exact (vc_k2 tid σ h).2

theorem vc_k3_step {P : Params} (tid : Nat) (σ : EStateX) (h : K3 P σ) {a : BitVec 64} (ha : a = P.d) :
    ∀ v (σ' : EStateX), (ETX P tid).step (.load .plain false a 4) σ v σ' →
      Own43 P σ'.r ∧ (σ'.cl → v = 43#128) := by
  subst ha; exact vc_k3 tid σ h

variable [layout : _root_.Layout] [Executable.ValidLayout (layout takeReaderX)]

local instance takeReaderX.env : CodeEnv := ⟨layout takeReaderX⟩

/-- The reader's precondition (and frame): `rdi = f`, `rsi = d`, neither word
in `dmem` (`X64MpVCGen.FrameRX`). -/
abbrev FrameTX (P : Params) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = P.f ∧ s.regs.get64 .rsi = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
    Mem.loadInt s.dmem P.d 4 = none

/-- The reader's table: `K1` at `spin`; at `done_t`, `Own43` and, under the
clean flag, `ebx = 43`. -/
abbrev readerTableKX (P : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ETX P tid)).State → Prop :=
  fun lb s σ => FrameTX P s ∧
    ((lb = "spin" ∧ K1 P σ.1) ∨
      (lb = "done_t" ∧ Own43 P σ.1.r ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 43)))

/-- **The x64 writing reader on `EnvGTX`** (counted, partial): every run
that reaches the end holds all of `Dt` with maximal write `(43, tw)`, and
under the clean flag has `ebx = 43`. -/
theorem takeReaderX_envGT (P : Params) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (ETX P tid))
      (fun s σ => FrameTX P s ∧ K1 P σ.1)
      takeReaderX (fun s σ => Own43 P σ.1.r ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 43))
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTableKX P tid) (hP := by funext s g; simp [readerTableKX])
  cfg_cases_env [takeReaderX]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre hl =>
    obtain ⟨⟨⟨hx0, -, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx0
    simp [hx0] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the back edge (`je` taken): `K1` again; the counter moved
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK := (vc_k1_step tid σ.1 hT (by simp [hx0]) w σ1.1 hst.1).1 (by simpa using hz)
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
        by simpa using hdd⟩, .inl ⟨rfl, K1.fence (K1.fence hK hf1.1) hf2.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    obtain ⟨⟨⟨-, hx1, -, hdd⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1, hdd]
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : K2 P σ3.1 := K2.fence (K2.fence
        ((vc_k1_step tid σ.1 hT (by simp [hx0]) w σ1.1 hst.1).2 (by simpa using hz)) hf1.1) hf2.1
      exact vc_k2_ok tid σ3.1 hK2 (by simp [hx1]) (by decide)
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 b σ4 hst hdm =>
    obtain ⟨⟨⟨-, hx1, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1] <;> trivial
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 b σ4 hst w σ5 hld2 =>
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : K2 P σ3.1 := K2.fence (K2.fence
        ((vc_k1_step tid σ.1 hT (by simp [hx0]) u σ1.1 hst1.1).2 (by simpa using hz)) hf1.1) hf2.1
      have hK3 := vc_k2_step tid σ3.1 hK2 (by simp [hx1]) (by decide) b σ4.1 hst.1
      rcases hld2 with ⟨y, hm, -, -⟩ | ⟨-, y, hst2, rfl⟩
      · simp [hx1, hdd] at hm
      · have h5 := vc_k3_step tid σ4.1 hK3 (by simp [hx1]) y σ5.1 hst2.1
        refine ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf, by simpa using hdd⟩,
          .inr ⟨rfl, h5.1, fun hcl => ?_⟩⟩
        obtain rfl := h5.2 hcl
        simp
  case vc1 s σ pre =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    exact hT

end Kraken.Promising.X64.EnvG.TakeMp

#print axioms Kraken.Promising.X64.EnvG.TakeMp.takeReaderX_envGT
