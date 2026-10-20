/-
**Part 4: the x64 relay and reader by
`vcgen`** (the `swpl` relay's `EnvG/RelaySwplVCGen.lean` and the x64 take route's
`EnvG/X64TakeMpVCGen.lean` pattern).

- `relayX_envGTC`: the relay (`spin: movl; cmpl; je; movl $43; movl $1;
  xchgl`), a `PartialTripleEnv` in the counted `EnvGTCX` with plan
  `mpPlan rp.Q`, by `cfgEnv_partial` with a two-label table: `RK1` at
  `spin`, `RK4` (the token `W2`) at `done_y`. The `xchgl` goes through the
  generic `MachineWP.xchg32_shared_spec` (one `.acqRel` RMW writing `ecx`).
- `readerX_envGT`: x64 MP's reader text `mpReaderX` on `f2`, in the counted
  `EnvGTX` (the x64 take route's `ETX`): `DK1` at `spin`; at `done_r`, `Own43` and, under
  the clean flag, `ebx = 43`.

One `vcgen` call per cut; the goals are discharged by the VCs of
`EnvG/X64RelayXchgSpec.lean`, restated at an address and value given by
equations. The writer is x64 MP's (`mpWriterX_envG`).
-/
import Kraken.Promising.SLR.EnvG.X64RelayXchgSpec
import Kraken.Promising.SLR.EnvG.X64MpVCGen
import Kraken.EnvCfg

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp
open Kraken.Promising.X64.EnvG.MpSmoke Kraken.Promising.X64.EnvG.TakeMp

namespace Kraken.Promising.X64.EnvG.RelayX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The VCs at an address and value given by equations -/

section At

variable {rp : RP} {tid : Nat} {a : BitVec 64}

theorem vc_r1_at (σ : EStateX) (h : RK1 rp σ) (ha : a = rp.f1) :
    ∀ v (σ' : EStateX), (ERX rp tid).step (.load .plain false a 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → RK1 rp σ') ∧ (BitVec.setWidth 32 v ≠ 0 → RK2 rp σ') := by
  subst ha; exact vc_r1 tid σ h

theorem vc_r2_ok_at (hL : MpLocs rp.Q) (σ : EStateX) (h : RK2 rp σ) {v : Val} (ha : a = rp.d)
    (hv : v = 43#128) : (ERX rp tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; exact (vc_r2 hL tid σ h).1

theorem vc_r2_at (hL : MpLocs rp.Q) (σ : EStateX) (h : RK2 rp σ) {v : Val} (ha : a = rp.d)
    (hv : v = 43#128) :
    ∀ b (σ' : EStateX), (ERX rp tid).step (.store .plain false a 4 v) σ b σ' → RK3 rp σ' := by
  subst ha hv; exact (vc_r2 hL tid σ h).2

theorem vc_r3_ok_at (hL : MpLocs rp.Q) (σ : EStateX) (h : RK3 rp σ) {op : Val → Option Val} (ha : a = rp.f2)
    (hop : ∀ x y, op x = some y → y = 1#128) : (ERX rp tid).ok (.rmw .acqRel a 4 op) σ := by
  subst ha; exact (vc_r3 hL tid σ h op hop).1

theorem vc_r3_at (hL : MpLocs rp.Q) (σ : EStateX) (h : RK3 rp σ) {op : Val → Option Val} (ha : a = rp.f2)
    (hop : ∀ x y, op x = some y → y = 1#128) :
    ∀ old (σ' : EStateX), (ERX rp tid).step (.rmw .acqRel a 4 op) σ old σ' → RK4 rp σ' := by
  subst ha; exact (vc_r3 hL tid σ h op hop).2

theorem vc_d1_at {Q : Params} (σ : EStateX) (h : DK1 Q σ) (ha : a = Q.f) :
    ∀ v (σ' : EStateX), (EDX Q tid).step (.load .plain false a 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → DK1 Q σ') ∧ (BitVec.setWidth 32 v ≠ 0 → DK2 Q σ') := by
  subst ha; exact vc_d1 tid σ h

theorem vc_d2_at {Q : Params} (σ : EStateX) (h : DK2 Q σ) (ha : a = Q.d) :
    ∀ v (σ' : EStateX), (EDX Q tid).step (.load .plain false a 4) σ v σ' →
      Own43 Q σ'.r ∧ (σ'.cl → v = 43#128) := by
  subst ha; exact vc_d2 tid σ h

end At

/-- The `xchgl`'s operation writes `ecx`'s low word, here `1`. -/
theorem rmwOp128_one {r : BitVec 64} (hr : BitVec.setWidth 32 r = 1#32) :
    ∀ x y, rmwOp128 Width.W32 (fun _ => some (BitVec.setWidth 32 r)) x = some y → y = 1#128 := by
  intro x y h
  simp [rmwOp128, hr] at h
  exact h.symm

variable [layout : _root_.Layout]

/-! ## The relay -/

section Relay

variable [Executable.ValidLayout (layout relayX)]

local instance relayX.env : CodeEnv := ⟨layout relayX⟩

/-- The relay's precondition (and frame): `rdi = f1`, `rsi = d`, `rdx = f2`,
none of the three words in `dmem`. -/
abbrev RFrameX (rp : RP) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = rp.f1 ∧ s.regs.get64 .rsi = rp.d ∧ s.regs.get64 .rdx = rp.f2 ∧
    Mem.loadInt s.dmem rp.f1 4 = none ∧ Mem.loadInt s.dmem rp.d 4 = none ∧ Mem.loadInt s.dmem rp.f2 4 = none

/-- The relay's table: `RK1` at `spin`, `RK4` at `done_y`. -/
abbrev relayTableX (rp : RP) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ERX rp tid)).State → Prop :=
  fun lb s σ => RFrameX rp s ∧ ((lb = "spin" ∧ RK1 rp σ.1) ∨ (lb = "done_y" ∧ RK4 rp σ.1))

/-- **The x64 relay on `EnvGTCX`** (counted, partial): from `RK1` every run
that reaches the end keeps the token `W2`, having taken `Dt`, written `43`
and released `Dt` to `f2` by `xchgl`. -/
theorem relayX_envGTC (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (ERX rp tid))
      (fun s σ => RFrameX rp s ∧ RK1 rp σ.1) relayX (fun _ σ => RK4 rp σ.1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (relayTableX rp tid) (hP := by funext s g; simp [relayTableX])
  cfg_cases_env [relayX]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre hl =>
    obtain ⟨⟨⟨hx0, -, -, -, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx0
    simp [hx0] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the back edge (`je` taken): `RK1` again; the counter moved
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTCX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK := (vc_r1_at σ.1 hT (by simp [hx0]) w σ1.1 hst.1).1 (by simpa using hz)
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf,
        by simpa using hdd, by simpa using hdg⟩, .inl ⟨rfl, RK1.fence (RK1.fence hK hf1.1) hf2.1⟩⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    obtain ⟨⟨⟨-, hx1, -, -, hdd, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1, hdd]
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTCX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : RK2 rp σ3.1 := RK2.fence (RK2.fence
        ((vc_r1_at σ.1 hT (by simp [hx0]) w σ1.1 hst.1).2 (by simpa using hz)) hf1.1) hf2.1
      simp only [SharedEnv.counted_ok]
      exact vc_r2_ok_at hL σ3.1 hK2 (by simp [hx1]) (by decide)
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 b σ4 hst σ5 hf3 =>
    obtain ⟨⟨⟨-, -, hx2, -, -, hdg⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx2
    simp [hx2, hdg]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 b σ4 hst σ5 hf3 =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTCX] at hf1 hf2 hf3
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst1, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : RK2 rp σ3.1 := RK2.fence (RK2.fence
        ((vc_r1_at σ.1 hT (by simp [hx0]) w σ1.1 hst1.1).2 (by simpa using hz)) hf1.1) hf2.1
      have hK3 := vc_r2_at hL σ3.1 hK2 (by simp [hx1]) (by decide) b σ4.1 hst.1
      simp only [SharedEnv.counted_ok]
      exact vc_r3_ok_at hL σ5.1 (RK3.fence hK3 hf3.1) (by simp [hx2]) (rmwOp128_one (by simp))
  case vc7 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 b σ4 hst σ5 hf3 old σ6 hx =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTCX] at hf1 hf2 hf3
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst1, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : RK2 rp σ3.1 := RK2.fence (RK2.fence
        ((vc_r1_at σ.1 hT (by simp [hx0]) w σ1.1 hst1.1).2 (by simpa using hz)) hf1.1) hf2.1
      have hK3 := vc_r2_at hL σ3.1 hK2 (by simp [hx1]) (by decide) b σ4.1 hst.1
      have h4 := vc_r3_at hL σ5.1 (RK3.fence hK3 hf3.1) (by simp [hx2]) (rmwOp128_one (by simp)) old σ6.1 hx.1
      exact ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], hdf, hdd, hdg⟩, .inr ⟨rfl, h4⟩⟩
  case vc1 s σ pre =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    exact hT

end Relay


/-! ## The reader -/

section Reader

variable [Executable.ValidLayout (layout mpReaderX)]

local instance mpReaderX.envRelay : CodeEnv := ⟨layout mpReaderX⟩

/-- The reader's table on `f2`: `DK1` at `spin`; at `done_r`, `Own43` and,
under the clean flag, `ebx = 43`. -/
abbrev readerTableDX (Q : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (EDX Q tid)).State → Prop :=
  fun lb s σ => FrameRX Q s ∧
    ((lb = "spin" ∧ DK1 Q σ.1) ∨
      (lb = "done_r" ∧ Own43 Q σ.1.r ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 43)))

/-- **x64 MP's reader text on `f2`, on `EnvGTX`** (counted, partial): every
run that reaches the end holds all of `Dt` with maximal write `(43, tw)`, and
under the clean flag has `ebx = 43`. -/
theorem readerX_envGT (Q : Params) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (EDX Q tid))
      (fun s σ => FrameRX Q s ∧ DK1 Q σ.1)
      mpReaderX (fun s σ => Own43 Q σ.1.r ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 43))
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTableDX Q tid) (hP := by funext s g; simp [readerTableDX])
  cfg_cases_env [mpReaderX]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre hl =>
    obtain ⟨⟨⟨hx0, -, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx0
    simp [hx0] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the back edge (`je` taken): `DK1` again; the counter moved
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK := (vc_d1_at σ.1 hT (by simp [hx0]) w σ1.1 hst.1).1 (by simpa using hz)
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
        by simpa using hdd⟩, .inl ⟨rfl, DK1.fence (DK1.fence hK hf1.1) hf2.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 hn =>
    obtain ⟨⟨⟨-, hx1, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1] <;> trivial
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 w σ5 hld2 =>
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : DK2 Q σ3.1 := DK2.fence (DK2.fence
        ((vc_d1_at σ.1 hT (by simp [hx0]) u σ1.1 hst1.1).2 (by simpa using hz)) hf1.1) hf2.1
      rcases hld2 with ⟨y, hm, -, -⟩ | ⟨-, y, hst2, rfl⟩
      · simp [hx1, hdd] at hm
      · have h5 := vc_d2_at σ3.1 hK2 (by simp [hx1]) y σ5.1 hst2.1
        refine ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf, by simpa using hdd⟩,
          .inr ⟨rfl, h5.1, fun hcl => ?_⟩⟩
        obtain rfl := h5.2 hcl
        simp
  case vc1 s σ pre =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    exact hT

end Reader

end Kraken.Promising.X64.EnvG.RelayX

#print axioms Kraken.Promising.X64.EnvG.RelayX.relayX_envGTC
#print axioms Kraken.Promising.X64.EnvG.RelayX.readerX_envGT
