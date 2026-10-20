/-
**Part 6: the SPSC threads by `vcgen` on
`EnvGTX`** (the `X64TakeMpVCGen` pattern): one `cfgEnv_partial` table per
thread, one `vcgen` call per cut, the goals discharged by the VCs of
`EnvG/X64SpscVC.lean` restated at an address and value given by equations
(`…_at`).

- `spscProducerX_envGT`: table `prodTable` (`PR 1` at `producer`; at
  `produce` round `k ∈ {1,2,3}` with `r8d = k` and `PR k`; at `pfull` also
  `eax = eT k`, `ecx = tNew k`; at `pdone` all of `T`). Frame `FrameP`
  (`rbx = b`, `rdi = t`, `rsi = h`, no 4-byte word in the private memory).
- `spscConsumerX_envGT`: table `consTable` (`CS` at `consumer`; `CR k` at
  `cempty k`: `CE k`, `eax = eC k`, and under the clean flag the registers
  filled so far, `Got k`; at `cdone`, under the clean flag, `Got 3`:
  `r12d = 1`, `r13d = 2`, `r14d = 3`). The clean flag only decreases along a
  run (`LoadKeep.cl`, `cl_fence`, a store keeps it), so the final flag gives
  every earlier data load's value.
-/
import Kraken.Promising.SLR.EnvG.X64SpscVC
import Kraken.Promising.SLR.EnvG.X64SpscProg
import Kraken.Promising.SLR.EnvG.X64SpscWP
import Kraken.EnvCfg

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.SpscX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The frame of both threads. -/
abbrev FrameP (P : SP) (s : MachineData) : Prop :=
  s.regs.get64 .rbx = P.b ∧ s.regs.get64 .rdi = P.t ∧ s.regs.get64 .rsi = P.h ∧ DFrame s

/-- The producer's table. -/
abbrev prodTable (P : SP) (tid : Nat) : Label → MachineData → (SharedEnv.counted (EP P tid)).State → Prop :=
  fun lb s σ => FrameP P s ∧
    ((lb = "producer" ∧ PR P 1 σ.1) ∨
     (lb = "produce" ∧ ∃ k, (k = 1 ∨ k = 2 ∨ k = 3) ∧ (s.regs.get64 .r8).setWidth 32 = BitVec.ofNat 32 k ∧
        PR P k σ.1) ∨
     (lb = "pfull" ∧ ∃ k, (k = 1 ∨ k = 2 ∨ k = 3) ∧ (s.regs.get64 .r8).setWidth 32 = BitVec.ofNat 32 k ∧
        (s.regs.get64 .rax).setWidth 32 = (eT k).setWidth 32 ∧ (s.regs.get64 .rcx).setWidth 32 = (tNew k).setWidth 32 ∧
        PR P k σ.1) ∨
     (lb = "pdone" ∧ (σ.1.r.wr P.T).q = 1))

/-- The producer's VCs at an address and value given by equations. -/
theorem vcP_loadT_at {P : SP} (hL : SpscLocs P) {tid k : Nat} {σ σ' : EStateX} {v : Val} (h : PR P k σ)
    {a : BitVec 64} (ha : a = P.t) (hs : (EP P tid).step (.load .plain false a 4) σ v σ') : v = eT k ∧ PR P k σ' := by
  subst ha; exact vcP_loadT hL h hs

theorem vcP_spin_at {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 1 ∨ k = 2 ∨ k = 3) {σ σ' : EStateX}
    {v : Val} (h : PR P k σ) {a : BitVec 64} (ha : a = P.h) (hs : (EP P tid).step (.load .plain false a 4) σ v σ') :
    (v.setWidth 32 = (tNew k).setWidth 32 → PR P k σ') ∧ (v.setWidth 32 ≠ (tNew k).setWidth 32 → PX P k σ') := by
  subst ha; exact vcP_spin hL hk3 h hs

theorem vcP_storeB_ok_at {P : SP} (hL : SpscLocs P) {tid k : Nat} {σ : EStateX} (h : PX P k σ)
    {a : BitVec 64} {v : Val} (ha : a = (slot P k).addr) (hv : v = kval k) :
    (EP P tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; exact (vcP_storeB hL h).1

theorem vcP_storeB_at {P : SP} (hL : SpscLocs P) {tid k : Nat} {σ : EStateX} (h : PX P k σ)
    {a : BitVec 64} {v : Val} (ha : a = (slot P k).addr) (hv : v = kval k) :
    ∀ b (σ' : EStateX), (EP P tid).step (.store .plain false a 4 v) σ b σ' → PD P k σ' := by
  subst ha hv; exact (vcP_storeB hL h).2

theorem vcP_storeT_ok_at {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 1 ∨ k = 2 ∨ k = 3) {σ : EStateX}
    (h : PD P k σ) {a : BitVec 64} {v : Val} (ha : a = P.t) (hv : v = tNew k) :
    (EP P tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; exact (vcP_storeT hL hk3 h).1

theorem vcP_storeT_at {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 1 ∨ k = 2 ∨ k = 3) {σ : EStateX}
    (h : PD P k σ) {a : BitVec 64} {v : Val} (ha : a = P.t) (hv : v = tNew k) :
    ∀ b (σ' : EStateX), (EP P tid).step (.store .plain false a 4 v) σ b σ' →
      (k = 1 → PR P 2 σ') ∧ (k = 2 → PR P 3 σ') ∧ (σ'.r.wr P.T).q = 1 := by
  subst ha hv; exact (vcP_storeT hL hk3 h).2

theorem q_fence {x : Loc} {σ σ' : EStateX} (h : (σ.r.wr x).q = 1) (hf : FenceLe σ σ') : (σ'.r.wr x).q = 1 := by
  rw [hf.r]; exact h


section Producer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscProducerX)]

local instance spscProducerX.envP : CodeEnv := ⟨layout spscProducerX⟩

set_option maxHeartbeats 1000000 in
/-- **The x64 SPSC producer on `EnvGTX`** (counted, partial): every run that
reaches the end holds all of `T`. -/
theorem spscProducerX_envGT (P : SP) (hL : SpscLocs P) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (EP P tid))
      (fun s σ => FrameP P s ∧ PR P 1 σ.1) spscProducerX
      (fun _ σ => (σ.1.r.wr P.T).q = 1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (prodTable P tid) (hP := by funext s g; simp [prodTable])
  cfg_cases_env [spscProducerX]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre σ1 hf =>
    -- `producer` → `produce`
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf
    refine ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩,
      .inr (.inl ⟨rfl, 1, .inl rfl, by simp, hT.fence hf.1⟩)⟩
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hx1, -, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 σ3 hf2 af σ4 hf3 =>
    -- `produce` → `pfull`
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hr8
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx1, hdf] at hm
    · obtain ⟨hv, hPR'⟩ := vcP_loadT_at hL hPR (by simp [hx1]) hst.1
      refine ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩,
        .inr (.inr (.inl ⟨rfl, k, hk, by simpa using hr8, ?_, ?_, ((hPR'.fence hf1.1).fence hf2.1).fence hf3.1⟩))⟩
      · subst hv; simp
      · subst hv; rcases hk with rfl | rfl | rfl <;> simp [eT, tNew]
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, -, hx2, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx2
    simp [hx2] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the `je pfull` back edge
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx2, hdf] at hm
    · have hz' : w.setWidth 32 = (tNew k).setWidth 32 := by
        have h0 : w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
        bv_omega
      have hPR' := (vcP_spin_at hL hk hPR (by simp [hx2]) hst.1).1 hz'
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩,
        .inr (.inr (.inl ⟨rfl, k, hk, by simpa using hr8, by simpa using hax, by simpa using hcx,
          (hPR'.fence hf1.1).fence hf2.1⟩))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 => simp
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 hdm =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx2, hdf] at hm
    · have hz' : w.setWidth 32 ≠ (tNew k).setWidth 32 := by
        have h0 : ¬ w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
        bv_omega
      have hPX := (vcP_spin_at hL hk hPR (by simp [hx2]) hst.1).2 hz'
      have hPX' := (((hPX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
      refine vcP_storeB_ok_at hL hPX' ?_ ?_
      · simp [hx0, hax, Reg64s.get_low32]
        rcases hk with rfl | rfl | rfl <;> simp [eT, slot]
      · simp [hr8]
        rcases hk with rfl | rfl | rfl <;> simp [kval]
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 dm σ6 hst hdm =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx2, hdf] at hm
    have hz' : w.setWidth 32 ≠ (tNew k).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
      bv_omega
    have hPX := (vcP_spin_at hL hk hPR (by simp [hx2]) hst0.1).2 hz'
    have hPX' := (((hPX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hPD : PD P k σ6.1 := by
      refine vcP_storeB_at hL hPX' ?_ ?_ _ _ hs.1
      · simp [hx0, hax, Reg64s.get_low32]
        rcases hk with rfl | rfl | rfl <;> simp [eT, slot]
      · simp [hr8]
        rcases hk with rfl | rfl | rfl <;> simp [kval]
    refine vcP_storeT_ok_at hL hk hPD (by simp [hx1]) ?_
    simp [hcx]
    rcases hk with rfl | rfl | rfl <;> simp [tNew]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 dm σ6 hst dm2 σ7 hst2 σ8 hf5 σ9 hf6 hnz σ10 hf7 =>
    -- the `jne produce` back edge (rounds 1, 2)
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx2, hdf] at hm
    have hz' : w.setWidth 32 ≠ (tNew k).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
      bv_omega
    have hPX := (vcP_spin_at hL hk hPR (by simp [hx2]) hst0.1).2 hz'
    have hPX' := (((hPX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hPD : PD P k σ6.1 := by
      refine vcP_storeB_at hL hPX' ?_ ?_ _ _ hs.1
      · simp [hx0, hax, Reg64s.get_low32]
        rcases hk with rfl | rfl | rfl <;> simp [eT, slot]
      · simp [hr8]
        rcases hk with rfl | rfl | rfl <;> simp [kval]
    rcases hst2 with ⟨hv, -⟩ | ⟨-, rfl, b2, hs2⟩
    · simp [hdf] at hv
    have hR := by
      refine vcP_storeT_at hL hk hPD ?_ ?_ _ _ hs2.1
      · simp [hx1]
      · simp [hcx]
        rcases hk with rfl | rfl | rfl <;> simp [tNew]
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf5 hf6 hf7
    simp [hr8] at hnz
    have c0 := hst0.2; have c1 := hs.2; have c2 := hs2.2
    have e1 := hf1.2; have e2 := hf2.2; have e3 := hf3.2; have e4 := hf4.2
    have e5 := hf5.2; have e6 := hf6.2; have e7 := hf7.2
    rcases hk with rfl | rfl | rfl
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩,
        .inr (.inl ⟨rfl, 2, .inr (.inl rfl), by simp [hr8], (((hR.1 rfl).fence hf5.1).fence hf6.1).fence hf7.1⟩)⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg; simp [SharedAccess.tick] at c0 c1 c2; omega
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩,
        .inr (.inl ⟨rfl, 3, .inr (.inr rfl), by simp [hr8], (((hR.2.1 rfl).fence hf5.1).fence hf6.1).fence hf7.1⟩)⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg; simp [SharedAccess.tick] at c0 c1 c2; omega
    · exact absurd (by decide) hnz
  case vc7 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 dm σ6 hst dm2 σ7 hst2 σ8 hf5 σ9 hf6 hnz σ10 hf7
      σ11 hf8 =>
    -- the fall-through after round 3, `jmp pdone`
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx2, hdf] at hm
    have hz' : w.setWidth 32 ≠ (tNew k).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
      bv_omega
    have hPX := (vcP_spin_at hL hk hPR (by simp [hx2]) hst0.1).2 hz'
    have hPX' := (((hPX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hPD : PD P k σ6.1 := by
      refine vcP_storeB_at hL hPX' ?_ ?_ _ _ hs.1
      · simp [hx0, hax, Reg64s.get_low32]
        rcases hk with rfl | rfl | rfl <;> simp [eT, slot]
      · simp [hr8]
        rcases hk with rfl | rfl | rfl <;> simp [kval]
    rcases hst2 with ⟨hv, -⟩ | ⟨-, rfl, b2, hs2⟩
    · simp [hdf] at hv
    have hR := by
      refine vcP_storeT_at hL hk hPD ?_ ?_ _ _ hs2.1
      · simp [hx1]
      · simp [hcx]
        rcases hk with rfl | rfl | rfl <;> simp [tNew]
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf5 hf6 hf7 hf8
    have hq := q_fence (q_fence (q_fence (q_fence hR.2.2 hf5.1) hf6.1) hf7.1) hf8.1
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩, .inr (.inr (.inr ⟨rfl, hq⟩))⟩, .inl (by decide)⟩
  case vc1 s σ pre =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    exact hT

end Producer

/-! ## The consumer -/

/-- The consumer's VCs at an address and value given by equations. -/
theorem vcC_loadH_at {P : SP} (hL : SpscLocs P) {tid : Nat} {σ σ' : EStateX} {v : Val} (h : CS P σ)
    {a : BitVec 64} (ha : a = P.h) (hs : (EC P tid).step (.load .plain false a 4) σ v σ') : v = 0#128 ∧ CE P 0 σ' := by
  subst ha; exact vcC_loadH hL h hs

theorem vcC_spin_at {P : SP} {tid k : Nat} (hk3 : k = 0 ∨ k = 1 ∨ k = 2) {σ σ' : EStateX}
    {v : Val} (h : CE P k σ) {a : BitVec 64} (ha : a = P.t) (hs : (EC P tid).step (.load .plain false a 4) σ v σ') :
    (v.setWidth 32 = (eC k).setWidth 32 → CE P k σ') ∧ (v.setWidth 32 ≠ (eC k).setWidth 32 → CX P k σ') := by
  subst ha; exact vcC_spin hk3 h hs

theorem vcC_data_at {P : SP} (hL : SpscLocs P) {tid k : Nat} {σ σ' : EStateX} {v : Val} (h : CX P k σ)
    {a : BitVec 64} (ha : a = (cslot P k).addr) (hs : (EC P tid).step (.load .plain false a 4) σ v σ') :
    CX P k σ' ∧ (σ'.cl → v = cval k) := by
  subst ha; exact vcC_data hL h hs

theorem vcC_storeH_ok_at {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 0 ∨ k = 1 ∨ k = 2) {σ : EStateX}
    (h : CX P k σ) {a : BitVec 64} {v : Val} (ha : a = P.h) (hv : v = hNew k) :
    (EC P tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; exact (vcC_storeH hL hk3 h).1

theorem vcC_storeH_at {P : SP} (hL : SpscLocs P) {tid k : Nat} (hk3 : k = 0 ∨ k = 1 ∨ k = 2) {σ : EStateX}
    (h : CX P k σ) {a : BitVec 64} {v : Val} (ha : a = P.h) (hv : v = hNew k) :
    ∀ b (σ' : EStateX), (EC P tid).step (.store .plain false a 4 v) σ b σ' →
      ((k = 0 → CE P 1 σ') ∧ (k = 1 → CE P 2 σ')) ∧ σ'.cl = σ.cl := by
  subst ha hv
  intro b σ' hs
  obtain ⟨-, -, -, -, -, -, -, -, hcl, -⟩ := step_storeFactsT hs
  exact ⟨(vcC_storeH hL hk3 h).2 b σ' hs, hcl⟩

theorem cl_fence {σ σ' : EStateX} (hf : FenceLe σ σ') : σ'.cl → σ.cl := fun h => hf.cl ▸ h

/-- The registers the consumer has filled before round `k`, under the clean flag. -/
abbrev Got (k : Nat) (s : MachineData) : Prop :=
  (1 ≤ k → (s.regs.get64 .r12).setWidth 32 = 1) ∧ (2 ≤ k → (s.regs.get64 .r13).setWidth 32 = 2) ∧
    (3 ≤ k → (s.regs.get64 .r14).setWidth 32 = 3)

/-- At `cempty k`. -/
abbrev CR (P : SP) (k : Nat) (s : MachineData) (σ : EStateX) : Prop :=
  CE P k σ ∧ (s.regs.get64 .rax).setWidth 32 = (eC k).setWidth 32 ∧ (σ.cl → Got k s)

/-- The consumer's table. -/
abbrev consTable (P : SP) (tid : Nat) : Label → MachineData → (SharedEnv.counted (EC P tid)).State → Prop :=
  fun lb s σ => FrameP P s ∧
    ((lb = "consumer" ∧ CS P σ.1) ∨ (lb = "cempty0" ∧ CR P 0 s σ.1) ∨ (lb = "cempty1" ∧ CR P 1 s σ.1) ∨
      (lb = "cempty2" ∧ CR P 2 s σ.1) ∨ (lb = "cdone" ∧ (σ.1.cl → Got 3 s)))

section Consumer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscConsumerX)]

local instance spscConsumerX.envC : CodeEnv := ⟨layout spscConsumerX⟩

set_option maxHeartbeats 1000000 in
/-- **The x64 SPSC consumer on `EnvGTX`** (counted, partial): every run that
reaches the end has, under the clean flag, `r12d = 1`, `r13d = 2`,
`r14d = 3`. -/
theorem spscConsumerX_envGT (P : SP) (hL : SpscLocs P) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (EC P tid))
      (fun s σ => FrameP P s ∧ CS P σ.1) spscConsumerX
      (fun s σ => σ.1.cl → Got 3 s) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (consTable P tid) (hP := by funext s g; simp [consTable])
  cfg_cases_env [spscConsumerX]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, -, hx2, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx2
    simp [hx2] <;> trivial
  case vc2 s σ pre v σ1 hld =>
    -- `consumer` → `cempty0`
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx2, hdf] at hm
    obtain ⟨rfl, hCE⟩ := vcC_loadH_at hL hT (by simp [hx2]) hst0.1
    exact ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩, .inr (.inl ⟨rfl, hCE, by simp [eC], fun _ => by simp⟩)⟩
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hx1, -, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the `je cempty0` back edge
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 = (eC 0).setWidth 32 := by
      have h0 : w.setWidth 32 - (eC 0).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCE' := (vcC_spin_at (k := 0) (by decide) hCE (by simp [hx1]) hst0.1).1 hz'
    have hn := hst0.2
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩, .inr (.inl ⟨rfl, (hCE'.fence hf1.1).fence hf2.1,
      by simpa using hax, fun hc => ?_⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp
    · subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 => simp
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 hdm =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 0).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 0).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 0) (by decide) hCE (by simp [hx1]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    simp [hx0, hax, Reg64s.get_low32, eC] <;> trivial
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 hdm =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 0).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 0).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 0) (by decide) hCE (by simp [hx1]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 0 σ6.1 ∧ (σ6.1.cl → u = cval 0) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    refine vcC_storeH_ok_at hL (k := 0) (by decide) hCX8 (by simp [hx2]) ?_
    simp [hax, eC, hNew]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 dm σ9 hst =>
    -- the end of round 0
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 0).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 0).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 0) (by decide) hCE (by simp [hx1]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 0 σ6.1 ∧ (σ6.1.cl → u = cval 0) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hR : (((0 : Nat) = 0 → CE P 1 σ9.1) ∧ ((0 : Nat) = 1 → CE P 2 σ9.1)) ∧ σ9.1.cl = σ8.1.cl := by
      refine vcC_storeH_at hL (k := 0) (by decide) hCX8 ?_ ?_ _ _ hs.1
      · simp [hx2]
      · simp [hax, eC, hNew]
    have hcl : σ9.1.cl → σ.1.cl ∧ u = cval 0 := fun hc => by
      have h6 : σ6.1.cl := cl_fence hf5.1 (cl_fence hf6.1 (hR.2 ▸ hc))
      exact ⟨(loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 (cl_fence hf3.1 (cl_fence hf4.1
        ((loadKeep hst1.1).cl h6))))), hD.2 h6⟩
    refine ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩, .inr (.inr (.inl ⟨rfl, hR.1.1 rfl, by simp [hax, eC], fun hc => ?_⟩))⟩
    obtain ⟨hc0, rfl⟩ := hcl hc
    have := hgot hc0
    simp [cval] at this ⊢ <;> exact this
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hx1, -, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the `je cempty1` back edge
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 = (eC 1).setWidth 32 := by
      have h0 : w.setWidth 32 - (eC 1).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCE' := (vcC_spin_at (k := 1) (by decide) hCE (by simp [hx1]) hst0.1).1 hz'
    have hn := hst0.2
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩, .inr (.inr (.inl ⟨rfl, (hCE'.fence hf1.1).fence hf2.1,
      by simpa using hax, fun hc => ?_⟩))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · have := hgot ((loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 hc)))
      simpa using this
    · subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 => simp
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 hdm =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 1).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 1).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 1) (by decide) hCE (by simp [hx1]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    simp [hx0, hax, Reg64s.get_low32, eC] <;> trivial
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 hdm =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 1).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 1).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 1) (by decide) hCE (by simp [hx1]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 1 σ6.1 ∧ (σ6.1.cl → u = cval 1) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    refine vcC_storeH_ok_at hL (k := 1) (by decide) hCX8 (by simp [hx2]) ?_
    simp [hax, eC, hNew]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 dm σ9 hst =>
    -- the end of round 1
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 1).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 1).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 1) (by decide) hCE (by simp [hx1]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 1 σ6.1 ∧ (σ6.1.cl → u = cval 1) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hR : (((1 : Nat) = 0 → CE P 1 σ9.1) ∧ ((1 : Nat) = 1 → CE P 2 σ9.1)) ∧ σ9.1.cl = σ8.1.cl := by
      refine vcC_storeH_at hL (k := 1) (by decide) hCX8 ?_ ?_ _ _ hs.1
      · simp [hx2]
      · simp [hax, eC, hNew]
    have hcl : σ9.1.cl → σ.1.cl ∧ u = cval 1 := fun hc => by
      have h6 : σ6.1.cl := cl_fence hf5.1 (cl_fence hf6.1 (hR.2 ▸ hc))
      exact ⟨(loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 (cl_fence hf3.1 (cl_fence hf4.1
        ((loadKeep hst1.1).cl h6))))), hD.2 h6⟩
    refine ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩, .inr (.inr (.inr (.inl ⟨rfl, hR.1.2 rfl, by simp [hax, eC], fun hc => ?_⟩)))⟩
    obtain ⟨hc0, rfl⟩ := hcl hc
    have := hgot hc0
    simp [cval] at this ⊢ <;> exact this
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hx1, -, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the `je cempty2` back edge
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 = (eC 2).setWidth 32 := by
      have h0 : w.setWidth 32 - (eC 2).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCE' := (vcC_spin_at (k := 2) (by decide) hCE (by simp [hx1]) hst0.1).1 hz'
    have hn := hst0.2
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩, .inr (.inr (.inr (.inl ⟨rfl, (hCE'.fence hf1.1).fence hf2.1,
      by simpa using hax, fun hc => ?_⟩)))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · have := hgot ((loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 hc)))
      simpa using this
    · subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 => simp
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 hdm =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 2).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 2).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 2) (by decide) hCE (by simp [hx1]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    simp [hx0, hax, Reg64s.get_low32, eC] <;> trivial
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 hdm =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 2).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 2).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 2) (by decide) hCE (by simp [hx1]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 2 σ6.1 ∧ (σ6.1.cl → u = cval 2) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    refine vcC_storeH_ok_at hL (k := 2) (by decide) hCX8 (by simp [hx2]) ?_
    simp [hax, eC, hNew]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 dm σ9 hst σ10 hf7 =>
    -- the end of round 2
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6 hf7
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hx1, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 2).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 2).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 2) (by decide) hCE (by simp [hx1]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 2 σ6.1 ∧ (σ6.1.cl → u = cval 2) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hR : (((2 : Nat) = 0 → CE P 1 σ9.1) ∧ ((2 : Nat) = 1 → CE P 2 σ9.1)) ∧ σ9.1.cl = σ8.1.cl := by
      refine vcC_storeH_at hL (k := 2) (by decide) hCX8 ?_ ?_ _ _ hs.1
      · simp [hx2]
      · simp [hax, eC, hNew]
    have hcl : σ9.1.cl → σ.1.cl ∧ u = cval 2 := fun hc => by
      have h6 : σ6.1.cl := cl_fence hf5.1 (cl_fence hf6.1 (hR.2 ▸ hc))
      exact ⟨(loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 (cl_fence hf3.1 (cl_fence hf4.1
        ((loadKeep hst1.1).cl h6))))), hD.2 h6⟩
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf⟩, .inr (.inr (.inr (.inr ⟨rfl, fun hc => ?_⟩)))⟩, .inl (by decide)⟩
    obtain ⟨hc0, rfl⟩ := hcl (cl_fence hf7.1 hc)
    have := hgot hc0
    simp [cval] at this ⊢ <;> exact this
  case vc1 s σ pre hcl =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    simpa using hT hcl

end Consumer

end Kraken.Promising.X64.EnvG.SpscX

#print axioms Kraken.Promising.X64.EnvG.SpscX.spscProducerX_envGT
#print axioms Kraken.Promising.X64.EnvG.SpscX.spscConsumerX_envGT
