/-
**Part 5: both threads of
`spsc_queue.kl` by `vcgen` on `EnvGTU`** (the `TicketLockVCGen` /
`TakeUSkipVCGen` pattern: `cfgEnv_partial` with a label table, one `vcgen`
call per cut, the goals discharged by the isolated VCs of
`A64SpscVCP.lean`, `A64SpscVCC.lean`).

- `spscProdA_envGTU`: from `PR 1` (and the frame `FrameP`: `X0 = buf`,
  `X1 = head`, `X2 = tail`, no private byte at the four shared words), every
  run of the producer that reaches the end holds all of `T`. Table:
  `prod` (`PR 1`); `prod_loop` (round `k`: `W3 = k`, `X4 = k - 1`,
  `X7 = (slot k).addr`, `PR k`); `pdone`.
- `spscConsA_envGTU`: from `CE 1` (frame `FrameC`), every run of the
  consumer that reaches the end has, under the clean flag, `W10 = 1`,
  `W11 = 2`, `W12 = 3`. Table: `cons`; `c1`, `c2`, `c3` (`X4 = j - 1`,
  `X7` the round's slot, `CE j`, the earlier registers under the clean
  flag); `cdone`.
-/
import Kraken.Promising.SLR.EnvG.A64SpscVCC
import Kraken.Promising.SLR.EnvG.A64SpscProg
import Kraken.AArch64.EnvCfg
import Kraken.Promising.SLR.EnvG.A64MaskRunAt
open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG
namespace Kraken.Promising.SLR.EnvG.SpscA
set_option mvcgen.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

/-! ## The producer -/

/-- The producer's frame: the base registers and no private byte at the shared words. -/
def FrameP (P : SP) (s : MachineData) : Prop :=
  s.regs.X0.toBitVec = P.b ∧ s.regs.X1.toBitVec = P.h ∧ s.regs.X2.toBitVec = P.t ∧
    Mem.loadInt s.dmem P.h 8 = none ∧ Mem.loadInt s.dmem P.t 8 = none ∧ Mem.loadInt s.dmem P.b 4 = none ∧
    Mem.loadInt s.dmem (P.b ^^^ 8) 4 = none
/-- `vcP_storeT`'s next round. -/
theorem storeT_next {P : SP} {k : Nat} {σ : State isa}
    (h : (k = 1 → PR P 2 σ) ∧ (k = 2 → PR P 3 σ) ∧ (σ.r.wr P.T).q = 1) (hk : k = 1 ∨ k = 2) : PR P (k + 1) σ := by
  rcases hk with rfl | rfl
  · exact h.1 rfl
  · exact h.2.1 rfl
section ProdAt

variable [CodeEnv]

/-- The producer's table. -/
abbrev prodTable (P : SP) (tid : Nat) : Label → MachineData → (SharedEnv.counted (EP P tid)).State → Prop :=
  fun lb s σ => FrameP P s ∧
    ((lb = "prod" ∧ PR P 1 σ.1) ∨
     (lb = "prod_loop" ∧ ∃ k, (k = 1 ∨ k = 2 ∨ k = 3) ∧ s.regs.X3.toBitVec.setWidth 32 = BitVec.ofNat 32 k ∧
        s.regs.X4.toBitVec = BitVec.ofNat 64 (k - 1) ∧ s.regs.X7.toBitVec = (slot P k).addr ∧ PR P k σ.1) ∨
     (lb = "pdone" ∧ (σ.1.r.wr P.T).q = 1))
/-- **`spscProdA_envGTU` in any ambient code** in which `spscProdA` is `PlacedIn`, from `prod` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem spscProdA_envGTU_at (P : SP) (hL : SpscLocs P) (tid : Nat)
    (hpl : Program.PlacedIn spscProdA) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt spscProdA l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (prodTable P tid) "prod" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (EP P tid)))
      (fun x => (x.1.2 = endA ∧ (x.2.1.r.wr P.T).q = 1) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "prod"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EP P tid))
    (Q := fun _ σ => (σ.1.r.wr P.T).q = 1)
    (E := fun _ _ _ => False) (prodTable P tid) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [spscProdA]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hx2, hdh, hdt, hdb, hdb1⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try simp at hdb1
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGTU, SharedEnv.counted_step, SharedEnv.counted_ok, envGTU_step_load] at *
  all_goals try (simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1]; done)
  case vc1 =>
    rename_i σ1 σ2 σ3 hf1 hf2 hf3 _
    refine ⟨?_, .inr (.inl ⟨trivial, 1, .inl rfl, ?_, ?_, ?_, ((hT.fence hf1.1).fence hf2.1).fence hf3.1⟩)⟩
    all_goals simp [FrameP, slot, hx0, hx1, hx2, hdh, hdt, hdb]
    simpa using hdb1
  case vc4 =>
    rename_i m g0 v σ1 σ2 r1 σ3 hc σ4 hst1 hf1 hf2 hf3 _
    obtain ⟨k, hk, h3, h4, h7, hPR⟩ := hT
    rcases hk with rfl | rfl | rfl
    all_goals simp [slot] at h7
    all_goals simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1, h3, h4, h7] at hc hst1
    all_goals
      have hcnt : σ4.2 = g0.2 + 1 := by rw [hf3.2, hf2.2, hf1.2, hst1.2]
      have hPR' := (vcP_spin hL (by decide) hPR hst1.1).1 (by simp only [lo]; bv_omega)
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, .inr (.inl ⟨rfl, _, by decide, ?_, ?_, ?_,
        ((hPR'.fence hf1.1).fence hf2.1).fence hf3.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      · simp [FrameP, hx0, hx1, hx2, hdh, hdt, hdb]
        simpa using hdb1
      · simp [h3]
      · simp [h4]
      · simp [h7, slot, BitVec.xor_assoc]
      · have := congrArg Prod.snd hg; omega
  case vc6 =>
    rename_i v σ1 σ2 r1 σ3 hc σ4 r2 _ hst1 hf1 hf2 hf3 _
    obtain ⟨k, hk, h3, h4, h7, hPR⟩ := hT
    rcases hk with rfl | rfl | rfl
    all_goals simp [slot] at h7
    all_goals simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1, h3, h4, h7] at hc hst1
    all_goals
      have hPX := (((vcP_spin hL (by decide) hPR hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).fence
        hf1.1 |>.fence hf2.1).fence hf3.1
      have := (vcP_storeB hL (tid := tid) hPX).1
      simpa [slot, h7, h3] using this
  case vc8 =>
    rename_i m g0 v σ1 σ2 r1 σ3 hc σ4 r2 dm σ5 r3 σ6 σ7 hst1 hf1 hf2 hf3 hstr hf4 hf5 _
    obtain ⟨k, hk, h3, h4, h7, hPR⟩ := hT
    rcases hk with rfl | rfl | rfl
    all_goals simp [slot] at h7
    all_goals simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1, h3, h4, h7] at hstr
    all_goals simp [hstr.1, hx2, hdt]
  case vc9 =>
    rename_i m g0 v σ1 σ2 r1 σ3 hc σ4 r2 dm σ5 r3 σ6 σ7 hst1 hf1 hf2 hf3 hstr hf4 hf5 _
    obtain ⟨k, hk, h3, h4, h7, hPR⟩ := hT
    rcases hk with rfl | rfl | rfl
    all_goals simp [slot] at h7
    all_goals simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1, h3, h4, h7] at hc hst1 hstr
    all_goals
      have hPX := (((vcP_spin hL (by decide) hPR hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).fence
        hf1.1 |>.fence hf2.1).fence hf3.1
      have hPD5 := hstr.2.1.elim (fun h => (vcP_storeB hL (tid := tid) hPX).2 _ _ h)
        (fun h => (vcP_storeB hL (tid := tid) hPX).2 _ _ h)
      have hPD := (hPD5.fence hf4.1).fence hf5.1
      simpa [h3, h4, hx2] using (vcP_storeT hL (tid := tid) (by decide) hPD).1
  case vc10 =>
    rename_i m g0 v σ1 σ2 r1 σ3 hc σ4 r2 dm σ5 r3 σ6 σ7 b σ8 r4 σ9 r5 σ10 hne σ11 hst1 hf1 hf2 hf3 hstr hf4 hf5 hstl hf6 hf7 hf8 _
    obtain ⟨k, hk, h3, h4, h7, hPR⟩ := hT
    rcases hk with rfl | rfl | rfl
    all_goals simp [slot] at h7
    all_goals simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1, h3, h4, h7] at hc hst1 hstr hstl hne
    all_goals
      have hPX := (((vcP_spin hL (by decide) hPR hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).fence
        hf1.1 |>.fence hf2.1).fence hf3.1
      have hPD5 := hstr.2.1.elim (fun h => (vcP_storeB hL (tid := tid) hPX).2 _ _ h)
        (fun h => (vcP_storeB hL (tid := tid) hPX).2 _ _ h)
      have hPD := (hPD5.fence hf4.1).fence hf5.1
      have hst := (vcP_storeT hL (tid := tid) (by decide) hPD).2 b σ8.1 hstl.1
      have hcnt : σ11.2 = g0.2 + 3 := by rw [hf8.2, hf7.2, hf6.2, hstl.2, hf5.2, hf4.2, hstr.2.2, hf3.2, hf2.2, hf1.2, hst1.2]
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, .inr (.inl ⟨rfl, _, by decide, ?_, ?_, ?_,
        (((storeT_next hst (by decide)).fence hf6.1).fence hf7.1).fence hf8.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      · simp [FrameP, hx0, hx1, hx2, hstr.1, hdh, hdt, hdb]
        simpa using hdb1
      · simp [h3]
      · simp [h4]
      · simp [h7, slot, BitVec.xor_assoc]
      · have := congrArg Prod.snd hg; omega
  case vc11 =>
    rename_i m g0 v σ1 σ2 r1 σ3 hc σ4 r2 dm σ5 r3 σ6 σ7 b σ8 r4 σ9 r5 σ10 hne σ11 σ12 hst1 hf1 hf2 hf3 hstr hf4 hf5 hstl hf6 hf7 hf8 hf9 _
    obtain ⟨k, hk, h3, h4, h7, hPR⟩ := hT
    rcases hk with rfl | rfl | rfl
    all_goals simp [slot] at h7
    all_goals simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1, h3, h4, h7] at hc hst1 hstr hstl hne
    all_goals
      have hPX := (((vcP_spin hL (by decide) hPR hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).fence
        hf1.1 |>.fence hf2.1).fence hf3.1
      have hPD5 := hstr.2.1.elim (fun h => (vcP_storeB hL (tid := tid) hPX).2 _ _ h)
        (fun h => (vcP_storeB hL (tid := tid) hPX).2 _ _ h)
      have hPD := (hPD5.fence hf4.1).fence hf5.1
      have hst := (vcP_storeT hL (tid := tid) (by decide) hPD).2 b σ8.1 hstl.1
      have hq : (σ12.1.r.wr P.T).q = 1 := by rw [hf9.1.r, hf8.1.r, hf7.1.r, hf6.1.r]; exact hst.2.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, .inr (.inr ⟨rfl, hq⟩)⟩, .inl (by decide)⟩
      simp [FrameP, hx0, hx1, hx2, hstr.1, hdh, hdt, hdb]
      simpa using hdb1
  case vc1 => exact hT

end ProdAt

section Prod
variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscProdA)]
local instance spscProdA.env : CodeEnv := ⟨layout spscProdA⟩
/-- **The SPSC producer on `EnvGTU`** (counted, partial): from `PR 1`, every run that
reaches the end holds all of `T`. -/
theorem spscProdA_envGTU (P : SP) (hL : SpscLocs P) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (EP P tid))
      (fun s σ => FrameP P s ∧ PR P 1 σ.1) spscProdA
      (fun _ σ => (σ.1.r.wr P.T).q = 1) (fun _ _ _ => False) :=
  have hpl : Program.Placed spscProdA "prod" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [prodTable]) fun _ hlast =>
    spscProdA_envGTU_at P hL tid hpl.toPlacedIn hlast

end Prod

/-! ## The consumer -/

section ConsAt

theorem cl_loadC {P : SP} {tid : Nat} {σ σ' : State isa} {v : Val} (k : LoadKind) (a : BitVec 64) (n : Nat)
    (hs : (EC P tid).step (.load k false a n) σ v σ') : σ'.cl → σ.cl := (loadKeepU hs).cl

theorem cl_storeC {P : SP} {tid : Nat} {σ σ' : State isa} {k : StoreKind} {a : BitVec 64} {n : Nat} {v : Val}
    {b : Bool} (hs : (EC P tid).step (.store k false a n v) σ b σ') : σ'.cl = σ.cl := by
  obtain ⟨c, tw, -, -, -, -, -, -, hcl, -⟩ := step_storeFactsTU hs
  exact hcl


/-- The consumer's frame. -/
def FrameC (P : SP) (s : MachineData) : Prop :=
  s.regs.X0.toBitVec = P.b ∧ s.regs.X1.toBitVec = P.h ∧ s.regs.X2.toBitVec = P.t ∧
    Mem.loadInt s.dmem P.h 8 = none ∧ Mem.loadInt s.dmem P.t 8 = none ∧ Mem.loadInt s.dmem P.b 4 = none ∧
    Mem.loadInt s.dmem (P.b ^^^ 8) 4 = none

variable [CodeEnv]

/-- The consumer's table. -/
abbrev consTable (P : SP) (tid : Nat) : Label → MachineData → (SharedEnv.counted (EC P tid)).State → Prop :=
  fun lb s σ => FrameC P s ∧
    ((lb = "cons" ∧ CE P 1 σ.1) ∨
     (lb = "c1" ∧ s.regs.X4.toBitVec = 0 ∧ s.regs.X7.toBitVec = P.b ∧ CE P 1 σ.1) ∨
     (lb = "c2" ∧ s.regs.X4.toBitVec = 1 ∧ s.regs.X7.toBitVec = P.b ^^^ 8 ∧ CE P 2 σ.1 ∧
        (σ.1.cl → s.regs.X10.toBitVec.setWidth 32 = 1)) ∨
     (lb = "c3" ∧ s.regs.X4.toBitVec = 2 ∧ s.regs.X7.toBitVec = P.b ∧ CE P 3 σ.1 ∧
        (σ.1.cl → s.regs.X10.toBitVec.setWidth 32 = 1 ∧ s.regs.X11.toBitVec.setWidth 32 = 2)) ∨
     (lb = "cdone" ∧ (σ.1.cl → s.regs.X10.toBitVec.setWidth 32 = 1 ∧ s.regs.X11.toBitVec.setWidth 32 = 2 ∧
        s.regs.X12.toBitVec.setWidth 32 = 3)))

/-- **`spscConsA_envGTU` in any ambient code** in which `spscConsA` is `PlacedIn`, from `cons` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem spscConsA_envGTU_at (P : SP) (hL : SpscLocs P) (tid : Nat)
    (hpl : Program.PlacedIn spscConsA) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt spscConsA l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (consTable P tid) "cons" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (EC P tid)))
      (fun x => (x.1.2 = endA ∧ (x.2.1.cl → x.1.1.regs.X10.toBitVec.setWidth 32 = 1 ∧
        x.1.1.regs.X11.toBitVec.setWidth 32 = 2 ∧ x.1.1.regs.X12.toBitVec.setWidth 32 = 3)) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "cons"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EC P tid))
    (Q := fun s σ => σ.1.cl → s.regs.X10.toBitVec.setWidth 32 = 1 ∧ s.regs.X11.toBitVec.setWidth 32 = 2 ∧
        s.regs.X12.toBitVec.setWidth 32 = 3)
    (E := fun _ _ _ => False) (consTable P tid) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [spscConsA]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hx2, hdh, hdt, hdb, hdb1⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try simp at hdb1
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGTU, SharedEnv.counted_step, SharedEnv.counted_ok, envGTU_step_load] at *
  all_goals try (simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1]; done)
  case vc1 =>
    rename_i m g0 σ1 σ2 hf1 hf2 _
    refine ⟨?_, .inr (.inl ⟨trivial, ?_, ?_, (hT.ckeep (.fence hf1.1)).ckeep (.fence hf2.1)⟩)⟩
    all_goals simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb]
    simpa using hdb1
  case vc4 =>
    rename_i m g0 v σ1 σ2 hc σ3 hst1 hf1 hf2 _
    obtain ⟨h4, h7, hCE⟩ := hT
    simp [hx2, h4] at hc hst1
    have hcnt : σ3.2 = g0.2 + 1 := by rw [hf2.2, hf1.2, hst1.2]
    have hCE' := ((vcC_spin (by decide) hCE hst1.1).1 (by simp only [lo]; bv_omega)).ckeep (.fence hf1.1)
      |>.ckeep (.fence hf2.1)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, .inr (.inl ⟨rfl, ?_, ?_, hCE'⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb]
      simpa using hdb1
    · simp [h4]
    · simp [h7]
    · have := congrArg Prod.snd hg; omega
  case vc9 =>
    rename_i m g0 v σ1 σ2 hc σ3 r1 w σ4 r2 σ5 σ6 hst1 hf1 hf2 hld hf3 hf4 _
    obtain ⟨h4, h7, hCE⟩ := hT
    simp [hx2, h4] at hc hst1
    have hCX := ((vcC_spin (by decide) hCE hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).ckeep
      (.fence hf1.1) |>.ckeep (.fence hf2.1)
    simp [h7, hdb, hdb1] at hld
    obtain ⟨v', hl, rfl⟩ := hld
    have hCX4 := ((vcC_data hCX hl.1).1.ckeep (.fence hf3.1)).ckeep (.fence hf4.1)
    simpa [hx1, h4] using (vcC_storeH hL (tid := tid) (j := 1) (by decide) hCX4).1
  case vc10 =>
    rename_i m g0 v σ1 σ2 hc σ3 r1 w σ4 r2 σ5 σ6 b σ7 hst1 hf1 hf2 hld hf3 hf4 hstl _
    obtain ⟨h4, h7, hCE⟩ := hT
    simp [hx2, h4] at hc hst1
    have hCX := ((vcC_spin (by decide) hCE hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).ckeep
      (.fence hf1.1) |>.ckeep (.fence hf2.1)
    simp [h7, hdb, hdb1] at hld
    obtain ⟨v', hl, rfl⟩ := hld
    have hCX4 := ((vcC_data hCX hl.1).1.ckeep (.fence hf3.1)).ckeep (.fence hf4.1)
    have hdat := (vcC_data hCX hl.1).2
    simp [hx1, h4] at hstl
    have hCE2 : CE P 2 σ7.1 := ((vcC_storeH hL (tid := tid) (j := 1) (by decide) hCX4).2 b σ7.1 hstl.1).1 rfl
    have hcl : σ7.1.cl → σ4.1.cl := fun h =>
      hf3.1.cl.mp (hf4.1.cl.mp ((cl_storeC hstl.1).mp h))
    refine ⟨?_, .inr (.inr (.inl ⟨trivial, ?_, ?_, hCE2, fun hc7 => ?_⟩))⟩
    · simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb]
      simpa using hdb1
    · simp [h4]
    · simp [h7]
    · simp [hdat (hcl hc7)]
  case vc4 =>
    rename_i m g0 v σ1 σ2 hc σ3 hst1 hf1 hf2 _
    obtain ⟨h4, h7, hCE, hR⟩ := hT
    simp [hx2, h4] at hc hst1
    have hcnt : σ3.2 = g0.2 + 1 := by rw [hf2.2, hf1.2, hst1.2]
    have hCE' := ((vcC_spin (by decide) hCE hst1.1).1 (by simp only [lo]; bv_omega)).ckeep (.fence hf1.1)
      |>.ckeep (.fence hf2.1)
    have hcl : σ3.1.cl → g0.1.cl := fun h =>
      cl_loadC (P := P) (tid := tid) .acq P.t 8 hst1.1 (hf1.1.cl.mp (hf2.1.cl.mp h))
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, .inr (.inr (.inl ⟨rfl, ?_, ?_, hCE', fun h => ?_⟩))⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    · simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb]
      simpa using hdb1
    · simp [h4]
    · simp [h7]
    · simpa using hR (hcl h)
    · have := congrArg Prod.snd hg; omega
  case vc9 =>
    rename_i m g0 v σ1 σ2 hc σ3 r1 w σ4 r2 σ5 σ6 hst1 hf1 hf2 hld hf3 hf4 _
    obtain ⟨h4, h7, hCE, hR⟩ := hT
    simp [hx2, h4] at hc hst1
    have hCX := ((vcC_spin (by decide) hCE hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).ckeep
      (.fence hf1.1) |>.ckeep (.fence hf2.1)
    simp [h7, hdb, hdb1] at hld
    obtain ⟨v', hl, rfl⟩ := hld
    have hCX4 := ((vcC_data hCX hl.1).1.ckeep (.fence hf3.1)).ckeep (.fence hf4.1)
    simpa [hx1, h4] using (vcC_storeH hL (tid := tid) (j := 2) (by decide) hCX4).1
  case vc10 =>
    rename_i m g0 v σ1 σ2 hc σ3 r1 w σ4 r2 σ5 σ6 b σ7 hst1 hf1 hf2 hld hf3 hf4 hstl _
    obtain ⟨h4, h7, hCE, hR⟩ := hT
    simp [hx2, h4] at hc hst1
    have hCX := ((vcC_spin (by decide) hCE hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).ckeep
      (.fence hf1.1) |>.ckeep (.fence hf2.1)
    simp [h7, hdb, hdb1] at hld
    obtain ⟨v', hl, rfl⟩ := hld
    have hCX4 := ((vcC_data hCX hl.1).1.ckeep (.fence hf3.1)).ckeep (.fence hf4.1)
    have hdat := (vcC_data hCX hl.1).2
    simp [hx1, h4] at hstl
    have hCE2 : CE P 3 σ7.1 := ((vcC_storeH hL (tid := tid) (j := 2) (by decide) hCX4).2 b σ7.1 hstl.1).2 rfl
    have hcl : σ7.1.cl → σ4.1.cl := fun h =>
      hf3.1.cl.mp (hf4.1.cl.mp ((cl_storeC hstl.1).mp h))
    have hcl0 : σ4.1.cl → g0.1.cl := fun h =>
      cl_loadC (P := P) (tid := tid) .acq P.t 8 hst1.1 (hf1.1.cl.mp (hf2.1.cl.mp (cl_loadC (P := P) (tid := tid) .plain _ 4 hl.1 h)))
    refine ⟨?_, .inr (.inr (.inr (.inl ⟨trivial, ?_, ?_, hCE2, fun hc7 => ?_⟩)))⟩
    · simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb]
      simpa using hdb1
    · simp [h4]
    · simp [h7, BitVec.xor_assoc]
    · have := hR (hcl0 (hcl hc7))
      simp [hdat (hcl hc7)]
      simpa using this
  case vc4 =>
    rename_i m g0 v σ1 σ2 hc σ3 hst1 hf1 hf2 _
    obtain ⟨h4, h7, hCE, hR⟩ := hT
    simp [hx2, h4] at hc hst1
    have hcnt : σ3.2 = g0.2 + 1 := by rw [hf2.2, hf1.2, hst1.2]
    have hCE' := ((vcC_spin (by decide) hCE hst1.1).1 (by simp only [lo]; bv_omega)).ckeep (.fence hf1.1)
      |>.ckeep (.fence hf2.1)
    have hcl : σ3.1.cl → g0.1.cl := fun h =>
      cl_loadC (P := P) (tid := tid) .acq P.t 8 hst1.1 (hf1.1.cl.mp (hf2.1.cl.mp h))
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, .inr (.inr (.inr (.inl ⟨rfl, ?_, ?_, hCE',
      fun h => ?_⟩)))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb]
      simpa using hdb1
    · simp [h4]
    · simp [h7]
    · simpa using hR (hcl h)
    · have := congrArg Prod.snd hg; omega
  case vc9 =>
    rename_i m g0 v σ1 σ2 hc σ3 r1 w σ4 r2 σ5 σ6 hst1 hf1 hf2 hld hf3 hf4 _
    obtain ⟨h4, h7, hCE, hR⟩ := hT
    simp [hx2, h4] at hc hst1
    have hCX := ((vcC_spin (by decide) hCE hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).ckeep
      (.fence hf1.1) |>.ckeep (.fence hf2.1)
    simp [h7, hdb, hdb1] at hld
    obtain ⟨v', hl, rfl⟩ := hld
    have hCX4 := ((vcC_data hCX hl.1).1.ckeep (.fence hf3.1)).ckeep (.fence hf4.1)
    simpa [hx1, h4] using (vcC_storeH hL (tid := tid) (j := 3) (by decide) hCX4).1
  case vc10 =>
    rename_i m g0 v σ1 σ2 hc σ3 r1 w σ4 r2 σ5 σ6 b σ7 σ8 hst1 hf1 hf2 hld hf3 hf4 hstl hf5 _
    obtain ⟨h4, h7, hCE, hR⟩ := hT
    simp [hx2, h4] at hc hst1
    have hCX := ((vcC_spin (by decide) hCE hst1.1).2 (fun h => hc (by simp only [lo] at h; bv_omega))).ckeep
      (.fence hf1.1) |>.ckeep (.fence hf2.1)
    simp [h7, hdb, hdb1] at hld
    obtain ⟨v', hl, rfl⟩ := hld
    have hCX4 := ((vcC_data hCX hl.1).1.ckeep (.fence hf3.1)).ckeep (.fence hf4.1)
    have hdat := (vcC_data hCX hl.1).2
    simp [hx1, h4] at hstl
    have hcl : σ8.1.cl → σ4.1.cl := fun h =>
      hf3.1.cl.mp (hf4.1.cl.mp ((cl_storeC hstl.1).mp (hf5.1.cl.mp h)))
    have hcl0 : σ4.1.cl → g0.1.cl := fun h =>
      cl_loadC (P := P) (tid := tid) .acq P.t 8 hst1.1 (hf1.1.cl.mp (hf2.1.cl.mp (cl_loadC (P := P) (tid := tid) .plain _ 4 hl.1 h)))
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, .inr (.inr (.inr (.inr ⟨rfl, fun hc8 => ?_⟩)))⟩,
      .inl (by decide)⟩
    · simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb]
      simpa using hdb1
    · have := hR (hcl0 (hcl hc8))
      simp [hdat (hcl hc8)]
      simpa using this
  case vc1 =>
    rename_i hcl0 _
    simpa using hT hcl0

end ConsAt

section Cons

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscConsA)]
local instance spscConsA.env : CodeEnv := ⟨layout spscConsA⟩

/-- **The SPSC consumer on `EnvGTU`** (counted, partial): from `CE 1`, every run that
reaches the end has, under the clean flag, `W10 = 1`, `W11 = 2`, `W12 = 3`. -/
theorem spscConsA_envGTU (P : SP) (hL : SpscLocs P) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (EC P tid))
      (fun s σ => FrameC P s ∧ CE P 1 σ.1) spscConsA
      (fun s σ => σ.1.cl → s.regs.X10.toBitVec.setWidth 32 = 1 ∧ s.regs.X11.toBitVec.setWidth 32 = 2 ∧
        s.regs.X12.toBitVec.setWidth 32 = 3) (fun _ _ _ => False) :=
  have hpl : Program.Placed spscConsA "cons" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [consTable]) fun _ hlast =>
    spscConsA_envGTU_at P hL tid hpl.toPlacedIn hlast

end Cons

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.SpscA.spscProdA_envGTU
#print axioms Kraken.Promising.SLR.EnvG.SpscA.spscConsA_envGTU

