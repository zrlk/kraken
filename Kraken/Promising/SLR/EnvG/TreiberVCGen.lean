/-
Part 8: **the two threads of `treiber_pp.kl` on
`EnvGC` by `vcgen`**: `pusher_envGC` and `popper_envGC`, `PartialTripleEnv`s
in the counted `EnvGC` by `cfgEnv_partial` with the VCs of
`EnvG/TreiberVC.lean`.

Each run is stated once, over any ambient code in which the thread's
text is `Program.PlacedIn` (`pusher_envGC_at`, `popper_envGC_at`;
`EnvG/A64MaskRunAt.lean`). The per-thread triples are their instances in the
text's own layout (`PartialTripleEnv.of_runAtT`); the whole-image runs of
`EnvG/A64WholeTreiberVCGen.lean` are their instances at the image and its
mask.
-/
import Kraken.Promising.SLR.EnvG.TreiberVC
import Kraken.Promising.SLR.EnvG.TreiberSmoke
import Kraken.Promising.SLR.EnvG.A64VCGen
import Kraken.AArch64.EnvCfg
import Kraken.Promising.SLR.EnvG.A64MaskRunAt

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.Treiber

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The parameters of `treiber_pp.kl` at `top = t` (8 bytes) and the node
`n1 = n` (data word `[n]`, 4 bytes; link `[n + 8]`, 8 bytes), with the ghost
token `tok`. -/
def tParams (t n : BitVec 64) (tok : Loc) : Params :=
  ⟨⟨t, 8⟩, ⟨n, 4⟩, ⟨n + 8, 8⟩, tok, BitVec.setWidth 128 n⟩

section PusherAt

variable [CodeEnv]

/-- The pusher's table. -/
abbrev pushTable (t n : BitVec 64) (tok : Loc) :
    Label → MachineData → (SharedEnv.counted (EP (tParams t n tok))).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ Mem.loadInt s.dmem t 8 = none ∧
    Mem.loadInt s.dmem n 4 = none ∧ Mem.loadInt s.dmem (n + 8) 8 = none ∧
    ((lb = "pusher" ∧ s.regs.X9.toBitVec.setWidth 32 = 1 ∧ Pu0 (tParams t n tok) σ.1) ∨
      (lb = "push" ∧ Pu (tParams t n tok) σ.1) ∨ (lb = "pdone" ∧ Pd (tParams t n tok) σ.1))

/-- **`pusher_envGC` in any ambient code** in which `treiberPusher` is
`PlacedIn`, from `pusher` to the end address `endA` of its last block (its
script; `EnvG/A64MaskRunAt.lean`). -/
theorem pusher_envGC_at (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParams t n tok))
    (hpl : Program.PlacedIn treiberPusher) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt treiberPusher l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, pushTable t n tok "pusher" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EP (tParams t n tok))))
        (fun x => (x.1.2 = endA ∧ Pd (tParams t n tok) x.2.1) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "pusher"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EP (tParams t n tok)))
    (Q := fun _ σ => Pd (tParams t n tok) σ.1) (E := fun _ _ _ => False) (pushTable t n tok) ?_ (by rfl)
    (by decide) hpl hlast
  cfg_cases_env [treiberPusher]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdt, hdd, hdn, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGC, SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hdt, hdd, hdn]; done)
  all_goals have hdn' : Mem.loadInt _ (n + 8#64) 8 = none := hdn
  case vc2 =>
    have h := (vc_push_str_d hL _ hT.2 (1#128) rfl).1
    simp [hx1, hT.1]
    exact h
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hx1, hdd] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP : Pu (tParams t n tok) σ1.1 := by
      rcases hso with h | h <;> exact (vc_push_str_d hL _ hT.2 (1#128) rfl).2 _ σ1.1 (by simpa [tParams, hT.1] using h)
    simp (config := { decide := true }) [hx0, hx1, hdt, hdd, hdn']
    exact hP
  case vc5 =>
    rename_i s σ0 v σ1 rng hnone hld _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1]
    exact (vc_push_str_n hL _ hP _).1
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, -⟩ := hst
    subst hdm
    simp [hx0, hdt]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu (tParams t n tok) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str_n hL _ hP _).2 _ σ2.1 (by simpa [tParams] using h)
    have h := (vc_push_cas hL _ (hP2.fence hf.1) (BitVec.setWidth 64 v) n (by simp [tParams])).1
    simp [hx0, hx1]
    simpa [tParams, casOp64] using h
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 hld hst hf1 hcas hf2 hf3 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, hst2⟩ := hst
    subst hdm
    have hP2 : Pu (tParams t n tok) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str_n hL _ hP _).2 _ σ2.1 (by simpa [tParams] using h)
    have hc := (vc_push_cas hL _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) n (by simp [tParams])).2 old σ4.1
      (by simpa [hx0, hx1, tParams, casOp64] using hcas.1)
    simp at hbr
    rcases hc with ⟨-, hPu⟩ | ⟨heq, -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdt], by simp [hdd],
        by simp [hdn'], .inr (.inl ⟨rfl, Pu.fence (Pu.fence hPu hf2.1) hf3.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h1 := hld.2; have h2 := hcas.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 σ7 hld hst hf1 hcas hf2 hf3 hf4 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu (tParams t n tok) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str_n hL _ hP _).2 _ σ2.1 (by simpa [tParams] using h)
    have hc := (vc_push_cas hL _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) n (by simp [tParams])).2 old σ4.1
      (by simpa [hx0, hx1, tParams, casOp64] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hPd⟩
    · exact absurd (by bv_omega) hne
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdt], by simp [hdd],
        by simp [hdn'], .inr (.inr ⟨rfl, Pd.fence (Pd.fence (Pd.fence hPd hf2.1) hf3.1) hf4.1⟩)⟩, .inl (by decide)⟩
  case vc1 => exact hT
  all_goals done

end PusherAt

section Pusher

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberPusher)]

local instance treiberPusher.envG : CodeEnv := ⟨layout treiberPusher⟩

theorem pusher_envGC (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParams t n tok)) :
    PartialTripleEnv (SharedEnv.counted (EP (tParams t n tok)))
      (fun s σ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ Mem.loadInt s.dmem t 8 = none ∧
        Mem.loadInt s.dmem n 4 = none ∧ Mem.loadInt s.dmem (n + 8) 8 = none ∧
        s.regs.X9.toBitVec.setWidth 32 = 1 ∧ Pu0 (tParams t n tok) σ.1)
      treiberPusher (fun _ σ => Pd (tParams t n tok) σ.1) (fun _ _ _ => False) :=
  have hpl : Program.Placed treiberPusher "pusher" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [pushTable]) fun _ hlast =>
    pusher_envGC_at t n tok hL hpl.toPlacedIn hlast

end Pusher

section PopperAt

variable [CodeEnv]

/-- The popper's table: `dmem` maps no 4-byte word (the data load's address
is a loaded value). -/
abbrev popTable (t n : BitVec 64) (tok : Loc) :
    Label → MachineData → (SharedEnv.counted (EQ (tParams t n tok))).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = t ∧ Mem.loadInt s.dmem t 8 = none ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = "popper" ∧ Pp (tParams t n tok) σ.1) ∨
      (lb = "qdone" ∧ (σ.1.cl → s.regs.X10.toBitVec = n ∧ s.regs.X11.toBitVec = 1)))

/-- **`popper_envGC` in any ambient code** in which `treiberPopper` is
`PlacedIn`, from `popper` to the end address `endA` of its last block (its
script; `EnvG/A64MaskRunAt.lean`). -/
theorem popper_envGC_at (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParams t n tok))
    (hpl : Program.PlacedIn treiberPopper) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt treiberPopper l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, popTable t n tok "popper" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EQ (tParams t n tok))))
        (fun x => (x.1.2 = endA ∧ (x.2.1.cl → x.1.1.regs.X10.toBitVec = n ∧ x.1.1.regs.X11.toBitVec = 1))
          ∨ False)
        ((s, (_root_.Executable.labels cenv).label "popper"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EQ (tParams t n tok)))
    (Q := fun s σ => σ.1.cl → s.regs.X10.toBitVec = n ∧ s.regs.X11.toBitVec = 1) (E := fun _ _ _ => False)
    (popTable t n tok) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [treiberPopper]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hdt, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGC, SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hdt, hd4]; done)
  case vc4 =>
    rename_i s σ0 v σ1 hz σ2 hld hf _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hdt], by simp [hd4],
      .inl ⟨rfl, (vc_pop_load _ hT v σ1.1 hld.1).fence hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2
    simp only [SharedEnv.tick_load] at h1
    omega
  case vc9 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 hld hf1 hld2 hf2 _
    simp at hnz hld2
    have hP1 : Pp (tParams t n tok) σ2.1 := (vc_pop_load _ hT v σ1.1 hld.1).fence hf1.1
    have hP3 : Pp (tParams t n tok) σ3.1 := by
      rcases hld2 with ⟨_, _, _, rfl⟩ | ⟨_, _, h, _⟩
      · exact hP1
      · exact vc_pop_load _ hP1 _ σ3.1 h.1
    have h := (vc_pop_cas hL _ (hP3.fence hf2.1) (BitVec.setWidth 64 v) v4 hnz).1
    simp [hx0]
    simpa [tParams, casOp64] using h
  case vc10 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 hld hf1 hld2 hf2 hcas hf3 hf4 _
    simp at hnz hld2
    have hP1 : Pp (tParams t n tok) σ2.1 := (vc_pop_load _ hT v σ1.1 hld.1).fence hf1.1
    have hP3 : Pp (tParams t n tok) σ3.1 ∧ σ2.2 ≤ σ3.2 := by
      rcases hld2 with ⟨_, _, _, rfl⟩ | ⟨_, _, h, _⟩
      · exact ⟨hP1, by omega⟩
      · exact ⟨vc_pop_load _ hP1 _ σ3.1 h.1, by omega⟩
    have hc := (vc_pop_cas hL _ (hP3.1.fence hf2.1) (BitVec.setWidth 64 v) v4 hnz).2 old σ5.1
      (by simpa [hx0, tParams, casOp64] using hcas.1)
    simp at hbr
    rcases hc with ⟨-, hPp⟩ | ⟨heq, -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hdt], by simp [hd4],
        .inl ⟨rfl, Pp.fence (Pp.fence hPp hf3.1) hf4.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h1 := hld.2; have h2 := hcas.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc13 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 σ8 rng2 v11 σ9 σ10 hld hf1 hld2 hf2 hcas hf3 hf4 hf5
      hld3 hf6 _
    simp at hnz hld2 hbr hld3
    have hP1 : Pp (tParams t n tok) σ2.1 := (vc_pop_load _ hT v σ1.1 hld.1).fence hf1.1
    have hP3 : Pp (tParams t n tok) σ3.1 := by
      rcases hld2 with ⟨_, _, _, rfl⟩ | ⟨_, _, h, _⟩
      · exact hP1
      · exact vc_pop_load _ hP1 _ σ3.1 h.1
    have hc := (vc_pop_cas hL _ (hP3.fence hf2.1) (BitVec.setWidth 64 v) v4 hnz).2 old σ5.1
      (by simpa [hx0, tParams, casOp64] using hcas.1)
    rcases hc with ⟨hne, -⟩ | ⟨-, hPc⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    have hPc8 := ((hPc.fence hf3.1).fence hf4.1).fence hf5.1
    rcases hld3 with ⟨w, hw, -, -⟩ | ⟨-, w, ⟨hlo, -⟩, hv11⟩
    · simp [hd4] at hw
    have hfin := vc_pop_ldr (hd := by simp [tParams]) _ _ hPc8 w σ9.1 hlo
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hdt], by simp [hd4],
      .inr ⟨rfl, fun hcl => ?_⟩⟩, .inl (by decide)⟩
    obtain ⟨h1, h2⟩ := hfin (hf6.1.cl ▸ hcl)
    simp [tParams] at h1
    subst hv11
    simp
    exact ⟨h1.symm, by rw [h2]; rfl⟩
  case vc1 => exact hT ‹_›
  all_goals done

end PopperAt

section Popper

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberPopper)]

local instance treiberPopper.envG : CodeEnv := ⟨layout treiberPopper⟩

theorem popper_envGC (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParams t n tok)) :
    PartialTripleEnv (SharedEnv.counted (EQ (tParams t n tok)))
      (fun s σ => s.regs.X0.toBitVec = t ∧ Mem.loadInt s.dmem t 8 = none ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
        Pp (tParams t n tok) σ.1)
      treiberPopper (fun s σ => σ.1.cl → s.regs.X10.toBitVec = n ∧ s.regs.X11.toBitVec = 1)
      (fun _ _ _ => False) :=
  have hpl : Program.Placed treiberPopper "popper" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [popTable]) fun _ hlast =>
    popper_envGC_at t n tok hL hpl.toPlacedIn hlast

end Popper

end Kraken.Promising.SLR.EnvG.Treiber
