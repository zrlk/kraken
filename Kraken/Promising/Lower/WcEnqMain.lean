/-
**`MsqPilot`'s `main_e`, once, generic in the
`enq` fragment.** ISA: AArch64; machine: the executable
machine's per-thread environment semantics, partial correctness.

`MsqPilot`'s `mainE_run`/`mainE_pure` are stated at the ambient code
`layout MsqPilot.progE` (their block triples are the environment wp of that
executable), so they do not transport to a text with another `enq`. Here
`main_e` (`MsqPilot.mainEBody`, unchanged) is a placement-independent
`FragSpecEnvL` over `[mainEFrag, F]` for **every** `enq` fragment `F` with
`MsqPilot`'s `EnqPre`/`EnqPost` (`mainE_fragL`), and its purity twin for every
pure `F` (`mainE_pureL`); the runtime's return address `ra` replaces `endE`.
The blocks are `MsqPilot`'s `mainE_{pre,mid,tail}{,_pure}` with `ra` for
`endE`. `Kit.partialTripleEnv_of_fragL` turns both into the kit's fields at a
laid-out text (`Lower/WcEnqWhole.lean`).
-/
import Kraken.Promising.Lower.WcEnqSpecs
import Kraken.Promising.Lower.FragSpecCalls

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.WcMsq

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP)
open Kraken.Promising.Lower.MsqPilot (EnqPre EnqPost blTo ePre eMid eTail mainEBody)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- `main_e`'s fragment: its label and `MsqPilot`'s block. -/
def mainEFrag : Program := Directive.label "main_e" :: mainEBody

/-- At `main_e`: the return address `ra` in `x30`, `q`, the nodes, no `dmem`
word, `Start` of phase 1 (`MsqPilot`'s `MainEPre` with `ra` for `endE`). -/
def MainEPreF (P : Params2) (ra : Int64) (s : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = ra ∧ s.regs.X21.toBitVec = P.h ∧ s.regs.X22.toBitVec = P.n1 ∧
    s.regs.X23.toBitVec = P.n2 ∧ NoDmem s ∧ Start P (ph1 P) σ.1

/-- At a `bl enq` of phase `ph` (`MsqPilot`'s `AtEnq`, `ra` saved in `x19`). -/
def AtEnqF (P : Params2) (ph : Ph) (ra : Int64) (s : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) : Prop :=
  s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = ph.n ∧ Int64.ofBitVec s.regs.X19.toBitVec = ra ∧
    s.regs.X21.toBitVec = P.h ∧ s.regs.X23.toBitVec = P.n2 ∧ NoDmem s ∧ EL' P ph σ.1

/-- Behind a `bl enq` of phase `ph` (`MsqPilot`'s `AfterEnq`). -/
def AfterEnqF (P : Params2) (ph : Ph) (ra : Int64) (s : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) :
    Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X21.toBitVec = P.h ∧ s.regs.X23.toBitVec = P.n2 ∧
    NoDmem s ∧ Linked P ph σ.1

section Blocks

variable [CodeEnv]

theorem mainE_preF (P : Params2) (hL : QLocs2 P) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => MainEPreF P ra s σ ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨ePre⟩ : EnvProgram (SharedEnv.counted (EE2 P)))
    ⦃ (fun _ s σ => AtEnqF P (ph1 P) ra s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold ePre
  vcgen
  all_goals obtain ⟨⟨h30, h21, h22, h23, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp; done)
  case vc2 =>
    rename_i s σ0 σ1 σ2 rng hnone hf1 hf2 _
    have hE := (hT.fence (ph1_ok hL) hf1.1).fence (ph1_ok hL) hf2.1
    simp [h22]
    refine (vc_e_str2 (ph1_ok hL) _ hE _ ?_).1
    simp [ph1, D]
  case vc3 =>
    rename_i s σ0 σ1 σ2 rng dm σ3 σ4 σ5 hf1 hf2 hst hf3 hf4 _
    have hE := (hT.fence (ph1_ok hL) hf1.1).fence (ph1_ok hL) hf2.1
    simp [h22, hd4] at hst
    obtain ⟨rfl, hso, -⟩ := hst
    have hE' : EL' P (ph1 P) σ3.1 := by
      rcases hso with h | h <;>
        (refine (vc_e_str2 (ph1_ok hL) _ hE _ ?_).2 _ σ3.1 (by simpa [ph1, Params.dat] using h)
         simp [ph1, D])
    simp [AtEnqF, NoDmem, h21, h22, h23, h30, hd8, hd4]
    exact ⟨rfl, (hE'.fence (ph1_ok hL) hf3.1).fence (ph1_ok hL) hf4.1⟩
  all_goals done

theorem mainE_midF (P : Params2) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => AfterEnqF P (ph1 P) ra s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨eMid⟩ : EnvProgram (SharedEnv.counted (EE2 P))) ⦃ (fun _ s σ => AtEnqF P (ph2 P) ra s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold eMid
  vcgen
  all_goals obtain ⟨⟨h19, h21, h23, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp; done)
  case vc2 =>
    rename_i s σ0 σ1 rng hnone hf1 _
    simp [h23]
    refine (vc_e_str2 (ph2_ok P) _ (Start.fence (ph2_ok P) hT hf1.1) _ ?_).1
    simp [ph2, D2]
  case vc3 =>
    rename_i s σ0 σ1 rng dm σ2 σ3 σ4 hf1 hst hf2 hf3 _
    have hE : Start P (ph2 P) σ1.1 := Start.fence (ph2_ok P) hT hf1.1
    simp [h23, hd4] at hst
    obtain ⟨rfl, hso, -⟩ := hst
    have hE' : EL' P (ph2 P) σ2.1 := by
      rcases hso with h | h <;>
        (refine (vc_e_str2 (ph2_ok P) _ hE _ ?_).2 _ σ2.1 (by simpa [ph2, Params2.dat2] using h)
         simp [ph2, D2])
    simp [AtEnqF, NoDmem, h19, h21, h23, hd8, hd4]
    exact ⟨rfl, (hE'.fence (ph2_ok P) hf2.1).fence (ph2_ok P) hf3.1⟩
  all_goals done

theorem mainE_tailF (P : Params2) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => AfterEnqF P (ph2 P) ra s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨eTail⟩ : EnvProgram (SharedEnv.counted (EE2 P))) ⦃ (fun _ _ _ => False); fun a _ σ => a = ra ∧ ComE2 P σ.1 ⦄ := by
  intro s₀ g₀
  unfold eTail
  vcgen
  all_goals obtain ⟨⟨h19, h21, h23, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  rename_i s σ0 σ1 σ2 hf1 hf2 _
  exact ⟨by simpa using h19, ((hT.fence (ph2_ok P) hf1.1).fence (ph2_ok P) hf2.1).1⟩

end Blocks

/-- **`main_e`, placement-independent, for every `enq` fragment `F`** with
`MsqPilot`'s `EnqPre`/`EnqPost` (both phases): from `MainEPreF` it returns to
`ra` with `ComE2`. -/
theorem mainE_fragL (P : Params2) (hL : QLocs2 P) {F : Program}
    (hF : ∀ ph, PhOk P ph → FragSpecEnv (SharedEnv.counted (EE2 P)) F "enq" (EnqPre P ph) (EnqPost P ph)) :
    FragSpecEnvL (SharedEnv.counted (EE2 P)) [mainEFrag, F] "main_e" (MainEPreF P)
      (fun _ _ _ _ σ => ComE2 P σ.1) := by
  refine FragSpecEnvL.of_block (blk := ⟨"main_e", mainEBody, none⟩) (by decide) fun hpl ra s σ hpre => ?_
  have call : ∀ ph, PhOk P ph → ∀ s σ (rest : Program) (Q : MachineData → (SharedEnv.counted (EE2 P)).State → Prop)
      E, AtEnqF P ph ra s σ → (∀ s' σ', AfterEnqF P ph ra s' σ' → PartialWpEnv _ rest Q E s' σ') →
      PartialWpEnv (SharedEnv.counted (EE2 P)) (blTo "enq" :: rest) Q E s σ := by
    rintro ph hph s σ rest Q E ⟨h0, h1, h19, h21, h23, ⟨hd8, hd4⟩, hE⟩ hk
    refine PartialWpEnv.call ((hF ph hph).spec (hpl F (by simp))) fun ra' => ⟨⟨by simp [MachineData.lr,
      MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
      by simpa [MachineData.setLr, Reg64s.setXReg] using h1,
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩, hE⟩, ?_⟩
    rintro s' σ' ⟨⟨f19, -, f21, -, f23, -, -, -, -, -, fdm⟩, hLk⟩
    exact hk s' σ' ⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      by simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21,
      by simpa [f23, MachineData.setLr, Reg64s.setXReg] using h23,
      ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩, hLk⟩
  have h1 := (mainE_preF P hL ra s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
  refine fun s1 σ1 hA1 => call _ (ph1_ok hL) s1 σ1 _ _ _ hA1 fun s2 σ2 hB1 => ?_
  have h2 := (mainE_midF P ra s2 σ2).le_wp s2 σ2 ⟨hB1, rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
  exact fun s3 σ3 hA2 => call _ (ph2_ok P) s3 σ3 _ _ _ hA2 fun s4 σ4 hB2 =>
    PartialWpEnv.of_triple_exit (mainE_tailF P ra s4 σ4) ⟨hB2, rfl, rfl⟩

/-- The transport check: `MsqPilot`'s own `enq` fits `mainE_fragL` unchanged. -/
example (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) :=
  mainE_fragL P hL fun ph hph => MsqPilot.enqFrag_spec P hL ht ph hph

/-! ## Purity -/

section BlocksPure

variable [CodeEnv]

theorem mainE_pre_pureF (rel : Loc → Pred) (n1 n2 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X30.toBitVec = ra ∧
        s.regs.X22.toBitVec = n1 ∧ s.regs.X23.toBitVec = n2 ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨ePre⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X23.toBitVec = n2 ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold ePre
  vcgen
  all_goals obtain ⟨⟨h30, h22, h23, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem] at *
  case vc2 => rw [h22]; exact hd _
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hd4] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [h30, h23, hd8, hd4]

theorem mainE_mid_pureF (rel : Loc → Pred) (n2 : BitVec 64) (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v)
    (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X19.toBitVec = ra ∧
        s.regs.X23.toBitVec = n2 ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨eMid⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X23.toBitVec = n2 ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold eMid
  vcgen
  all_goals obtain ⟨⟨h19, h23, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem] at *
  case vc2 => rw [h23]; exact hd2 _
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hd4] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [h19, h23, hd8, hd4]

theorem mainE_tail_pureF (rel : Loc → Pred) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨eTail⟩ : EnvProgram (RP rel)) ⦃ (fun _ _ _ => False); fun a _ _ => a = ra ∧ True ⦄ := by
  intro s₀ g₀
  unfold eTail
  vcgen
  all_goals obtain ⟨h19, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  simpa using h19

end BlocksPure

/-- **`main_e` is pure, placement-independent, for every pure `enq`
fragment `F`** (release predicates pure at the data words `[n1]`, `[n2]`). -/
theorem mainE_pureL (rel : Loc → Pred) (n1 n2 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v) {F : Program}
    (hF : FragSpecEnv (RP rel) F "enq" (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s')) :
    FragSpecEnvL (RP rel) [mainEFrag, F] "main_e" (fun ra s _ => Int64.ofBitVec s.regs.X30.toBitVec = ra ∧
      s.regs.X22.toBitVec = n1 ∧ s.regs.X23.toBitVec = n2 ∧ NoDmem s) (fun _ _ _ _ _ => True) := by
  refine FragSpecEnvL.of_block (blk := ⟨"main_e", mainEBody, none⟩) (by decide) fun hpl ra s σ hpre => ?_
  have call : ∀ s σ (rest : Program) (Q : MachineData → (RP rel).State → Prop) E,
      Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X23.toBitVec = n2 ∧ NoDmem s →
      (∀ s' σ', Int64.ofBitVec s'.regs.X19.toBitVec = ra ∧ s'.regs.X23.toBitVec = n2 ∧ NoDmem s' →
        PartialWpEnv (RP rel) rest Q E s' σ') → PartialWpEnv (RP rel) (blTo "enq" :: rest) Q E s σ := by
    rintro s σ rest Q E ⟨h19, h23, ⟨hd8, hd4⟩⟩ hk
    refine PartialWpEnv.call (hF.spec (hpl F (by simp))) fun ra' => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩⟩, ?_⟩
    rintro s' σ' ⟨f19, -, -, -, f23, -, -, -, -, -, fdm⟩
    exact hk s' σ' ⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      by simpa [f23, MachineData.setLr, Reg64s.setXReg] using h23,
      ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩⟩
  have h1 := (mainE_pre_pureF rel n1 n2 hd ra s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
  refine fun s1 σ1 hA1 => call s1 σ1 _ _ _ hA1 fun s2 σ2 hB1 => ?_
  have h2 := (mainE_mid_pureF rel n2 hd2 ra s2 σ2).le_wp s2 σ2 ⟨hB1, rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
  exact fun s3 σ3 hA2 => call s3 σ3 _ _ _ hA2 fun s4 σ4 hB2 =>
    PartialWpEnv.of_triple_exit (mainE_tail_pureF rel ra s4 σ4) ⟨hB2.1, rfl, rfl⟩

end Kraken.Promising.Lower.WcMsq
