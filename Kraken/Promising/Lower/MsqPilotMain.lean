/-
**Part 3: `main_e` and `main_d` from the function
specifications.** Environments as in
`Lower/MsqPilotSpecs.lean`.

Each `main` is one block: its straight-line pieces by one `vcgen` call each
(the data-word stores by msqueue2's `vc_e_str2`), its two `bl`s by
`PartialWpEnv.call` through `enq_spec`/`deq_spec`, the callee-saved frame
(`x19`, `x20`, `x21`, `x23`, `dmem`) carried by `CalleeSaved`. The run returns
into the runtime's address (the end of the text); `main{E,D}_partialTripleEnv`
is that run as a `PartialTripleEnv` of the whole text, the form
`qa64CAdj_of_partialTripleEnv` takes, with msqueue2's postconditions (`ComE2`,
`Dn2 x10 x11`).
-/
import Kraken.Promising.Lower.MsqPilotSpecs

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.MsqPilot

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## `main_e` -/

section MainE

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progE)]

local instance progE.env' : CodeEnv := ⟨layout progE⟩

/-- The end of the enqueuer's text: the runtime's return address. -/
abbrev endE : Int64 := (layout progE).addrOf progE.length

/-- At `main_e`: the return address in `x30`, `q = &head` in `x21`, the
nodes in `x22`/`x23`, no `dmem` word, `Start` of phase 1. -/
def MainEPre (P : Params2) (s : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = endE ∧ s.regs.X21.toBitVec = P.h ∧ s.regs.X22.toBitVec = P.n1 ∧
    s.regs.X23.toBitVec = P.n2 ∧ NoDmem s ∧ Start P (ph1 P) σ.1

/-- At a `bl enq` of phase `ph`: its arguments, the saved link, `q`, `n2`. -/
def AtEnq (P : Params2) (ph : Ph) (s : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) : Prop :=
  s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = ph.n ∧ Int64.ofBitVec s.regs.X19.toBitVec = endE ∧
    s.regs.X21.toBitVec = P.h ∧ s.regs.X23.toBitVec = P.n2 ∧ NoDmem s ∧ EL' P ph σ.1

/-- Behind a `bl enq` of phase `ph`: the saved link, `q`, `n2`, `Linked`. -/
def AfterEnq (P : Params2) (ph : Ph) (s : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) : Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = endE ∧ s.regs.X21.toBitVec = P.h ∧ s.regs.X23.toBitVec = P.n2 ∧
    NoDmem s ∧ Linked P ph σ.1

omit [Executable.ValidLayout (layout progE)] in
/-- **The prefix**: link save, `n1`'s data word, the arguments. -/
theorem mainE_pre (P : Params2) (hL : QLocs2 P) :
    ∀ s₀ g₀, ⦃ fun s σ => MainEPre P s σ ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨ePre⟩ : EnvProgram (SharedEnv.counted (EE2 P)))
    ⦃ (fun _ s σ => AtEnq P (ph1 P) s σ); fun _ _ _ => False ⦄ := by
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
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hE' : EL' P (ph1 P) σ3.1 := by
      rcases hso with h | h <;>
        (refine (vc_e_str2 (ph1_ok hL) _ hE _ ?_).2 _ σ3.1 (by simpa [ph1, Params.dat] using h)
         simp [ph1, D])
    simp [AtEnq, NoDmem, h21, h22, h23, h30, hd8, hd4]
    exact ⟨rfl, (hE'.fence (ph1_ok hL) hf3.1).fence (ph1_ok hL) hf4.1⟩
  all_goals done

omit [Executable.ValidLayout (layout progE)] in
/-- **Between the calls**: `n2`'s data word, the arguments. -/
theorem mainE_mid (P : Params2) :
    ∀ s₀ g₀, ⦃ fun s σ => AfterEnq P (ph1 P) s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨eMid⟩ : EnvProgram (SharedEnv.counted (EE2 P)))
    ⦃ (fun _ s σ => AtEnq P (ph2 P) s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold eMid
  vcgen
  all_goals obtain ⟨⟨h19, h21, h23, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp; done)
  case vc2 =>
    rename_i s σ0 σ1 rng hnone hf1 _
    have hE : Start P (ph2 P) σ1.1 := Start.fence (ph2_ok P) hT hf1.1
    simp [h23]
    refine (vc_e_str2 (ph2_ok P) _ hE _ ?_).1
    simp [ph2, D2]
  case vc3 =>
    rename_i s σ0 σ1 rng dm σ2 σ3 σ4 hf1 hst hf2 hf3 _
    have hE : Start P (ph2 P) σ1.1 := Start.fence (ph2_ok P) hT hf1.1
    simp [h23, hd4] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hE' : EL' P (ph2 P) σ2.1 := by
      rcases hso with h | h <;>
        (refine (vc_e_str2 (ph2_ok P) _ hE _ ?_).2 _ σ2.1 (by simpa [ph2, Params2.dat2] using h)
         simp [ph2, D2])
    simp [AtEnq, NoDmem, h19, h21, h23, hd8, hd4]
    exact ⟨rfl, (hE'.fence (ph2_ok P) hf2.1).fence (ph2_ok P) hf3.1⟩
  all_goals done

omit [Executable.ValidLayout (layout progE)] in
/-- **The tail**: restore the link, return with `ComE2`. -/
theorem mainE_tail (P : Params2) :
    ∀ s₀ g₀, ⦃ fun s σ => AfterEnq P (ph2 P) s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨eTail⟩ : EnvProgram (SharedEnv.counted (EE2 P)))
    ⦃ (fun _ _ _ => False); fun a _ σ => a = endE ∧ ComE2 P σ.1 ⦄ := by
  intro s₀ g₀
  unfold eTail
  vcgen
  all_goals obtain ⟨⟨h19, h21, h23, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  rename_i s σ0 σ1 σ2 hf1 hf2 _
  exact ⟨by simpa using h19, ((hT.fence (ph2_ok P) hf1.1).fence (ph2_ok P) hf2.1).1⟩

/-- **`main_e`'s run**: from `main_e` to the return into the end of the
text with `ComE2`, through `enq_spec` twice. -/
theorem mainE_run (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (s : MachineData)
    (σ : (SharedEnv.counted (EE2 P)).State) (hpre : MainEPre P s σ) :
    Safely (cenv.instrStepEnv (SharedEnv.counted (EE2 P))) (fun x => x.1.2 = endE ∧ ComE2 P x.2.1)
      ((s, (_root_.Executable.labels cenv).label "main_e"), σ) := by
  have hb : Program.blockAt progE "main_e" = some ⟨"main_e", mainEBody, some "enq"⟩ := by decide
  have call : ∀ ph, PhOk P ph → ∀ s σ (rest : Program) (Q : MachineData → (SharedEnv.counted (EE2 P)).State → Prop)
      (E : Int64 → MachineData → (SharedEnv.counted (EE2 P)).State → Prop), AtEnq P ph s σ →
      (∀ s' σ', AfterEnq P ph s' σ' → PartialWpEnv (SharedEnv.counted (EE2 P)) rest Q E s' σ') →
      PartialWpEnv (SharedEnv.counted (EE2 P)) (blTo "enq" :: rest) Q E s σ := by
    rintro ph hph s σ rest Q E ⟨h0, h1, h19, h21, h23, ⟨hd8, hd4⟩, hE⟩ hk
    refine PartialWpEnv.call (enq_spec P hL ht ph hph) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      by simpa [MachineData.setLr, Reg64s.setXReg] using h0, by simpa [MachineData.setLr, Reg64s.setXReg] using h1,
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩, hE⟩, ?_⟩
    rintro s' σ' ⟨⟨f19, -, f21, -, f23, -, -, -, -, -, fdm⟩, hLk⟩
    exact hk s' σ' ⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      by simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21,
      by simpa [f23, MachineData.setLr, Reg64s.setXReg] using h23,
      ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩, hLk⟩
  have hbody : PartialWpEnv (SharedEnv.counted (EE2 P)) mainEBody (fun _ _ => False)
      (fun a _ σ => a = endE ∧ ComE2 P σ.1) s σ := by
    have h1 := (mainE_pre P hL s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
    intro s1 σ1 hA1
    refine call _ (ph1_ok hL) s1 σ1 _ _ _ hA1 fun s2 σ2 hB1 => ?_
    have h2 := (mainE_mid P s2 σ2).le_wp s2 σ2 ⟨hB1, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
    intro s3 σ3 hA2
    refine call _ (ph2_ok P) s3 σ3 _ _ _ hA2 fun s4 σ4 hB2 => ?_
    have h3 := (mainE_tail P s4 σ4).le_wp s4 σ4 ⟨hB2, rfl, rfl⟩
    rw [wpEnv_eq] at h3
    exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h3)
  exact (hbody _ (progE_placed.block _ _ hb)).mono fun x hx => hx.resolve_left fun h => h.2

/-- **`main_e` as a partial triple of the whole text**. -/
theorem mainE_partialTripleEnv (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) :
    PartialTripleEnv (SharedEnv.counted (EE2 P)) (MainEPre P) progE (fun _ σ => ComE2 P σ.1)
      (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := progE) progE [] 0 (by simp)
  rw [← progE_placed.entry pc hpc]
  refine (mainE_run P hL ht s σ hpre).mono fun x ⟨hx, hd⟩ => .inl ⟨?_, hd⟩
  rw [hx, progE_placed.entry _ hs0]
  rw [Nat.zero_add] at haf
  exact haf.symm

end MainE

/-! ## `main_d` -/

section MainD

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD)]

local instance progD.env' : CodeEnv := ⟨layout progD⟩

/-- The end of the dequeuer's text: the runtime's return address. -/
abbrev endD : Int64 := (layout progD).addrOf progD.length

/-- At `main_d`: the return address in `x30`, `q = &head` in `x21`, no `dmem`
word, `ComD2`. -/
def MainDPre (P : Params2) (s : MachineData) (σ : (SharedEnv.counted (ED2 P)).State) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = endD ∧ s.regs.X21.toBitVec = P.h ∧ NoDmem s ∧ ComD2 P σ.1

/-- At a `bl deq`: its argument, the saved link, `q`, `ComD2`, and the frame
fact `Y` (`True`, then the first result's `First`). -/
def AtDeq (P : Params2) (Y : MachineData → State isa → Prop) (s : MachineData)
    (σ : (SharedEnv.counted (ED2 P)).State) : Prop :=
  s.regs.X0.toBitVec = P.h ∧ Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ s.regs.X21.toBitVec = P.h ∧ NoDmem s ∧
    ComD2 P σ.1 ∧ Y s σ.1

omit [Executable.ValidLayout (layout progD)] in
theorem mainD_pre (P : Params2) :
    ∀ s₀ g₀, ⦃ fun s σ => MainDPre P s σ ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨dPre⟩ : EnvProgram (SharedEnv.counted (ED2 P)))
    ⦃ (fun _ s σ => AtDeq P (fun _ _ => True) s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold dPre
  vcgen
  all_goals obtain ⟨⟨h30, h21, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  rename_i s σ0 σ1 σ2 hf1 hf2 _
  simp [AtDeq, NoDmem, h21, h30, hd8, hd4]
  exact (hT.fence hf1.1).fence hf2.1

omit [Executable.ValidLayout (layout progD)] in
/-- Between the calls: the first result to the callee-saved `x20`. -/
theorem mainD_mid (P : Params2) :
    ∀ s₀ g₀, ⦃ fun s σ => (Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ s.regs.X21.toBitVec = P.h ∧ NoDmem s ∧
        ComD2 P σ.1 ∧ First P s.regs.X0.toBitVec σ.1) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨dMid⟩ : EnvProgram (SharedEnv.counted (ED2 P)))
    ⦃ (fun _ s σ => AtDeq P (fun s σ => First P s.regs.X20.toBitVec σ) s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold dMid
  vcgen
  all_goals obtain ⟨⟨h19, h21, ⟨hd8, hd4⟩, hC, hF⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  rename_i s σ0 σ1 σ2 hf1 hf2 _
  have hY := yok_first (P := P) s.regs.X0.toBitVec
  simp [AtDeq, NoDmem, h21, h19, hd8, hd4]
  exact ⟨(hC.fence hf1.1).fence hf2.1, hY.fence (hY.fence hF hf1.1) hf2.1⟩

omit [Executable.ValidLayout (layout progD)] in
/-- The tail: the results to `x10`/`x11`, return with `Dn2`. -/
theorem mainD_tail (P : Params2) :
    ∀ s₀ g₀, ⦃ fun s σ => (Int64.ofBitVec s.regs.X19.toBitVec = endD ∧
        Dn2 P s.regs.X20.toBitVec s.regs.X0.toBitVec σ.1) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨dTail⟩ : EnvProgram (SharedEnv.counted (ED2 P)))
    ⦃ (fun _ _ _ => False); fun a s σ => a = endD ∧ Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1 ⦄ := by
  intro s₀ g₀
  unfold dTail
  vcgen
  all_goals obtain ⟨⟨h19, hD⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  rename_i s σ0 σ1 σ2 σ3 σ4 hf1 hf2 hf3 hf4 _
  refine ⟨by simpa using h19, ?_⟩
  simpa using (((hD.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1

/-- **`main_d`'s run**: from `main_d` to the return into the end of the
text with `Dn2 x10 x11`, through `deq_spec` twice. -/
theorem mainD_run (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (s : MachineData)
    (σ : (SharedEnv.counted (ED2 P)).State) (hpre : MainDPre P s σ) :
    Safely (cenv.instrStepEnv (SharedEnv.counted (ED2 P)))
      (fun x => x.1.2 = endD ∧ Dn2 P x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.2.1)
      ((s, (_root_.Executable.labels cenv).label "main_d"), σ) := by
  have hb : Program.blockAt progD "main_d" = some ⟨"main_d", mainDBody, some "deq"⟩ := by decide
  have hbody : PartialWpEnv (SharedEnv.counted (ED2 P)) mainDBody (fun _ _ => False)
      (fun a s σ => a = endD ∧ Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) s σ := by
    have h1 := (mainD_pre P s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
    rintro s1 σ1 ⟨h0, h19, h21, ⟨hd8, hd4⟩, hC, -⟩
    refine PartialWpEnv.call (deq_spec P hL ht) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩, hC⟩, ?_⟩
    rintro s2 σ2 ⟨⟨f19, -, f21, -, -, -, -, -, -, -, fdm⟩, hC2, hF2, -⟩
    have h2 := (mainD_mid P s2 σ2).le_wp s2 σ2 ⟨⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      by simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21,
      ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩, hC2, hF2⟩,
      rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
    rintro s3 σ3 ⟨h0', h19', h21', ⟨hd8', hd4'⟩, hC3, hF3⟩
    refine PartialWpEnv.call (deq_spec P hL ht) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      by simpa [MachineData.setLr, Reg64s.setXReg] using h0',
      ⟨by simpa [MachineData.setLr] using hd8', by simpa [MachineData.setLr] using hd4'⟩, hC3⟩, ?_⟩
    rintro s4 σ4 ⟨⟨g19, g20, -, -, -, -, -, -, -, -, -⟩, hC4, -, hD4⟩
    have h20 : s4.regs.X20.toBitVec = s3.regs.X20.toBitVec := by
      simpa [MachineData.setLr, Reg64s.setXReg] using congrArg (·.toBitVec) g20
    have h3 := (mainD_tail P s4 σ4).le_wp s4 σ4 ⟨⟨by simpa [g19, MachineData.setLr, Reg64s.setXReg] using h19',
      hC4, by rw [h20]; exact hD4 _ hF3⟩, rfl, rfl⟩
    rw [wpEnv_eq] at h3
    exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h3)
  exact (hbody _ (progD_placed.block _ _ hb)).mono fun x hx => hx.resolve_left fun h => h.2

/-- **`main_d` as a partial triple of the whole text**. -/
theorem mainD_partialTripleEnv (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) :
    PartialTripleEnv (SharedEnv.counted (ED2 P)) (MainDPre P) progD
      (fun s σ => Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := progD) progD [] 0 (by simp)
  rw [← progD_placed.entry pc hpc]
  refine (mainD_run P hL ht s σ hpre).mono fun x ⟨hx, hd⟩ => .inl ⟨?_, hd⟩
  rw [hx, progD_placed.entry _ hs0]
  rw [Nat.zero_add] at haf
  exact haf.symm

end MainD

end Kraken.Promising.Lower.MsqPilot
