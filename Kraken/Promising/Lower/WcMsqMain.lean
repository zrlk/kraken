/-
**Shape A's `main_d`** (one dequeuer calling
WeakCore's `deq` twice) as a partial triple of the whole text `progD`, in
msqueue2's dequeuer environment `ED2 P`, counted.

`main_d` is `MsqPilot`'s (`dPre`, `bl deq`, `dMid`, `bl deq`, `dTail`), keeping
the first result `(tag, payload)` in `x20`/`x23`; the results end in
`x10, x11` (first) and `x12, x13` (second). Its postcondition `WDn`: `ComD2`
and `WDone`, which says per call "tag `1` (empty), or tag `0` and a `Deq`
of the payload", and `DoneD2` (FIFO) when both calls dequeued.
-/
import Kraken.Promising.Lower.WcMsqSpecs

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.WcMsq

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem)
open Kraken.Promising.Lower.MsqPilot (Kept dPre blTo)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- **The dequeuer's two results**: per call, tag `1` (empty) or tag `0`
with a `Deq` of the payload; both dequeued: `DoneD2` (the first swing below
the second). -/
def WDone (m : Memory) (P : Params2) (t1 v1 t2 v2 : BitVec 64) : Prop :=
  (t1 = 1 ∨ (t1 = 0 ∧ ∃ V, Deq m P V v1)) ∧ (t2 = 1 ∨ (t2 = 0 ∧ ∃ V, Deq m P V v2)) ∧
    (t1 = 0 → t2 = 0 → DoneD2 m P v1 v2)

theorem WDone.mono {m m' : Memory} (h : m.Prefix m') {P : Params2} {t1 v1 t2 v2 : BitVec 64}
    (hd : WDone m P t1 v1 t2 v2) : WDone m' P t1 v1 t2 v2 :=
  ⟨hd.1.imp_right fun ⟨e, V, hV⟩ => ⟨e, V, hV.mono h⟩, hd.2.1.imp_right fun ⟨e, V, hV⟩ => ⟨e, V, hV.mono h⟩,
    fun e1 e2 => (hd.2.2 e1 e2).mono h⟩

/-- **`d_end`** with the results in `x10`…`x13`. -/
def WDn (P : Params2) (x10 x11 x12 x13 : BitVec 64) (σ : State isa) : Prop :=
  ComD2 P σ ∧ WDone σ.snap.mem P x10 x11 x12 x13

section MainD

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD)]

local instance progD.env' : CodeEnv := ⟨layout progD⟩

/-- The end of the dequeuer's text: the runtime's return address. -/
abbrev endD : Int64 := (layout progD).addrOf progD.length

/-- At `main_d`: the return address in `x30`, `q = &head` in `x21`, no `dmem`
word, `ComD2`. -/
def MainDPre (P : Params2) (s : MachineData) (σ : (SharedEnv.counted (ED2 P)).State) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = endD ∧ s.regs.X21.toBitVec = P.h ∧ NoDmem s ∧ ComD2 P σ.1

/-- At a `bl deq`: its argument, the saved link, `q`, `ComD2`, and a frame
fact `Y`. -/
def AtDeq (P : Params2) (Y : MachineData → State isa → Prop) (s : MachineData)
    (σ : (SharedEnv.counted (ED2 P)).State) : Prop :=
  s.regs.X0.toBitVec = P.h ∧ Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ s.regs.X21.toBitVec = P.h ∧ NoDmem s ∧
    ComD2 P σ.1 ∧ Y s σ.1

/-- A result `(tag, payload)` of `deq`: empty, or the payload's `First`. -/
def Res1 (P : Params2) (tag v : BitVec 64) (σ : State isa) : Prop := tag = 1 ∨ (tag = 0 ∧ First P v σ)

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
/-- Between the calls: the first result to the callee-saved `x20`/`x23`. -/
theorem mainD_mid (P : Params2) :
    ∀ s₀ g₀, ⦃ fun s σ => (Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ s.regs.X21.toBitVec = P.h ∧ NoDmem s ∧
        ComD2 P σ.1 ∧ Res1 P s.regs.X0.toBitVec s.regs.X1.toBitVec σ.1) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨dMid⟩ : EnvProgram (SharedEnv.counted (ED2 P)))
    ⦃ (fun _ s σ => AtDeq P (fun s σ => Res1 P s.regs.X20.toBitVec s.regs.X23.toBitVec σ) s σ);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold dMid
  vcgen
  all_goals obtain ⟨⟨h19, h21, ⟨hd8, hd4⟩, hC, hF⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  rename_i s σ0 σ1 σ2 σ3 hf1 hf2 hf3 _
  have hY := yok_first (P := P) s.regs.X1.toBitVec
  simp [AtDeq, NoDmem, h21, h19, hd8, hd4]
  refine ⟨((hC.fence hf1.1).fence hf2.1).fence hf3.1, hF.imp_right fun ⟨e, h⟩ => ⟨e, ?_⟩⟩
  exact hY.fence (hY.fence (hY.fence h hf1.1) hf2.1) hf3.1

omit [Executable.ValidLayout (layout progD)] in
/-- The tail: the results to `x10`…`x13`, return with `WDn`. -/
theorem mainD_tail (P : Params2) :
    ∀ s₀ g₀, ⦃ fun s σ => (Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ ComD2 P σ.1 ∧
        WDone σ.1.snap.mem P s.regs.X20.toBitVec s.regs.X23.toBitVec s.regs.X0.toBitVec s.regs.X1.toBitVec) ∧
        s = s₀ ∧ σ = g₀ ⦄
      (⟨dTail⟩ : EnvProgram (SharedEnv.counted (ED2 P)))
    ⦃ (fun _ _ _ => False); fun a s σ => a = endD ∧
        WDn P s.regs.X10.toBitVec s.regs.X11.toBitVec s.regs.X12.toBitVec s.regs.X13.toBitVec σ.1 ⦄ := by
  intro s₀ g₀
  unfold dTail
  vcgen
  all_goals obtain ⟨⟨h19, hC, hD⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  rename_i s σ0 σ1 σ2 σ3 σ4 σ5 σ6 hf1 hf2 hf3 hf4 hf5 hf6 _
  refine ⟨by simpa using h19, (((((hC.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1).fence hf5.1).fence hf6.1,
    ?_⟩
  simpa [hf1.1.snap, hf2.1.snap, hf3.1.snap, hf4.1.snap, hf5.1.snap, hf6.1.snap] using hD

/-- **`main_d`'s run**: from `main_d` to the return into the end of the
text with `WDn`, through `wdeq_spec` twice. -/
theorem mainD_run (P : Params2) (hL : QLocs2 P) (s : MachineData)
    (σ : (SharedEnv.counted (ED2 P)).State) (hpre : MainDPre P s σ) :
    Safely (cenv.instrStepEnv (SharedEnv.counted (ED2 P)))
      (fun x => x.1.2 = endD ∧ WDn P x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.1.1.regs.X12.toBitVec
        x.1.1.regs.X13.toBitVec x.2.1)
      ((s, (_root_.Executable.labels cenv).label "main_d"), σ) := by
  have hb : Program.blockAt progD "main_d" = some ⟨"main_d", mainDBody, some "deq"⟩ := by decide
  have hbody : PartialWpEnv (SharedEnv.counted (ED2 P)) mainDBody (fun _ _ => False)
      (fun a s σ => a = endD ∧ WDn P s.regs.X10.toBitVec s.regs.X11.toBitVec s.regs.X12.toBitVec
        s.regs.X13.toBitVec σ.1) s σ := by
    have h1 := (mainD_pre P s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
    rintro s1 σ1 ⟨h0, h19, h21, ⟨hd8, hd4⟩, hC, -⟩
    refine PartialWpEnv.call (wdeq_spec P hL) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩, hC⟩, ?_⟩
    rintro s2 σ2 ⟨⟨f19, -, f21, -, -, -, -, -, -, -, fdm⟩, hC2, -, hR2⟩
    have h2 := (mainD_mid P s2 σ2).le_wp s2 σ2 ⟨⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      by simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21,
      ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩, hC2,
      hR2.imp_right (fun h => ⟨h.1, h.2.1⟩)⟩, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
    rintro s3 σ3 ⟨h0', h19', h21', ⟨hd8', hd4'⟩, hC3, hR3⟩
    refine PartialWpEnv.call (wdeq_spec P hL) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      by simpa [MachineData.setLr, Reg64s.setXReg] using h0',
      ⟨by simpa [MachineData.setLr] using hd8', by simpa [MachineData.setLr] using hd4'⟩, hC3⟩, ?_⟩
    rintro s4 σ4 ⟨⟨g19, g20, -, -, g23, -, -, -, -, -, -⟩, hC4, hK4, hR4⟩
    have h20 : s4.regs.X20.toBitVec = s3.regs.X20.toBitVec := by
      simpa [MachineData.setLr, Reg64s.setXReg] using congrArg (·.toBitVec) g20
    have h23 : s4.regs.X23.toBitVec = s3.regs.X23.toBitVec := by
      simpa [MachineData.setLr, Reg64s.setXReg] using congrArg (·.toBitVec) g23
    have hD : WDone σ4.1.snap.mem P s4.regs.X20.toBitVec s4.regs.X23.toBitVec s4.regs.X0.toBitVec
        s4.regs.X1.toBitVec := by
      rw [h20, h23]
      refine ⟨?_, ?_, fun e1 e2 => ?_⟩
      · rcases hR3 with h | ⟨e, hF⟩
        · exact .inl h
        · obtain ⟨V, hV, -⟩ := hK4 _ hF; exact .inr ⟨e, V, hV⟩
      · rcases hR4 with h | ⟨e, ⟨V, hV, -⟩, -⟩
        · exact .inl h
        · exact .inr ⟨e, V, hV⟩
      · rcases hR3 with h | ⟨-, hF⟩
        · rw [h] at e1; cases e1
        rcases hR4 with h | ⟨-, -, hD⟩
        · rw [h] at e2; cases e2
        exact hD _ hF
    have h3 := (mainD_tail P s4 σ4).le_wp s4 σ4 ⟨⟨by simpa [g19, MachineData.setLr, Reg64s.setXReg] using h19',
      hC4, hD⟩, rfl, rfl⟩
    rw [wpEnv_eq] at h3
    exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h3)
  exact (hbody _ (progD_placed.block _ _ hb)).mono fun x hx => hx.resolve_left fun h => h.2

/-- **`main_d` as a partial triple of the whole text**. -/
theorem mainD_partialTripleEnv (P : Params2) (hL : QLocs2 P) :
    PartialTripleEnv (SharedEnv.counted (ED2 P)) (MainDPre P) progD
      (fun s σ => WDn P s.regs.X10.toBitVec s.regs.X11.toBitVec s.regs.X12.toBitVec s.regs.X13.toBitVec σ.1)
      (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := progD) progD [] 0 (by simp)
  rw [← progD_placed.entry pc hpc]
  refine (mainD_run P hL s σ hpre).mono fun x ⟨hx, hd⟩ => .inl ⟨?_, hd⟩
  rw [hx, progD_placed.entry _ hs0]
  rw [Nat.zero_add] at haf
  exact haf.symm

end MainD

end Kraken.Promising.Lower.WcMsq
