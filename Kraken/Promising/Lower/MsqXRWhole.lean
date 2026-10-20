/-
**The whole program through the x64 kit,
unconditional.** `enqT`/`deqT` are `msqXR`'s threads as
`KitX.LowerThreadX`s on `sAll` (`mainE_specXR`/`mainD_specXR`, the twins, the
shared post `MQX`); `msqXR_promising` goes through
`KitX.lower_promising_x64` (no value bridge: `dmem` empty), with the final
reading of `x64_msqueue2_envG_verbatim` (`tokH_pair_false`, `final_values`).
-/
import Kraken.Promising.Lower.MsqXRPure
import Kraken.Promising.Lower.KitX64

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.MsqXR

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 split_sAll)
open Kraken.Promising.Lower.KitX (LowerThreadX lower_promising_x64)
open Kraken.Promising.Lower.PilotXR (D8)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqXR)]

set_option maxRecDepth 20000 in
/-- The label `done` is the end of the text. -/
theorem labX_done : labX "done" = (layout msqXR).addrOf msqXR.length := by
  have hl : fragE.length + fragD.length = 66 := rfl
  have hm : msqXR[66]? = some (Directive.label "done") := by
    simp only [msqXR, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp [← hl]
  have hd : labX "done" = (layout msqXR).addrOf 66 :=
    Program.label_addrOf_drop msqXR_wf.nodup (by decide) (by decide)
  have h66 : (layout msqXR).2[66]? = some (Directive.label "done", Kraken.Layout.size Directive 66) := by
    simp [Layout.apply_snd, Layout.frag, hm]
  rw [show msqXR.length = 66 + 1 by simp [msqXR, ← hl]; omega, Executable.addrOf_succ _ h66,
    Executable.ValidLayout.label_size 66 "done" _ h66, hd]
  simp

/-- **No instruction steps at `done`.** -/
theorem msqXR_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labX "done" → ¬ (layout msqXR).instrStepEnv env x R := by
  rw [labX_done]
  exact not_instrStepEnv_of_end_labels env 1

omit [Executable.ValidLayout (layout msqXR)] in
/-- **`hB` of the enqueuer**: its token, whole (`hB_EV`'s proof). -/
theorem hB_E (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    (∃ n, (fun x : MachineState × (EStateX × Nat) => x.1.2 = labX "done" ∧ ComE P x.2.1) (t.st.st, (σ, n))) →
      t.prom = [] → EnvRel 0 (planE P) σ c t r g cl → cl → MQX P c r g := by
  rintro c t r g cl σ ⟨_, -, hcom⟩ hp hrel -
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2
  · rw [hp] at hts; cases hts

omit [Executable.ValidLayout (layout msqXR)] in
/-- **`hB` of the dequeuer**: `Dn` gives `DoneD2` (`hB_DV`'s proof). -/
theorem hB_D (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    (∃ n, (fun x : MachineState × (EStateX × Nat) =>
      x.1.2 = labX "done" ∧ Dn P (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13) x.2.1) (t.st.st, (σ, n))) →
      t.prom = [] → EnvRel 1 (planD P) σ c t r g cl → cl → MQX P c r g := by
  rintro c t r g cl σ ⟨_, -, hcom, hd⟩ hp hrel -
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1⟩
  · rw [hp] at hts; cases hts

/-- **The enqueuer of `msqXR` as a lowered x64 thread** (thread `0`). -/
noncomputable def enqT (P : Params) (hL : QLocs P) : LowerThreadX 0 sAll (MQX P) where
  e := layout msqXR
  valid := inferInstance
  pl := planE P
  hpl := planE_valid P
  shape := msqXR_phase1FX
  entry := labX "main_e"
  endPc := labX "done"
  stuck := msqXR_stuck
  Q x := x.1.2 = labX "done" ∧ ComE P x.2.1
  Q_end _ h := h.1
  hB := hB_E P
  PreR s _ := D8 s.dmem ∧ s.regs.get64 .r11 = (labX "done").toBitVec
  QR x := x.1.2 = labX "done"
  QR_end _ h := h
  pure := msqXR_pureE
  Pre := MainEPre P (labX "done")
  main := mainE_specXR P hL _

/-- **The dequeuer of `msqXR` as a lowered x64 thread** (thread `1`). -/
noncomputable def deqT (P : Params) (hL : QLocs P) (hpt : P.trk = false) : LowerThreadX 1 sAll (MQX P) where
  e := layout msqXR
  valid := inferInstance
  pl := planD P
  hpl := planD_valid P
  shape := msqXR_phase1FX
  entry := labX "main_d"
  endPc := labX "done"
  stuck := msqXR_stuck
  Q x := x.1.2 = labX "done" ∧ Dn P (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13) x.2.1
  Q_end _ h := h.1
  hB := hB_D P
  PreR s _ := D8 s.dmem ∧ s.regs.get64 .r11 = (labX "done").toBitVec
  QR x := x.1.2 = labX "done"
  QR_end _ h := h
  pure := msqXR_pureD
  Pre := MainDPre P (labX "done")
  main := mainD_specXR P hL hpt _

/-- The two threads. -/
noncomputable def msqT (P : Params) (hL : QLocs P) (hpt : P.trk = false) :
    (tid : Nat) → tid < 2 → LowerThreadX tid sAll (MQX P)
  | 0, _ => enqT P hL
  | 1, _ => deqT P hL hpt
  | _ + 2, h => absurd h (by omega)

/-- **The enqueuer at its start**: the image, pc at `main_e`, end and link at
`done`, `rbx = &tail`, `r12`/`r13` the nodes, `dmem` empty. -/
structure StartE (P : Params) (s : isa.State) : Prop where
  exe : s.exe = layout msqXR
  decls : s.decls = {}
  pc : s.st.2 = labX "main_e"
  endPc : s.endPc = labX "done"
  r11 : s.st.1.regs.get64 .r11 = (labX "done").toBitVec
  rbx : s.st.1.regs.get64 .rbx = P.t
  r12 : s.st.1.regs.get64 .r12 = P.n1
  r13 : s.st.1.regs.get64 .r13 = P.n2
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **The dequeuer at its start**: pc `main_d`, `rbx = &head`, `r14 = &tail`. -/
structure StartD (P : Params) (s : isa.State) : Prop where
  exe : s.exe = layout msqXR
  decls : s.decls = {}
  pc : s.st.2 = labX "main_d"
  endPc : s.endPc = labX "done"
  r11 : s.st.1.regs.get64 .r11 = (labX "done").toBitVec
  rbx : s.st.1.regs.get64 .rbx = P.h
  r14 : s.st.1.regs.get64 .r14 = P.t
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **The two-node Michael–Scott queue lowered to x64 functions (stackless
register-link convention), whole program, unconditional**: thread `0` runs
`main_e`, thread `1` `main_d`, started at `StartE`/`StartD` with the queue
initialised (`InitV`); every final configuration reachable under `Arch.tso`
has the dequeuer's `r12 = n1`, `r13 = n2` (FIFO). -/
theorem msqXR_promising {fuel : Nat} {P : Params} (hL : QLocs P) (hpt : P.trk = false) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartE P s0) (h1 : StartD P s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2FinalX P.n1 P.n2 cfg := by
  refine lower_promising_x64 (Φ := MsQueue2FinalX P.n1 P.n2) fuel sAll_le16 (erase_init hL _) rfl
    (msqT P hL hpt) ?_ hc hf ?_
  · intro tid h
    rcases tid with _ | _ | i
    · exact ⟨⟨h0.exe, h0.decls, h0.endPc, h0.pc, split_sAll h0.dmem, 0, d8_of_dmem h0.dmem, h0.r11⟩,
        0, h0.r11, h0.rbx, h0.r12, h0.r13, d8_of_dmem h0.dmem, e0_init P _⟩
    · exact ⟨⟨h1.exe, h1.decls, h1.endPc, h1.pc, split_sAll h1.dmem, 0, d8_of_dmem h1.dmem, h1.r11⟩,
        0, h1.r11, h1.rbx, h1.r14, d8_of_dmem h1.dmem, comD_init P _ hi⟩
    · simp only [List.length_cons, List.length_nil] at h; omega
  intro rF' g' E' hle hsize hB
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw P).mono hle
  have fin : ∀ i, i < cfg.threads.size → MQX P cfg (rF' i) g' → 1 ≤ ((rF' i).wr P.tokH).q ∨
      MsQueue2FinalX P.n1 P.n2 cfg := by
    rintro i hi (⟨th, hth, hd, hiv, hacq⟩ | hq)
    · exact .inr ⟨th, hth, final_values E' hW hL hiv
        (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hd⟩
    · exact .inl hq
  rcases fin 0 hi0 (hB 0 (Config.final_done hf hi0)) with hq0 | h
  · rcases fin 1 hi1 (hB 1 (Config.final_done hf hi1)) with hq1 | h
    · exact (tokH_pair_false E' hi0 hi1 (by decide) hq0 hq1).elim
    · exact h
  · exact h

end Kraken.Promising.Lower.MsqXR

#print axioms Kraken.Promising.Lower.MsqXR.msqXR_promising
