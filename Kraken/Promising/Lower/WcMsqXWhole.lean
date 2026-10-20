/-
**WeakCore's try-once Michael–Scott queue lowered to x64, whole program, on
the executable Promising machine** (`Reachable Arch.tso`). ISA: x64 (`isa`).

`wcMsqX_promising` goes through `KitX.lower_promising_x64` (`dmem` empty, no
value bridge): thread `0` runs the pilot's enqueuer (`main_e`: `enq(n1);
enq(n2)`), thread `1` runs `main_w` (`wdeq` twice, results in `r12`/`r13`,
`r14`/`r15`), on the try-once protocol (`erase_initW`, `ghost₀W`). The shared
postcondition `MQW` is the dequeuer done (`DoneW`, `InitV`, acquire ids) or
the enqueuer's token whole; `tokH_pair_false` excludes both holding it and
`final_valuesW` reads the results (`WcMsqXFinal`): `(n1, n2)`, `(n1, ∅)`,
`(∅, n1)` or `(∅, ∅)` (∅: tag non-zero), the explorer's finals.
-/
import Kraken.Promising.Lower.WcMsqXPure
import Kraken.Promising.Lower.KitX64

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.WcMsqX

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 split_sAll)
open Kraken.Promising.Lower.KitX (LowerThreadX lower_promising_x64)
open Kraken.Promising.Lower.PilotXR (D8)
open Kraken.Promising.Lower.MsqXR (fragE)

/-! ## The final reading -/

/-- **The try-once results**: `(n1, n2)`, `(n1, ∅)`, `(∅, n1)` or `(∅, ∅)`. -/
def WValsX (n1 n2 : BitVec 64) (r1 r2 : Option (BitVec 64)) : Prop :=
  (r1 = some n1 ∧ r2 = some n2) ∨ (r1 = some n1 ∧ r2 = none) ∨ (r1 = none ∧ r2 = some n1) ∨
    (r1 = none ∧ r2 = none)

/-- **The property of `wcMsqX`**: thread `1`'s results (`resW` of `r12`,
`r13` and of `r14`, `r15`) satisfy `WValsX`. -/
def WcMsqXFinal (n1 n2 : BitVec 64) (c : Config isa) : Prop :=
  ∃ th, c.threads[1]? = some th ∧ WValsX n1 n2 (resW (th.st.st.1.regs.get64 .r12) (th.st.st.1.regs.get64 .r13))
    (resW (th.st.st.1.regs.get64 .r14) (th.st.st.1.regs.get64 .r15))

/-- **The shared postcondition**: the dequeuer (thread `1`) done with its
results, the initial values and the acquire id `0` of every queue word; or
the enqueuer's token whole. -/
def MQW (P : Params) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  (∃ th, c.threads[1]? = some th ∧
    DoneW c.mem P r (resW (th.st.st.1.regs.get64 .r12) (th.st.st.1.regs.get64 .r13))
      (resW (th.st.st.1.regs.get64 .r14) (th.st.st.1.regs.get64 .r15)) ∧ InitV c.mem P ∧
    ∀ x, P.IsW x → 1 ≤ r.acq x 0) ∨ 1 ≤ (r.wr P.tokH).q

/-- Alias of `MsQueueX.DoneW.mono` (`SLR/EnvG/X64MsQueueWFinal.lean`). -/
theorem DoneW.mono {P : Params} {m m' : Memory} (h : m.Prefix m') {R : Res} {r1 r2 : Option (BitVec 64)}
    (hd : DoneW m P R r1 r2) : DoneW m' P R r1 r2 :=
  MsQueueX.DoneW.mono h hd

variable [layout : _root_.Layout] [Executable.ValidLayout (layout wcMsqX)]

set_option maxRecDepth 20000 in
/-- The label `done` is the end of the text. -/
theorem labW_done : labW "done" = (layout wcMsqX).addrOf wcMsqX.length := by
  have hl : fragE.length + fragW.length = 60 := rfl
  have hm : wcMsqX[60]? = some (Directive.label "done") := by
    simp only [wcMsqX, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp [← hl]
  have hd : labW "done" = (layout wcMsqX).addrOf 60 :=
    Program.label_addrOf_drop wcMsqX_wf.nodup (by decide) (by decide)
  have h60 : (layout wcMsqX).2[60]? = some (Directive.label "done", Kraken.Layout.size Directive 60) := by
    simp [Layout.apply_snd, Layout.frag, hm]
  rw [show wcMsqX.length = 60 + 1 by simp [wcMsqX, ← hl]; omega, Executable.addrOf_succ _ h60,
    Executable.ValidLayout.label_size 60 "done" _ h60, hd]
  simp

/-- **No instruction steps at `done`.** -/
theorem wcMsqX_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labW "done" → ¬ (layout wcMsqX).instrStepEnv env x R := by
  rw [labW_done]
  exact not_instrStepEnv_of_end_labels env 1

omit [Executable.ValidLayout (layout wcMsqX)] in
/-- **`hB` of the enqueuer**: its token, whole. -/
theorem hB_EW (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    (∃ n, (fun x : MachineState × (EStateX × Nat) => x.1.2 = labW "done" ∧ ComEW P x.2.1) (t.st.st, (σ, n))) →
      t.prom = [] → EnvRel 0 (planE P) σ c t r g cl → cl → MQW P c r g := by
  rintro c t r g cl σ ⟨_, -, hcom⟩ hp hrel -
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2
  · rw [hp] at hts; cases hts

omit [Executable.ValidLayout (layout wcMsqX)] in
/-- **`hB` of the dequeuer**: `DnW` at the thread's resource. -/
theorem hB_W (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    (∃ n, (fun x : MachineState × (EStateX × Nat) => x.1.2 = labW "done" ∧
      DnW P (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13) (x.1.1.regs.get64 .r14) (x.1.1.regs.get64 .r15)
        x.2.1) (t.st.st, (σ, n))) →
      t.prom = [] → EnvRel 1 (planDW P) σ c t r g cl → cl → MQW P c r g := by
  rintro c t r g cl σ ⟨_, -, hcom, hiv, hd⟩ hp hrel -
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, DoneW.mono hpre hd, hiv.of_init hrel.snap.init, hcom.2.2.1⟩
  · rw [hp] at hts; cases hts

/-- **The enqueuer of `wcMsqX` as a lowered x64 thread** (thread `0`). -/
noncomputable def enqTW (P : Params) (hL : QLocs P) : LowerThreadX 0 sAll (MQW P) where
  e := layout wcMsqX
  valid := inferInstance
  pl := planE P
  hpl := planE_valid P
  shape := wcMsqX_phase1FX
  entry := labW "main_e"
  endPc := labW "done"
  stuck := wcMsqX_stuck
  Q x := x.1.2 = labW "done" ∧ ComEW P x.2.1
  Q_end _ h := h.1
  hB := hB_EW P
  PreR s _ := D8 s.dmem ∧ s.regs.get64 .r11 = (labW "done").toBitVec
  QR x := x.1.2 = labW "done"
  QR_end _ h := h
  pure := wcMsqX_pureE
  Pre := MainEPreW P (labW "done")
  main := mainE_specXW P hL _

/-- **The try-once dequeuer of `wcMsqX` as a lowered x64 thread** (thread `1`). -/
noncomputable def deqTW (P : Params) (hL : QLocs P) (hpt : P.trk = false) : LowerThreadX 1 sAll (MQW P) where
  e := layout wcMsqX
  valid := inferInstance
  pl := planDW P
  hpl := planDW_valid P
  shape := wcMsqX_phase1FX
  entry := labW "main_w"
  endPc := labW "done"
  stuck := wcMsqX_stuck
  Q x := x.1.2 = labW "done" ∧ DnW P (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13) (x.1.1.regs.get64 .r14)
    (x.1.1.regs.get64 .r15) x.2.1
  Q_end _ h := h.1
  hB := hB_W P
  PreR s _ := D8 s.dmem ∧ s.regs.get64 .r11 = (labW "done").toBitVec
  QR x := x.1.2 = labW "done"
  QR_end _ h := h
  pure := wcMsqX_pureW
  Pre := MainWPre P (labW "done")
  main := mainW_specXW P hL hpt _

/-- The two threads. -/
noncomputable def wcT (P : Params) (hL : QLocs P) (hpt : P.trk = false) :
    (tid : Nat) → tid < 2 → LowerThreadX tid sAll (MQW P)
  | 0, _ => enqTW P hL
  | 1, _ => deqTW P hL hpt
  | _ + 2, h => absurd h (by omega)

/-- **The enqueuer at its start**: the image, pc at `main_e`, end and link at
`done`, `rbx = &tail`, `r12`/`r13` the nodes, `dmem` empty. -/
structure StartEW (P : Params) (s : isa.State) : Prop where
  exe : s.exe = layout wcMsqX
  decls : s.decls = {}
  pc : s.st.2 = labW "main_e"
  endPc : s.endPc = labW "done"
  r11 : s.st.1.regs.get64 .r11 = (labW "done").toBitVec
  rbx : s.st.1.regs.get64 .rbx = P.t
  r12 : s.st.1.regs.get64 .r12 = P.n1
  r13 : s.st.1.regs.get64 .r13 = P.n2
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **The dequeuer at its start**: pc `main_w`, `rbx = &head`. -/
structure StartW (P : Params) (s : isa.State) : Prop where
  exe : s.exe = layout wcMsqX
  decls : s.decls = {}
  pc : s.st.2 = labW "main_w"
  endPc : s.endPc = labW "done"
  r11 : s.st.1.regs.get64 .r11 = (labW "done").toBitVec
  rbx : s.st.1.regs.get64 .rbx = P.h
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **WeakCore's try-once Michael–Scott queue lowered to x64, whole
program**: thread `0` runs `main_e`, thread `1` `main_w`, started at
`StartEW`/`StartW` with the queue initialised (`InitV`); at every final
configuration reachable under `Arch.tso` the dequeuer's two results are
`(n1, n2)`, `(n1, ∅)`, `(∅, n1)` or `(∅, ∅)`. -/
theorem wcMsqX_promising {fuel : Nat} {P : Params} (hL : QLocs P) (hpt : P.trk = false) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartEW P s0) (h1 : StartW P s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : WcMsqXFinal P.n1 P.n2 cfg := by
  refine lower_promising_x64 (Φ := WcMsqXFinal P.n1 P.n2) fuel sAll_le16 (erase_initW hL _) rfl
    (wcT P hL hpt) ?_ hc hf ?_
  · intro tid h
    rcases tid with _ | _ | i
    · exact ⟨⟨h0.exe, h0.decls, h0.endPc, h0.pc, split_sAll h0.dmem, 0, d8_of_dmem h0.dmem, h0.r11⟩,
        0, h0.r11, h0.rbx, h0.r12, h0.r13, d8_of_dmem h0.dmem, e0_initW P _⟩
    · refine ⟨⟨h1.exe, h1.decls, h1.endPc, h1.pc, split_sAll h1.dmem, 0, d8_of_dmem h1.dmem, h1.r11⟩,
        0, h1.r11, h1.rbx, d8_of_dmem h1.dmem, comDW_init P _, hi, ?_⟩
      unfold TokFrozen; show (1 : Rat) ≤ fracDW P P.tokQ; simp [fracDW]
    · simp only [List.length_cons, List.length_nil] at h; omega
  intro rF' g' E' hle hsize hB
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀W_gww P).mono hle
  have fin : ∀ i, i < cfg.threads.size → MQW P cfg (rF' i) g' → 1 ≤ ((rF' i).wr P.tokH).q ∨
      WcMsqXFinal P.n1 P.n2 cfg := by
    rintro i hi (⟨th, hth, hd, hiv, hacq⟩ | hq)
    · exact .inr ⟨th, hth, final_valuesW E' hW hL hiv
        (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hpt hi hd⟩
    · exact .inl hq
  exact (fin 0 hi0 (hB 0 (Config.final_done hf hi0))).elim (fun hq0 => (fin 1 hi1
    (hB 1 (Config.final_done hf hi1))).elim (fun hq1 => (tokH_pair_false E' hi0 hi1 (by decide) hq0 hq1).elim) id) id

end Kraken.Promising.Lower.WcMsqX

#print axioms Kraken.Promising.Lower.WcMsqX.wcMsqX_promising
