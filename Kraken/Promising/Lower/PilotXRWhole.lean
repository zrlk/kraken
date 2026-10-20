/-
**The whole-program theorem through the x64
kit, unconditional.** ISA: x64; machine: the executable
Promising machine (`Reachable Arch.tso`), through
`KitX.lower_promising_x64` (no value bridge: `dmem` is empty and the shared
layout is `sAll`).

- `xrT`: thread `w` of `pilotXR` as a `KitX.LowerThreadX` on `sAll`: `main`
  from `main_specXR`, purity from `pilotXR_pure`, the end of the text (the
  label `done`) stuck, `hB_xr` (the x64 Treiber proof's `hB_wV` with `pilotXR`'s post).
- `StartXR`: what the runtime sets up: the image, no declarations, pc at
  `main`, end at `done`, the link `r11 = done`, `rbx = &top`, the arena at
  node `w` with room for it, `dmem` empty.
- `pilotXR_promising`: from the two start states and `top = 0` initially,
  every final configuration reachable under `Arch.tso` has the two threads'
  `r12` the two nodes, in some order (`Treiber2FinalX`; the final reading is
  the x64 pilot's `pilotX_final`). In particular no pop returned `0`.
- `pilotXR_concrete`: the instance at the explorer's layout and start states
  (`Lower/PilotXRProg.lean`).
-/
import Kraken.Promising.Lower.PilotXRPure
import Kraken.Promising.Lower.KitX64
import Kraken.Promising.Lower.PilotX64Link

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.PilotXR

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 split_sAll mem_sAll8)
open Kraken.Promising.SLR.EnvG.TreiberCommon (initVal_eq)
open Kraken.Promising.Lower.KitX (LowerThreadX lower_promising_x64)

variable [layout : _root_.Layout]

omit layout in
/-- `pilotXR`'s labels have no duplicates. -/
theorem pilotXR_nodup : (Program.labels pilotXR).Nodup := pilotXR_wf.nodup

/-- The label `done` is the end of the text. -/
theorem labXR_done [Executable.ValidLayout (layout pilotXR)] :
    labXR "done" = (layout pilotXR).addrOf pilotXR.length := by
  have hd : labXR "done" = (layout pilotXR).addrOf 34 :=
    Program.label_addrOf_drop pilotXR_nodup (by decide) (by decide)
  have h34 : (layout pilotXR).2[34]? = some (Directive.label "done", Kraken.Layout.size Directive 34) := by
    simp [Layout.apply_snd, Layout.frag, pilotXR]
  rw [show pilotXR.length = 34 + 1 from rfl, Executable.addrOf_succ _ h34,
    Executable.ValidLayout.label_size 34 "done" _ h34, hd]
  simp

/-- **No instruction steps at `done`** (the end of the text). -/
theorem pilotXR_stuck [Executable.ValidLayout (layout pilotXR)] (env : SharedEnv) :
    ∀ x R, x.1.2 = labXR "done" → ¬ (layout pilotXR).instrStepEnv env x R := by
  rw [labXR_done]
  exact not_instrStepEnv_of_end_labels env 1

/-- Thread `w`'s counted post: at `done`, `Dn` of `r12`. -/
abbrev QXR (P : Params) (w : Nat) : MachineState × (EStateX × Nat) → Prop :=
  fun x => x.1.2 = labXR "done" ∧ Dn P w (x.1.1.regs.get64 .r12) x.2.1

/-- **`hB` for thread `w`**: `Dn` at the anchor gives `DoneR` at the
configuration (`hB_wV`'s proof with `QXR`). -/
theorem hB_xr (P : Params) {w : Nat} (hw : w < 2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    (∃ n, QXR P w (t.st.st, (σ, n))) → t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2X P c r g := by
  rintro c t r g cl σ ⟨_, -, hcom, hd⟩ hp hrel -
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePop.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

variable [Executable.ValidLayout (layout pilotXR)]

/-- **Thread `w` of `pilotXR` as a lowered x64 thread** (frameless, `sAll`). -/
noncomputable def xrT (P : Params) (hL : TLocs P) (w : Nat) (hw : w < 2) : LowerThreadX w sAll (TB2X P) where
  e := layout pilotXR
  valid := inferInstance
  pl := plan P w
  hpl := plan_valid P w
  shape := pilotXR_phase1FX
  entry := labXR "main"
  endPc := labXR "done"
  stuck := pilotXR_stuck
  Q := QXR P w
  Q_end _ h := h.1
  hB := hB_xr P hw
  PreR s _ := D8 s.dmem ∧ s.regs.get64 .r11 = (labXR "done").toBitVec ∧
    s.regs.get64 .r14 + 16 ≤ s.regs.get64 .r15
  QR x := (x.1.2 = labXR "done" ∧ True) ∨ False
  QR_end _ h := h.elim And.left False.elim
  pure := pilotXR_pure
  Pre := MainPreR P w (labXR "done")
  main := main_specXR P w hL hw _

/-- **Thread `w` at its start**: the image, no declarations, pc at `main`,
end at `done`, `main`'s link `r11 = done`, `rbx = &top`, `r14` node `w` with
room for it below `r15`, `dmem` empty. -/
structure StartXR (P : Params) (w : Nat) (s : isa.State) : Prop where
  exe : s.exe = layout pilotXR
  decls : s.decls = {}
  pc : s.st.2 = labXR "main"
  endPc : s.endPc = labXR "done"
  r11 : s.st.1.regs.get64 .r11 = (labXR "done").toBitVec
  rbx : s.st.1.regs.get64 .rbx = P.t
  r14 : s.st.1.regs.get64 .r14 = P.n w
  r15 : s.st.1.regs.get64 .r14 + 16 ≤ s.st.1.regs.get64 .r15
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **Thread `w`'s kit start** from `StartXR`. -/
theorem xrT_start {P : Params} (hL : TLocs P) {w : Nat} (hw : w < 2) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} {s : isa.State} (hS : StartXR P w s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    (xrT P hL w hw).Start (σInitX (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P w)
      (ghost₀ P)) s := by
  have htr : tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  have hd8 : D8 s.st.1.dmem := fun a => (split_sAll hS.dmem).loadInt_none (mem_sAll8 a) (by decide) (by decide)
  rw [htr]
  exact ⟨⟨hS.exe, hS.decls, hS.endPc, hS.pc, split_sAll hS.dmem, 0, hd8, hS.r11, hS.r15⟩,
    0, hS.r11, hS.rbx, hS.r14, hS.r15, hd8, pu_init P hL hw _ hT0⟩

/-- **The stackless x64 Treiber pilot, whole program, unconditional**: the
two threads of `pilotXR` (each pushes its node, then pops) started at
`StartXR` with `top` initially `0`; in every final configuration reachable
under `Arch.tso`, the threads' `r12` are the two nodes in some order. -/
theorem pilotXR_promising {fuel : Nat} {P : Params} (hL : TLocs P) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartXR P 0 s0) (h1 : StartXR P 1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2FinalX (P.n 0) (P.n 1) cfg := by
  refine lower_promising_x64 (Φ := Treiber2FinalX (P.n 0) (P.n 1)) fuel sAll_le16 (erase_init hL _) rfl
    (fun tid h => xrT P hL tid (by simpa using h)) ?_ hc hf
    fun _ _ E' hle hsize hB => PilotX.pilotX_final hL hf E' hle hsize hB
  intro tid h
  rcases tid with _ | _ | i
  · exact xrT_start hL (by decide) h0 hT0
  · exact xrT_start hL (by decide) h1 hT0
  · simp only [List.length_cons, List.length_nil] at h; omega

end Kraken.Promising.Lower.PilotXR

#print axioms Kraken.Promising.Lower.PilotXR.pilotXR_promising
