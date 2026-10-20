/-
**Validation of the x64 lowering kit.** ISA: x64; machine: the executable Promising machine
(`Reachable Arch.tso`).

Re-derives the x64 Treiber proof's whole-program headline
`Treiber2X.x64_treiber2_envG_verbatim` (`EnvG/X64Treiber2Public.lean`: the
two-thread Treiber stack `treiber2.kl`, verbatim, run from the label `worker`
of the runner's image) through `KitX.lower_promising_x64`, as
`x64_treiber2_envG_verbatim_viaKit`, with an `rfl` statement-identity check.

What stays per program: one `LowerThreadX` value per thread (`t2T`, each
field an existing lemma), the start discharge (`t2T_start`), and the final
reading, here the x64 pilot's `pilotX_final` (the case split of
`x64_treiber2_envG_verbatim`, written once for every lowering of the
two-thread Treiber stack). The existing triples (`workerV_envGCAdj`,
`workerV_noNT`) are used as they are: they are `Safely` judgments from the
label `worker`, the kit's shape.
-/
import Kraken.Promising.Lower.KitX64
import Kraken.Promising.Lower.PilotX64Link

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Treiber2X

namespace Kraken.Promising.Lower.KitX.Treiber2

open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 split_sAll)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2ImageV)]

local instance treiber2ImageV.envK : CodeEnv := ⟨layout treiber2ImageV⟩

/-- **Thread `w` of the verbatim `treiber2` as a lowered x64 thread** (every
field an existing lemma of `EnvG/X64Treiber2{VCGen,Public}.lean`). -/
noncomputable def t2T (hL : TLocs tPV) (w : Nat) (hw : w < 2) : LowerThreadX w sAll (TB2X tPV) where
  e := layout treiber2ImageV
  valid := inferInstance
  pl := plan tPV w
  hpl := plan_valid tPV w
  shape := treiber2ImageV_phase1FX
  entry := labT2 "worker"
  endPc := labT2 "done"
  stuck := workerV_stuck
  Q x := (x.1.2 = labT2 "done" ∧ Dn tPV w (x.1.1.regs.get64 .r12) x.2.1) ∨ False
  Q_end _ h := h.elim And.left False.elim
  hB := hB_wV tPV hw
  PreR s _ := ∀ a, Mem.loadInt s.dmem a 8 = none
  QR x := (x.1.2 = labT2 "done" ∧ True) ∨ False
  QR_end _ h := h.elim And.left False.elim
  pure := workerV_noNT
  Pre s g := s.regs.get64 .rbx = tPV.n w ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ Pu tPV w g.1
  main := workerV_envGCAdj tPV w hL hw rfl

/-- **Thread `w`'s kit start** from the runner's `StartWV`. -/
theorem t2T_start (hL : TLocs tPV) {w : Nat} (hw : w < 2) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    {s : isa.State} (hS : StartWV (tPV.n w) s) (hT0 : (Config.init [s0, s1] initMem).mem.initVal tPV.top = 0) :
    (t2T hL w hw).Start (σInitX (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem tPV w)
      (ghost₀ tPV)) s := by
  have htr : tRes (Config.init [s0, s1] initMem).mem tPV w = thrRes (Config.init [s0, s1] initMem).mem tPV w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  exact ⟨⟨hS.exe, hS.decls, hS.endPc, hS.pc, split_sAll hS.dmem, 0, hS.d8⟩,
    0, hS.rbx, hS.d8, pu_init tPV hL hw _ hT0⟩

/-- **`x64_treiber2_envG_verbatim` through the x64 kit** (same statement). -/
theorem x64_treiber2_envG_verbatim_viaKit {fuel : Nat} (h1 : symT2 "top" ≠ symT2 "n1")
    (h2 : symT2 "top" ≠ symT2 "n2") (hn : symT2 "n1" ≠ symT2 "n2") (hn1 : symT2 "n1" ≠ 0) (hn2 : symT2 "n2" ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartWV (symT2 "n1") s0) (h1' : StartWV (symT2 "n2") s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symT2 "top", 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th0 th1, cfg.threads[0]? = some th0 ∧ cfg.threads[1]? = some th1 ∧
      ((th0.st.st.1.regs.get64 .r12 = symT2 "n1" ∧ th1.st.st.1.regs.get64 .r12 = symT2 "n2") ∨
        (th0.st.st.1.regs.get64 .r12 = symT2 "n2" ∧ th1.st.st.1.regs.get64 .r12 = symT2 "n1")) := by
  have hL := tLocs_tPV h1 h2 hn hn1 hn2
  refine lower_promising_x64 (Φ := Treiber2FinalX (symT2 "n1") (symT2 "n2")) fuel sAll_le16 (erase_init hL _) rfl
    (fun tid h => t2T hL tid (by simpa using h)) ?_ hc hf
    fun _ _ E' hle hsize hB => PilotX.pilotX_final hL hf E' hle hsize hB
  intro tid h
  rcases tid with _ | _ | i
  · exact t2T_start hL (by decide) h0 hT0
  · exact t2T_start hL (by decide) h1' hT0
  · simp only [List.length_cons, List.length_nil] at h; omega

/-- **Statement identity**: the kit re-derivation has exactly the original
statement. -/
example : @x64_treiber2_envG_verbatim_viaKit = @x64_treiber2_envG_verbatim := rfl

end Kraken.Promising.Lower.KitX.Treiber2

#print axioms Kraken.Promising.Lower.KitX.Treiber2.x64_treiber2_envG_verbatim_viaKit
