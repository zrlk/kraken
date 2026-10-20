/-
The reachable thread states of MP (`MpReach`, kept by every machine step) and
the per-instruction condition of `theorem1IIPure_of_relWrites`: at a
reachable state the next instruction's non-release writes are pure for the
initial ghost (`mp_cell`). The writer's only plain store writes `Dt`, whose
release predicate is `Pred.emp`; its flag store is a release; the reader
writes nothing.

The writer and the reader are laid out by separate layouts `lW`, `lR`: a
`Layout` assigns sizes by directive index, and the two programs have labels
at different indices (`ValidLayout` asks labels to take 0 bytes and
instructions 4), so no single layout is valid for both.
-/
import Kraken.Promising.SLR.MpInit
import Kraken.Promising.SLR.PromisePureGeneral

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.Spinlock

/-! ## The writer's reachable states -/

section Writer

variable [layout : _root_.Layout] [hw : Executable.ValidLayout (layout mpWriter)]

/-- The writer at one of its positions. -/
def ReachW (P : Params) (st : State) : Prop :=
  FrameW P st ∧ ∃ i, AtPos mpWriter st i ∧ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)

/-- **A writer step keeps `ReachW`.** -/
theorem reachW_step (P : Params) {st : State} (h : ReachW P st) (tree : EvTree State)
    (hex : isa.exec st = some tree) : tree.All (ReachW P) := by
  obtain ⟨hF, i, hp, hi⟩ := h
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · rw [exec_w_mov2 st (hF.at hp (by decide))] at hex
    cases hex
    exact ⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 1, rfl, by decide⟩
  · rw [exec_w_str st (hF.at hp (by decide)) hF.x1 hF.dd] at hex
    cases hex
    intro _
    exact ⟨hF.goto rfl rfl rfl, 2, rfl, by decide⟩
  · rw [exec_w_mov3 st (hF.at hp (by decide))] at hex
    cases hex
    exact ⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 3, rfl, by decide⟩
  · rw [exec_w_stlr st (hF.at hp (by decide)) hF.x0 hF.df] at hex
    cases hex
    intro _
    exact ⟨hF.goto rfl rfl rfl, 4, rfl, by decide⟩
  · rw [exec_end_w hF hp] at hex
    cases hex

/-- The writer's non-release writes are pure for `mpGhost`. -/
theorem cellW (P : Params) (hL : MpLocs P) (A : Arch) (st : State) (tree : EvTree State)
    (h : ReachW P st) (hex : isa.exec st = some tree) :
    tree.RelWrites A fun l v => Pred.Pure ((mpGhost P).rel l) v := by
  obtain ⟨hF, i, hp, hi⟩ := h
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · rw [exec_w_mov2 st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_w_str st (hF.at hp (by decide)) hF.x1 hF.dd] at hex
    cases hex
    exact ⟨fun _ => by
      show Pred.Pure ((mpGhost P).rel P.Dt) _
      rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure _, fun _ => trivial⟩
  · rw [exec_w_mov3 st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_w_stlr st (hF.at hp (by decide)) hF.x0 hF.df] at hex
    cases hex
    exact EvTree.relWrites_relStore rfl
  · rw [exec_end_w hF hp] at hex; cases hex

end Writer

/-! ## The reader's reachable states -/

section Reader

variable [layout : _root_.Layout] [hr : Executable.ValidLayout (layout mpReader)]

/-- The reader at one of its positions. -/
def ReachR (P : Params) (st : State) : Prop :=
  FrameR P st ∧ ∃ i, AtPos mpReader st i ∧ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)

/-- **A reader step keeps `ReachR`.** -/
theorem reachR_step (P : Params) {st : State} (h : ReachR P st) (tree : EvTree State)
    (hex : isa.exec st = some tree) : tree.All (ReachR P) := by
  obtain ⟨hF, i, hp, hi⟩ := h
  rcases hi with rfl | rfl | rfl | rfl
  · rw [exec_r_ldar st (hF.at hp (by decide)) hF.x0 hF.df] at hex
    cases hex
    intro _
    exact ⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 2, rfl, by decide⟩
  · rw [exec_r_cbz st (hF.at hp (by decide))] at hex
    cases hex
    have hF' := hF.goto (m := st.st.1) (pc := if BitVec.setWidth 32 st.st.1.regs.X3.toBitVec = 0#32 then
      (layout mpReader).addrOf 1 else (layout mpReader).addrOf 3) rfl rfl rfl
    by_cases hz : BitVec.setWidth 32 st.st.1.regs.X3.toBitVec = 0#32
    · exact ⟨hF', 1, by simp [AtPos, hz], by decide⟩
    · exact ⟨hF', 3, by simp [AtPos, hz], by decide⟩
  · rw [exec_r_ldr st (hF.at hp (by decide)) hF.x1 hF.dd] at hex
    cases hex
    intro _
    exact ⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 4, rfl, by decide⟩
  · rw [exec_end_r hF hp] at hex
    cases hex

/-- The reader writes nothing. -/
theorem cellR (P : Params) (A : Arch) (st : State) (tree : EvTree State)
    (h : ReachR P st) (hex : isa.exec st = some tree) :
    tree.RelWrites A fun l v => Pred.Pure ((mpGhost P).rel l) v := by
  obtain ⟨hF, i, hp, hi⟩ := h
  rcases hi with rfl | rfl | rfl | rfl
  · rw [exec_r_ldar st (hF.at hp (by decide)) hF.x0 hF.df] at hex; cases hex; exact fun _ => trivial
  · rw [exec_r_cbz st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_r_ldr st (hF.at hp (by decide)) hF.x1 hF.dd] at hex; cases hex; exact fun _ => trivial
  · rw [exec_end_r hF hp] at hex; cases hex

end Reader

/-! ## Both threads -/

/-- The reachable thread states: the writer (layout `lW`) or the reader
(layout `lR`) at one of its positions. -/
def MpReach (lW lR : _root_.Layout) (P : Params) (st : State) : Prop :=
  ReachW (layout := lW) P st ∨ ReachR (layout := lR) P st

variable (lW lR : _root_.Layout) [hw : Executable.ValidLayout (lW mpWriter)]
  [hr : Executable.ValidLayout (lR mpReader)]

/-- **Every machine step keeps `MpReach`.** -/
theorem mpReach_stepPreserves (P : Params) (A : Arch) :
    StepPreserves (I := isa) A (fun _ _ => True) (fun _ st => MpReach lW lR P st) := by
  intro tid t mem outs o h _ hstep ho
  refine ⟨?_, ⟨fun _ => trivial, fun _ _ => trivial⟩⟩
  rcases h with h | h
  · exact .inl (stepOne_leaf A hstep ho (reachW_step (layout := lW) P h))
  · exact .inr (stepOne_leaf A hstep ho (reachR_step (layout := lR) P h))

/-- **The per-instruction condition**: at a reachable state the next
instruction's non-release writes are pure for `mpGhost`. -/
theorem mp_cell (P : Params) (hL : MpLocs P) (A : Arch) (st : State) (tree : EvTree State)
    (h : MpReach lW lR P st) (hex : isa.exec st = some tree) :
    tree.RelWrites A fun l v => Pred.Pure ((mpGhost P).rel l) v := by
  rcases h with h | h
  · exact cellW (layout := lW) P hL A st tree h hex
  · exact cellR (layout := lR) P A st tree h hex

/-- **`MpReach` at every reachable configuration** from the two start
states. -/
theorem mpReach_reachable (P : Params) {A : Arch} {fuel : Nat} {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : FrameW (layout := lW) P sW ∧ AtPos (layout := lW) mpWriter sW 0)
    (hR : FrameR (layout := lR) P sR ∧ AtPos (layout := lR) mpReader sR 0)
    {c : Config isa} (hc : Reachable A fuel (Config.init [sW, sR] initMem) c) {tid : Nat} {t : Thread isa}
    (ht : c.threads[tid]? = some t) : MpReach lW lR P t.st := by
  refine (configInv_reachable (mpReach_stepPreserves lW lR P A) ⟨⟨fun _ => trivial, fun _ _ => trivial⟩,
    fun tid t ht => ?_⟩ hc).2 tid t ht
  obtain ⟨s, hs, rfl⟩ := Config.init_get?_thread ht
  match tid, hs with
  | 0, hs =>
    cases hs
    exact .inl ⟨hW.1, 0, hW.2, by decide⟩
  | 1, hs =>
    cases hs
    exact .inr ⟨hR.1, 1, by show sR.st.2 = _; rw [r_addr_1 (layout := lR)]; exact hR.2, by decide⟩
  | n + 2, hs => cases hs

end Kraken.Promising.SLR.Mp
