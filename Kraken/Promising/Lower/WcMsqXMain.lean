/-
**`main_e` and `main_w` of the x64 try-once MS queue program `wcMsqX`**, by
`Safely.blockAt` on each block (one `vcgen` each) and the register-link call
rule `FunSpecPartialEnv.jcall` at `enq_fragXW` / `wdeq_fragXW` placed in
`wcMsqX`.

`mainW_specXW` ends in `DnW`: `ComDW`, `InitV`, and `DoneW` of the two
results (`resW` of the tag and payload registers `r12`/`r13`, `r14`/`r15`).
Before the second call the dequeuer holds `W1` of the first result: empty
with `tokQ` whole, or a node it dequeued (`First`) with `tokQ` whole unless
the node is `n1` (`doneW_two` combines it with the second call).
-/
import Kraken.Promising.Lower.WcMsqXSpecs
import Kraken.Promising.Lower.PilotXRMain

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.WcMsqX

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.Lower.PilotX (Saved)
open Kraken.Promising.Lower.PilotXR (D8 ofBitVec_reg)
open Kraken.Promising.Lower.MsqXR (Kept mainEBody retE1Body retE2Body)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The dequeuer's results -/

/-- A result `(tag, payload)`: tag `0` is the node, any other tag empty. -/
def resW (tag pay : BitVec 64) : Option (BitVec 64) := if tag = 0 then some pay else none

/-- **After the first call** with tag `t` and payload `x`. -/
def W1 (P : Params) (t x : BitVec 64) (σ : EStateX) : Prop :=
  (t = 1 ∧ TokFrozen P.tokQ σ.r) ∨ (t = 0 ∧ First P x σ ∧ (TokFrozen P.tokQ σ.r ∨ x = P.n1))

/-- **The dequeuer done**: `ComDW`, `InitV` and `DoneW` of its two results. -/
def DnW (P : Params) (t1 x1 t2 x2 : BitVec 64) (σ : EStateX) : Prop :=
  ComDW P σ ∧ InitV σ.snap.mem P ∧ DoneW σ.snap.mem P σ.r (resW t1 x1) (resW t2 x2)

section
variable {P : Params} {σ σ' : EStateX}

theorem W1.fence {t x : BitVec 64} (h : W1 P t x σ) (hf : X64.EnvG.FenceLe σ σ') : W1 P t x σ' := by
  have hr : TokFrozen P.tokQ σ.r → TokFrozen P.tokQ σ'.r := fun h => by unfold TokFrozen at *; rw [hf.r]; exact h
  exact h.imp (fun ⟨h1, h2⟩ => ⟨h1, hr h2⟩) fun ⟨h1, h2, h3⟩ => ⟨h1, (yokW_first x).fence h2 hf, h3.imp_left hr⟩

theorem DnW.fence {t1 x1 t2 x2 : BitVec 64} (h : DnW P t1 x1 t2 x2 σ) (hf : X64.EnvG.FenceLe σ σ') :
    DnW P t1 x1 t2 x2 σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.fence hf, hf.snap ▸ h2, ?_⟩
  rw [hf.snap, hf.r]; exact h3

/-- **The two calls' results give `DoneW`.** -/
theorem doneW_two {σ1 : EStateX} {t1 x1 t2 x2 : BitVec 64} (h1 : W1 P t1 x1 σ1) (hK : Kept P σ1 σ)
    (h2 : (t2 = 1 ∧ TK P σ1 σ) ∨ (t2 = 0 ∧ First P x2 σ ∧
      (∀ x0, First P x0 σ1 → DoneD2 σ.snap.mem P x0 x2) ∧
      (TokFrozen P.tokQ σ1.r → TokFrozen P.tokQ σ.r ∨ x2 = P.n1))) :
    DoneW σ.snap.mem P σ.r (resW t1 x1) (resW t2 x2) := by
  rcases h1 with ⟨rfl, ht1⟩ | ⟨rfl, hF1, ht1⟩ <;> rcases h2 with ⟨rfl, hk⟩ | ⟨rfl, hF2, hD, hk⟩ <;>
    simp only [resW, ↓reduceIte, show (1 : BitVec 64) ≠ 0 by decide]
  · exact ⟨.inl (hk ht1), trivial⟩
  · exact ⟨(hk ht1).imp_right fun h => .inr (by rw [h]), hF2.imp fun _ h => h.1⟩
  · exact ⟨ht1.elim (fun h => .inl (hk h)) fun h => .inr (.inl (by rw [h])), (hK x1 hF1).imp fun _ h => h.1⟩
  · exact ⟨ht1.elim (fun h => (hk h).imp_right fun h => .inr (by rw [h])) fun h => .inr (.inl (by rw [h])),
      hD x1 hF1⟩

end

/-! ## The blocks -/

theorem blockAt_mainE : Program.blockAt wcMsqX "main_e" = some ⟨"main_e", mainEBody, some "ret_e1"⟩ := by decide
theorem blockAt_retE1 : Program.blockAt wcMsqX "ret_e1" = some ⟨"ret_e1", retE1Body, some "ret_e2"⟩ := by decide
theorem blockAt_retE2 : Program.blockAt wcMsqX "ret_e2" = some ⟨"ret_e2", retE2Body, some "enq"⟩ := by decide
theorem blockAt_mainW : Program.blockAt wcMsqX "main_w" = some ⟨"main_w", mainWBody, some "ret_w1"⟩ := by decide
theorem blockAt_retW1 : Program.blockAt wcMsqX "ret_w1" = some ⟨"ret_w1", retW1Body, some "ret_w2"⟩ := by decide
theorem blockAt_retW2 : Program.blockAt wcMsqX "ret_w2" = some ⟨"ret_w2", retW2Body, some "wdeq"⟩ := by decide

theorem wcMsqX_wf : Program.WF wcMsqX := by decide

variable [layout : _root_.Layout] [Executable.ValidLayout (layout wcMsqX)]

local instance wcMsqX.env : CodeEnv := ⟨layout wcMsqX⟩

/-- A label's address in the laid-out `wcMsqX`. -/
abbrev labW (x : Label) : Int64 := (_root_.Executable.labels (layout wcMsqX)).label x

theorem wcMsqX_placed : Program.Placed wcMsqX "main_e" := Program.placed_of_layout wcMsqX_wf rfl (by decide)

/-! ## `main_e` -/

/-- `main_e`'s precondition: link `raM`, `rbx = &tail`, the nodes, `E0W` of `n1`. -/
def MainEPreW (P : Params) (raM : Int64) (s : MachineData) (σ : (SharedEnv.counted (EEX P)).State) : Prop :=
  s.regs.get64 .r11 = raM.toBitVec ∧ s.regs.get64 .rbx = P.t ∧ s.regs.get64 .r12 = P.n1 ∧
    s.regs.get64 .r13 = P.n2 ∧ D8 s.dmem ∧ E0W P P.n1 σ.1

/-- **`main_e`'s run** (counted `EEX`, partial). -/
theorem mainE_specXW (P : Params) (hL : QLocs P) (raM : Int64) :
    ∀ s g, MainEPreW P raM s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EEX P))) (fun x => x.1.2 = raM ∧ ComEW P x.2.1)
        ((s, labW "main_e"), g) := by
  have hpl : Program.PlacedIn wcMsqX := wcMsqX_placed.toPlacedIn
  have hE : ∀ n, FunSpecPartialEnv (SharedEnv.counted (EEX P)) (labW "enq") (EnqPreW P n) (EnqPostW P n) :=
    fun n => (enq_fragXW P n hL).of_placed wcMsqX_placed (by decide)
  rintro s g ⟨h11, hbx, h12, h13, hd8, hE0⟩
  refine Safely.blockAt hpl blockAt_mainE (X := fun a s₁ => a = labW "enq" ∧
      s₁.regs.get64 .r11 = (labW "ret_e1").toBitVec ∧ s₁.regs.get64 .rdi = P.t ∧ s₁.regs.get64 .rsi = P.n1 ∧
      s₁.regs.get64 .rbp = raM.toBitVec ∧ s₁.regs.get64 .rbx = P.t ∧ s₁.regs.get64 .r13 = P.n2 ∧
      s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainEBody]; vcgen
    case vc1 s' hs => subst hs; simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h12, h11, h13, and_true]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1di, h1si, h1bp, h1bx, h113, h1dm⟩ hle₁
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₁
  refine (hE P.n1).jcall (ra := labW "ret_e1") ⟨h1r11, h1di, h1si, h1dm ▸ hd8, hE0.fence hle₁.1⟩
    fun s₂ g₂ ⟨⟨h2bx, h2bp, _, h213, _, _, h2dm⟩, y3, hLk⟩ => ?_
  refine Safely.blockAt hpl blockAt_retE1 (X := fun a s₃ => a = labW "enq" ∧
      s₃.regs.get64 .r11 = (labW "ret_e2").toBitVec ∧ s₃.regs.get64 .rdi = P.t ∧ s₃.regs.get64 .rsi = P.n2 ∧
      s₃.regs.get64 .rbp = s₂.regs.get64 .rbp ∧ s₃.dmem = s₂.dmem) ?_ ?_
  · simp only [retE1Body]; vcgen
    case vc1 s' hs => subst hs; simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h2bx, h1bx, h213, h113, and_true]
  rintro a s₃ g₃ ⟨rfl, h3r11, h3di, h3si, h3bp, h3dm⟩ hle₃
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₃
  refine (hE P.n2).jcall (ra := labW "ret_e2")
    ⟨h3r11, h3di, h3si, by rw [h3dm, h2dm, h1dm]; exact hd8, (LinkedW.next hL hLk).fence hle₃.1⟩
    fun s₄ g₄ ⟨⟨_, h4bp, _, _, _, _, _⟩, y3', hLk'⟩ => ?_
  refine Safely.blockAt hpl blockAt_retE2 (X := fun a _ => a = Int64.ofBitVec (s₄.regs.get64 .rbp)) ?_ ?_
  · simp only [retE2Body]; vcgen
    case vc1 s' hs => subst hs; rfl
  rintro a s₅ g₅ rfl hle₅
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₅
  exact Safely.fold (.inl ⟨ofBitVec_reg (by rw [h4bp, h3bp, h2bp, h1bp]), (hLk'.fence hle₅.1).1⟩)

/-! ## `main_w` -/

/-- `main_w`'s precondition: link `raM`, `rbx = &head`, `ComDW`, `InitV`,
`tokQ` whole. -/
def MainWPre (P : Params) (raM : Int64) (s : MachineData) (σ : (SharedEnv.counted (EDXW P)).State) : Prop :=
  s.regs.get64 .r11 = raM.toBitVec ∧ s.regs.get64 .rbx = P.h ∧ D8 s.dmem ∧ ComDW P σ.1 ∧
    InitV σ.1.snap.mem P ∧ TokFrozen P.tokQ σ.1.r

/-- **`main_w`'s run** (counted `EDXW`, partial): at the link, `DnW` of the
two results. -/
theorem mainW_specXW (P : Params) (hL : QLocs P) (hpt : P.trk = false) (raM : Int64) :
    ∀ s g, MainWPre P raM s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EDXW P)))
        (fun x => x.1.2 = raM ∧ DnW P (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13)
          (x.1.1.regs.get64 .r14) (x.1.1.regs.get64 .r15) x.2.1)
        ((s, labW "main_w"), g) := by
  have hpl : Program.PlacedIn wcMsqX := wcMsqX_placed.toPlacedIn
  have hD : FunSpecPartialEnv (SharedEnv.counted (EDXW P)) (labW "wdeq") (WDeqPre P) (WDeqPost P) :=
    (wdeq_fragXW P hL hpt).of_placed wcMsqX_placed (by decide)
  rintro s g ⟨h11, hbx, hd8, hC, hI, hT⟩
  refine Safely.blockAt hpl blockAt_mainW (X := fun a s₁ => a = labW "wdeq" ∧
      s₁.regs.get64 .r11 = (labW "ret_w1").toBitVec ∧ s₁.regs.get64 .rdi = P.h ∧
      s₁.regs.get64 .rbp = raM.toBitVec ∧ s₁.regs.get64 .rbx = P.h ∧ s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainWBody]; vcgen
    case vc1 s' hs => subst hs; simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h11, and_true]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1di, h1bp, h1bx, h1dm⟩ hle₁
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₁
  refine hD.jcall (ra := labW "ret_w1") ⟨h1r11, h1di, h1dm ▸ hd8, hC.fence hle₁.1, hle₁.1.snap ▸ hI⟩
    fun s₂ g₂ ⟨⟨h2bx, h2bp, _, _, _, _, h2dm⟩, hC2, ⟨_, hI2⟩, hR⟩ => ?_
  have hT1 : TokFrozen P.tokQ g₁.1.r := by unfold TokFrozen; rw [hle₁.1.r]; exact hT
  have hW1 : W1 P (s₂.regs.get64 .rax) (s₂.regs.get64 .rdx) g₂.1 := by
    rcases hR with ⟨h1, hk⟩ | ⟨h0, hF, -, hk⟩
    · exact .inl ⟨h1, hk hT1⟩
    · exact .inr ⟨h0, hF, hk hT1⟩
  refine Safely.blockAt hpl blockAt_retW1 (X := fun a s₃ => a = labW "wdeq" ∧
      s₃.regs.get64 .r11 = (labW "ret_w2").toBitVec ∧ s₃.regs.get64 .rdi = P.h ∧
      s₃.regs.get64 .rbp = s₂.regs.get64 .rbp ∧ s₃.regs.get64 .r12 = s₂.regs.get64 .rax ∧
      s₃.regs.get64 .r13 = s₂.regs.get64 .rdx ∧ s₃.dmem = s₂.dmem) ?_ ?_
  · simp only [retW1Body]; vcgen
    case vc1 s' hs => subst hs; simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h2bx, h1bx, and_true]
  rintro a s₃ g₃ ⟨rfl, h3r11, h3di, h3bp, h312, h313, h3dm⟩ hle₃
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₃
  refine hD.jcall (ra := labW "ret_w2")
    ⟨h3r11, h3di, by rw [h3dm, h2dm, h1dm]; exact hd8, hC2.fence hle₃.1, hle₃.1.snap ▸ hI2⟩
    fun s₄ g₄ ⟨⟨_, h4bp, h412, h413, _, _, _⟩, hC4, ⟨hK4, hI4⟩, hR4⟩ => ?_
  refine Safely.blockAt hpl blockAt_retW2 (X := fun a s₅ => a = Int64.ofBitVec (s₄.regs.get64 .rbp) ∧
      s₅.regs.get64 .r12 = s₄.regs.get64 .r12 ∧ s₅.regs.get64 .r13 = s₄.regs.get64 .r13 ∧
      s₅.regs.get64 .r14 = s₄.regs.get64 .rax ∧ s₅.regs.get64 .r15 = s₄.regs.get64 .rdx) ?_ ?_
  · simp only [retW2Body]; vcgen
    case vc1 s' hs => subst hs; simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_true]
  rintro a s₅ g₅ ⟨rfl, h512, h513, h514, h515⟩ hle₅
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₅
  refine Safely.fold (.inl ⟨ofBitVec_reg (by rw [h4bp, h3bp, h2bp, h1bp]), ?_⟩)
  rw [h512, h513, h514, h515, h412, h413, h312, h313]
  exact DnW.fence ⟨hC4, hI4, doneW_two (hW1.fence hle₃.1) hK4 hR4⟩ hle₅.1

end Kraken.Promising.Lower.WcMsqX
