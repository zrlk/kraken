/-
**Part 3: `main_e` and `main_d`**, by `Safely.blockAt`
on each block (one `vcgen` each) and the x64 register-link pilot's link-register call rule
`FunSpecPartialEnv.jcall` (`Lower/PilotXRMain.lean`) at `enq_fragXR` /
`deq_fragXR` placed in `msqXR` (`FragSpecEnv.of_placed`). `mainD_specXR` is
the relational FIFO step: the second `deq`'s `DoneD2` after the first
result's `First`.
-/
import Kraken.Promising.Lower.MsqXRSpecs
import Kraken.Promising.Lower.PilotXRMain

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.MsqXR

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.Lower.PilotX (Saved)
open Kraken.Promising.Lower.PilotXR (D8 ofBitVec_reg)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The blocks -/

theorem blockAt_mainE : Program.blockAt msqXR "main_e" = some ⟨"main_e", mainEBody, some "ret_e1"⟩ := by decide
theorem blockAt_retE1 : Program.blockAt msqXR "ret_e1" = some ⟨"ret_e1", retE1Body, some "ret_e2"⟩ := by decide
theorem blockAt_retE2 : Program.blockAt msqXR "ret_e2" = some ⟨"ret_e2", retE2Body, some "enq"⟩ := by decide
theorem blockAt_mainD : Program.blockAt msqXR "main_d" = some ⟨"main_d", mainDBody, some "ret_d1"⟩ := by decide
theorem blockAt_retD1 : Program.blockAt msqXR "ret_d1" = some ⟨"ret_d1", retD1Body, some "ret_d2"⟩ := by decide
theorem blockAt_retD2 : Program.blockAt msqXR "ret_d2" = some ⟨"ret_d2", retD2Body, some "deq"⟩ := by decide

theorem msqXR_wf : Program.WF msqXR := by decide

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqXR)]

local instance msqXR.env : CodeEnv := ⟨layout msqXR⟩

/-- A label's address in the laid-out `msqXR`. -/
abbrev labX (x : Label) : Int64 := (_root_.Executable.labels (layout msqXR)).label x

theorem msqXR_placed : Program.Placed msqXR "main_e" := Program.placed_of_layout msqXR_wf rfl (by decide)

/-! ## `main_e` -/

/-- `main_e`'s precondition: link `raM`, `rbx = &tail`, the nodes, `E0` of `n1`. -/
def MainEPre (P : Params) (raM : Int64) (s : MachineData) (σ : (SharedEnv.counted (EEX P)).State) : Prop :=
  s.regs.get64 .r11 = raM.toBitVec ∧ s.regs.get64 .rbx = P.t ∧ s.regs.get64 .r12 = P.n1 ∧
    s.regs.get64 .r13 = P.n2 ∧ D8 s.dmem ∧ E0 P P.n1 σ.1

/-- **`main_e`'s run** (counted `EEX`, partial). -/
theorem mainE_specXR (P : Params) (hL : QLocs P) (raM : Int64) :
    ∀ s g, MainEPre P raM s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EEX P))) (fun x => x.1.2 = raM ∧ ComE P x.2.1)
        ((s, labX "main_e"), g) := by
  have hpl : Program.PlacedIn msqXR := msqXR_placed.toPlacedIn
  have hE : ∀ n, FunSpecPartialEnv (SharedEnv.counted (EEX P)) (labX "enq") (EnqPre P n) (EnqPost P n) :=
    fun n => (enq_fragXR P n hL).of_placed msqXR_placed (by decide)
  rintro s g ⟨h11, hbx, h12, h13, hd8, hE0⟩
  refine Safely.blockAt hpl blockAt_mainE (X := fun a s₁ => a = labX "enq" ∧
      s₁.regs.get64 .r11 = (labX "ret_e1").toBitVec ∧ s₁.regs.get64 .rdi = P.t ∧ s₁.regs.get64 .rsi = P.n1 ∧
      s₁.regs.get64 .rbp = raM.toBitVec ∧ s₁.regs.get64 .rbx = P.t ∧ s₁.regs.get64 .r13 = P.n2 ∧
      s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainEBody]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h12, h11, h13, and_true]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1di, h1si, h1bp, h1bx, h113, h1dm⟩ hle₁
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₁
  refine (hE P.n1).jcall (ra := labX "ret_e1") ⟨h1r11, h1di, h1si, h1dm ▸ hd8, hE0.fence hle₁.1⟩
    fun s₂ g₂ ⟨⟨h2bx, h2bp, _, h213, _, _, h2dm⟩, y3, hLk⟩ => ?_
  refine Safely.blockAt hpl blockAt_retE1 (X := fun a s₃ => a = labX "enq" ∧
      s₃.regs.get64 .r11 = (labX "ret_e2").toBitVec ∧ s₃.regs.get64 .rdi = P.t ∧ s₃.regs.get64 .rsi = P.n2 ∧
      s₃.regs.get64 .rbp = s₂.regs.get64 .rbp ∧ s₃.dmem = s₂.dmem) ?_ ?_
  · simp only [retE1Body]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h2bx, h1bx, h213, h113, and_true]
  rintro a s₃ g₃ ⟨rfl, h3r11, h3di, h3si, h3bp, h3dm⟩ hle₃
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₃
  refine (hE P.n2).jcall (ra := labX "ret_e2")
    ⟨h3r11, h3di, h3si, by rw [h3dm, h2dm, h1dm]; exact hd8, (Linked.next hL hLk).fence hle₃.1⟩
    fun s₄ g₄ ⟨⟨_, h4bp, _, _, _, _, _⟩, y3', hLk'⟩ => ?_
  refine Safely.blockAt hpl blockAt_retE2 (X := fun a _ => a = Int64.ofBitVec (s₄.regs.get64 .rbp)) ?_ ?_
  · simp only [retE2Body]
    vcgen
    case vc1 s' hs => subst hs; rfl
  rintro a s₅ g₅ rfl hle₅
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₅
  exact Safely.fold (.inl ⟨ofBitVec_reg (by rw [h4bp, h3bp, h2bp, h1bp]), (hLk'.fence hle₅.1).1⟩)

/-! ## `main_d` -/

/-- `main_d`'s precondition: link `raM`, `rbx = &head`, `r14 = &tail`, `ComD`. -/
def MainDPre (P : Params) (raM : Int64) (s : MachineData) (σ : (SharedEnv.counted (EDX P)).State) : Prop :=
  s.regs.get64 .r11 = raM.toBitVec ∧ s.regs.get64 .rbx = P.h ∧ s.regs.get64 .r14 = P.t ∧ D8 s.dmem ∧
    ComD P σ.1

/-- **`main_d`'s run** (counted `EDX`, partial): at the link, `Dn` of `r12`, `r13`. -/
theorem mainD_specXR (P : Params) (hL : QLocs P) (hpt : P.trk = false) (raM : Int64) :
    ∀ s g, MainDPre P raM s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EDX P)))
        (fun x => x.1.2 = raM ∧ Dn P (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13) x.2.1)
        ((s, labX "main_d"), g) := by
  have hpl : Program.PlacedIn msqXR := msqXR_placed.toPlacedIn
  have hD : FunSpecPartialEnv (SharedEnv.counted (EDX P)) (labX "deq") (DeqPre P) (DeqPost P) :=
    (deq_fragXR P hL hpt).of_placed msqXR_placed (by decide)
  rintro s g ⟨h11, hbx, h14, hd8, hC⟩
  refine Safely.blockAt hpl blockAt_mainD (X := fun a s₁ => a = labX "deq" ∧
      s₁.regs.get64 .r11 = (labX "ret_d1").toBitVec ∧ s₁.regs.get64 .rdi = P.h ∧ s₁.regs.get64 .rsi = P.t ∧
      s₁.regs.get64 .rbp = raM.toBitVec ∧ s₁.regs.get64 .rbx = P.h ∧ s₁.regs.get64 .r14 = P.t ∧
      s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainDBody]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h14, h11, and_true]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1di, h1si, h1bp, h1bx, h114, h1dm⟩ hle₁
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₁
  refine hD.jcall (ra := labX "ret_d1") ⟨h1r11, h1di, h1si, h1dm ▸ hd8, hC.fence hle₁.1⟩
    fun s₂ g₂ ⟨⟨h2bx, h2bp, _, _, h214, _, h2dm⟩, hC2, hF2, _⟩ => ?_
  refine Safely.blockAt hpl blockAt_retD1 (X := fun a s₃ => a = labX "deq" ∧
      s₃.regs.get64 .r11 = (labX "ret_d2").toBitVec ∧ s₃.regs.get64 .rdi = P.h ∧ s₃.regs.get64 .rsi = P.t ∧
      s₃.regs.get64 .rbp = s₂.regs.get64 .rbp ∧ s₃.regs.get64 .r12 = s₂.regs.get64 .rax ∧
      s₃.dmem = s₂.dmem) ?_ ?_
  · simp only [retD1Body]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h2bx, h1bx, h214, h114, and_true]
  rintro a s₃ g₃ ⟨rfl, h3r11, h3di, h3si, h3bp, h312, h3dm⟩ hle₃
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₃
  refine hD.jcall (ra := labX "ret_d2")
    ⟨h3r11, h3di, h3si, by rw [h3dm, h2dm, h1dm]; exact hd8, hC2.fence hle₃.1⟩
    fun s₄ g₄ ⟨⟨_, h4bp, h412, _, _, _, _⟩, hC4, _, hD4⟩ => ?_
  refine Safely.blockAt hpl blockAt_retD2 (X := fun a s₅ => a = Int64.ofBitVec (s₄.regs.get64 .rbp) ∧
      s₅.regs.get64 .r12 = s₄.regs.get64 .r12 ∧ s₅.regs.get64 .r13 = s₄.regs.get64 .rax) ?_ ?_
  · simp only [retD2Body]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_true]
  rintro a s₅ g₅ ⟨rfl, h512, h513⟩ hle₅
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₅
  refine Safely.fold (.inl ⟨ofBitVec_reg (by rw [h4bp, h3bp, h2bp, h1bp]), ?_⟩)
  rw [h512, h513, h412, h312]
  exact Dn.fence (show Dn P _ _ _ from ⟨hC4, hD4 _ ((yok_first _).fence hF2 hle₃.1)⟩) hle₅.1

end Kraken.Promising.Lower.MsqXR
