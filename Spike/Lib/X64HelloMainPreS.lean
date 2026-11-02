/-
**`hello.w`'s `scc_rt_main` up to `wc_rodata`'s entry** (x86-64; twin of `Spike/Lib/A64HelloMainPreS.lean`'s live
part): `scc_rt_main`'s prologue and call block as one segment, from its entry to `wc_rodata`'s entry at the call
(`Hello1.mNC`). At the real run `scc_rt_main`'s own states stay at no frame with the setup start's control, as
`MainWf.mainPreWH_W0SH` proves them; the source's call of `rodata` is taken at `wc_rodata`'s entry.

- `main_call_segW`: `scc_rt_main`'s prologue and call block, from its entry to `wc_rodata`'s entry (`mNC`).

## Differences from the AArch64 version

- The prologue is x86-64's five-node `XProW` (frame 64 under the saved `%rbp`, `%rdi` at `-8(%rbp)`; AArch64's
  `ProW` of frame 80), its segment `prologue_seg_ofW` at `HelloM.hello_mainPro`, its limit word at
  `%fs:8` (`hlimM`: `LimOk ms F (fsBase + 8) (rsp - 8 - 64)`). `call` pushes `.Lscc_rt_main.x2` (at `-80`),
  read from the block's run through `label_labelGapB` (`.x2 = .entry + 5`). The bounds are `R.lo ≤ -288`,
  `8 ≤ R.hi`, with no 16-alignment; the nodes take the region (`mN0 lab R J`, `mNC lab R J`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `blkW_at0`,
  `hello_main_pre_segWS`.
-/
import Spike.Lib.X64HelloMain

namespace Spike.Lib.X64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (LimOk seg_oneW)
open Spike.Lib.X64.Flow.Hello1 (mB0 mB0_ok mB0_run mainIn mN0 mNC mO mJ)
open Scc.Cert.Rt.X64 (Lays endOf code_field label_labelGapB)

set_option linter.unusedSimpArgs false

section MainPreS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main`'s prologue and call block are one segment inside `W`** in any valid layout of `helloCells`:
from its entry (invariant `J`) to `wc_rodata`'s entry at the call (`mNC`), the limit word's facts for the
frame (`hlimM`), its states inside `W` (`hpro`, `hcall`). -/
theorem main_call_segW {W : Frag isa} {K : State → State → Prop} {ms : MemSide isa}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop}
    (hpro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 64 8
      ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J)
    (hcall : BlkW W K exe endPc R F (mN0 (_root_.Executable.labels exe).label R J) mB0)
    (hlimM : ∀ σ c, J σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F (mNC (_root_.Executable.labels exe).label R J)) := by
  have hin := hello_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨h0, -⟩, hg1⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e5 : (_root_.Executable.labels exe).label ".Lscc_rt_main.x2" =
      (_root_.Executable.labels exe).label ".Lscc_rt_main.entry" + Int64.ofNat 5 := label_labelGapB hp hg1
  refine SegW.seq (prologue_seg_ofW hp hend hello_mainPro (nb := ⟨lab ".Lscc_rt_main.entry", mO, mJ J⟩)
    (by decide) hF hR (by have : (64 : Int64).toInt = 64 := (by decide); omega) (by omega) (by decide)
    rfl (by show SO.le mO (oF 64) = true; decide) hpro ?_)
    ((seg_oneW (seg_ndW (n := mN0 lab R J) (by simp [mB0]) mB0_ok hF hR hlo hhi
      (code_field hp hend h0 (ofNat_zero' _)) hcall fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => Hello1.At.reg_addr (r := .rbp) (k := -8) rfl h)
  · -- the prologue
    intro σ c hJ
    have hl := hlimM σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  · simp only [mN0, mNC]; rw [mB0_run]
  · simp only [mN0, mNC]; rw [mB0_run]; rfl
  · simp only [mN0, mNC] at hJ ⊢
    rw [mB0_run]
    obtain ⟨⟨σe, hJe, h0', h8, h16, hsp, hfs⟩, hb⟩ := hJ
    refine ⟨σe, hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [upd_apply]; exact h0'
    · simp only [upd_apply]; exact h8
    · simp only [upd_apply]; exact h16
    · simp [Reg64s.set64, hsp]
    · simp [Reg64s.set64, hfs]
    · rw [Reg64s.get64_set64_ne _ (by decide)]; exact hb
    · rw [e5]
      simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add]
      rfl

end MainPreS

end Spike.Lib.X64.Flow.HelloM

/-- info: 'Spike.Lib.X64.Flow.HelloM.main_call_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloM.main_call_segW
