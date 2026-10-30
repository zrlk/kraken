/-
**`print`'s call instances with the frames placed knowing the block**
(AArch64; the twin of `Spike/Lib/LowerX64/PrintCallInstJ.lean`): the
`print` call lemmas of `Spike/Lib/LowerA64/PrintWEW2.lean` and
`Spike/Lib/LowerA64/PrintWBW2.lean` with the suspended frames asked only at
the argument block's states (`printBlkWE_w2'`, `hfpJ`) rather than under the
caller's whole frame condition (`hfp`), so with no `FStable` of it.

- `printWE_w2J`, `printW_w2J`, `printW_w2BJ`: `printWE_w2'`, `printW_w2'`,
  `printW_w2B'` at `hfpJ`;
- `printW_hPWJ_ABJ`, `printWE_hPWEJ_J`: `printW_hPWJ_AB`, `printWE_hPWEJ`
  (`Spike/Lib/LowerA64/PrintFramesJ.lean`) at `hfpJ`, the continuation free
  of `ZBad` (`hNoS`) and `print`'s `svc` states detached (`hDtP`) asked once
  for every call;
- `printCallC_instJ`, `printCallCH_instJ`: `printCallC_inst`,
  `printCallCH_inst` (`Spike/Lib/LowerA64/PrintCallInst.lean`) with `hPer`,
  `hPerE` split into `hNoS`, `hfpJ`, the residual `PrintCallOkR` (`hcall`,
  `hcallE`) and `hDtP`.
-/
import Spike.Lib.LowerA64.PrintWBW2
import Spike.Lib.LowerA64.PrintFramesJ
import Spike.Lib.LowerA64.PrintCallW2
import Spike.Lib.LowerA64.PrintCallC2H

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable AI AS)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange lbl_lt32 printTop0)
open Spike.Lib.LowerShape (printInsts)
open Spike.Lib.A64.Flow.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (PrintC printN loadC nextC)
open Spike.Lib.A64.StubW (printPhOk)
open Spike.Lib.A64.PrintG (printPhOkF)
open Spike.Lib.ByteOut (ByteOut)
open Spike.Lib.PrintSvc (printTop_ext self_mem_printTerms)
open Spike.Lib.A64.PrintA (PrintAW)
open Spike.Lib.PrintSrc (printLD)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **`printWE_w2'` with the frames placed knowing the block**
(`printBlkWE_w2'`): the suspended frames asked only at the argument block's
states (`hfpJ`, for every code `L` of the call), not under the caller's
whole frame condition, so no `FStable` of it. -/
theorem printWE_w2J {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc')
    {x : String} {e : Expr} {c1 : Ctl} {envR : TermRun.Env} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = ⟨.ret .unit, envR, none⟩)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfpJ : ∀ L, PrintCode cx n b o m cw L →
      BlkW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F ⟨pc, oF cx, Jn⟩ (directives L ++ blPrintD))
    (hcall : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
        σC.regs.X1.toBitVec.toNat)
    (hfr : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (callN (_root_.Executable.labels exe).label cx pc L Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) :
    PrintWE' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c
      (printFrame x e c1 :: fs)) K exe endPc R F cx pc n b o m cw Jn ⟨.ret .unit, envR, none⟩ := by
  have hfE : FrOk2 ⟨.ret .unit, envR, none⟩ (printFrame x e c1 :: fs) := frOk2_ret he hfs
  intro L hL
  refine ⟨printBlkWE_w2' hI hpr habI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hi hL
    (fun σ c h => .inr (by rw [hJn σ c h]; rfl)) (hfpJ L hL)
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfE⟩), ?_⟩
  intro σC c hc F' hJF
  have hk := hcall L hL σC c hc
  refine printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit
    (fun md h => hk.off md (hJF.2 md h).1) hk.len hk.raPh hk.raAb
    hp (fun _ c h => h.elim (fun h => h ▸ hfE) False.elim) ?_
  exact PrintAW.ofJF hJF.1 fun _ c' s h hF =>
    .of_ext (.inr (h.elim (fun h => by rw [h]; rfl) False.elim))
      (hfr L hL σC c hc F' hJF s hF).choose_spec.toFramesPlaced

/-- **`printW_w2'` with the frames placed knowing the block**
(`printBlkWE_w2'`): the suspended frames asked only at the argument block's
states (`hfpJ`, for every code `L` of the call), so no `FStable` of the
caller's frame condition. -/
theorem printW_w2J {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc')
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfpJ : ∀ L, PrintCode cx n b o m cw L →
      BlkW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F ⟨pc, oF cx, Jn⟩ (directives L ++ blPrintD))
    (hcall : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
        σC.regs.X1.toBitVec.toNat)
    (hfr : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (callN (_root_.Executable.labels exe).label cx pc L Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    {ms : MemSide isaLSE2}
    (hDt : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      ∀ (F' : MachineData → Prop), pFJ R F (callN (_root_.Executable.labels exe).label cx pc L Jn) σC F' → ∀ s c',
      At exe endPc (pR (-(cx.frame : Int)) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' → Dt s)
    (hms : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      σC.regs.X1.toBitVec.toNat = printN nv mv →
      ∀ (F' : MachineData → Prop), pFJ R F (callN (_root_.Executable.labels exe).label cx pc L Jn) σC F' → ∀ s c',
      At exe endPc (pR (-(cx.frame : Int)) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' →
      (∀ k j, k + j < printN nv mv →
        ms.bo s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC pw wn mv (k + j))
          (fun c0 => ∃ mw b, c0 = nextC pw wn mv (k + j) mw b)) ∧
      ∀ k c1, PrintC pw wn nv mv k c1 → ms.we s c1) :
    PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c
      (printFrame x e c1 :: fs)) K exe endPc R F ms cx pc n b o m cw Jn pw wn nv mv := by
  have hfT := frOk2_printTop0 (pw := pw) (wn := wn) (mv := mv) (x := x) (c1 := c1) he hfs
  have hfP : ∀ j c, PrintC pw wn nv mv j c ∨ PrintC pw wn nv mv j c → FrOk2 c (printFrame x e c1 :: fs) :=
    fun _ _ h => h.elim (fun h => frOk2_printC h he hfs) fun h => frOk2_printC h he hfs
  have hlo' : R.lo ≤ -(cx.frame : Int) := by omega
  intro L hL
  refine ⟨⟨printBlkWE_w2' hI hpr habI hf h1 h16 hR hal hlo' hhi hl hh hsub hfit hFO hp hCd hBl hi hL
    (fun σ c h => by rw [hJn σ c h]; exact printTop_ext (self_mem_printTerms _)) (hfpJ L hL)
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfT⟩), ?_⟩, ?_⟩
  · intro σC c hc F' hJF
    have hk := hcall L hL σC c hc
    exact printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit
      (fun md h => hk.off md (hJF.2 md h).1) hk.len hk.raPh hk.raAb
      hp hfP (printAW_placedSE hJF.1 (fun j c h => h.elim printC_top printC_top) (hfr L hL σC c hc F' hJF))
  · intro σC c hc hN F' hJF s c' hAt
    obtain ⟨j, hj, -⟩ := printSys_src hAt hN
    have hlo2 : R.lo ≤ -(cx.frame : Int) + -48 := by omega
    have hkc : -(cx.frame : Int) < R.hi := by have := frame_ge16 hf; omega
    have hk16 : (-(cx.frame : Int)) % 16 = 0 := by omega
    have hw := printSvc_w2 (kc := -(cx.frame : Int)) (F' := F') (Λ := Λ) (p := p) (rd := rd) (G := G) (ar := ar)
      (J := J) (lsize := lsize) hI hpr habI hph hR hal hl hh hlo2 hkc hk16 hsub hFO (fun md h => (hJF.2 md h).1) hN hp
      (hfP j c' (.inl hj)) (printSvc_placedSE hAt hN (hfr L hL σC c hc F' hJF))
      (hDt L hL σC c hc F' hJF) hAt
    rw [hI.labOk] at hw
    exact ⟨hw, hms L hL σC c hc hN F' hJF s c' hAt⟩

/-- **`printW_w2B'` with the frames placed knowing the block**
(`printW_w2J`): the suspended frames asked only at the argument block's
states (`hfpJ`). -/
theorem printW_w2BJ {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc')
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfpJ : ∀ L, PrintCode cx n b o m cw L →
      BlkW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F ⟨pc, oF cx, Jn⟩ (directives L ++ blPrintD))
    (hcall : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
        σC.regs.X1.toBitVec.toNat)
    (hfr : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (callN (_root_.Executable.labels exe).label cx pc L Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    {ms : MemSide isaLSE2}
    (hDt : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      ∀ (F' : MachineData → Prop), pFJ R F (callN (_root_.Executable.labels exe).label cx pc L Jn) σC F' → ∀ s c',
      At exe endPc (pR (-(cx.frame : Int)) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' → Dt s)
    (hbo : ms.bo = ByteOut p lbl) (hwe : ms.we = WeAb abi (Spike.Lib.A64.WriteAb.Ab lab))
    (hpw : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some σC.regs.X0.toBitVec.toNat)
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) :
    PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c
      (printFrame x e c1 :: fs)) K exe endPc R F ms cx pc n b o m cw Jn pw wn nv mv := by
  refine printW_w2J hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hi hJn he hfs hfpJ
    hcall hfr hDt ?_
  intro L hL σC c hc hN F' hF' s c' hAt
  have hk := hcall L hL σC c hc
  obtain ⟨l, hpw', hlb⟩ := hpw L hL σC c hc
  have h32 := lbl_lt32 hrg hb32 hlb
  have hlen := hk.len
  refine ⟨fun k j hkj => ?_, fun k c2 _ => ?_⟩
  · rw [hbo]
    exact Spike.Lib.A64.Flow.byteOut_at hpw' hlb (by omega) hkj
  · rw [hwe]
    have hlo2 : (pR (-(cx.frame : Int)) R).lo ≤ -48 := hk.lo
    have hhi2 : 0 ≤ (pR (-(cx.frame : Int)) R).hi := hk.hi
    have hw := Spike.Lib.A64.PrintG.printSvcWe hI hpr hph hlo2 hhi2 hlen hAt
    rw [hI.labOk] at hw
    exact hw

/-- **`printW_hPWJ_AB` with the frames placed knowing the block**
(`printW_w2BJ`): at each call the frames along the argument block
(`hfpJ`), the residual `PrintCallOkR` (`hcall`); the continuation free of
`ZBad` (`hNoS`) and `print`'s `svc` states detached (`hDtP`) once for all
calls; the frames inside `print` by `framesPlaced_printFJ`. -/
theorem printW_hPWJ_ABJ {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hfpJ : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (cT : Ctl)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L →
      BlkW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F ⟨pc, oF cx, (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          cT)⟩
        (directives L ++ blPrintD))
    (hcall : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc) s c' → Dt s) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some σC.regs.X0.toBitVec.toNat) →
      PrintSlots lbl Λ.imms cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c
        (printFrame x e c1 :: fs)) K exe endPc R F
        (msOfAB Λ μ p rd G ownA ar IA (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize (printFrame x e c1 :: fs))
        cx pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) pw wn nv mv := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hi hpw hS
  exact printW_w2BJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hi
    (fun _ _ h => h.1) (hNoS x is a e hT) hfs (hfpJ c0 pc env lits cs bufs n x is a e b o m cw c1 _ kk pc' hG0 hT hi)
    (hcall c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn mv kk pc' hG0 hT hi)
    (framesPlaced_printFJ hf hlo hhi hS hFP) (fun _ _ _ _ _ _ _ _ _ hAt => hDtP _ _ _ _ _ _ _ hAt) rfl rfl hpw hrg hb32

/-- **`printWE_hPWEJ` with the frames placed knowing the block**
(`printWE_w2J`): at each call the frames along the argument block
(`hfpJ`), the residual `PrintCallOkR` (`hcallE`); the continuation free of
`ZBad` once for all calls (`hNoS`). -/
theorem printWE_hPWEJ_J {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hfpJ : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (cT : Ctl)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L →
      BlkW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F ⟨pc, oF cx, (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          cT)⟩
        (directives L ++ blPrintD))
    (hcallE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      PrintSlots lbl Λ.imms cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c
        (printFrame x e c1 :: fs)) K exe endPc R F cx pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩ := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hi hS
  have hlo' : R.lo ≤ -(cx.frame : Int) := by omega
  exact printWE_w2J hI hpr habI hph hf h1 h16 hR hal hlo' hhi hl hh hsub hfit hFO hp hCd hBl hi
    (fun _ _ h => h.1) (hNoS x is a e hT) hfs (hfpJ c0 pc env lits cs bufs n x is a e b o m cw c1 _ kk pc' hG0 hT hi)
    (hcallE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hi)
    (framesPlaced_printFJ hf hlo hhi hS hFP)

/-- **An output call at `PrintCallC`, assembled with the frames placed knowing
the block** (`printCallC_of'` as `printCallC_inst`, its `hPW`, `hPWE` by
`printW_hPWJ_ABJ`, `printWE_hPWEJ_J`): the per-call `hPer`, `hPerE` split
into the continuation free of `ZBad` (`hNoS`), the frames along the
argument block (`hfpJ`), the residual `PrintCallOkR` (`hcall`, `hcallE`)
and `print`'s `svc` states detached (`hDtP`). -/
theorem printCallC_instJ {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    {lcx : Scc.Lower.Ctx} (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop}
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hfpJ : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (cT : Ctl)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L →
      BlkW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F ⟨pc, oF cx, (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          cT)⟩
        (directives L ++ blPrintD))
    (hcall : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat)
    (hcallE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ax : FragS isaLSE2} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallC_of' hf h1 h16 hFS hR hal hlo hhi (fun _ _ h => cdOf_of_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ h => cdOf_of_blC hI (hBl _ _ _ h).1) hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isaLSE2) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 h16 hR hal (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k, -⟩ := rsOf_cell hf hk; exact ⟨h1k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWJ_ABJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hrg hb32 hfs hFP
      fp ra tp hNoS hfpJ hcall hDtP)
    (printWE_hPWEJ_J hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hfs hFP fp ra tp hNoS
      hfpJ hcallE)
    hAb

/-- **An output call at `PrintCallCH`, assembled with the frames placed knowing
the block** (`printCallCH_of'` as `printCallCH_inst`, its `hPW`, `hPWE` by
`printW_hPWJ_ABJ`, `printWE_hPWEJ_J`): the per-call `hPer`, `hPerE` split
into the continuation free of `ZBad` (`hNoS`), the frames along the
argument block (`hfpJ`), the residual `PrintCallOkR` (`hcall`, `hcallE`)
and `print`'s `svc` states detached (`hDtP`). -/
theorem printCallCH_instJ {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    {lcx : Scc.Lower.Ctx} (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop}
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hfpJ : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (cT : Ctl)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L →
      BlkW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F ⟨pc, oF cx, (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          cT)⟩
        (directives L ++ blPrintD))
    (hcall : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat)
    (hcallE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ax : FragS isaLSE2} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx cx Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallCH_of' hf h1 h16 hFS hR hal hlo hhi (fun _ _ h => cdOf_of_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ h => cdOf_of_blC hI (hBl _ _ _ h).1) hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isaLSE2) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 h16 hR hal (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k, -⟩ := rsOf_cell hf hk; exact ⟨h1k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWJ_ABJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hrg hb32 hfs hFP
      fp ra tp hNoS hfpJ hcall hDtP)
    (printWE_hPWEJ_J hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hfs hFP fp ra tp hNoS
      hfpJ hcallE)
    hAb

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.printWE_w2J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printWE_w2J

/-- info: 'Spike.Lib.LowerA64.printW_w2J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printW_w2J

/-- info: 'Spike.Lib.LowerA64.printW_w2BJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printW_w2BJ

/-- info: 'Spike.Lib.LowerA64.printW_hPWJ_ABJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printW_hPWJ_ABJ

/-- info: 'Spike.Lib.LowerA64.printWE_hPWEJ_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printWE_hPWEJ_J

/-- info: 'Spike.Lib.LowerA64.printCallC_instJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallC_instJ

/-- info: 'Spike.Lib.LowerA64.printCallCH_instJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallCH_instJ
