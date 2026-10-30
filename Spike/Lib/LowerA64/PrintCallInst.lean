/-
**An output call, assembled** (AArch64): `printCallC_of'`
(`Spike/Lib/LowerA64/PrintCallC2.lean`) and `printCallCH_of'`
(`Spike/Lib/LowerA64/PrintCallC2H.lean`) at the per-pair facts `W2` in the
write abort's phase and the rows' memory side `msOfAB`, every
construct-side premise discharged: the `let` by `printWL_w2`, `print`'s
states by `printW_hPWJ_AB` and `printWE_hPWEJ` (`Spike/Lib/LowerA64/PrintFramesJ.lean`),
the code from the instance (`InstOk`), the kernel and the byte step's
closure by definition (`ByteOut.closed`). So a walk applies one lemma per
`print` site; what stays is the walk's: the frames below placed (`hFP`),
the ghost free of `ZBad` (`hG0F`), the layout (`hrg`, `hb32`), and at each
call (`hPer`, `hPerE`) the continuation free of `ZBad`, the frames placed
along the block, `PrintCallOkR` and the write tail; the abort's landing
(`hAb`).

- `printCallC_inst`: at `PrintCallC`;
- `printCallCH_inst`: at `PrintCallCH` (the source held at `print`'s `ret `).
-/
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
open Spike.Lib.A64.Flow (NodeW BlkW ND At FStable)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange printTop0)
open Spike.Lib.LowerShape (printInsts)
open Spike.Lib.A64.Flow.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (printLD)
open Spike.Lib.A64.StubW (printPhOk)
open Spike.Lib.A64.PrintG (printPhOkF)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.ByteOut (ByteOut)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **An output call at `PrintCallC`, assembled**: `printCallC_of'` inside
`W2` at `msOfAB`, its `hWL` by `printWL_w2`, its `hPW`, `hPWE` by
`printW_hPWJ_AB`, `printWE_hPWEJ`; the walk's facts stay premises. -/
theorem printCallC_inst {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
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
    (hPer : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat) ∧
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∀ (F' : MachineData → Prop), pFJ R F (callN (_root_.Executable.labels exe).label cx pc L
          (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
            (printTop0 pw wn mv))) σC F' → ∀ s c',
        At exe endPc (pR (-(cx.frame : Int)) R) F' (pN (_root_.Executable.labels exe).label
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' → Dt s))
    (hPerE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat))
    {Ax : FragS isaLSE2} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallC_of' hf h1 h16 hFS hR hal hlo hhi (fun _ _ h => cdOf_of_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ h => cdOf_of_blC hI (hBl _ _ _ h).1) hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isaLSE2) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 h16 hR hal (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k, -⟩ := rsOf_cell hf hk; exact ⟨h1k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWJ_AB hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hrg hb32 hfs hFP
      fp ra tp hPer)
    (printWE_hPWEJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hfs hFP fp ra tp hPerE)
    hAb

/-- **An output call at `PrintCallCH`, assembled** (`printCallCH_of'` as
`printCallC_inst` is `printCallC_of'`). -/
theorem printCallCH_inst {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
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
    (hPer : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat) ∧
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∀ (F' : MachineData → Prop), pFJ R F (callN (_root_.Executable.labels exe).label cx pc L
          (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
            (printTop0 pw wn mv))) σC F' → ∀ s c',
        At exe endPc (pR (-(cx.frame : Int)) R) F' (pN (_root_.Executable.labels exe).label
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' → Dt s))
    (hPerE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat))
    {Ax : FragS isaLSE2} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx cx Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallCH_of' hf h1 h16 hFS hR hal hlo hhi (fun _ _ h => cdOf_of_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ h => cdOf_of_blC hI (hBl _ _ _ h).1) hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isaLSE2) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 h16 hR hal (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k, -⟩ := rsOf_cell hf hk; exact ⟨h1k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWJ_AB hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hrg hb32 hfs hFP
      fp ra tp hPer)
    (printWE_hPWEJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hfs hFP fp ra tp hPerE)
    hAb

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.printCallC_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallC_inst

/-- info: 'Spike.Lib.LowerA64.printCallCH_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallCH_inst
