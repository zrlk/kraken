/-
**An output call, assembled** (x86-64; the twin of
`Spike/Lib/LowerA64/PrintCallInst.lean`): `printCallC_of'`
(`Spike/Lib/LowerX64/PrintCallC2.lean`) and `printCallCH_ofR`
(`Spike/Lib/LowerX64/PrintCallC2H.lean`) at the per-pair facts `W2` in the
write abort's phase and the rows' memory side `msOfAB`, every
construct-side premise discharged: the `let` by `printWL_w2`, `print`'s
states by `printW_hPWJ_AB` and `printWE_hPWEJ` (`Spike/Lib/LowerX64/PrintFramesJ.lean`),
the code from the instance (`InstOk`), the kernel and the byte step's
closure by definition (`ByteOut.closed`). So a walk applies one lemma per
`print` site; what stays is the walk's: the frames below placed (`hFP`),
the ghost free of `ZBad` (`hG0F`), the layout (`hrg`, `hb32`), and at each
call (`hPer`, `hPerE`) the continuation free of `ZBad`, the frames placed
along the block, `PrintCallOkR` and the write tail; the abort's landing
(`hAb`).

- `printCallC_inst`: at `PrintCallC`;
- `printCallCH_inst`: at `PrintCallCH` (the source held at `print`'s `ret ()`).
-/
import Spike.Lib.LowerX64.PrintFramesJ
import Spike.Lib.LowerX64.PrintCallW2
import Spike.Lib.LowerX64.PrintCallC2H

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Lower.InvX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND AS At FStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange printTop0)
open Spike.Lib.X64.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (printLD)
open Spike.Lib.X64.PrintG (printPhOk)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.ByteOut (ByteOut)
open Spike.Lib.LowerShape (printInsts)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **An output call at `PrintCallC`, assembled**: `printCallC_of'` inside
`W2` at `msOfAB`, its `hWL` by `printWL_w2`, its `hPW`, `hPWE` by
`printW_hPWJ_AB`, `printWE_hPWEJ`; the walk's facts stay premises. -/
theorem printCallC_inst {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
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
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∀ (F' : MachineData → Prop), pFJ R F (B.nC (_root_.Executable.labels exe).label fr
          (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
            (printTop0 pw wn mv))) σC F' → ∀ s c',
        At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
        Dt s))
    (hPerE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat))
    {Ax : FragS isa} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallC_of' hf h1 hFS hR hlo hhi (fun _ _ h => codeAt_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => by
      obtain ⟨L, j, off, hpc, hb, -⟩ := (hBl _ _ _ _ h).1
      intro s hs hn
      have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
      rwa [hI.labOk, hpc] at this)
    hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isa) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 hR (by omega) (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k⟩ := rsOf_bounds hf hk; exact ⟨h2k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWJ_AB hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hrg hb32 hfs hFP
      fp ra tp hPer)
    (printWE_hPWEJ hI hpr habI hph hf h1 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hfs hFP fp ra tp hPerE)
    hAb

/-- **An output call at `PrintCallCH`, assembled** (`printCallCH_ofR`, as
`printCallC_inst` is `printCallC_of'`). -/
theorem printCallCH_inst {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
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
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∀ (F' : MachineData → Prop), pFJ R F (B.nC (_root_.Executable.labels exe).label fr
          (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
            (printTop0 pw wn mv))) σC F' → ∀ s c',
        At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
        Dt s))
    (hPerE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat))
    {Ax : FragS isa} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallCH_ofR hf h1 hFS hR hlo hhi (fun _ _ h => codeAt_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => by
      obtain ⟨L, j, off, hpc, hb, -⟩ := (hBl _ _ _ _ h).1
      intro s hs hn
      have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
      rwa [hI.labOk, hpc] at this)
    hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isa) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 hR (by omega) (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k⟩ := rsOf_bounds hf hk; exact ⟨h2k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWJ_AB hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hrg hb32 hfs hFP
      fp ra tp hPer)
    (printWE_hPWEJ hI hpr habI hph hf h1 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hfs hFP fp ra tp hPerE)
    hAb

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.printCallC_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallC_inst

/-- info: 'Spike.Lib.LowerX64.printCallCH_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallCH_inst
