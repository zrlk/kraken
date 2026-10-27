/-
**A call of `print` of an empty slice inside `W2`** (AArch64): `PrintWE`
(`Spike/Lib/LowerA64/PrintCallC2.lean`) at the per-pair facts `W2`
(`Spike/Lib/LowerA64/SFactsA2.lean`) at `print`'s frames
`printFrame x e c1 :: fs`, the source at `print`'s `ret ()` (`cE`).

The argument block with its `bl` is `printBlkW_w2C` with the write abort's
phase (`printBlkW_ab`), the placement at `PlacedSE` (`blkW_placedSE`: `cE`'s
`ret ()` reads no variable) and `FrOk2` at `cE` (`printJ_hJ`, `frOk2_ret`).
`print`'s blocks are `printW2` at every call state, its `hpl` from
`PrintAW.ofJF`, given `print`'s region, frame condition and return address
at the call state (`PrintCallOk`, the call builder's obligation).

- `PrintCallOk`: `printW2`'s premises at a call state not given by the
  program (`print`'s region `Rp` and frame condition `Fp`, the count, the
  return address's phase and position, the suspended frames placed under
  `Fp`);
- `printBlkWE_w2`: the argument block and its `bl` inside `W2`, at controls
  at model terms or reading no variable;
- `printWE_w2`: `PrintWE` inside `W2`;
- `frOk2_printTop0`: `FrOk2` at `printL`'s top at word 0 (`printTop0`);
- `printW_w2`: `PrintW` (a nonempty slice) inside `W2`, its system call by
  `printSvc_w2` (`hpl` by `printSvc_placedSE`), given the memory side's
  byte steps and output words (`hms`) and the write tail at the call
  (`hDt`);
- `printBlkWE_w2'`: `printBlkWE_w2` with the suspended frames placed only at
  the block's states (`blkW_placedSE'`);
- `PrintCallOkR` (`PrintCallOk.toR`), `printWE_w2'`, `printW_w2'`: the same
  at `PrintWE'`, `PrintW'`, the suspended frames placed under frame
  conditions that know the call (`pFJ`, `hfr`).
-/
import Spike.Lib.LowerA64.PrintPlacedSE

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
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame)
open Spike.Lib.LowerShape (printInsts)
open Spike.Lib.A64.Flow.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (PrintC printN loadC nextC)
open Spike.Lib.PrintSvc (printTop_ext self_mem_printTerms)
open Spike.Lib.A64.PrintA (PrintAW)
open Spike.Lib.A64.StubW (printPhOk)

/-- **`printW2`'s premises at a call state** not given by the program: in
`print`'s region `Rp` (16-aligned, 8-aligned bounds holding the 48 bytes
below its base) under its frame condition `Fp` (kept off `Rp`, the words of
`rS` off `Rp`, the suspended frames `fs` placed in slots), the count `len0`
below `2 ^ 63`, the return address `ra` in the phase of `print`'s `done`
and off the write abort. -/
structure PrintCallOk (Λ : Scc.Sem.Layout) (ph : Nat → Nat) (lab : Label → Int64) (rS : Range) (lbl : Lbl)
    (fs : List TermRun.Frame) (Rp : Region) (Fp : MachineData → Prop) (ra : BitVec 64) (len0 : Nat) : Prop where
  ok : Rp.OK
  al : Rp.base.toNat % 16 = 0
  lo : Rp.lo ≤ -48
  hi : 0 ≤ Rp.hi
  lo8 : Rp.lo % 8 = 0
  hi8 : Rp.hi % 8 = 0
  off : ∀ m, Fp m → StackOff rS Rp m
  len : len0 < 2 ^ 63
  raPh : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat
  raAb : Int64.ofBitVec ra ∉ Spike.Lib.A64.WriteAb.abPcs lab
  stable : FStable Rp Fp
  frames : ∀ s : State, Fp s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B

/-- **`PrintCallOk` without the frames**: `printW2`'s premises at a call
state other than the suspended frames' placement and the frame condition's
stability, which `printWE_w2'`, `printW_w2'` take under frame conditions
that know the call (`pFJ`). -/
structure PrintCallOkR (ph : Nat → Nat) (lab : Label → Int64) (rS : Range) (Rp : Region)
    (Fp : MachineData → Prop) (ra : BitVec 64) (len0 : Nat) : Prop where
  ok : Rp.OK
  al : Rp.base.toNat % 16 = 0
  lo : Rp.lo ≤ -48
  hi : 0 ≤ Rp.hi
  lo8 : Rp.lo % 8 = 0
  hi8 : Rp.hi % 8 = 0
  off : ∀ m, Fp m → StackOff rS Rp m
  len : len0 < 2 ^ 63
  raPh : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat
  raAb : Int64.ofBitVec ra ∉ Spike.Lib.A64.WriteAb.abPcs lab

/-- `PrintCallOk` gives `PrintCallOkR`. -/
theorem PrintCallOk.toR {Λ : Scc.Sem.Layout} {ph : Nat → Nat} {lab : Label → Int64} {rS : Range} {lbl : Lbl}
    {fs : List TermRun.Frame} {Rp : Region} {Fp : MachineData → Prop} {ra : BitVec 64} {len0 : Nat}
    (h : PrintCallOk Λ ph lab rS lbl fs Rp Fp ra len0) : PrintCallOkR ph lab rS Rp Fp ra len0 :=
  ⟨h.ok, h.al, h.lo, h.hi, h.lo8, h.hi8, h.off, h.len, h.raPh, h.raAb⟩

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A call of `print`'s argument block and its `bl` inside `W2`**, the
write abort's phase from the code predicates off it (`hCd`, `hBl`,
`printBlkW_ab`), the states at `PlacedSE` (`blkW_placedSE`: the node's
controls at model terms or reading no variable, `hext`; the suspended
frames placed under the frame condition, `hfp`), `FrOk2` at the controls
(`hJ`). -/
theorem printBlkWE_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc') {L : List Item}
    (hL : PrintCode cx n b o m cw L) {Jn : AS → Ctl → Prop}
    (hext : ∀ σ c, Jn σ c → c.term ∈ externModelTerms ∨ exprFv c.term = [])
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, Jn σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs) K exe endPc
      R F ⟨pc, oF cx, Jn⟩ (directives L ++ blPrintD) :=
  printBlkW_w2C hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp (fun _ _ h => (hCd _ _ h).toCdC)
    (fun _ _ _ h => (hBl _ _ _ h).1) hi hL (printBlkW_ab hI hpr habI hf h1 h16 hR hal hlo hhi hCd hBl hi hL)
    (blkW_placedSE hFS hext hfp) hJ

/-- **`printBlkWE_w2` with the frames placed knowing the block**
(`blkW_placedSE'`: the suspended frames asked only at the block's states,
`hfpJ`). -/
theorem printBlkWE_w2' {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc') {L : List Item}
    (hL : PrintCode cx n b o m cw L) {Jn : AS → Ctl → Prop}
    (hext : ∀ σ c, Jn σ c → c.term ∈ externModelTerms ∨ exprFv c.term = [])
    (hfpJ : BlkW (fun s _ => ∃ B, FramesPlacedInI Λ lbl s fs B) (fun _ _ => False) exe endPc R F ⟨pc, oF cx, Jn⟩
      (directives L ++ blPrintD))
    (hJ : ∀ σ c, Jn σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs) K exe endPc
      R F ⟨pc, oF cx, Jn⟩ (directives L ++ blPrintD) :=
  printBlkW_w2C hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp (fun _ _ h => (hCd _ _ h).toCdC)
    (fun _ _ _ h => (hBl _ _ _ h).1) hi hL (printBlkW_ab hI hpr habI hf h1 h16 hR hal hlo hhi hCd hBl hi hL)
    (blkW_placedSE' hext hfpJ) hJ

/-- **A call of `print` of an empty slice inside `W2`** (`PrintWE`) at
`print`'s frames `printFrame x e c1 :: fs`, the source at `print`'s
`ret ()` (`cE`): the argument block by `printBlkWE_w2`, `print`'s blocks by
`printW2` at every call state, given `PrintCallOk` there (`hcall`, in
`print`'s region and frame condition); the caller's continuation and frames
free of `ZBad` (`he`, `hfs`), the frames placed along the block (`hfp`). -/
theorem printWE_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOk okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc')
    {x : String} {e : Expr} {c1 : Ctl} {envR : TermRun.Env} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = ⟨.ret .unit, envR, none⟩)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    (hcall : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      PrintCallOk Λ ph lab rS lbl (printFrame x e c1 :: fs) (pR (-(cx.frame : Int)) R)
        (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat) :
    PrintWE (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c
      (printFrame x e c1 :: fs)) K exe endPc R F cx pc n b o m cw Jn ⟨.ret .unit, envR, none⟩ := by
  have hfE : FrOk2 ⟨.ret .unit, envR, none⟩ (printFrame x e c1 :: fs) := frOk2_ret he hfs
  intro L hL
  refine ⟨printBlkWE_w2 hI hpr habI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hi hL
    (fun σ c h => .inr (by rw [hJn σ c h]; rfl)) hfp
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfE⟩), ?_⟩
  intro σC c hc
  have hk := hcall L hL σC c hc
  refine printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit hk.off hk.len hk.raPh hk.raAb
    hp (fun _ c h => h.elim (fun h => h ▸ hfE) False.elim) ?_
  exact PrintAW.ofJF hk.stable fun _ c s h hF =>
    .of_ext (.inr (h.elim (fun h => by rw [h]; rfl) False.elim)) (hk.frames s hF).choose_spec.toFramesPlaced

/-- **`FrOk2` at `printL`'s top at word 0** inside the call: the caller's
continuation `e` and frames `fs` free of `ZBad`. -/
theorem frOk2_printTop0 {pw wn : TermRun.Word} {mv : Nat} {x : String} {e : Expr} {c1 : Ctl}
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) :
    FrOk2 (Spike.Lib.LowerNode.printTop0 pw wn mv) (printFrame x e c1 :: fs) := by
  refine ⟨printLBody_noZBad, ?_⟩
  intro fr hfr
  rcases List.mem_cons.mp hfr with rfl | hfr
  · exact he
  · exact hfs fr hfr

/-- **A call of `print` of a nonempty slice inside `W2`** (`PrintW`) at
`print`'s frames `printFrame x e c1 :: fs`, the source entering `printL` at
word 0 (`printTop0`): the argument block by `printBlkWE_w2`, `print`'s
blocks by `printW2` and its system call by `printSvc_w2` at every call
state, given `PrintCallOk` there (`hcall`); the memory side's byte steps
and output words at the system call (`hms`), the write tail there (`hDt`);
the caller's continuation and frames free of `ZBad` (`he`, `hfs`), the
frames placed along the block (`hfp`). -/
theorem printW_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOk okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc')
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    (hcall : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      PrintCallOk Λ ph lab rS lbl (printFrame x e c1 :: fs) (pR (-(cx.frame : Int)) R)
        (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat)
    {ms : MemSide isaLSE2}
    (hDt : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      ∀ (F' : MachineData → Prop), (∀ md, F' md → pF (-(cx.frame : Int)) R F md) → ∀ s c',
      At exe endPc (pR (-(cx.frame : Int)) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' → Dt s)
    (hms : ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      σC.regs.X1.toBitVec.toNat = printN nv mv →
      ∀ (F' : MachineData → Prop), (∀ md, F' md → pF (-(cx.frame : Int)) R F md) → ∀ s c',
      At exe endPc (pR (-(cx.frame : Int)) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' →
      (∀ k j, k + j < printN nv mv →
        ms.bo s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC pw wn mv (k + j))
          (fun c0 => ∃ mw b, c0 = nextC pw wn mv (k + j) mw b)) ∧
      ∀ k c1, PrintC pw wn nv mv k c1 → ms.we s c1) :
    PrintW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c
      (printFrame x e c1 :: fs)) K exe endPc R F ms cx pc n b o m cw Jn pw wn nv mv := by
  have hfT := frOk2_printTop0 (pw := pw) (wn := wn) (mv := mv) (x := x) (c1 := c1) he hfs
  have hfP : ∀ j c, PrintC pw wn nv mv j c ∨ PrintC pw wn nv mv j c → FrOk2 c (printFrame x e c1 :: fs) :=
    fun _ _ h => h.elim (fun h => frOk2_printC h he hfs) fun h => frOk2_printC h he hfs
  have hlo' : R.lo ≤ -(cx.frame : Int) := by omega
  intro L hL
  refine ⟨⟨printBlkWE_w2 hI hpr habI hf h1 h16 hR hal hlo' hhi hl hh hsub hfit hFO hp hFS hCd hBl hi hL
    (fun σ c h => by rw [hJn σ c h]; exact printTop_ext (self_mem_printTerms _)) hfp
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfT⟩), ?_⟩, ?_⟩
  · intro σC c hc
    have hk := hcall L hL σC c hc
    exact printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit hk.off hk.len hk.raPh hk.raAb
      hp hfP (printAW_placedSE hk.stable (fun j c h => h.elim printC_top printC_top) hk.frames)
  · intro σC c hc hN F' hF' s c' hAt
    have hk := hcall L hL σC c hc
    obtain ⟨j, hj, -⟩ := printSys_src hAt hN
    have hlo2 : R.lo ≤ -(cx.frame : Int) + -48 := by omega
    have hkc : -(cx.frame : Int) < R.hi := by have := frame_ge16 hf; omega
    have hk16 : (-(cx.frame : Int)) % 16 = 0 := by omega
    have hw := printSvc_w2 (kc := -(cx.frame : Int)) (F' := F') (Λ := Λ) (p := p) (rd := rd) (G := G) (ar := ar)
      (J := J) (lsize := lsize) hI hpr habI hph hR hal hl hh hlo2 hkc hk16 hsub hFO hF' hN hp
      (hfP j c' (.inl hj)) (printSvc_placedSE hAt hN fun s hF => hk.frames s (hF' _ hF))
      (hDt L hL σC c hc F' hF') hAt
    rw [hI.labOk] at hw
    exact ⟨hw, hms L hL σC c hc hN F' hF' s c' hAt⟩


/-- **`printWE_w2` under frame conditions that know the call**
(`PrintWE'`): `print`'s blocks at every `F'` with `pFJ` at the call node,
the suspended frames placed under such `F'` (`hfr`), the rest of
`PrintCallOk` at the call states (`hcall`). -/
theorem printWE_w2' {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOk okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc')
    {x : String} {e : Expr} {c1 : Ctl} {envR : TermRun.Env} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = ⟨.ret .unit, envR, none⟩)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
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
  refine ⟨printBlkWE_w2 hI hpr habI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hi hL
    (fun σ c h => .inr (by rw [hJn σ c h]; rfl)) hfp
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfE⟩), ?_⟩
  intro σC c hc F' hJF
  have hk := hcall L hL σC c hc
  refine printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit
    (fun md h => hk.off md (hJF.2 md h).1) hk.len hk.raPh hk.raAb
    hp (fun _ c h => h.elim (fun h => h ▸ hfE) False.elim) ?_
  exact PrintAW.ofJF hJF.1 fun _ c' s h hF =>
    .of_ext (.inr (h.elim (fun h => by rw [h]; rfl) False.elim))
      (hfr L hL σC c hc F' hJF s hF).choose_spec.toFramesPlaced

/-- **`printW_w2` under frame conditions that know the call** (`PrintW'`):
`print`'s blocks and its system call at every `F'` with `pFJ` at the call
node, the suspended frames placed under such `F'` (`hfr`), the rest of
`PrintCallOk` at the call states (`hcall`); the write tail (`hDt`) and the
memory side (`hms`) asked under such `F'`. -/
theorem printW_w2' {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOk okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc')
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
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
  refine ⟨⟨printBlkWE_w2 hI hpr habI hf h1 h16 hR hal hlo' hhi hl hh hsub hfit hFO hp hFS hCd hBl hi hL
    (fun σ c h => by rw [hJn σ c h]; exact printTop_ext (self_mem_printTerms _)) hfp
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

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.printWE_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printWE_w2

/-- info: 'Spike.Lib.LowerA64.printW_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printW_w2

/-- info: 'Spike.Lib.LowerA64.printWE_w2'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printWE_w2'

/-- info: 'Spike.Lib.LowerA64.printW_w2'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printW_w2'

/-- info: 'Spike.Lib.LowerA64.printBlkWE_w2'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printBlkWE_w2'
