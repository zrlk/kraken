/-
**The frames inside a call of `print` placed under frame conditions that
know the call** (AArch64): `printCallC_of'` (`Spike/Lib/LowerA64/PrintCallC2.lean`)
asks `print`'s states only under frame conditions `F'` with `pFJ` at the
call node; such an `F'` has, at each of its states, a caller's state at the
call whose cells outside `print`'s region it keeps (`CKept`). With the
caller's control placed in the call state's slots (`PrintSlots`, which
`printCallC_of'` gives), the caller's frame `printFrame x e c1` is placed
in its frame's slots, kept by `print`, on the caller's frames placed under
`F` (`framesPlaced_calleeF2`'s pattern). So `printWE_w2'`, `printW_w2B'`'s
`hfr` needs no more than the frames below placed under `F`.

- `framesPlaced_printFJ`: the frames `printFrame x e c1 :: fs` placed
  under every `F'` with `pFJ` at the call node;
- `printWE_hPWEJ`, `printW_hPWJ`: `printCallC_of'`'s `hPWE`, `hPW` inside
  `W2` (`printWE_w2'`, `printW_w2B'`), the frames inside `print` by
  `framesPlaced_printFJ`;
- `printW_hPWJ_AB`: `printW_hPWJ` at the rows' memory side `msOfAB`, its
  byte step and write abort by definition (`hms` from `hrg`, `hb32` only).
-/
import Spike.Lib.LowerA64.PrintWBW2
import Spike.Lib.LowerA64.CtxC2
import Spike.Lib.A64ConsumerAB

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable AI AS Abs CKept)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange printTop0 SlotRepAt)
open Spike.Lib.LowerShape (printInsts)
open Spike.Lib.A64.Flow.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (PrintC printN loadC nextC)
open Spike.Lib.A64.StubW (printPhOk)
open Spike.Lib.A64.PrintG (printPhOkF)
open Spike.Lib.ByteOut (ByteOut)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **The frames inside a call of `print` placed** under a frame condition
`F'` that knows the call (`pFJ` at `callN`): the caller's frame
`printFrame x e c1` placed in its frame's slots at the caller's state the
condition keeps (`PrintSlots` at the layout's immediates,
`slotPlacedI_of_slotRepAt`, `FramesPlacedInI.of_cKept`), on the frames
`fs` placed under `F` (`hFP`). -/
theorem framesPlaced_printFJ {cx : FnCtx} (hf : FrameOk cx) (hlo : R.lo ≤ -(cx.frame : Int) - 48)
    (hhi : 0 ≤ R.hi) {lab : Label → Int64} {pc : Int64} {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg}
    {m cw : Scc.IR.Operand} {Jn : AS → Ctl → Prop} {x : String} {e : Expr} {c1 : Ctl}
    (hS : PrintSlots lbl Λ.imms cx lab pc n b o m cw Jn x e c1)
    (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A) :
    ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN lab cx pc L Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (callN lab cx pc L Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A := by
  intro L hL σC c hc F' hJF s hm
  obtain ⟨⟨hF, -⟩, mC, -, hA, -, hk⟩ := hJF.2 _ hm
  obtain ⟨A2, h2⟩ := hFP s hF
  have hsr := hS L hL σC c hc
  have hout : ∀ r k, rsOf cx r = some k →
      R.Off k ∧ ¬ (R.callee (-(cx.frame : Int)) (-48) 0).Off (k - (-(cx.frame : Int))) := by
    intro r k hk
    obtain ⟨hk1, hk2, hk3, -⟩ := rsOf_cell hf hk
    exact frame_outA (D := 48) hlo hhi (by decide) hk1 hk2 (by omega)
  let A1 : Nat → Prop := fun a => ∃ r k, rsOf cx r = some k ∧ a = (R.addr k).toNat
  let sC : State := { s with st := (mC, s.st.2) }
  have hsp : SlotPlacedI Λ lbl sC { c1 with term := .let_ x (.atom .unit) e } A1 e := by
    refine slotPlacedI_of_slotRepAt (addr := R.addr) hsr ?_ (fun r k hk => ⟨r, k, hk, rfl⟩)
    intro r k hk
    obtain ⟨jj, hl, hv⟩ := hA.slot k (hout r k hk).1
    show (mC.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64) = _
    rw [hl, Option.map_some, hv]
  have h1 : FramesPlacedInI Λ lbl sC [printFrame x e c1] A1 :=
    FramesPlacedInI.push hsp (FramesPlacedInI.nil A1) rfl rfl rfl rfl
  have h1' : FramesPlacedInI Λ lbl s [printFrame x e c1] A1 :=
    h1.of_cKept (s := sC) hk fun a ⟨r, k, hk', ha⟩ => ⟨k, (hout r k hk').1, (hout r k hk').2, ha⟩
  exact ⟨fun a => A1 a ∨ A2 a, FramesPlacedInI.cons1 (h1'.mono fun _ h => .inl h) (h2.mono fun _ h => .inr h)⟩

/-- **`printCallC_of'`'s `hPW` inside `W2`** (`printW_w2B'` at `printJ`):
`printW_hPW'` with the frames inside `print` by `framesPlaced_printFJ`
from the caller's slots (`printCallC_of'`'s `PrintSlots`) and the frames
below placed under `F` (`hFP`). -/
theorem printW_hPWJ {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    {ms : List TermRun.Frame → MemSide isaLSE2} (hbo : ∀ fs', (ms fs').bo = ByteOut p lbl)
    (hwe : ∀ fs', (ms fs').we = WeAb abi (Spike.Lib.A64.WriteAb.Ab lab))
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
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
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' → Dt s)) :
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
        (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) cx pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) pw wn nv mv := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hi hpw hS
  obtain ⟨he, hfp, hcall, hDt⟩ := hPer c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hi
  exact printW_w2B' hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hi
    (fun _ _ h => h.1) he hfs hfp hcall (framesPlaced_printFJ hf hlo hhi hS hFP) hDt (hbo _) (hwe _) hpw hrg hb32

/-- **`printW_hPWJ` at the rows' memory side** (`msOfAB` at the write
abort's phase): `print`'s byte step and the write abort's justification
(`hbo`, `hwe`) hold by definition, so `printW_w2`'s `hms` needs only the
labels in the heap or `.data` (`hrg`, e.g. `lblRange_reach`) and the layout
below `2 ^ 32` (`hb32`, `below32_of_placeOKAt`). -/
theorem printW_hPWJ_AB {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
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
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c' → Dt s)) :
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
  obtain ⟨he, hfp, hcall, hDt⟩ := hPer c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hi
  exact printW_w2B' hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hi
    (fun _ _ h => h.1) he hfs hfp hcall (framesPlaced_printFJ hf hlo hhi hS hFP) hDt rfl rfl hpw hrg hb32

/-- **`printCallC_of'`'s `hPWE` inside `W2`** (`printWE_w2'` at `printJ`
at `print`'s `ret `): the frames inside `print` by
`framesPlaced_printFJ` from the caller's slots and the frames below placed
under `F` (`hFP`); at each call (`hPer`) the caller's continuation free of
`ZBad`, the frames placed along the block and the rest of `PrintCallOk` at
the call states. -/
theorem printWE_hPWEJ {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hPer : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat)) :
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
  obtain ⟨he, hfp, hcall⟩ := hPer c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hi
  have hlo' : R.lo ≤ -(cx.frame : Int) := by omega
  exact printWE_w2' hI hpr habI hph hf h1 h16 hR hal hlo' hhi hl hh hsub hfit hFO hp hFS hCd hBl hi
    (fun _ _ h => h.1) he hfs hfp hcall (framesPlaced_printFJ hf hlo hhi hS hFP)

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.framesPlaced_printFJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.framesPlaced_printFJ

/-- info: 'Spike.Lib.LowerA64.printW_hPWJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printW_hPWJ

/-- info: 'Spike.Lib.LowerA64.printWE_hPWEJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printWE_hPWEJ

/-- info: 'Spike.Lib.LowerA64.printW_hPWJ_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printW_hPWJ_AB
