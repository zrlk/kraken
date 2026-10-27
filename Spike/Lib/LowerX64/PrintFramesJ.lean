/-
**The frames inside a call of `print` placed under frame conditions that
know the call** (x86-64; the twin of `Spike/Lib/LowerA64/PrintFramesJ.lean`):
`printCallC_of'` (`Spike/Lib/LowerX64/PrintCallC2.lean`) asks `print`'s
states only under frame conditions `F'` with `pFJ` at the call node; such
an `F'` has, at each of its states, a caller's state at the call whose
cells outside `print`'s region it keeps (`CKept`). With the caller's
control placed in the call state's slots (`PrintSlots`, which
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
import Spike.Lib.LowerX64.PrintWBW2
import Spike.Lib.LowerX64.CtxC2
import Spike.Lib.X64ConsumerAB

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND AS At FStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange printTop0 SlotRepAt)
open Spike.Lib.X64.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (PrintC printN loadC nextC)
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

omit [Kraken.Executable.ValidLayout exe] in
/-- **The frames inside a call of `print` placed** under a frame condition
`F'` that knows the call (`pFJ` at `PBlk.nC`): the caller's frame
`printFrame x e c1` placed in its frame's slots at the caller's state the
condition keeps (`PrintSlots` at the layout's immediates,
`placedPf_of_slotRep`, `FramesPlacedInI.of_cKept`), on the frames `fs`
placed under `F` (`hFP`). -/
theorem framesPlaced_printFJ {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (hlo : R.lo ≤ -(fr.size : Int) - 56)
    (hhi : 16 ≤ R.hi) {lab' : String → Int64} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {kk : Nat} {pc : Int64} {n : Nat} {b : Scc.IR.Operand}
    {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {Jn : AS → Ctl → Prop} {x : String} {e : Expr} {c1 : Ctl}
    (hS : PrintSlots lbl Λ.imms fr Cd Bl kk lab' pc n b o m cw Jn x e c1)
    (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A) :
    ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC lab' fr Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (B.nC lab' fr Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A := by
  intro B hB σC c hc F' hJF s hm
  obtain ⟨⟨hF, -⟩, mC, -, hA, -, hk⟩ := hJF.2 _ hm
  obtain ⟨A2, h2⟩ := hFP s hF
  have hsr := hS B hB σC c hc
  have hout : ∀ r k, rsOf fr r = some k →
      R.Off k ∧ ¬ (R.callee (-(fr.size : Int) - 8 - 8) (-40) 16).Off (k - (-(fr.size : Int) - 8 - 8)) := by
    intro r k hk
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hk
    simp only [Region.Off, Region.callee]
    omega
  let A1 : Nat → Prop := fun a => ∃ r k, rsOf fr r = some k ∧ a = (R.addr k).toNat
  let sC : State := { s with st := (mC, s.st.2) }
  obtain ⟨envm, hrep, htot', hpl, himm'⟩ := placedPf_of_slotRep (s := sC)
    (pf := fun k => .slot (R.addr k).toNat) hsr fun r k hk => by
      obtain ⟨jj, hl, hv⟩ := hA.slot k (hout r k hk).1
      show (Scc.Sem.X64.privLoad sC (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      show ((mC.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64)).map (·.toNat) = _
      rw [hl, Option.map_some, hv]; rfl
  have hsp : SlotPlacedI Λ lbl sC { c1 with term := .let_ x (.atom .unit) e } A1 e := by
    refine ⟨envm, hrep, htot', fun y k wp hem qq hq => ?_, himm'⟩
    obtain ⟨r, k', hk', rfl⟩ := hpl y k wp hem qq hq
    exact ⟨_, rfl, r, k', hk', rfl⟩
  have h1 : FramesPlacedInI Λ lbl sC [printFrame x e c1] A1 :=
    Spike.Lib.X64ConsumerS.FramesPlacedInI.push hsp (Spike.Lib.X64ConsumerS.FramesPlacedInI.nil A1) rfl rfl rfl rfl
  have h1' := h1.of_cKept (s' := s) (by exact hk)
    fun a ⟨r, k, hk', ha⟩ => ⟨k, (hout r k hk').1, (hout r k hk').2, ha⟩
  exact ⟨fun a => A1 a ∨ A2 a, FramesPlacedInI.cons1 (h1'.mono fun _ h => .inl h) (h2.mono fun _ h => .inr h)⟩

/-- **`printCallC_of'`'s `hPW` inside `W2`** (`printW_w2B'` at `printJ`):
`printW_hPW'` with the frames inside `print` by `framesPlaced_printFJ`
from the caller's slots (`printCallC_of'`'s `PrintSlots`) and the frames
below placed under `F` (`hFP`). -/
theorem printW_hPWJ {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    {ms : List TermRun.Frame → MemSide isa} (hbo : ∀ fs', (ms fs').bo = ByteOut p lbl)
    (hwe : ∀ fs', (ms fs').we = WeAb abi (Ab lab))
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
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
        Dt s)) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintSlots lbl Λ.imms fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
        endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) pw wn nv mv := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi hpw hS
  obtain ⟨he, hfp, hcall, hDt⟩ :=
    hPer c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi
  exact printW_w2B' hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl
    (fun _ _ h => h.1) he hfs hfp hcall (framesPlaced_printFJ hf hlo hhi hS hFP) hDt (hbo _) (hwe _) hpw
    hrg hb32

/-- **`printW_hPWJ` at the rows' memory side** (`msOfAB` at the write
abort's phase): `print`'s byte step and the write abort's justification
(`hbo`, `hwe`) hold by definition, so `printW_w2`'s `hms` needs only the
labels in the heap or `.data` (`hrg`, e.g. `lblRange_reach`) and the layout
below `2 ^ 32` (`hb32`, `below32_of_placeOKAt`). -/
theorem printW_hPWJ_AB {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
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
        Dt s)) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintSlots lbl Λ.imms fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
        endPc R F (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize (printFrame x e c1 :: fs)) fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) pw wn nv mv := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi hpw hS
  obtain ⟨he, hfp, hcall, hDt⟩ :=
    hPer c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi
  exact printW_w2B' hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl
    (fun _ _ h => h.1) he hfs hfp hcall (framesPlaced_printFJ hf hlo hhi hS hFP) hDt rfl rfl hpw
    hrg hb32

/-- **`printCallC_of'`'s `hPWE` inside `W2`** (`printWE_w2'` at `printJ`
at `print`'s `ret ()`): the frames inside `print` by
`framesPlaced_printFJ` from the caller's slots and the frames below placed
under `F` (`hFP`); at each call (`hPer`) the caller's continuation free of
`ZBad`, the frames placed along the block and `PrintCallOkR` at the call
states. -/
theorem printWE_hPWEJ {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hPer : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintSlots lbl Λ.imms fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
        endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩ := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hi hS
  obtain ⟨he, hfp, hcall⟩ := hPer c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hi
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hlo' : R.lo ≤ -(fr.size : Int) - 8 := by omega
  exact printWE_w2' hI hpr habI hph hf h1 hR hR8 hlo' hhi hl hh hsub hfit hFO hp hFS hCd hBl
    (fun _ _ h => h.1) he hfs hfp hcall (framesPlaced_printFJ hf hlo hhi hS hFP)

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.framesPlaced_printFJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.framesPlaced_printFJ

/-- info: 'Spike.Lib.LowerX64.printW_hPWJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_hPWJ

/-- info: 'Spike.Lib.LowerX64.printWE_hPWEJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printWE_hPWEJ

/-- info: 'Spike.Lib.LowerX64.printW_hPWJ_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_hPWJ_AB
