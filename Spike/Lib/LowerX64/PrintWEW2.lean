/-
**A call of `print` inside `W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/PrintWEW2.lean`): `PrintWE` and `PrintW`
(`Spike/Lib/LowerX64/PrintCallC2.lean`) at the per-pair facts `W2`
(`Spike/Lib/LowerX64/SFactsA2.lean`) at `print`'s frames
`printFrame x e c1 :: fs`.

The argument block's four pieces are `printArgW_w2` with the write abort's
phase (`printArgW_ab`), the placement at `PlacedSE` (`printArgW_placedSE`:
the controls at model terms or reading no variable) and `FrOk2` at the
controls (`frOk2_ret`, `frOk2_printTop0`). `print`'s blocks are `printW2` at
every call state, its `hpl` from `PrintAW.ofJF` (an empty slice) or
`printAW_placedSE` (a nonempty one), given `print`'s region, frame condition
and return address at the call state (`PrintCallOk`, the call builder's
obligation); a nonempty slice's system call is `printSvc_w2` (`hpl` by
`printSvc_placedSE`).

- `PrintCallOk`: `printW2`'s premises at a call state not given by the
  program (`print`'s region `Rp` and frame condition `Fp`, the count, the
  return address's phase and position, the suspended frames placed under
  `Fp`);
- `printArgW_placedSE`: the four pieces' states at `PlacedSE`;
- `printArgW_placedSE'`, `PrintArgW.framesOfF`, `printArgWE_w2'`: the same
  with the suspended frames placed only at the pieces' states;
- `printArgWE_w2`: the four pieces inside `W2`, at controls at model terms or
  reading no variable;
- `printWE_w2`: `PrintWE` inside `W2`;
- `frOk2_printTop0`: `FrOk2` at `printL`'s top at word 0 (`printTop0`);
- `printW_w2`: `PrintW` (a nonempty slice) inside `W2`, given the memory
  side's byte steps and output words (`hms`) and the write tail at the call
  (`hDt`);
- `PrintCallOkR` (`PrintCallOk.toR`), `printWE_w2'`, `printW_w2'`: the same
  at `PrintWE'`, `PrintW'`, the suspended frames placed under frame
  conditions that know the call (`pFJ`, `hfr`).
-/
import Spike.Lib.LowerX64.PrintArgW2
import Spike.Lib.LowerX64.PrintPlacedSE

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND AS At FStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame)
open Spike.Lib.X64.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (PrintC printN loadC nextC)
open Spike.Lib.PrintSvc (printTop_ext self_mem_printTerms)
open Spike.Lib.X64.PrintA (PrintAW)
open Spike.Lib.X64.PrintG (printPhOk)
open Spike.Lib.X64.WriteAb (Ab)

/-- **`printW2`'s premises at a call state** not given by the program: in
`print`'s region `Rp` (8-aligned, 8-aligned bounds holding the 40 bytes
below its base and the 16 above) under its frame condition `Fp` (kept off
`Rp`, the words of `rS` off `Rp`, the suspended frames `fs` placed in
slots), the count `len0` below `2 ^ 63`, the return address `ra` in the
phase of `print`'s `done` and off the write abort. -/
structure PrintCallOk (Λ : Scc.Sem.Layout) (ph : Nat → Nat) (lab : Label → Int64) (rS : Range) (lbl : Lbl)
    (fs : List TermRun.Frame) (Rp : Region) (Fp : MachineData → Prop) (ra : BitVec 64) (len0 : Nat) : Prop where
  ok : Rp.OK
  al : Rp.base.toNat % 8 = 0
  lo : Rp.lo ≤ -40
  hi : 16 ≤ Rp.hi
  lo8 : Rp.lo % 8 = 0
  hi8 : Rp.hi % 8 = 0
  off : ∀ m, Fp m → StackOff rS Rp m
  len : len0 < 2 ^ 63
  raPh : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat
  raAb : Int64.ofBitVec ra ∉ Spike.Lib.X64.WriteAb.abPcs lab
  stable : FStable Rp Fp
  frames : ∀ s : State, Fp s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B

/-- **`PrintCallOk` without the frames**: `printW2`'s premises at a call
state other than the suspended frames' placement and the frame condition's
stability, which `printWE_w2'`, `printW_w2'` take under frame conditions
that know the call (`pFJ`). -/
structure PrintCallOkR (ph : Nat → Nat) (lab : Label → Int64) (rS : Range) (Rp : Region)
    (Fp : MachineData → Prop) (ra : BitVec 64) (len0 : Nat) : Prop where
  ok : Rp.OK
  al : Rp.base.toNat % 8 = 0
  lo : Rp.lo ≤ -40
  hi : 16 ≤ Rp.hi
  lo8 : Rp.lo % 8 = 0
  hi8 : Rp.hi % 8 = 0
  off : ∀ m, Fp m → StackOff rS Rp m
  len : len0 < 2 ^ 63
  raPh : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat
  raAb : Int64.ofBitVec ra ∉ Spike.Lib.X64.WriteAb.abPcs lab

/-- `PrintCallOk` gives `PrintCallOkR`. -/
theorem PrintCallOk.toR {Λ : Scc.Sem.Layout} {ph : Nat → Nat} {lab : Label → Int64} {rS : Range} {lbl : Lbl}
    {fs : List TermRun.Frame} {Rp : Region} {Fp : MachineData → Prop} {ra : BitVec 64} {len0 : Nat}
    (h : PrintCallOk Λ ph lab rS lbl fs Rp Fp ra len0) : PrintCallOkR ph lab rS Rp Fp ra len0 :=
  ⟨h.ok, h.al, h.lo, h.hi, h.lo8, h.hi8, h.off, h.len, h.raPh, h.raAb⟩

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The four pieces' states at `PlacedSE`**: the invariant's controls at
model terms of the output extern or reading no variable (`hext`), the
suspended frames placed at every state of the frame condition (`hfp`, kept
off the region, `FStable`). -/
theorem printArgW_placedSE (hFS : FStable R F) {fr : Scc.Emit.X64.Frame} {B : PBlk} {Jn : AS → Ctl → Prop}
    (hext : ∀ σ c, Jn σ c → c.term ∈ externModelTerms ∨ exprFv c.term = [])
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) :
    PrintArgW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F fr B Jn :=
  ⟨blkW_placedSE hFS hext hfp,
    fun s c ⟨_, _, _, _, _, _, hF, σ0, hJ0, _⟩ =>
      ⟨.of_ext (hext σ0 c hJ0) (hfp s hF).choose_spec.toFramesPlaced, fun _ h => h⟩,
    blkW_placedSE hFS (fun _ c ⟨σ0, _, hJ0, _⟩ => hext σ0 c hJ0) hfp,
    blkW_placedSE hFS (fun _ c ⟨σ0, _, hJ0, _⟩ => hext σ0 c hJ0) hfp⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The four pieces' states at `PlacedSE`, the frames placed knowing the
block** (`printArgW_placedSE` with the suspended frames asked only at the
pieces' states, `hfpJ`, which carry the invariant and the abstract state,
e.g. the caller's frame in its slots). -/
theorem printArgW_placedSE' {fr : Scc.Emit.X64.Frame} {B : PBlk} {Jn : AS → Ctl → Prop}
    (hext : ∀ σ c, Jn σ c → c.term ∈ externModelTerms ∨ exprFv c.term = [])
    (hfpJ : PrintArgW (fun s _ => ∃ B, FramesPlacedInI Λ lbl s fs B) (fun _ _ => False) exe endPc R F fr B Jn) :
    PrintArgW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F fr B Jn :=
  ⟨blkW_placedSE' hext hfpJ.1,
    fun s c h => ⟨.of_ext (let ⟨_, _, _, _, _, _, _, σ0, hJ0, _⟩ := h; hext σ0 c hJ0)
      (hfpJ.2.1 s c h).1.choose_spec.toFramesPlaced, fun _ h => h⟩,
    blkW_placedSE' (fun _ c ⟨σ0, _, hJ0, _⟩ => hext σ0 c hJ0) hfpJ.2.2.1,
    blkW_placedSE' (fun _ c ⟨σ0, _, hJ0, _⟩ => hext σ0 c hJ0) hfpJ.2.2.2⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The frames placed under the frame condition are placed at the four
pieces' states** (`printArgW_placedSE`'s `hfp` gives
`printArgW_placedSE'`'s `hfpJ`). -/
theorem PrintArgW.framesOfF (hFS : FStable R F) {fr : Scc.Emit.X64.Frame} {B : PBlk} {Jn : AS → Ctl → Prop}
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) :
    PrintArgW (fun s _ => ∃ B, FramesPlacedInI Λ lbl s fs B) (fun _ _ => False) exe endPc R F fr B Jn :=
  ⟨BlkW.framesOfF hFS hfp, fun s _ ⟨_, _, _, _, _, _, hF, _⟩ => ⟨hfp s hF, fun _ h => h⟩,
    BlkW.framesOfF hFS hfp, BlkW.framesOfF hFS hfp⟩

/-- **A call of `print`'s argument block and its `call` inside `W2`**, the
write abort's phase from the code predicates off it (`hCd`, `hBl`,
`printArgW_ab`), the states at `PlacedSE` (`printArgW_placedSE`: the
invariant's controls at model terms or reading no variable, `hext`; the
suspended frames placed under the frame condition, `hfp`), `FrOk2` at the
controls (`hJ`). -/
theorem printArgWE_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {B : PBlk}
    (hB : PrintCodeC fr Cd Bl kk pc n b o m cw B) {Jn : AS → Ctl → Prop}
    (hext : ∀ σ c, Jn σ c → c.term ∈ externModelTerms ∨ exprFv c.term = [])
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, Jn σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    PrintArgW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs) K exe endPc R F fr B Jn :=
  printArgW_w2 hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hp (fun _ _ h => (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => (hBl _ _ _ _ h).1) hB (printArgW_ab hI hpr habI hf h1 hR hlo hhi hCd hBl hB)
    (printArgW_placedSE hFS hext hfp) hJ

/-- **`printArgWE_w2` with the frames placed knowing the block**
(`printArgW_placedSE'`: the suspended frames asked only at the pieces'
states, `hfpJ`). -/
theorem printArgWE_w2' {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {B : PBlk}
    (hB : PrintCodeC fr Cd Bl kk pc n b o m cw B) {Jn : AS → Ctl → Prop}
    (hext : ∀ σ c, Jn σ c → c.term ∈ externModelTerms ∨ exprFv c.term = [])
    (hfpJ : PrintArgW (fun s _ => ∃ B, FramesPlacedInI Λ lbl s fs B) (fun _ _ => False) exe endPc R F fr B Jn)
    (hJ : ∀ σ c, Jn σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    PrintArgW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs) K exe endPc R F fr B Jn :=
  printArgW_w2 hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hp (fun _ _ h => (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => (hBl _ _ _ _ h).1) hB (printArgW_ab hI hpr habI hf h1 hR hlo hhi hCd hBl hB)
    (printArgW_placedSE' hext hfpJ) hJ

/-- **A call of `print` of an empty slice inside `W2`** (`PrintWE`) at
`print`'s frames `printFrame x e c1 :: fs`, the source at `print`'s
`ret ()` (`cE`): the argument block by `printArgWE_w2`, `print`'s blocks by
`printW2` at every call state, given `PrintCallOk` there (`hcall`, in
`print`'s region and frame condition); the caller's continuation and frames
free of `ZBad` (`he`, `hfs`), the frames placed along the block (`hfp`). -/
theorem printWE_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {x : String} {e : Expr} {c1 : Ctl} {envR : TermRun.Env} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = ⟨.ret .unit, envR, none⟩)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    (hcall : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      PrintCallOk Λ ph lab rS lbl (printFrame x e c1 :: fs) (pR (-(fr.size : Int) - 8 - 8) R)
        (pF (-(fr.size : Int) - 8 - 8) R F) (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat) :
    PrintWE (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
      endPc R F fr Cd Bl kk pc n b o m cw Jn ⟨.ret .unit, envR, none⟩ := by
  have hfE : FrOk2 ⟨.ret .unit, envR, none⟩ (printFrame x e c1 :: fs) := frOk2_ret he hfs
  intro B hB
  refine PrintBlkW.of (printArgWE_w2 hI hpr habI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hB
    (fun σ c h => .inr (by rw [hJn σ c h]; rfl)) hfp
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfE⟩)) ?_
  intro σC c hc
  have hk := hcall B hB σC c hc
  refine printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit hk.off hk.len hk.raPh hk.raAb
    hp (fun _ c h => h.elim (fun h => h ▸ hfE) False.elim) ?_
  exact PrintAW.ofJF hk.stable fun _ c s h hF =>
    .of_ext (.inr (h.elim (fun h => by rw [h]; rfl) False.elim)) (hk.frames s hF).choose_spec.toFramesPlaced

omit [Kraken.Executable.ValidLayout exe] in
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
word 0 (`printTop0`): the argument block by `printArgWE_w2`, `print`'s
blocks by `printW2` and its system call by `printSvc_w2` at every call
state, given `PrintCallOk` there (`hcall`); the memory side's byte steps
and output words at the system call (`hms`), the write tail there (`hDt`);
the caller's continuation and frames free of `ZBad` (`he`, `hfs`), the
frames placed along the block (`hfp`), the frame 16-aligned (`h16`). -/
theorem printW_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    (hcall : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      PrintCallOk Λ ph lab rS lbl (printFrame x e c1 :: fs) (pR (-(fr.size : Int) - 8 - 8) R)
        (pF (-(fr.size : Int) - 8 - 8) R F) (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    {ms : MemSide isa}
    (hDt : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ (F' : MachineData → Prop), (∀ md, F' md → pF (-(fr.size : Int) - 8 - 8) R F md) → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      Dt s)
    (hms : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      (σC.regs.get64 .rsi).toNat = printN nv mv →
      ∀ (F' : MachineData → Prop), (∀ md, F' md → pF (-(fr.size : Int) - 8 - 8) R F md) → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      (∀ k j, k + j < printN nv mv →
        ms.bo s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC pw wn mv (k + j))
          (fun c0 => ∃ mw b, c0 = nextC pw wn mv (k + j) mw b)) ∧
      ∀ k c1, PrintC pw wn nv mv k c1 → ms.we s c1) :
    PrintW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
      endPc R F ms fr Cd Bl kk pc n b o m cw Jn pw wn nv mv := by
  have hfT := frOk2_printTop0 (fs := fs) (pw := pw) (wn := wn) (mv := mv) (x := x) (c1 := c1) he hfs
  have hfP : ∀ j c, PrintC pw wn nv mv j c ∨ PrintC pw wn nv mv j c → FrOk2 c (printFrame x e c1 :: fs) :=
    fun _ _ h => h.elim (fun h => frOk2_printC h he hfs) fun h => frOk2_printC h he hfs
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hlo' : R.lo ≤ -(fr.size : Int) - 8 := by omega
  intro B hB
  refine ⟨PrintBlkW.of (printArgWE_w2 hI hpr habI hf h1 hR hR8 hlo' hhi hl hh hsub hfit hFO hp hFS hCd hBl hB
    (fun σ c h => by rw [hJn σ c h]; exact printTop_ext (self_mem_printTerms _)) hfp
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfT⟩)) ?_, ?_⟩
  · intro σC c hc
    have hk := hcall B hB σC c hc
    exact printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit hk.off hk.len hk.raPh hk.raAb
      hp hfP (printAW_placedSE hk.stable (fun j c h => h.elim printC_top printC_top) hk.frames)
  · intro σC c hc hN F' hF' s c' hAt
    have hk := hcall B hB σC c hc
    obtain ⟨j, hj, -⟩ := printSys_src hAt hN
    have hlo2 : R.lo ≤ (-(fr.size : Int) - 8 - 8) + -40 := by omega
    have hkb : (-(fr.size : Int) - 8 - 8) + 16 ≤ R.hi := by omega
    have hk16 : (-(fr.size : Int) - 8 - 8) % 16 = 0 := by omega
    have hw := printSvc_w2 (kb := -(fr.size : Int) - 8 - 8) (F' := F') (Λ := Λ) (p := p) (rd := rd) (G := G)
      (ar := ar) (J := J) (lsize := lsize) hI hpr habI hph hR hal hl hh hlo2 hkb hk16 hsub hFO hF' hN hp
      (hfP j c' (.inl hj)) (printSvc_placedSE hAt hN fun s hF => hk.frames s (hF' _ hF))
      (hDt B hB σC c hc F' hF') hAt
    rw [hI.labOk] at hw
    exact ⟨hw, hms B hB σC c hc hN F' hF' s c' hAt⟩

/-- **`printWE_w2` under frame conditions that know the call**
(`PrintWE'`): `print`'s blocks at every `F'` with `pFJ` at the call node,
the suspended frames placed under such `F'` (`hfr`), the rest of
`PrintCallOk` at the call states (`hcall`). -/
theorem printWE_w2' {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {x : String} {e : Expr} {c1 : Ctl} {envR : TermRun.Env} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = ⟨.ret .unit, envR, none⟩)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    (hcall : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
        (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hfr : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) :
    PrintWE' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
      endPc R F fr Cd Bl kk pc n b o m cw Jn ⟨.ret .unit, envR, none⟩ := by
  have hfE : FrOk2 ⟨.ret .unit, envR, none⟩ (printFrame x e c1 :: fs) := frOk2_ret he hfs
  intro B hB
  have hA : PrintArgW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs))
      K exe endPc R F fr B Jn := printArgWE_w2 hI hpr habI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hB
    (fun σ c h => .inr (by rw [hJn σ c h]; rfl)) hfp
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfE⟩)
  refine ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩
  intro σC c hc F' hJF
  have hk := hcall B hB σC c hc
  refine printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit
    (fun md h => hk.off md (hJF.2 md h).1) hk.len hk.raPh hk.raAb
    hp (fun _ c h => h.elim (fun h => h ▸ hfE) False.elim) ?_
  exact PrintAW.ofJF hJF.1 fun _ c' s h hF =>
    .of_ext (.inr (h.elim (fun h => by rw [h]; rfl) False.elim))
      (hfr B hB σC c hc F' hJF s hF).choose_spec.toFramesPlaced

/-- **`printW_w2` under frame conditions that know the call** (`PrintW'`):
`print`'s blocks and its system call at every `F'` with `pFJ` at the call
node, the suspended frames placed under such `F'` (`hfr`), the rest of
`PrintCallOk` at the call states (`hcall`); the write tail (`hDt`) and the
memory side (`hms`) asked under such `F'`. -/
theorem printW_w2' {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    (hcall : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
        (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hfr : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    {ms : MemSide isa}
    (hDt : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ (F' : MachineData → Prop), pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      Dt s)
    (hms : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      (σC.regs.get64 .rsi).toNat = printN nv mv →
      ∀ (F' : MachineData → Prop), pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      (∀ k j, k + j < printN nv mv →
        ms.bo s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC pw wn mv (k + j))
          (fun c0 => ∃ mw b, c0 = nextC pw wn mv (k + j) mw b)) ∧
      ∀ k c1, PrintC pw wn nv mv k c1 → ms.we s c1) :
    PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
      endPc R F ms fr Cd Bl kk pc n b o m cw Jn pw wn nv mv := by
  have hfT := frOk2_printTop0 (fs := fs) (pw := pw) (wn := wn) (mv := mv) (x := x) (c1 := c1) he hfs
  have hfP : ∀ j c, PrintC pw wn nv mv j c ∨ PrintC pw wn nv mv j c → FrOk2 c (printFrame x e c1 :: fs) :=
    fun _ _ h => h.elim (fun h => frOk2_printC h he hfs) fun h => frOk2_printC h he hfs
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hlo' : R.lo ≤ -(fr.size : Int) - 8 := by omega
  intro B hB
  have hA : PrintArgW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs))
      K exe endPc R F fr B Jn := printArgWE_w2 hI hpr habI hf h1 hR hR8 hlo' hhi hl hh hsub hfit hFO hp hFS hCd hBl hB
    (fun σ c h => by rw [hJn σ c h]; exact printTop_ext (self_mem_printTerms _)) hfp
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfT⟩)
  refine ⟨⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩, ?_⟩
  · intro σC c hc F' hJF
    have hk := hcall B hB σC c hc
    exact printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit
      (fun md h => hk.off md (hJF.2 md h).1) hk.len hk.raPh hk.raAb
      hp hfP (printAW_placedSE hJF.1 (fun j c h => h.elim printC_top printC_top) (hfr B hB σC c hc F' hJF))
  · intro σC c hc hN F' hJF s c' hAt
    obtain ⟨j, hj, -⟩ := printSys_src hAt hN
    have hlo2 : R.lo ≤ (-(fr.size : Int) - 8 - 8) + -40 := by omega
    have hkb : (-(fr.size : Int) - 8 - 8) + 16 ≤ R.hi := by omega
    have hk16 : (-(fr.size : Int) - 8 - 8) % 16 = 0 := by omega
    have hw := printSvc_w2 (kb := -(fr.size : Int) - 8 - 8) (F' := F') (Λ := Λ) (p := p) (rd := rd) (G := G)
      (ar := ar) (J := J) (lsize := lsize) hI hpr habI hph hR hal hl hh hlo2 hkb hk16 hsub hFO
      (fun md h => (hJF.2 md h).1) hN hp
      (hfP j c' (.inl hj)) (printSvc_placedSE hAt hN (hfr B hB σC c hc F' hJF))
      (hDt B hB σC c hc F' hJF) hAt
    rw [hI.labOk] at hw
    exact ⟨hw, hms B hB σC c hc hN F' hJF s c' hAt⟩

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.printWE_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printWE_w2

/-- info: 'Spike.Lib.LowerX64.printW_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_w2

/-- info: 'Spike.Lib.LowerX64.printWE_w2'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printWE_w2'

/-- info: 'Spike.Lib.LowerX64.printW_w2'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_w2'

/-- info: 'Spike.Lib.LowerX64.printArgW_placedSE'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printArgW_placedSE'

/-- info: 'Spike.Lib.LowerX64.printArgWE_w2'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printArgWE_w2'
