/-
**The x86-64 setup block's call at its ghost frame condition**
(`mainS_segWSF`, `Spike/Lib/Rt/X64MainSSF.lean`, with the setup block's
interface knowing its frame condition; the twin of
`Spike/Lib/Rt/A64MainSSB.lean`): `call_ndSG` (`Spike/Lib/X64CallS.lean`)
passes the call's ghost frame condition to the callee, so that the setup
function, run in the frame `fr` its call pushes, can record the suspended
`scc_rt_main` below its frames (the stack records' bottom) and resume it
from a landing.

- `SetupCallWSB`: `SetupCallWS` with a premise `Fs F' g fr` on the frame
  condition, the ghost and the frame; `SetupCallWS.toB`,
  `SetupCallWSB.toS`: at `Fs` true it is `SetupCallWS`;
- `SetupGF`: the setup call's `Fs` at `scc_rt_main`: the frame condition is
  `CallGF` at the call node `mainSC` and the entry `uN0`, at a ghost whose
  frame and parameters are the call's;
- `mainSC_segWSB`: `mainSC_segWS` at `SetupCallWSB` at `SetupGF`
  (`call_ndSG`);
- `mainS_segWSFB`, `mainES_segWSFB`, `startS_segWSFB`: `mainS_segWSF`,
  `mainES_segWSF`, `startS_segWSF` over it;
- `MainCallWSFB`, `MainCallWSF.toB`, `MainCallWSFB.toF`: `MainCallWSF` at a
  premise `Fs F' g` on the frame condition and the ghost; `MainGF`: the
  user function's call's `Fs` at `scc_rt_main` (`MainGFr` at `mainSM`);
- `mainS_segWSFBM`: `mainS_segWSFB` with the user function at `MainGF`
  (`call_nd_FWKSFG`).
-/
import Spike.Lib.Rt.X64MainSSF

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The setup interface at a known frame condition -/

/-- **The setup block's interface at depth, at a known frame condition**:
`SetupCallWS` at the frame conditions `F'`, ghosts `g` and frames `fr` in
`Fs`. -/
def SetupCallWSB (W : FragS isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isa)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (PostR : Ctl → Reg64s → Prop) (ra : BitVec 64) (c0 : Ctl)
    (tp : UInt64) (Fs : (MachineData → Prop) → WcG → TermRun.Frame → Prop) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
    FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
    (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
    ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ra → g.tp = tp → CallTo p c0 g.c0 fr → Fs F' g fr →
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
          (uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g)).at [fr])
        ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' (uNxS PostR g)).at [fr])

section B

variable {W : FragS isa} {K : State → State → Prop} {p : Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {PostR : Ctl → Reg64s → Prop} {ra : BitVec 64} {c0 : Ctl}
  {tp : UInt64}

/-- An interface at every frame condition is one at any `Fs`. -/
theorem SetupCallWS.toB (h : SetupCallWS W K p lbl ms exe endPc R F fn Z D ZU PostR ra c0 tp)
    (Fs : (MachineData → Prop) → WcG → TermRun.Frame → Prop) :
    SetupCallWSB W K p lbl ms exe endPc R F fn Z D ZU PostR ra c0 tp Fs :=
  fun F' hR hF hFF g fr hra htp hct _ => h F' hR hF hFF g fr hra htp hct

/-- At `Fs` true, `SetupCallWSB` is `SetupCallWS`. -/
theorem SetupCallWSB.toS (h : SetupCallWSB W K p lbl ms exe endPc R F fn Z D ZU PostR ra c0 tp fun _ _ _ => True) :
    SetupCallWS W K p lbl ms exe endPc R F fn Z D ZU PostR ra c0 tp :=
  fun F' hR hF hFF g fr hra htp hct => h F' hR hF hFF g fr hra htp hct trivial

end B

/-- **The setup call's frame condition at `scc_rt_main`**: `call_ndSG`'s
ghost frame condition `CallGF` at the call node `mainSC` (the region `R`,
the frame condition `F`, the return address at `e0 = 0`, the callee's
region `R.callee (-8 - Z - 8) (-D1) 8`) and the setup function's entry
`uN0` (limit room `ZU1`), at a ghost whose frame is `fr` and whose
parameters are `g'`. -/
def SetupGF (p : Prog) (lab : Label → Int64) (ms : MemSide isa) (R : Region) (F : MachineData → Prop)
    (sc : SetupCode) (D1 : Int) (ZU1 : Int64) (g : MainG) (x0 : BitVec 64) :
    (MachineData → Prop) → WcG → TermRun.Frame → Prop := fun F' g' fr =>
  ∃ G, F' = CallGF p R F (mainSC lab sc g x0) 0 (-D1) 8 (uN0 lab ms F sc.setup ZU1) G ∧
    G.2.2.2.2.1 = fr ∧ G.2.2.2.2.2 = g'

/-- **The user function's interface at a known frame condition**:
`MainCallWSF` at the frame conditions `F'` and ghosts `g` in `Fs`. -/
def MainCallWSFB (W : FragS isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isa)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Pre : Ctl → Reg64s → Prop)
    (Post : Ctl → List TermRun.Frame → BitVec 64 → Prop) (ra : BitVec 64) (tp : UInt64)
    (Fs : (MachineData → Prop) → WcG → Prop) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
    FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
    (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
    ∀ g : WcG, g.ra = ra → g.tp = tp → Fs F' g →
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
          (uNM (_root_.Executable.labels exe).label (ms []) F fn ZU Pre g)).at [])
        (NxF exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' Post g)

section BM

variable {W : FragS isa} {K : State → State → Prop} {p : Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {Pre : Ctl → Reg64s → Prop}
  {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop} {ra : BitVec 64} {tp : UInt64}

/-- An interface at every frame condition is one at any `Fs`. -/
theorem MainCallWSF.toB (h : MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre Post ra tp)
    (Fs : (MachineData → Prop) → WcG → Prop) :
    MainCallWSFB W K p lbl ms exe endPc R F fn Z D ZU Pre Post ra tp Fs :=
  fun F' hR hF hFF g hra htp _ => h F' hR hF hFF g hra htp

/-- At `Fs` true, `MainCallWSFB` is `MainCallWSF`. -/
theorem MainCallWSFB.toF (h : MainCallWSFB W K p lbl ms exe endPc R F fn Z D ZU Pre Post ra tp fun _ _ => True) :
    MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre Post ra tp :=
  fun F' hR hF hFF g hra htp => h F' hR hF hFF g hra htp trivial

end BM

/-- **The user function's call's frame condition at `scc_rt_main`**:
`call_nd_FWKSFG`'s ghost frame condition `MainGFr` at the call node `mainSM`
(the region `R`, the frame condition `F`, the return address at `e0 = 0`,
the callee's region `R.callee (-8 - Z - 8) (-D2) 8`) and the user function's
entry `uNM` (limit room `ZU2`, the marshalled arguments
`SetupArgs PostS sc.sw x0`), at a ghost whose parameters are `g'`. -/
def MainGF (lab : Label → Int64) (ms : MemSide isa) (R : Region) (F : MachineData → Prop)
    (sc : SetupCode) (D2 : Int) (ZU2 : Int64) (PostS : Ctl → Reg64s → Prop) (g : MainG) (x0 : BitVec 64) :
    (MachineData → Prop) → WcG → Prop := fun F' g' =>
  ∃ G, F' = MainGFr R F (mainSM lab sc PostS g x0) 0 (-D2) 8 (uNM lab ms F sc.fn ZU2 (SetupArgs PostS sc.sw x0)) G ∧
    G.2.2.2 = g'

/-! ## The segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- `%rbp`'s offset moved by `8` with `%rsp`. -/
private theorem rbp_shiftSB (r : BitVec 64) (z : Int) :
    r + BitVec.ofInt 64 (-8 - (-8 - z)) = r - 8#64 + BitVec.ofInt 64 (-8 - (-8 - z - 8)) := by
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  show r + y = r - 8#64 + (y + 8#64)
  bv_omega

/-- `%rbp` back at the saved `%rbp` after a call's return: the callee
restored `%rbp` and popped the return address. -/
private theorem rbp_retSB {rbpC rspC rbpR rspR : BitVec 64} (z : Int)
    (hb : rbpC = rspC + BitVec.ofInt 64 (-8 - (-8 - z - 8))) (hbR : rbpR = rbpC) (hspR : rspR = rspC + 8#64) :
    rbpR = rspR + BitVec.ofInt 64 (-8 - (-8 - z)) := by
  rw [hbR, hspR, hb]
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  bv_omega

omit [Kraken.Executable.ValidLayout exe] in
/-- **`call setup` as a source call at its ghost frame condition, at depth**
(`mainSC_segWS` at `SetupCallWSB` at `SetupGF`, by `call_ndSG`). -/
theorem mainSC_segWSB {W : FragS isa} {K : State → State → Prop} {sc : SetupCode} {D1 : Int} (hD10 : 0 ≤ D1)
    (hD18 : D1 % 8 = 0) (hZ8 : sc.Z.toInt % 8 = 0) (hZ : 8 ≤ sc.Z.toInt) {ZU1 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} (hF : FStable R F) (hR : R.OK)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hhi : 0 ≤ R.hi) (g : MainG) (x0 : BitVec 64)
    (hlimS : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU1.toBitVec))
    (hS : SetupCallWSB W K p lbl ms exe endPc R F sc.setup sc.Z D1 ZU1 PostR
      ((_root_.Executable.labels exe).label sc.sp0).toBitVec g.c0 g.tp
      (SetupGF p (_root_.Executable.labels exe).label (ms []) R F sc D1 ZU1 g x0))
    (hcall : ∃ cE fr, CallTo p g.c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p g.c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ s c, At exe endPc R F (mainSC (_root_.Executable.labels exe).label sc g x0) s c → W s c []) :
    SegWS W K p lbl ms ((At exe endPc R F (mainSC (_root_.Executable.labels exe).label sc g x0)).at [])
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g x0)).at []) := by
  let lab := (_root_.Executable.labels exe).label
  refine seg_oneWS (call_ndSG (KC := False) (e0 := 0) (lo' := -D1) (hi' := 8) (M := fun _ => True)
    (Ne := uN0 lab (ms []) F sc.setup ZU1) (Ex := fun g _ => uNxS PostR g)
    hR hF (by show R.lo ≤ -8 - sc.Z.toInt - 8 - 0 + -D1; omega) (by omega)
    (by show -8 - sc.Z.toInt - 8 - 0 < R.hi; omega) (by show -8 - sc.Z.toInt - 8 - 0 + 8 ≤ R.hi; omega)
    (by show (-8 - sc.Z.toInt - 8 - 0) % 8 = 0; omega) (by omega) (by decide)
    (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h) hWC
    (fun R' F' hR' _ _ hF' _ hFF hR'e hcc g' fr hGF hg' _ => by
      subst hR'e
      obtain ⟨σC, c, cE, ⟨⟨hc, -, htp⟩, hsl, -, -⟩, hCT, ⟨⟨hc', -, hra, -, htp'⟩, -⟩⟩ := hg'
      subst hc hc'
      have hr : g'.ra = (lab sc.sp0).toBitVec := by
        rw [← hra, ← hsl]; show σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0) = _; congr 1; omega
      exact (hS F' hR' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' fr hr (htp'.symm.trans htp) hCT hGF).mono_post
        fun _ _ _ h => ⟨⟨(), h.1, trivial⟩, h.2⟩)
    (fun _ => rfl) ?_ ?_)
  · rintro σC c ⟨⟨rfl, hsp, htp⟩, -, -, -⟩
    obtain ⟨cE, fr, hCT⟩ := hcall
    refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, cE⟩, cE, fr,
      hCT, rfl, ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
    show LimOk (ms []) F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - ZU1.toBitVec)
    rw [hsp]; exact hlimS
  · rintro g' x σC c cE fr σx c' σR ⟨⟨rfl, hspC, htpC⟩, hsl, hb, hx0⟩ hCT ⟨⟨hc, hfp, hra, hsp, htp'⟩, -⟩
      ⟨hP, hb', hsp', htpx⟩ hregs - - hslot
    obtain ⟨c'', hrun, hP''⟩ := hPS cE fr c' σx.regs hCT hP
    refine ⟨c'', hrun, .inl ⟨(), ?_, by simp [SO.le, mainS0, mainSC, uNxS], ⟨?_, ?_, ?_, ?_⟩, ?_⟩⟩
    · show lab sc.sp0 = Int64.ofBitVec g'.ra
      rw [← hra]
      show lab _ = Int64.ofBitVec (σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0))
      rw [show -8 - sc.Z.toInt - 8 - 0 + 0 = -8 - sc.Z.toInt - 8 by omega, hsl, int64_ofBitVec_toBitVec]
    · rw [hregs]; exact hP''
    · rw [hregs, hsp', ← hsp]
      show σC.regs.rsp.toBitVec + 8#64 = _
      rw [hspC]; exact BitVec.sub_add_cancel _ _
    · rw [hregs, htpx, ← htp']; exact htpC
    · rw [hslot (-16) ⟨by omega, by omega, by omega⟩
        (by simp only [Region.Off, Region.callee, mainSC]; omega)]
      exact hx0
    · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt))
      rw [hregs]
      simp only [Reg64s.get64] at hb ⊢
      exact rbp_retSB sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))

/-- **`mainS_segWSF` with the setup block at its ghost frame condition**
(`SetupCallWSB` at `SetupGF`; the setup block's call by
`mainSC_segWSB`). -/
theorem mainS_segWSFB {W : FragS isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) {sc : SetupCode} (hin : mainSIn cells sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hlo2 : R.lo ≤ -8 - sc.Z.toInt - 8 - D2) (hhi : 0 ≤ R.hi)
    (g : MainG) (x0 : BitVec 64)
    (hlimM : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hS : SetupCallWSB W K p lbl ms exe endPc R F sc.setup sc.Z D1 ZU1 PostR
      ((_root_.Executable.labels exe).label sc.sp0).toBitVec g.c0 g.tp
      (SetupGF p (_root_.Executable.labels exe).label (ms []) R F sc D1 ZU1 g x0))
    (hcall : ∃ cE fr, CallTo p g.c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p g.c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ s c, At exe endPc R F (mainSC (_root_.Executable.labels exe).label sc g x0) s c → W s c [])
    (hU : MainCallWSF W K p lbl ms exe endPc R F sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec g.tp)
    (hexit : ∀ s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : MainSW (nilW W) K exe endPc R F (ms []) sc PostS (fun c v => Post c [] v) g x0)
    (hWx : ∀ fs, XExitW (fun s c => W s c fs) K exe endPc R F
      (mainSRR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) (-8 - sc.Z.toInt) (-8) sc.k 4 4 5)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((At exe endPc R F (mainSN0 (_root_.Executable.labels exe).label g x0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainSIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hpro, hb0⟩, hg0⟩, hb1⟩, hg1⟩, hex⟩ := hin
  have esp0 := label_labelGapB hp hg0
  have esp1 := label_labelGapB hp hg1
  have hloZ : R.lo ≤ -8 - sc.Z.toInt := by omega
  -- the prologue and `call setup`
  have h1 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainSN0 lab g x0))
      (At exe endPc R F (mainSC lab sc g x0)) := by
    refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainS1 lab sc g x0) (by omega) hF hR hloZ hhi ?_ rfl
      (by simp [SO.le, lk, mainS1]) hW.pro ?_) ?_
    · -- the TCB's store
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      show Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + (-8 : Int64).toInt) = true
      rw [show (-8 : Int64).toInt = -8 by decide]
      simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega
    · -- the prologue
      rintro σ c ⟨⟨rfl, hsp, htp⟩, hx⟩
      have ha : σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA g.tp := by rw [limA, htp]
      rw [ha]
      refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr hs => ⟨rfl, ?_, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlimM.room v hv
      · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
      · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
      · rw [hs, hr]
        simp [xStSlots, xS1, Spike.Lib.upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hx]
    · -- `call setup`
      refine (seg_oneW (seg_ndW (n := mainS1R lab sc g x0) (lo := -8 - sc.Z.toInt - 8) (hi := 0)
        (by simp [callB]) (okBlk_callB _ (by simp [Spike.Lib.offOk, mainS1R]; omega)) hF hR (by omega) hhi
        (code_field hp hend hb0 (ofNat_zero' _)) hW.call0
          fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
        fun _ _ h => Ret0.At.rbp_get rfl h
      · dsimp only [mainS1R, mainSC]; rw [callB_run]
      · dsimp only [mainS1R, mainSC]; rw [callB_run]; simp [SO.le]
      · dsimp only [mainS1R, mainS1, mainSC] at hJ ⊢; rw [callB_run]
        obtain ⟨⟨rfl, hsp, htp, hsl⟩, hb⟩ := hJ
        refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · simp [Reg64s.set64, hsp]
        · simp [Reg64s.set64, htp]
        · simp only [Spike.Lib.upd_apply, ↓reduceIte]
          rw [show lab sc.sp0 = _ from esp0]; rfl
        · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]
          exact rbp_shiftSB _ _
        · dsimp only
          simp only [Spike.Lib.upd_apply,
            show ((-16 : Int) = -8 - sc.Z.toInt - 8) = False from eq_false (by omega), ↓reduceIte]
          exact hsl
  -- the setup block's call
  have h2 := mainSC_segWSB (lbl := lbl) (ms := ms) hD10 hD18 hZ8 (by omega) hF hR hlo1 hhi g x0 hlimS hS hcall hPS hWC
  -- the marshalling block and `call fn`
  have h3 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainS0 lab sc PostS g x0))
      (At exe endPc R F (mainSM lab sc PostS g x0)) := by
    refine (seg_oneW (seg_ndW (n := mainS0R lab sc PostS g x0) (lo := -8 - sc.Z.toInt - 8) (hi := 0)
      (by simp [marshal, callB])
      (okBlk_marshal hsw _ (fun i hi => by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)) hF hR (by omega) hhi
      (code_field hp hend hb1 (ofNat_zero' _)) hW.sp0
        fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp h fun _ _ h => h.2
    · dsimp only [mainS0R, mainSM]; rw [marshal_run]
    · dsimp only [mainS0R, mainSM]; rw [marshal_run]; simp [SO.le]
    · dsimp only [mainS0R, mainS0, mainSM] at hJ ⊢; rw [marshal_run]
      obtain ⟨⟨hP, hsp, htp, hsl⟩, hb⟩ := hJ
      obtain ⟨hr, hx, hrbp, hfs⟩ := marshal_regs hsw σ.slot σ.regs
      have hrsp := xLdRegs_get_of_not_mem (xStSlots σ.regs (mshSt sc.sw) σ.slot) (mshLd sc.sw) σ.regs
        (q := .rsp) fun p hp => (mshLd_reg hp).1
      refine ⟨⟨⟨σ.regs, hP, fun i hi => ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
      · rw [Reg64s.get64_set64_ne _ (argXs_getD_ne i).1]; exact hr i hi
      · rw [Reg64s.get64_set64_ne _ (argXs_getD_ne _).1, hx]; exact hsl
      · show (Reg64s.set64 _ .rsp _).get64 .rsp = _
        rw [Reg64s.get64_set64_self]
        simp only [Reg64s.get64] at hrsp
        rw [hrsp, hsp]
      · simp only [Reg64s.set64]; rw [hfs]; exact htp
      · simp only [Spike.Lib.upd_apply, ↓reduceIte]
        rw [pc_marshal]; exact congrArg Int64.toBitVec esp1.symm
      · rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self, hrbp, hb]
        simp only [Reg64s.get64] at hrsp ⊢
        rw [hrsp]
        exact rbp_shiftSB _ _
  -- the user function's call
  have h4 : SegWS W K p lbl ms ((At exe endPc R F (mainSM lab sc PostS g x0)).at [])
      (fun s c fs => At exe endPc R F (mainSR lab sc (fun c v => Post c fs v)) s c) := by
    refine (call_nd_FWKSF (KC := False) (e0 := 0) (lo' := -D2) (hi' := 8) (M := fun _ => True)
      (N := fun fs (_ : Unit) => mainSR lab sc (fun c v => Post c fs v)) (E := fun _ (e : Empty) => e.elim)
      (Ne := uNM lab (ms []) F sc.fn ZU2 (SetupArgs PostS sc.sw x0))
      (Ex := fun g fs (_ : Unit) => uNx (fun c v => Post c fs v) g)
      hR hF (by show R.lo ≤ -8 - sc.Z.toInt - 8 - 0 + -D2; omega) (by omega)
      (by show -8 - sc.Z.toInt - 8 - 0 < R.hi; omega) (by show -8 - sc.Z.toInt - 8 - 0 + 8 ≤ R.hi; omega)
      (by show (-8 - sc.Z.toInt - 8 - 0) % 8 = 0; omega) (by omega) (by decide)
      (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨-, -, htp⟩, hsl, -⟩, ⟨⟨-, -, hra, -, htp'⟩, -⟩⟩ := hg'
        have hr : g'.ra = (lab sc.sp1).toBitVec := by
          rw [← hra, ← hsl]; show σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0) = _; congr 1; omega
        exact (hU F' hR' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' hr
          (htp'.symm.trans htp)).mono_post fun _ _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_).mono_post fun _ _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    · rintro σC c ⟨⟨hA, hsp, htp⟩, -, -⟩
      refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, c⟩, rfl,
        ⟨hA, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk (ms []) F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - ZU2.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' fs' x σC c σx c' σR ⟨-, hsl, hb⟩ ⟨⟨-, hfp, hra, hsp, -⟩, -⟩ ⟨hP, hb', hsp'⟩ hregs - - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainSR, mainSM, uNx], by rw [hregs]; exact hP, ?_⟩
      · show lab sc.sp1 = Int64.ofBitVec g'.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0))
        rw [show -8 - sc.Z.toInt - 8 - 0 + 0 = -8 - sc.Z.toInt - 8 by omega, hsl, int64_ofBitVec_toBitVec]
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt))
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        exact rbp_retSB sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))
  -- the exit: `exit_group(v)` after the source's frame run back to depth 0, from the frames `fs` the
  -- source has at the return
  have h5 : SegWS W K p lbl ms (fun s c fs => At exe endPc R F (mainSR lab sc (fun c v => Post c fs v)) s c)
      (fun _ _ _ => False) := by
    simp only [exitIn, Bool.and_eq_true] at hex
    refine (SegWS.exists_pre (P := fun fs => (At exe endPc R F (mainSRR lab sc (fun c v => Post c fs v))).at fs)
      fun fs => ?_).mono_pre fun _ _ fs h => ⟨fs, At.rbp h fun _ _ h => h.2, rfl⟩
    refine xExitTail_segWSF (lo := -8 - sc.Z.toInt) (hi := 0) (n := mainSRR lab sc (fun c v => Post c fs v)) rfl hK
      hF hR hloZ hhi hk (code_field hp hend hex.1 (ofNat_zero' _))
      (code_field hp hend hex.2 (by rw [ofNat_add', ofNat_add']; rfl)) (hWx fs).w0 (hWx fs).w1
      fun s c σ0 hJ0 hs => ?_
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hs
    exact exitGroup_of_mainExitFA
      (hexit s c fs _ hJ0.1 ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.rdi.toBitVec = _; rw [hx]⟩)
  exact (SegWS.liftS [] h1 fun _ _ h => h).seq (h2.seq ((SegWS.liftS [] h3 fun _ _ h => h).seq
    (h4.seq (h5.mono_post fun _ _ _ h => h.elim))))

/-- **`mainS_segWSFB` with the user function at its ghost frame condition**
(`MainCallWSFB` at `MainGF`; the user function's call by
`call_nd_FWKSFG`). -/
theorem mainS_segWSFBM {W : FragS isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) {sc : SetupCode} (hin : mainSIn cells sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hlo2 : R.lo ≤ -8 - sc.Z.toInt - 8 - D2) (hhi : 0 ≤ R.hi)
    (g : MainG) (x0 : BitVec 64)
    (hlimM : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hS : SetupCallWSB W K p lbl ms exe endPc R F sc.setup sc.Z D1 ZU1 PostR
      ((_root_.Executable.labels exe).label sc.sp0).toBitVec g.c0 g.tp
      (SetupGF p (_root_.Executable.labels exe).label (ms []) R F sc D1 ZU1 g x0))
    (hcall : ∃ cE fr, CallTo p g.c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p g.c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ s c, At exe endPc R F (mainSC (_root_.Executable.labels exe).label sc g x0) s c → W s c [])
    (hU : MainCallWSFB W K p lbl ms exe endPc R F sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec g.tp
      (MainGF (_root_.Executable.labels exe).label (ms []) R F sc D2 ZU2 PostS g x0))
    (hexit : ∀ s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : MainSW (nilW W) K exe endPc R F (ms []) sc PostS (fun c v => Post c [] v) g x0)
    (hWx : ∀ fs, XExitW (fun s c => W s c fs) K exe endPc R F
      (mainSRR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) (-8 - sc.Z.toInt) (-8) sc.k 4 4 5)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((At exe endPc R F (mainSN0 (_root_.Executable.labels exe).label g x0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainSIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hpro, hb0⟩, hg0⟩, hb1⟩, hg1⟩, hex⟩ := hin
  have esp0 := label_labelGapB hp hg0
  have esp1 := label_labelGapB hp hg1
  have hloZ : R.lo ≤ -8 - sc.Z.toInt := by omega
  -- the prologue and `call setup`
  have h1 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainSN0 lab g x0))
      (At exe endPc R F (mainSC lab sc g x0)) := by
    refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainS1 lab sc g x0) (by omega) hF hR hloZ hhi ?_ rfl
      (by simp [SO.le, lk, mainS1]) hW.pro ?_) ?_
    · -- the TCB's store
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      show Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + (-8 : Int64).toInt) = true
      rw [show (-8 : Int64).toInt = -8 by decide]
      simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega
    · -- the prologue
      rintro σ c ⟨⟨rfl, hsp, htp⟩, hx⟩
      have ha : σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA g.tp := by rw [limA, htp]
      rw [ha]
      refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr hs => ⟨rfl, ?_, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlimM.room v hv
      · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
      · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
      · rw [hs, hr]
        simp [xStSlots, xS1, Spike.Lib.upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hx]
    · -- `call setup`
      refine (seg_oneW (seg_ndW (n := mainS1R lab sc g x0) (lo := -8 - sc.Z.toInt - 8) (hi := 0)
        (by simp [callB]) (okBlk_callB _ (by simp [Spike.Lib.offOk, mainS1R]; omega)) hF hR (by omega) hhi
        (code_field hp hend hb0 (ofNat_zero' _)) hW.call0
          fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
        fun _ _ h => Ret0.At.rbp_get rfl h
      · dsimp only [mainS1R, mainSC]; rw [callB_run]
      · dsimp only [mainS1R, mainSC]; rw [callB_run]; simp [SO.le]
      · dsimp only [mainS1R, mainS1, mainSC] at hJ ⊢; rw [callB_run]
        obtain ⟨⟨rfl, hsp, htp, hsl⟩, hb⟩ := hJ
        refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · simp [Reg64s.set64, hsp]
        · simp [Reg64s.set64, htp]
        · simp only [Spike.Lib.upd_apply, ↓reduceIte]
          rw [show lab sc.sp0 = _ from esp0]; rfl
        · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]
          exact rbp_shiftSB _ _
        · dsimp only
          simp only [Spike.Lib.upd_apply,
            show ((-16 : Int) = -8 - sc.Z.toInt - 8) = False from eq_false (by omega), ↓reduceIte]
          exact hsl
  -- the setup block's call
  have h2 := mainSC_segWSB (lbl := lbl) (ms := ms) hD10 hD18 hZ8 (by omega) hF hR hlo1 hhi g x0 hlimS hS hcall hPS hWC
  -- the marshalling block and `call fn`
  have h3 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainS0 lab sc PostS g x0))
      (At exe endPc R F (mainSM lab sc PostS g x0)) := by
    refine (seg_oneW (seg_ndW (n := mainS0R lab sc PostS g x0) (lo := -8 - sc.Z.toInt - 8) (hi := 0)
      (by simp [marshal, callB])
      (okBlk_marshal hsw _ (fun i hi => by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)) hF hR (by omega) hhi
      (code_field hp hend hb1 (ofNat_zero' _)) hW.sp0
        fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp h fun _ _ h => h.2
    · dsimp only [mainS0R, mainSM]; rw [marshal_run]
    · dsimp only [mainS0R, mainSM]; rw [marshal_run]; simp [SO.le]
    · dsimp only [mainS0R, mainS0, mainSM] at hJ ⊢; rw [marshal_run]
      obtain ⟨⟨hP, hsp, htp, hsl⟩, hb⟩ := hJ
      obtain ⟨hr, hx, hrbp, hfs⟩ := marshal_regs hsw σ.slot σ.regs
      have hrsp := xLdRegs_get_of_not_mem (xStSlots σ.regs (mshSt sc.sw) σ.slot) (mshLd sc.sw) σ.regs
        (q := .rsp) fun p hp => (mshLd_reg hp).1
      refine ⟨⟨⟨σ.regs, hP, fun i hi => ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
      · rw [Reg64s.get64_set64_ne _ (argXs_getD_ne i).1]; exact hr i hi
      · rw [Reg64s.get64_set64_ne _ (argXs_getD_ne _).1, hx]; exact hsl
      · show (Reg64s.set64 _ .rsp _).get64 .rsp = _
        rw [Reg64s.get64_set64_self]
        simp only [Reg64s.get64] at hrsp
        rw [hrsp, hsp]
      · simp only [Reg64s.set64]; rw [hfs]; exact htp
      · simp only [Spike.Lib.upd_apply, ↓reduceIte]
        rw [pc_marshal]; exact congrArg Int64.toBitVec esp1.symm
      · rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self, hrbp, hb]
        simp only [Reg64s.get64] at hrsp ⊢
        rw [hrsp]
        exact rbp_shiftSB _ _
  -- the user function's call, at its ghost frame condition
  have h4 : SegWS W K p lbl ms ((At exe endPc R F (mainSM lab sc PostS g x0)).at [])
      (fun s c fs => At exe endPc R F (mainSR lab sc (fun c v => Post c fs v)) s c) := by
    refine (call_nd_FWKSFG (KC := False) (e0 := 0) (lo' := -D2) (hi' := 8) (M := fun _ => True)
      (N := fun fs (_ : Unit) => mainSR lab sc (fun c v => Post c fs v)) (E := fun _ (e : Empty) => e.elim)
      (Ne := uNM lab (ms []) F sc.fn ZU2 (SetupArgs PostS sc.sw x0))
      (Ex := fun g fs (_ : Unit) => uNx (fun c v => Post c fs v) g)
      hR hF (by show R.lo ≤ -8 - sc.Z.toInt - 8 - 0 + -D2; omega) (by omega)
      (by show -8 - sc.Z.toInt - 8 - 0 < R.hi; omega) (by show -8 - sc.Z.toInt - 8 - 0 + 8 ≤ R.hi; omega)
      (by show (-8 - sc.Z.toInt - 8 - 0) % 8 = 0; omega) (by omega) (by decide)
      (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' _ _ hF' _ hFF hR'e hcc g' hGF hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨-, -, htp⟩, hsl, -⟩, ⟨⟨-, -, hra, -, htp'⟩, -⟩⟩ := hg'
        have hr : g'.ra = (lab sc.sp1).toBitVec := by
          rw [← hra, ← hsl]; show σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0) = _; congr 1; omega
        exact (hU F' hR' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' hr
          (htp'.symm.trans htp) hGF).mono_post fun _ _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_).mono_post fun _ _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    · rintro σC c ⟨⟨hA, hsp, htp⟩, -, -⟩
      refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, c⟩, rfl,
        ⟨hA, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk (ms []) F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - ZU2.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' fs' x σC c σx c' σR ⟨-, hsl, hb⟩ ⟨⟨-, hfp, hra, hsp, -⟩, -⟩ ⟨hP, hb', hsp'⟩ hregs - - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainSR, mainSM, uNx], by rw [hregs]; exact hP, ?_⟩
      · show lab sc.sp1 = Int64.ofBitVec g'.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0))
        rw [show -8 - sc.Z.toInt - 8 - 0 + 0 = -8 - sc.Z.toInt - 8 by omega, hsl, int64_ofBitVec_toBitVec]
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt))
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        exact rbp_retSB sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))
  -- the exit: `exit_group(v)` after the source's frame run back to depth 0, from the frames `fs` the
  -- source has at the return
  have h5 : SegWS W K p lbl ms (fun s c fs => At exe endPc R F (mainSR lab sc (fun c v => Post c fs v)) s c)
      (fun _ _ _ => False) := by
    simp only [exitIn, Bool.and_eq_true] at hex
    refine (SegWS.exists_pre (P := fun fs => (At exe endPc R F (mainSRR lab sc (fun c v => Post c fs v))).at fs)
      fun fs => ?_).mono_pre fun _ _ fs h => ⟨fs, At.rbp h fun _ _ h => h.2, rfl⟩
    refine xExitTail_segWSF (lo := -8 - sc.Z.toInt) (hi := 0) (n := mainSRR lab sc (fun c v => Post c fs v)) rfl hK
      hF hR hloZ hhi hk (code_field hp hend hex.1 (ofNat_zero' _))
      (code_field hp hend hex.2 (by rw [ofNat_add', ofNat_add']; rfl)) (hWx fs).w0 (hWx fs).w1
      fun s c σ0 hJ0 hs => ?_
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hs
    exact exitGroup_of_mainExitFA
      (hexit s c fs _ hJ0.1 ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.rdi.toBitVec = _; rw [hx]⟩)
  exact (SegWS.liftS [] h1 fun _ _ h => h).seq (h2.seq ((SegWS.liftS [] h3 fun _ _ h => h).seq
    (h4.seq (h5.mono_post fun _ _ _ h => h.elim))))

/-- **`mainES_segWSF` with the setup block at its ghost frame condition**
(`mainS_segWSFB` at the new region). -/
theorem mainES_segWSFB {W : FragS isa} {K : State → State → Prop} {rS : Scc.Sem.Range} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {sc : SetupCode} (hin : mainSIn cells sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop} {L : Int}
    (hL1 : 8 + 8 + sc.Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + sc.Z.toInt + 8 + D2 ≤ L) (hL8 : L % 8 = 0)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ (limA (tpOf tcb)) (top - 8#64 - 8#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ (limA (tpOf tcb)) (top - 8#64 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ (limA (tpOf tcb)) (top - 8#64 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWSB W K p lbl ms exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.setup sc.Z D1 ZU1 PostR ((_root_.Executable.labels exe).label sc.sp0).toBitVec c0 (tpOf tcb)
      (SetupGF p (_root_.Executable.labels exe).label (ms []) ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
        sc D1 ZU1 ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec))
    (hcall : ∃ cE fr, CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, At exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSC (_root_.Executable.labels exe).label sc ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec) s c →
      W s c [])
    (hU : ∀ v, MainCallWSF W K p lbl ms exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (tpOf tcb).toBitVec) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec (tpOf tcb))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainSW (nilW W) K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (ms [])
      sc PostS (fun c v => Post c [] v) ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec)
    (hWx : ∀ v fs, XExitW (fun s c => W s c fs) K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) (-8 - sc.Z.toInt) (-8) sc.k 4 4 5)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((MainE exe endPc rS tcb top c0 L).at []) Q := by
  refine (SegWS.exists_pre (P := fun g : {v : BitVec 64 // (swR v (-L) 0).OK} =>
      (At exe endPc ((swR g.1 (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => swFSL L rS top (limA (tpOf tcb)) g.1 m ∧ CallerCells (swR g.1 (-L) 0) (-8 - 0) (8 - L) 8 m)
        (mainSN0 (_root_.Executable.labels exe).label ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec)).at [])
    fun g => ?_).mono_pre fun _ _ _ ⟨⟨v, h1, hA⟩, e⟩ => ⟨⟨v, h1⟩, hA, e⟩
  obtain ⟨v, hv⟩ := g
  obtain ⟨hR, hF⟩ := mainE_ok (rS := rS) (tcb := tcb) (top := top) (by omega) hL8 hv hfit hout hfitS
  have hun : ∀ m, (swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
      Mem.loadInt m.dmem (limA (tpOf tcb)) 8 = none := fun _ h => h.1.1.2
  exact mainS_segWSFB hp hend hin hZ8 hsw hZw hk hD10 hD18 hD20 hD28 hK hF hR
    (show 8 - L ≤ -8 - sc.Z.toInt - 8 - D1 by omega) (show 8 - L ≤ -8 - sc.Z.toInt - 8 - D2 by omega)
    (show (0 : Int) ≤ 8 by decide) ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec
    ⟨hlimM.rt, hlimM.mp, hun, hlimM.room⟩ ⟨hlimS.rt, hlimS.mp, hun, hlimS.room⟩
    ⟨hlimU.rt, hlimU.mp, hun, hlimU.room⟩ (hS v) hcall hPS (hWC v) (hU v)
    (fun s c fs x hP hAt => hexit _ _ s c fs x hP hAt) (hW v)
    (hWx v)

/-- **`startS_segWSF` with the setup block at its ghost frame condition**
(`startE_segWS` then `mainES_segWSFB`). -/
theorem startS_segWSFB {W : FragS isa} {rS : Scc.Sem.Range} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {xr : Label} (hc : RtCodeInTi cells xr) {L : Int}
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk (ms []) F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hk0 : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hWE : StartEW (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F rS n0 k0 c0 L xr)
    {sc : SetupCode} (hin : mainSIn cells sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hL1 : 8 + 8 + sc.Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + sc.Z.toInt + 8 + D2 ≤ L) (hL8 : L % 8 = 0)
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec -
        8#64 - 8#64 - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec -
        8#64 - 8#64 - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWSB W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.setup sc.Z D1 ZU1 PostR ((_root_.Executable.labels exe).label sc.sp0).toBitVec c0
      (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))
      (SetupGF p (_root_.Executable.labels exe).label (ms []) ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
            (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m ∧
          CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
        sc D1 ZU1 ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64,
          tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
        (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)).toBitVec))
    (hcall : ∃ cE fr, CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, At exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSC (_root_.Executable.labels exe).label sc ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 -
        8#64, tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
        (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)).toBitVec) s c → W s c [])
    (hU : ∀ v, MainCallWSF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)).toBitVec)
      Post ((_root_.Executable.labels exe).label sc.sp1).toBitVec
      (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainSW (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (ms [])
      sc PostS (fun c v => Post c [] v) ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64,
        tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
      (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)).toBitVec)
    (hWx : ∀ v fs, XExitW (fun s c => W s c fs) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS)
      exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) (-8 - sc.Z.toInt) (-8) sc.k 4 4 5)
    {Q : FragS isa} :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0)).at []) Q :=
  (startE_segWS hp hend hc (by omega) hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk0 hfld htk hok hsub hfit hout
    hun hRS hfitS houtS hFt hWE).seq
    (mainES_segWSFB hp hend hin hZ8 hsw hZw hk hD10 hD18 hD20 hD28 hL1 hL2 hL8 hK _ _ c0 hfitS hfit hout hlimM hlimS
      hlimU hS hcall hPS hWC hU hexit hW hWx)

end Proof

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.SetupCallWSB.toS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms SetupCallWSB.toS

/-- info: 'Spike.Lib.X64.Rt.mainSC_segWSB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSC_segWSB

/-- info: 'Spike.Lib.X64.Rt.mainS_segWSFB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainS_segWSFB

/-- info: 'Spike.Lib.X64.Rt.mainS_segWSFBM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainS_segWSFBM

/-- info: 'Spike.Lib.X64.Rt.mainES_segWSFB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainES_segWSFB

/-- info: 'Spike.Lib.X64.Rt.startS_segWSFB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startS_segWSFB

end Spike.Lib.X64.Rt
