/-
**The setup function's bottom frame at any key memory side** (x86-64):
`setupBot_seg` / `setupBot_segK` (`Spike/Lib/LowerX64/SetupBot.lean`) with
the key's memory side `ms0` (inside `CallGF`'s entry `uN0`) free of the
segment's `ms`: the key is the one the setup call's segment recorded (at
its placement and invariant family), the segment the one a landing runs at
(an extended placement, any family). The return reads only the key's frame
condition, not the memory side's facts. The twin of
`Spike/Lib/LowerA64/SetupBotM.lean`.

- `setupBot_segM`, `setupBot_segKM`: `setupBot_seg`, `setupBot_segK` at a
  key memory side `ms0`;
- `setupBot_exitStkM`: the exits `ExitStk` at a `SetupBot` key at `ms0`
  (`H1OpenXW.hbot`'s shape), the frame pop at every return type;
  `setupBot_exitStkMT`: at the key's block's return type only.
-/
import Spike.Lib.LowerX64.SetupBot
import Spike.Lib.LowerX64.ResumeStk2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (SetupCode mainSC mainS0 uN0 uNxS)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- `rbp` at the return to `mainS0` (a copy of `SetupBot.lean`'s private
`rbp_retBot`). -/
private theorem rbp_retBotM {rbpC rspC rbpR rspR : BitVec 64} (z : Int)
    (hb : rbpC = rspC + BitVec.ofInt 64 (-8 - (-8 - z - 8))) (hbR : rbpR = rbpC) (hspR : rspR = rspC + 8#64) :
    rbpR = rspR + BitVec.ofInt 64 (-8 - (-8 - z)) := by
  rw [hbR, hspR, hb]
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  bv_omega

/-- **`setupBot_seg` at a key memory side `ms0`**: the same proof, the
entry `uN0` at `ms0` rather than the segment's `ms []`. -/
theorem setupBot_segM {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {sc : SetupCode}
    {ms0 : MemSide isa}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (hZ8 : sc.Z.toInt % 8 = 0) (hZ : 8 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {ty : Ty} {G : MachineData × AS × Ctl × Ctl × TermRun.Frame × WcG}
    {tp : UInt64} {c0 : Ctl} {Ab : FragS isa}
    (hbase : (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8).base = G.2.2.2.2.2.sp) (htp : tp = G.2.2.2.2.2.tp)
    (hPS : ∀ cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hW : ∀ s c, ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8))
      (CallGF p R F (mainSC (_root_.Executable.labels exe).label sc g0 x0) 0 (-D1) 8
        (uN0 (_root_.Executable.labels exe).label ms0 F sc.setup ZU1) G)
      G.2.2.2.2.2.fp G.2.2.2.2.2.ra tp c0 [G.2.2.2.2.1] ty (fun _ _ _ => False) s c [G.2.2.2.2.1] →
      W s c [G.2.2.2.2.1])
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8))
      (CallGF p R F (mainSC (_root_.Executable.labels exe).label sc g0 x0) 0 (-D1) 8
        (uN0 (_root_.Executable.labels exe).label ms0 F sc.setup ZU1) G)
      G.2.2.2.2.2.fp G.2.2.2.2.2.ra tp c0 [G.2.2.2.2.1] ty Ab) Q := by
  let lab := (_root_.Executable.labels exe).label
  let RC := R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8
  let FC := CallGF p R F (mainSC lab sc g0 x0) 0 (-D1) 8 (uN0 lab ms0 F sc.setup ZU1) G
  let P1 : FragS isa := fun s c fs => fs = [G.2.2.2.2.1] ∧ ∃ c0', FrameRunM p (c0, [G.2.2.2.2.1])
    (c0', [G.2.2.2.2.1]) ∧ At exe endPc (rbR RC) FC ((retNSL p lbl G.2.2.2.2.2.fp G.2.2.2.2.2.ra c0' ty).withTp tp) s c
  suffices h1 : SegWS W K p lbl ms P1 Q from (SegWS.or_pre h1 hAb).mono_pre fun _ _ _ h => h
  refine SegWS.pre_run h0 ?_
  intro s c fs h
  obtain ⟨rfl, c0', hr, hA⟩ := h
  refine ⟨hW s c (.inl ⟨rfl, c0', hr, hA⟩), ?_⟩
  have hA' := uPostSR_ret hbase htp hA
  have hF : F s.st.1 := by
    obtain ⟨-, -, -, -, -, -, ⟨hF, -⟩, -⟩ := hA'
    exact hF
  have hA'' : At exe endPc (R.callee ((mainSC lab sc g0 x0).o.sp - 0) (-D1) 8) FC
      ((fun g (_ : Unit) => uNxS (SRetR lbl ty) g) G.2.2.2.2.2 ()) s c := hA'
  have hret : ∀ g x σC c cE fr σx c' (σR : AS), (mainSC lab sc g0 x0).J σC c → CallTo p c cE fr →
      (uN0 lab ms0 F sc.setup ZU1 g).J (enter ((mainSC lab sc g0 x0).o.sp - 0) σC) cE →
      ((fun g (_ : Unit) => uNxS (SRetR lbl ty) g) g x).J σx c' → σR.regs = σx.regs → σR.zmms = σx.zmms →
      σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee ((mainSC lab sc g0 x0).o.sp - 0) (-D1) 8).Off
        (k - ((mainSC lab sc g0 x0).o.sp - 0)) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: []) (c'', []) ∧ Lands (fun _ : Unit => mainS0 lab sc PostS g0 x0)
        (fun e : Empty => e.elim)
        ⟨((fun g (_ : Unit) => uNxS (SRetR lbl ty) g) g x).pc,
          ⟨(mainSC lab sc g0 x0).o.sp - 0 + ((fun g (_ : Unit) => uNxS (SRetR lbl ty) g) g x).o.sp, []⟩, σR⟩
        c'' := by
    rintro g' x σC c cE fr σx c' σR ⟨⟨rfl, hspC, htpC⟩, hsl, hb, hx0⟩ hCT ⟨⟨hc, hfp, hra, hsp, htp'⟩, -⟩
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
      exact rbp_retBotM sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))
  obtain ⟨c'', hrun, hN⟩ := CallGF.ret (p := p) (exe := exe) (endPc := endPc) (R := R) (F := F)
    (N := fun _ : Unit => mainS0 lab sc PostS g0 x0) (E := fun e : Empty => e.elim)
    (nC := mainSC lab sc g0 x0) (e0 := 0) (lo' := -D1) (hi' := 8) (Ne := uN0 lab ms0 F sc.setup ZU1)
    (Ex := fun g (_ : Unit) => uNxS (SRetR lbl ty) g) (G := G) (x := ()) (fs := []) (F₂ := F) hret hA'' hF
  exact ⟨c'', [], hrun, hN.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim, rfl⟩

/-- **`setupBot_segM` at a bottom key**: `setupBot_segK` with the key's
memory side `ms0` free of the segment's. -/
theorem setupBot_segKM {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {sc : SetupCode}
    {ms0 : MemSide isa}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (hZ8 : sc.Z.toInt % 8 = 0) (hZ : 8 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {ty : Ty} {k : StkKey} {fs : List TermRun.Frame} {c0 : Ctl} {Ab : FragS isa}
    (hB : SetupBot p (_root_.Executable.labels exe).label ms0 R F sc D1 ZU1 g0 x0 k fs)
    (hPS : ∀ cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hW : ∀ s c, ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs →
      W s c fs)
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty Ab) Q := by
  obtain ⟨j, R', F', fp, ra, tp, G0⟩ := k
  obtain ⟨G, rfl, hR, hF, hfp, hra, htp, hbase⟩ := hB
  dsimp only at hR hF hfp hra htp hbase hW ⊢
  subst hR hF hfp hra htp
  exact setupBot_segM hD10 hZ8 hZ hlo1 hhi hbase rfl hPS hW hAb h0

/-- **The exits `ExitStk` at a setup bottom key** (`H1OpenXW.hbot`'s shape
at a `SetupBot` key at any key memory side `ms0`): the frame pop at every
return type (`hPS`), the key's exits at each ghost in `k.G0` and each
return type inside `W` (`hW`), `setupBot_segKM` at each. -/
theorem setupBot_exitStkM {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {P : Prog}
    {sc : SetupCode} {ms0 : MemSide isa}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (hZ8 : sc.Z.toInt % 8 = 0) (hZ : 8 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {k : StkKey} {fs : List TermRun.Frame} {Ab : FragS isa}
    (hB : SetupBot p (_root_.Executable.labels exe).label ms0 R F sc D1 ZU1 g0 x0 k fs)
    (hPS : ∀ ty cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hW : ∀ c0 ty, k.G0 c0 → ∀ s c,
      ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs → W s c fs)
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitStk p P lbl exe endPc k fs Ab) Q := by
  refine (SegWS.exists_pre (P := fun g : {c0 // k.G0 c0} × Ty =>
      ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp g.1.1 fs g.2 Ab)
    fun g => setupBot_segKM hD10 hZ8 hZ hlo1 hhi hB (hPS g.2) (hW g.1.1 g.2 g.1.2) hAb h0).mono_pre ?_
  rintro s c fs' ⟨c0, ty, hG, -, hE⟩
  exact ⟨(⟨c0, hG⟩, ty), hE⟩

/-- **`setupBot_exitStkM` at the key's return type**: the frame pop `hPS`
and the exits `hW` only at the return type `ty` of the key's block in `P`
(the one `ExitStk` names), so a post `PostS` may depend on it.

The exits `ExitStk` at a setup bottom key** (`H1OpenXW.hbot`'s shape
at a `SetupBot` key at any key memory side `ms0`): the frame pop at every
return type (`hPS`), the key's exits at each ghost in `k.G0` and each
return type inside `W` (`hW`), `setupBot_segKM` at each. -/
theorem setupBot_exitStkMT {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {P : Prog}
    {sc : SetupCode} {ms0 : MemSide isa}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (hZ8 : sc.Z.toInt % 8 = 0) (hZ : 8 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {k : StkKey} {fs : List TermRun.Frame} {Ab : FragS isa}
    (hB : SetupBot p (_root_.Executable.labels exe).label ms0 R F sc D1 ZU1 g0 x0 k fs)
    (hPS : ∀ ty, (∃ d, P[k.j]? = some d ∧ d.retTy = ty) → ∀ cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hW : ∀ c0 ty, k.G0 c0 → (∃ d, P[k.j]? = some d ∧ d.retTy = ty) → ∀ s c,
      ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs → W s c fs)
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitStk p P lbl exe endPc k fs Ab) Q := by
  refine (SegWS.exists_pre (P := fun g : {c0 // k.G0 c0} × {ty // ∃ d, P[k.j]? = some d ∧ d.retTy = ty} =>
      ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp g.1.1 fs g.2.1 Ab)
    fun g => setupBot_segKM hD10 hZ8 hZ hlo1 hhi hB (hPS g.2.1 g.2.2) (hW g.1.1 g.2.1 g.1.2 g.2.2) hAb h0).mono_pre ?_
  rintro s c fs' ⟨c0, ty, hG, hd, hE⟩
  exact ⟨(⟨c0, hG⟩, ⟨ty, hd⟩), hE⟩

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.setupBot_segM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.setupBot_segM

/-- info: 'Spike.Lib.LowerX64.setupBot_segKM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.setupBot_segKM

/-- info: 'Spike.Lib.LowerX64.setupBot_exitStkM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.setupBot_exitStkM

/-- info: 'Spike.Lib.LowerX64.setupBot_exitStkMT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.setupBot_exitStkMT
