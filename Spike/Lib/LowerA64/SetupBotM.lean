/-
**The setup function's bottom frame at any key memory side** (AArch64):
`setupBot_seg` / `setupBot_segK` (`Spike/Lib/LowerA64/SetupBot.lean`) with
the key's memory side `ms0` (inside `CallGF`'s entry `uN0`) free of the
segment's `ms`: the key is the one the setup call's segment recorded (at
its placement and invariant family), the segment the one a landing runs at
(an extended placement, any family). The return reads only the key's frame
condition, not the memory side's facts.

- `setupBot_segM`, `setupBot_segKM`: `setupBot_seg`, `setupBot_segK` at a
  key memory side `ms0`;
- `setupBot_exitStkM`: the exits `ExitStk` at a `SetupBot` key at `ms0`
  (`H1OpenA.hbot`'s shape), the frame pop at every return type;
  `setupBot_exitStkMT`: at the key's block's return type only.
-/
import Spike.Lib.LowerA64.SetupBot
import Spike.Lib.LowerA64.ResumeStk2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (SetupCode mainSC mainS0 uN0 uNxS)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`setupBot_seg` at a key memory side `ms0`**: the same proof, the
entry `uN0` at `ms0` rather than the segment's `ms []`. -/
theorem setupBot_segM {W : FragS isaLSE2} {K : State → State → Prop} {Q : FragS isaLSE2} {sc : SetupCode}
    {ms0 : MemSide isaLSE2}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -sc.Z.toInt - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {ty : Ty} {G : MachineData × AS × Ctl × Ctl × TermRun.Frame × WcG}
    {tp : UInt64} {c0 : Ctl} {Ab : FragS isaLSE2}
    (hbase : (R.callee (-sc.Z.toInt) (-D1) 0).base = G.2.2.2.2.2.sp) (htp : tp = G.2.2.2.2.2.tp)
    (esp0 : (_root_.Executable.labels exe).label sc.sp0 = (_root_.Executable.labels exe).label sc.e0 + 4)
    (hPS : ∀ cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hW : ∀ s c, ExitC2SL p lbl exe endPc (R.callee (-sc.Z.toInt) (-D1) 0)
      (CallGF p R F (mainSC (_root_.Executable.labels exe).label sc g0 x0) (-D1) 0
        (uN0 (_root_.Executable.labels exe).label ms0 F exe endPc sc.setup ZU1) G)
      G.2.2.2.2.2.fp G.2.2.2.2.2.ra tp c0 [G.2.2.2.2.1] ty (fun _ _ _ => False) s c [G.2.2.2.2.1] →
      W s c [G.2.2.2.2.1])
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitC2SL p lbl exe endPc (R.callee (-sc.Z.toInt) (-D1) 0)
      (CallGF p R F (mainSC (_root_.Executable.labels exe).label sc g0 x0) (-D1) 0
        (uN0 (_root_.Executable.labels exe).label ms0 F exe endPc sc.setup ZU1) G)
      G.2.2.2.2.2.fp G.2.2.2.2.2.ra tp c0 [G.2.2.2.2.1] ty Ab) Q := by
  let lab := (_root_.Executable.labels exe).label
  let RC := R.callee (-sc.Z.toInt) (-D1) 0
  let FC := CallGF p R F (mainSC lab sc g0 x0) (-D1) 0 (uN0 lab ms0 F exe endPc sc.setup ZU1) G
  let P1 : FragS isaLSE2 := fun s c fs => fs = [G.2.2.2.2.1] ∧ ∃ c0', FrameRunM p (c0, [G.2.2.2.2.1])
    (c0', [G.2.2.2.2.1]) ∧ At exe endPc RC FC ((retNSL p lbl G.2.2.2.2.2.fp G.2.2.2.2.2.ra c0' ty).withTp tp) s c
  suffices h1 : SegWS W K p lbl ms P1 Q from (SegWS.or_pre h1 hAb).mono_pre fun _ _ _ h => h
  refine SegWS.pre_run h0 ?_
  intro s c fs h
  obtain ⟨rfl, c0', hr, hA⟩ := h
  refine ⟨hW s c (.inl ⟨rfl, c0', hr, hA⟩), ?_⟩
  have hA' := uPostSR_ret hbase htp hA
  have hF : F s.st.1 := by
    obtain ⟨-, -, -, -, -, -, ⟨hF, -⟩, -⟩ := hA'
    exact hF
  have hA'' : At exe endPc (R.callee (mainSC lab sc g0 x0).o.sp (-D1) 0) FC
      ((fun g (_ : Unit) => uNxS (SRetR lbl ty) g) G.2.2.2.2.2 ()) s c := hA'
  have hret : ∀ g x σC c cE fr σx c' (σR : AS), (mainSC lab sc g0 x0).J σC c → CallTo p c cE fr →
      (uN0 lab ms0 F exe endPc sc.setup ZU1 g).J (enter (mainSC lab sc g0 x0).o.sp σC) cE →
      ((fun g (_ : Unit) => uNxS (SRetR lbl ty) g) g x).J σx c' → σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (mainSC lab sc g0 x0).o.sp (-D1) 0).Off (k - (mainSC lab sc g0 x0).o.sp) →
        σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: []) (c'', []) ∧ Lands (fun _ : Unit => mainS0 lab sc PostS g0 x0)
        (fun e : Empty => e.elim)
        ⟨((fun g (_ : Unit) => uNxS (SRetR lbl ty) g) g x).pc,
          ⟨(mainSC lab sc g0 x0).o.sp + ((fun g (_ : Unit) => uNxS (SRetR lbl ty) g) g x).o.sp, []⟩, σR⟩ c'' := by
    rintro g' x σC c cE fr σx c' σR ⟨⟨rfl, hsp, htp, hsl⟩, h30⟩ hCT ⟨⟨-, -, h30', hsp', htp'⟩, -⟩
      ⟨hP, -, -, hspx, htpx⟩ hreg - hslot
    obtain ⟨c'', hrun, hP''⟩ := hPS cE fr c' σx.regs hCT hP
    refine ⟨c'', hrun, .inl ⟨(), ?_, by simp [SO.le, mainS0, mainSC, uNxS], ?_⟩⟩
    · show lab sc.sp0 = Int64.ofBitVec g'.ra
      rw [← h30']
      show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [h30, Spike.Lib.int64_ofBitVec_toBitVec]; exact esp0
    · show PostS c'' σR.regs ∧ σR.regs.SP.toBitVec = g0.sp0 - sc.Z.toBitVec ∧ σR.regs.TPIDR_EL0 = g0.tp ∧
        σR.slot (-sc.Z.toInt) = x0
      rw [hreg]
      refine ⟨hP'', hspx.trans (hsp'.symm.trans hsp), htpx.trans (htp'.symm.trans htp), ?_⟩
      · rw [hslot (-sc.Z.toInt) ⟨by omega, by omega, by omega⟩
          (by simp only [mainSC, Spike.Lib.Region.Off, Spike.Lib.Region.callee]; omega)]
        exact hsl
  obtain ⟨c'', hrun, hN⟩ := CallGF.ret (p := p) (exe := exe) (endPc := endPc) (R := R) (F := F)
    (N := fun _ : Unit => mainS0 lab sc PostS g0 x0) (E := fun e : Empty => e.elim)
    (nC := mainSC lab sc g0 x0) (lo' := -D1) (hi' := 0) (Ne := uN0 lab ms0 F exe endPc sc.setup ZU1)
    (Ex := fun g (_ : Unit) => uNxS (SRetR lbl ty) g) (G := G) (x := ()) (fs := []) (F₂ := F) hret hA'' hF
  exact ⟨c'', [], hrun, hN.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim, rfl⟩

/-- **`setupBot_segM` at a bottom key**: `setupBot_segK` with the key's
memory side `ms0` free of the segment's. -/
theorem setupBot_segKM {W : FragS isaLSE2} {K : State → State → Prop} {Q : FragS isaLSE2} {sc : SetupCode}
    {ms0 : MemSide isaLSE2}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -sc.Z.toInt - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {ty : Ty} {k : StkKey} {fs : List TermRun.Frame} {c0 : Ctl} {Ab : FragS isaLSE2}
    (hB : SetupBot p (_root_.Executable.labels exe).label ms0 exe endPc R F sc D1 ZU1 g0 x0 k fs)
    (esp0 : (_root_.Executable.labels exe).label sc.sp0 = (_root_.Executable.labels exe).label sc.e0 + 4)
    (hPS : ∀ cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hW : ∀ s c, ExitC2SL p lbl exe endPc k.R k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs →
      W s c fs)
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitC2SL p lbl exe endPc k.R k.F k.fp k.ra k.tp c0 fs ty Ab) Q := by
  obtain ⟨j, R', F', fp, ra, tp, G0⟩ := k
  obtain ⟨G, rfl, hR, hF, hfp, hra, htp, hbase⟩ := hB
  dsimp only at hR hF hfp hra htp hbase hW ⊢
  subst hR hF hfp hra htp
  exact setupBot_segM hD10 h16 hZ hlo1 hhi hbase rfl esp0 hPS hW hAb h0

/-- **The exits `ExitStk` at a setup bottom key** (`H1OpenA.hbot`'s shape
at a `SetupBot` key at any key memory side `ms0`): the frame pop at every
return type (`hPS`), the key's exits at each ghost in `k.G0` and each
return type inside `W` (`hW`), `setupBot_segKM` at each. -/
theorem setupBot_exitStkM {W : FragS isaLSE2} {K : State → State → Prop} {Q : FragS isaLSE2} {P : Prog}
    {sc : SetupCode} {ms0 : MemSide isaLSE2}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -sc.Z.toInt - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {k : StkKey} {fs : List TermRun.Frame} {Ab : FragS isaLSE2}
    (hB : SetupBot p (_root_.Executable.labels exe).label ms0 exe endPc R F sc D1 ZU1 g0 x0 k fs)
    (esp0 : (_root_.Executable.labels exe).label sc.sp0 = (_root_.Executable.labels exe).label sc.e0 + 4)
    (hPS : ∀ ty cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hW : ∀ c0 ty, k.G0 c0 → ∀ s c,
      ExitC2SL p lbl exe endPc k.R k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs → W s c fs)
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitStk p P lbl exe endPc k fs Ab) Q := by
  refine (SegWS.exists_pre (P := fun g : {c0 // k.G0 c0} × Ty =>
      ExitC2SL p lbl exe endPc k.R k.F k.fp k.ra k.tp g.1.1 fs g.2 Ab)
    fun g => setupBot_segKM hD10 h16 hZ hlo1 hhi hB esp0 (hPS g.2) (hW g.1.1 g.2 g.1.2) hAb h0).mono_pre ?_
  rintro s c fs' ⟨c0, ty, hG, -, hE⟩
  exact ⟨(⟨c0, hG⟩, ty), hE⟩

/-- **`setupBot_exitStkM` at the key's return type**: the frame pop `hPS`
and the exits `hW` only at the return type `ty` of the key's block in `P`
(the one `ExitStk` names), so a post `PostS` may depend on it.

The exits `ExitStk` at a setup bottom key** (`H1OpenA.hbot`'s shape
at a `SetupBot` key at any key memory side `ms0`): the frame pop at every
return type (`hPS`), the key's exits at each ghost in `k.G0` and each
return type inside `W` (`hW`), `setupBot_segKM` at each. -/
theorem setupBot_exitStkMT {W : FragS isaLSE2} {K : State → State → Prop} {Q : FragS isaLSE2} {P : Prog}
    {sc : SetupCode} {ms0 : MemSide isaLSE2}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -sc.Z.toInt - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {k : StkKey} {fs : List TermRun.Frame} {Ab : FragS isaLSE2}
    (hB : SetupBot p (_root_.Executable.labels exe).label ms0 exe endPc R F sc D1 ZU1 g0 x0 k fs)
    (esp0 : (_root_.Executable.labels exe).label sc.sp0 = (_root_.Executable.labels exe).label sc.e0 + 4)
    (hPS : ∀ ty, (∃ d, P[k.j]? = some d ∧ d.retTy = ty) → ∀ cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hW : ∀ c0 ty, k.G0 c0 → (∃ d, P[k.j]? = some d ∧ d.retTy = ty) → ∀ s c,
      ExitC2SL p lbl exe endPc k.R k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs → W s c fs)
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitStk p P lbl exe endPc k fs Ab) Q := by
  refine (SegWS.exists_pre (P := fun g : {c0 // k.G0 c0} × {ty // ∃ d, P[k.j]? = some d ∧ d.retTy = ty} =>
      ExitC2SL p lbl exe endPc k.R k.F k.fp k.ra k.tp g.1.1 fs g.2.1 Ab)
    fun g => setupBot_segKM hD10 h16 hZ hlo1 hhi hB esp0 (hPS g.2.1 g.2.2) (hW g.1.1 g.2.1 g.1.2 g.2.2) hAb
      h0).mono_pre ?_
  rintro s c fs' ⟨c0, ty, hG, hd, hE⟩
  exact ⟨(⟨c0, hG⟩, ⟨ty, hd⟩), hE⟩

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.setupBot_segM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.setupBot_segM

/-- info: 'Spike.Lib.LowerA64.setupBot_segKM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.setupBot_segKM

/-- info: 'Spike.Lib.LowerA64.setupBot_exitStkM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.setupBot_exitStkM

/-- info: 'Spike.Lib.LowerA64.setupBot_exitStkMT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.setupBot_exitStkMT
