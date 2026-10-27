/-
**The setup function's bottom frame** (AArch64): the setup function runs
in the frame `fr` `scc_rt_main`'s `bl setup` pushes, under the call's ghost
frame condition (`CallGF` at `mainSC`, `SetupGF`,
`Spike/Lib/Rt/A64MainSSB.lean`). A frame's exit at that frame condition
(`ExitC2SL` at `[fr]`) is the setup call's return: the frame pops back to
`scc_rt_main` at `mainS0` (`CallGF.ret`), from where its segment runs on.

- `SetupBot`: the stack records' bottom key at the setup frame: the frames
  `[fr]`, the region the setup call's callee region, the frame condition
  `CallGF` at a ghost whose frame is `fr`, the key's `fp`/`ra`/`tp` the
  ghost's parameters', the region's base the ghost's `sp`;
- `setupBot_seg`: from the exits `ExitC2SL` at `CallGF` at the ghost `G`,
  a segment to `Q` from `mainS0`'s (`uPostSR_ret`, `CallGF.ret`,
  `SegWS.pre_run`), the aborts' by their own;
- `setupBot_segK`: `setupBot_seg` at a key with `SetupBot`;
- `setupBot_ofGF`: `SetupBot` from the setup call's `SetupGF` (the
  producer side, for `CxOkS.bot`).
-/
import Spike.Lib.LowerA64.SetupCallB2
import Spike.Lib.LowerA64.Stk2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (SetupCode mainSC mainS0 uN0 uNxS)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The bottom key at the setup function's frame**: the frames `[fr]` of
the call ghost `G`, the key's region the setup call's callee region
`R.callee (-Z) (-D1) 0` at `scc_rt_main`'s `R`, its frame condition
`CallGF` at `mainSC` and the entry `uN0` at `G`, its `fp`, `ra`, `tp` the
ghost's parameters' and its region's base their `sp`. -/
def SetupBot (p : Prog) (lab : Label → Int64) (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (sc : SetupCode) (D1 : Int) (ZU1 : Int64) (g0 : MainG) (x0 : BitVec 64)
    (k : StkKey) (fs : List TermRun.Frame) : Prop :=
  ∃ G : MachineData × AS × Ctl × Ctl × TermRun.Frame × WcG, fs = [G.2.2.2.2.1] ∧
    k.R = R.callee (-sc.Z.toInt) (-D1) 0 ∧
    k.F = CallGF p R F (mainSC lab sc g0 x0) (-D1) 0 (uN0 lab ms F exe endPc sc.setup ZU1) G ∧
    k.fp = G.2.2.2.2.2.fp ∧ k.ra = G.2.2.2.2.2.ra ∧ k.tp = G.2.2.2.2.2.tp ∧ k.R.base = G.2.2.2.2.2.sp

/-- **The bottom key from the setup call's frame condition**: in the
setup function's segment (`SetupCallWSB` at `SetupGF`), the frame
condition `F'`, ghost `g` and frame `fr` it runs at, the callee region's
base `g`'s `sp`, give the bottom key `SetupBot` at the frames `[fr]` (any
block `j` and ghost predicate `G0`). The premise `CxOkS.bot` takes. -/
theorem setupBot_ofGF {lab : Label → Int64} {ms0 : MemSide isaLSE2} {sc : SetupCode} {D1 : Int} {ZU1 : Int64}
    {g0 : MainG} {x0 : BitVec 64} {F' : MachineData → Prop} {g : WcG} {fr : TermRun.Frame}
    (hGF : Spike.Lib.A64.Rt.SetupGF p lab ms0 exe endPc R F sc D1 ZU1 g0 x0 F' g fr)
    (hbase : (R.callee (-sc.Z.toInt) (-D1) 0).base = g.sp) (j : Nat) (G0 : Ctl → Prop) :
    SetupBot p lab ms0 exe endPc R F sc D1 ZU1 g0 x0
      ⟨j, R.callee (-sc.Z.toInt) (-D1) 0, F', g.fp, g.ra, g.tp, G0⟩ [fr] := by
  obtain ⟨G, rfl, rfl, rfl⟩ := hGF
  exact ⟨G, rfl, rfl, rfl, rfl, rfl, rfl, hbase⟩

/-- **The setup function's exits at its ghost frame condition, to
`scc_rt_main`'s segment after the setup block**: the exits `ExitC2SL` at
the frame `G`'s and `CallGF` at `mainSC` at `G` (the key `SetupBot`
describes), inside `W` (`hW`), are the return `uNxS` at `SRetR`
(`uPostSR_ret`), whose frame pops back to `mainS0` at the empty frames
(`CallGF.ret` with the pop `hPS` at `SRetR`); from there `h0`'s segment;
the aborts `Ab` by `hAb`. -/
theorem setupBot_seg {W : FragS isaLSE2} {K : State → State → Prop} {Q : FragS isaLSE2} {sc : SetupCode}
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
        (uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc sc.setup ZU1) G)
      G.2.2.2.2.2.fp G.2.2.2.2.2.ra tp c0 [G.2.2.2.2.1] ty (fun _ _ _ => False) s c [G.2.2.2.2.1] →
      W s c [G.2.2.2.2.1])
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitC2SL p lbl exe endPc (R.callee (-sc.Z.toInt) (-D1) 0)
      (CallGF p R F (mainSC (_root_.Executable.labels exe).label sc g0 x0) (-D1) 0
        (uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc sc.setup ZU1) G)
      G.2.2.2.2.2.fp G.2.2.2.2.2.ra tp c0 [G.2.2.2.2.1] ty Ab) Q := by
  let lab := (_root_.Executable.labels exe).label
  let RC := R.callee (-sc.Z.toInt) (-D1) 0
  let FC := CallGF p R F (mainSC lab sc g0 x0) (-D1) 0 (uN0 lab (ms []) F exe endPc sc.setup ZU1) G
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
      (uN0 lab (ms []) F exe endPc sc.setup ZU1 g).J (enter (mainSC lab sc g0 x0).o.sp σC) cE →
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
    (nC := mainSC lab sc g0 x0) (lo' := -D1) (hi' := 0) (Ne := uN0 lab (ms []) F exe endPc sc.setup ZU1)
    (Ex := fun g (_ : Unit) => uNxS (SRetR lbl ty) g) (G := G) (x := ()) (fs := []) (F₂ := F) hret hA'' hF
  exact ⟨c'', [], hrun, hN.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim, rfl⟩

/-- **`setupBot_seg` at a bottom key**: from the exits `ExitC2SL` at the
key `k`'s region, frame condition, pair and thread pointer at its frames
`fs`, `k` the setup frame's (`SetupBot`), inside `W` (`hW`), to `Q`, given
`scc_rt_main`'s segment from `mainS0` (`h0`) and the aborts' (`hAb`). The
shape `resume_stk` ends in at the bottom. -/
theorem setupBot_segK {W : FragS isaLSE2} {K : State → State → Prop} {Q : FragS isaLSE2} {sc : SetupCode}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -sc.Z.toInt - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {ty : Ty} {k : StkKey} {fs : List TermRun.Frame} {c0 : Ctl} {Ab : FragS isaLSE2}
    (hB : SetupBot p (_root_.Executable.labels exe).label (ms []) exe endPc R F sc D1 ZU1 g0 x0 k fs)
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
  exact setupBot_seg hD10 h16 hZ hlo1 hhi hbase rfl esp0 hPS hW hAb h0

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.setupBot_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.setupBot_seg

/-- info: 'Spike.Lib.LowerA64.setupBot_ofGF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.setupBot_ofGF

/-- info: 'Spike.Lib.LowerA64.setupBot_segK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.setupBot_segK
