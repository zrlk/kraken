/-
**The setup function's bottom frame** (x86-64; the twin of
`Spike/Lib/LowerA64/SetupBot.lean`): the setup function runs in the frame
`fr` `scc_rt_main`'s `call setup` pushes, under the call's ghost frame
condition (`CallGF` at `mainSC`, `SetupGF`, `Spike/Lib/Rt/X64MainSSB.lean`).
A frame's exit at that frame condition (`ExitC2SL` at `[fr]`, in the
rebased callee region `rbR`) is the setup call's return: the frame pops
back to `scc_rt_main` at `mainS0` (`CallGF.ret`), from where its segment
runs on.

- `SetupBot`: the stack records' bottom key at the setup frame: the frames
  `[fr]`, the region the setup call's callee (entry) region, the frame
  condition `CallGF` at a ghost whose frame is `fr`, the key's
  `fp`/`ra`/`tp` the ghost's parameters', the region's base the ghost's
  `sp`;
- `setupBot_seg`: from the exits `ExitC2SL` at `rbR` of that region and
  `CallGF` at the ghost `G`, a segment to `Q` from `mainS0`'s
  (`uPostSR_ret`, `CallGF.ret`, `SegWS.pre_run`), the aborts' by their own;
- `setupBot_segK`: `setupBot_seg` at a key with `SetupBot`;
- `setupBot_ofGF`: `SetupBot` from the setup call's `SetupGF` (the
  producer side, for `CxOkS.bot`).
-/
import Spike.Lib.LowerX64.SetupCallB2
import Spike.Lib.LowerX64.Stk2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (SetupCode mainSC mainS0 uN0 uNxS)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- `%rbp` back at the saved `%rbp` after a call's return: the callee
restored `%rbp` and popped the return address. -/
private theorem rbp_retBot {rbpC rspC rbpR rspR : BitVec 64} (z : Int)
    (hb : rbpC = rspC + BitVec.ofInt 64 (-8 - (-8 - z - 8))) (hbR : rbpR = rbpC) (hspR : rspR = rspC + 8#64) :
    rbpR = rspR + BitVec.ofInt 64 (-8 - (-8 - z)) := by
  rw [hbR, hspR, hb]
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  bv_omega

/-- **The bottom key at the setup function's frame**: the frames `[fr]` of
the call ghost `G`, the key's region the setup call's callee (entry) region
`R.callee (-8 - Z - 8 - 0) (-D1) 8` at `scc_rt_main`'s `R`, its frame
condition `CallGF` at `mainSC` and the entry `uN0` at `G`, its `fp`, `ra`,
`tp` the ghost's parameters' and its region's base their `sp`. -/
def SetupBot (p : Prog) (lab : Label → Int64) (ms : MemSide isa) (R : Region) (F : MachineData → Prop)
    (sc : SetupCode) (D1 : Int) (ZU1 : Int64) (g0 : MainG) (x0 : BitVec 64) (k : StkKey)
    (fs : List TermRun.Frame) : Prop :=
  ∃ G : MachineData × AS × Ctl × Ctl × TermRun.Frame × WcG, fs = [G.2.2.2.2.1] ∧
    k.R = R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8 ∧
    k.F = CallGF p R F (mainSC lab sc g0 x0) 0 (-D1) 8 (uN0 lab ms F sc.setup ZU1) G ∧
    k.fp = G.2.2.2.2.2.fp ∧ k.ra = G.2.2.2.2.2.ra ∧ k.tp = G.2.2.2.2.2.tp ∧ k.R.base = G.2.2.2.2.2.sp

/-- **The bottom key from the setup call's frame condition**: in the
setup function's segment (`SetupCallWSB` at `SetupGF`), the frame
condition `F'`, ghost `g` and frame `fr` it runs at, the callee region's
base `g`'s `sp`, give the bottom key `SetupBot` at the frames `[fr]` (any
block `j` and ghost predicate `G0`). The premise `CxOkS.bot` takes. -/
theorem setupBot_ofGF {lab : Label → Int64} {ms0 : MemSide isa} {sc : SetupCode} {D1 : Int} {ZU1 : Int64}
    {g0 : MainG} {x0 : BitVec 64} {F' : MachineData → Prop} {g : WcG} {fr : TermRun.Frame}
    (hGF : Spike.Lib.X64.Rt.SetupGF p lab ms0 R F sc D1 ZU1 g0 x0 F' g fr)
    (hbase : (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8).base = g.sp) (j : Nat) (G0 : Ctl → Prop) :
    SetupBot p lab ms0 R F sc D1 ZU1 g0 x0
      ⟨j, R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8, F', g.fp, g.ra, g.tp, G0⟩ [fr] := by
  obtain ⟨G, rfl, rfl, rfl⟩ := hGF
  exact ⟨G, rfl, rfl, rfl, rfl, rfl, rfl, hbase⟩

/-- **The setup function's exits at its ghost frame condition, to
`scc_rt_main`'s segment after the setup block**: the exits `ExitC2SL` at
the frame `G`'s, in the rebased callee region, and `CallGF` at `mainSC` at
`G` (the key `SetupBot` describes), inside `W` (`hW`), are the return
`uNxS` at `SRetR` (`uPostSR_ret`), whose frame pops back to `mainS0` at the
empty frames (`CallGF.ret` with the pop `hPS` at `SRetR`); from there
`h0`'s segment; the aborts `Ab` by `hAb`. -/
theorem setupBot_seg {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {sc : SetupCode}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (hZ8 : sc.Z.toInt % 8 = 0) (hZ : 8 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {ty : Ty} {G : MachineData × AS × Ctl × Ctl × TermRun.Frame × WcG}
    {tp : UInt64} {c0 : Ctl} {Ab : FragS isa}
    (hbase : (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8).base = G.2.2.2.2.2.sp) (htp : tp = G.2.2.2.2.2.tp)
    (hPS : ∀ cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hW : ∀ s c, ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8))
      (CallGF p R F (mainSC (_root_.Executable.labels exe).label sc g0 x0) 0 (-D1) 8
        (uN0 (_root_.Executable.labels exe).label (ms []) F sc.setup ZU1) G)
      G.2.2.2.2.2.fp G.2.2.2.2.2.ra tp c0 [G.2.2.2.2.1] ty (fun _ _ _ => False) s c [G.2.2.2.2.1] →
      W s c [G.2.2.2.2.1])
    (hAb : SegWS W K p lbl ms Ab Q)
    (h0 : SegWS W K p lbl ms
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0)).at []) Q) :
    SegWS W K p lbl ms (ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8))
      (CallGF p R F (mainSC (_root_.Executable.labels exe).label sc g0 x0) 0 (-D1) 8
        (uN0 (_root_.Executable.labels exe).label (ms []) F sc.setup ZU1) G)
      G.2.2.2.2.2.fp G.2.2.2.2.2.ra tp c0 [G.2.2.2.2.1] ty Ab) Q := by
  let lab := (_root_.Executable.labels exe).label
  let RC := R.callee (-8 - sc.Z.toInt - 8 - 0) (-D1) 8
  let FC := CallGF p R F (mainSC lab sc g0 x0) 0 (-D1) 8 (uN0 lab (ms []) F sc.setup ZU1) G
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
      (uN0 lab (ms []) F sc.setup ZU1 g).J (enter ((mainSC lab sc g0 x0).o.sp - 0) σC) cE →
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
      exact rbp_retBot sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))
  obtain ⟨c'', hrun, hN⟩ := CallGF.ret (p := p) (exe := exe) (endPc := endPc) (R := R) (F := F)
    (N := fun _ : Unit => mainS0 lab sc PostS g0 x0) (E := fun e : Empty => e.elim)
    (nC := mainSC lab sc g0 x0) (e0 := 0) (lo' := -D1) (hi' := 8) (Ne := uN0 lab (ms []) F sc.setup ZU1)
    (Ex := fun g (_ : Unit) => uNxS (SRetR lbl ty) g) (G := G) (x := ()) (fs := []) (F₂ := F) hret hA'' hF
  exact ⟨c'', [], hrun, hN.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim, rfl⟩

/-- **`setupBot_seg` at a bottom key**: from the exits `ExitC2SL` at the
rebased region `rbR k.R` of the key `k`, its frame condition, pair and
thread pointer at its frames `fs`, `k` the setup frame's (`SetupBot`),
inside `W` (`hW`), to `Q`, given `scc_rt_main`'s segment from `mainS0`
(`h0`) and the aborts' (`hAb`). -/
theorem setupBot_segK {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {sc : SetupCode}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (hZ8 : sc.Z.toInt % 8 = 0) (hZ : 8 ≤ sc.Z.toInt)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hhi : 0 ≤ R.hi) {PostS : Ctl → Reg64s → Prop} {g0 : MainG}
    {x0 : BitVec 64} {ty : Ty} {k : StkKey} {fs : List TermRun.Frame} {c0 : Ctl} {Ab : FragS isa}
    (hB : SetupBot p (_root_.Executable.labels exe).label (ms []) R F sc D1 ZU1 g0 x0 k fs)
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
  exact setupBot_seg hD10 hZ8 hZ hlo1 hhi hbase rfl hPS hW hAb h0

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.setupBot_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.setupBot_seg

/-- info: 'Spike.Lib.LowerX64.setupBot_segK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.setupBot_segK

/-- info: 'Spike.Lib.LowerX64.setupBot_ofGF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.setupBot_ofGF
