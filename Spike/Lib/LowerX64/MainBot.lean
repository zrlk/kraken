/-
**The user function's bottom frames** (x86-64; the twin of
`Spike/Lib/LowerA64/MainBot.lean`): `main` runs at the empty frames in the
frame `scc_rt_main`'s `call fn` pushes, under the call's ghost frame
condition (`MainGFr` at `mainSM`, `MainGF`, `Spike/Lib/Rt/X64MainSSB.lean`).
Its body's exits at that frame condition (`ExitC2SL` at `[]`, at `int`, in
the rebased callee region `rbR`) are `main`'s return: the machine lands
back in `scc_rt_main` at `mainSR` (`MainGFr.ret`), from where the
`exit_group` tail runs. The twin of `Spike/Lib/LowerX64/SetupBot.lean` for
`main`.

- `MainBot`: the stack records' bottom key at `main`'s frame: the frames
  `[]`, the region the user function's callee region, the frame condition
  `MainGFr` at a ghost, the key's `fp`/`ra`/`tp` the ghost's parameters',
  the region's base the ghost's `sp`;
- `mainBot_ofGF`: `MainBot` from the user function's call's `MainGF` (the
  producer side);
- `mainBot_seg`: from the exits `ExitC2SL` at `rbR` of that region and
  `MainGFr` at the ghost `G`, a segment to `Q` from `mainSR`'s at the post
  `UPostRF` (`uPostRF_ret`, `MainGFr.ret`, `SegWS.pre_run`), the aborts' by
  their own;
- `mainBot_segK`: `mainBot_seg` at a key with `MainBot`;
- `mainBot_exitStk`: the exits `ExitStk` at a `MainBot` key (`H1OpenA.hbot`'s
  shape).
-/
import Spike.Lib.LowerX64.MainExitF
import Spike.Lib.LowerX64.Stk2
import Spike.Lib.LowerX64.ResumeStk2
import Spike.Lib.Rt.X64MainSSB

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (SetupCode mainSM mainSR uNM SetupArgs MainGF)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- `%rbp` back at the saved `%rbp` after a call's return: the callee
restored `%rbp` and popped the return address. -/
private theorem rbp_retMBot {rbpC rspC rbpR rspR : BitVec 64} (z : Int)
    (hb : rbpC = rspC + BitVec.ofInt 64 (-8 - (-8 - z - 8))) (hbR : rbpR = rbpC) (hspR : rspR = rspC + 8#64) :
    rbpR = rspR + BitVec.ofInt 64 (-8 - (-8 - z)) := by
  rw [hbR, hspR, hb]
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  bv_omega

/-- **The bottom key at the user function's frame**: the empty frames, the
key's region the user function's callee region `R.callee (-8 - Z - 8 - 0)
(-D2) 8` at `scc_rt_main`'s `R`, its frame condition `MainGFr` at `mainSM`
and the entry `uNM` at a ghost `G`, its `fp`, `ra`, `tp` the ghost's
parameters' and its region's base their `sp`. -/
def MainBot (lab : Label → Int64) (ms : MemSide isa) (R : Region) (F : MachineData → Prop) (sc : SetupCode)
    (D2 : Int) (ZU2 : Int64) (PostS : Ctl → Reg64s → Prop) (g0 : MainG) (x0 : BitVec 64) (k : StkKey)
    (fs : List TermRun.Frame) : Prop :=
  ∃ G : MachineData × AS × Ctl × WcG, fs = [] ∧ k.R = R.callee (-8 - sc.Z.toInt - 8 - 0) (-D2) 8 ∧
    k.F = MainGFr R F (mainSM lab sc PostS g0 x0) 0 (-D2) 8 (uNM lab ms F sc.fn ZU2 (SetupArgs PostS sc.sw x0)) G ∧
    k.fp = G.2.2.2.fp ∧ k.ra = G.2.2.2.ra ∧ k.tp = G.2.2.2.tp ∧ k.R.base = G.2.2.2.sp

/-- **The bottom key from the user function's call's frame condition**: in
the user function's segment (`MainCallWSFB` at `MainGF`), the frame
condition `F'` and ghost `g` it runs at, the callee region's base `g`'s
`sp`, give the bottom key `MainBot` at the empty frames (any block `j` and
ghost predicate `G0`). -/
theorem mainBot_ofGF {lab : Label → Int64} {ms0 : MemSide isa} {sc : SetupCode} {D2 : Int} {ZU2 : Int64}
    {PostS : Ctl → Reg64s → Prop} {g0 : MainG} {x0 : BitVec 64} {F' : MachineData → Prop} {g : WcG}
    (hGF : MainGF lab ms0 R F sc D2 ZU2 PostS g0 x0 F' g)
    (hbase : (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D2) 8).base = g.sp) (j : Nat) (G0 : Ctl → Prop) :
    MainBot lab ms0 R F sc D2 ZU2 PostS g0 x0
      ⟨j, R.callee (-8 - sc.Z.toInt - 8 - 0) (-D2) 8, F', g.fp, g.ra, g.tp, G0⟩ [] := by
  obtain ⟨G, rfl, rfl⟩ := hGF
  exact ⟨G, rfl, rfl, rfl, rfl, rfl, rfl, hbase⟩

/-- **The user function's exits at its ghost frame condition, to
`scc_rt_main`'s segment after its return**: the exits `ExitC2SL` at the
empty frames, at the frame `G`'s, in the rebased callee region, and
`MainGFr` at `mainSM` at `G` (the key `MainBot` describes), inside `W`
(`hW`), are the return `uNx` at `UPostRF` (`uPostRF_ret`), which lands at
`mainSR` (`MainGFr.ret`); from there `h5`'s segment; the aborts `Ab` by
`hAb`. -/
theorem mainBot_seg {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {sc : SetupCode}
    {D2 : Int} {ZU2 : Int64} {PostS : Ctl → Reg64s → Prop} {g0 : MainG} {x0 : BitVec 64}
    {G : MachineData × AS × Ctl × WcG} {tp : UInt64} {c0 : Ctl} {Ab : FragS isa}
    (hbase : (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D2) 8).base = G.2.2.2.sp) (htp : tp = G.2.2.2.tp)
    (hW : ∀ s c, ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D2) 8))
      (MainGFr R F (mainSM (_root_.Executable.labels exe).label sc PostS g0 x0) 0 (-D2) 8
        (uNM (_root_.Executable.labels exe).label (ms []) F sc.fn ZU2 (SetupArgs PostS sc.sw x0)) G)
      G.2.2.2.fp G.2.2.2.ra tp c0 [] .int (fun _ _ _ => False) s c [] → W s c [])
    (hAb : SegWS W K p lbl ms Ab Q)
    (h5 : SegWS W K p lbl ms
      ((At exe endPc R F (mainSR (_root_.Executable.labels exe).label sc (fun c v => UPostRF p lbl c [] v))).at [])
      Q) :
    SegWS W K p lbl ms (ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - sc.Z.toInt - 8 - 0) (-D2) 8))
      (MainGFr R F (mainSM (_root_.Executable.labels exe).label sc PostS g0 x0) 0 (-D2) 8
        (uNM (_root_.Executable.labels exe).label (ms []) F sc.fn ZU2 (SetupArgs PostS sc.sw x0)) G)
      G.2.2.2.fp G.2.2.2.ra tp c0 [] .int Ab) Q := by
  let lab := (_root_.Executable.labels exe).label
  let RC := R.callee (-8 - sc.Z.toInt - 8 - 0) (-D2) 8
  let FC := MainGFr R F (mainSM lab sc PostS g0 x0) 0 (-D2) 8
    (uNM lab (ms []) F sc.fn ZU2 (SetupArgs PostS sc.sw x0)) G
  let P1 : FragS isa := fun s c fs => fs = [] ∧ ∃ c0', FrameRunM p (c0, []) (c0', []) ∧
    At exe endPc (rbR RC) FC ((retNSL p lbl G.2.2.2.fp G.2.2.2.ra c0' .int).withTp tp) s c
  suffices h1 : SegWS W K p lbl ms P1 Q from (SegWS.or_pre h1 hAb).mono_pre fun _ _ _ h => h
  refine SegWS.pre_run h5 ?_
  intro s c fs h
  obtain ⟨rfl, c0', hr, hA⟩ := h
  refine ⟨hW s c (.inl ⟨rfl, c0', hr, hA⟩), ?_⟩
  subst htp
  have hA' := uPostRF_ret hbase (.refl _) hA
  have hF : F s.st.1 := by
    obtain ⟨-, -, -, -, -, -, ⟨hF, -⟩, -⟩ := hA'
    exact hF
  have hN := MainGFr.ret (exe := exe) (endPc := endPc) (R := R) (F := F) (F₂ := F)
    (N := fun fs (_ : Unit) => mainSR lab sc (fun c v => UPostRF p lbl c fs v))
    (E := fun _ (e : Empty) => e.elim)
    (nC := mainSM lab sc PostS g0 x0) (e0 := 0) (lo' := -D2) (hi' := 8)
    (Ne := uNM lab (ms []) F sc.fn ZU2 (SetupArgs PostS sc.sw x0))
    (Ex := fun g fs (_ : Unit) => Spike.Lib.X64.Rt.uNx (fun c v => UPostRF p lbl c fs v) g)
    (G := G) (fs' := []) (x := ()) ?_ hA' hF
  · exact ⟨c, [], .refl _, hN.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim, rfl⟩
  · rintro g' fs' x σC c σx c' σR ⟨-, hsl, hb⟩ ⟨⟨-, hfp, hra, hsp, -⟩, -⟩ ⟨hP, hb', hsp'⟩ hregs - - -
    refine .inl ⟨(), ?_, by simp [SO.le, mainSR, mainSM, Spike.Lib.X64.Rt.uNx], by rw [hregs]; exact hP, ?_⟩
    · show lab sc.sp1 = Int64.ofBitVec g'.ra
      rw [← hra]
      show lab _ = Int64.ofBitVec (σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0))
      rw [show -8 - sc.Z.toInt - 8 - 0 + 0 = -8 - sc.Z.toInt - 8 by omega, hsl, int64_ofBitVec_toBitVec]
    · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt))
      rw [hregs]
      simp only [Reg64s.get64] at hb ⊢
      exact rbp_retMBot sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))

/-- **`mainBot_seg` at a bottom key**: from the exits `ExitC2SL` at the
rebased region `rbR k.R` of the key `k`, its frame condition, pair and
thread pointer at its frames `fs`, at `int`, `k` the user function's
frame's (`MainBot`), inside `W` (`hW`), to `Q`, given `scc_rt_main`'s
segment from `mainSR` (`h5`) and the aborts' (`hAb`). The shape
`resume_stk` ends in at `main`'s bottom. -/
theorem mainBot_segK {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {sc : SetupCode}
    {D2 : Int} {ZU2 : Int64} {PostS : Ctl → Reg64s → Prop} {g0 : MainG} {x0 : BitVec 64}
    {k : StkKey} {fs : List TermRun.Frame} {c0 : Ctl} {Ab : FragS isa}
    (hB : MainBot (_root_.Executable.labels exe).label (ms []) R F sc D2 ZU2 PostS g0 x0 k fs)
    (hW : ∀ s c, ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs .int (fun _ _ _ => False) s c fs →
      W s c fs)
    (hAb : SegWS W K p lbl ms Ab Q)
    (h5 : SegWS W K p lbl ms
      ((At exe endPc R F (mainSR (_root_.Executable.labels exe).label sc (fun c v => UPostRF p lbl c [] v))).at [])
      Q) :
    SegWS W K p lbl ms (ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs .int Ab) Q := by
  obtain ⟨j, R', F', fp, ra, tp, G0⟩ := k
  obtain ⟨G, rfl, hR, hF, hfp, hra, htp, hbase⟩ := hB
  dsimp only at hR hF hfp hra htp hbase hW ⊢
  subst hR hF hfp hra htp
  exact mainBot_seg hbase rfl hW hAb h5

/-- **The exits `ExitStk` at a bottom key at `main`'s frame** (`H1OpenA.hbot`'s
shape at a `MainBot` key): the key's block returning `int` (`hty`), its
exits at each ghost in `k.G0` inside `W` (`hW`), `mainBot_segK` at each
ghost. -/
theorem mainBot_exitStk {W : FragS isa} {K : State → State → Prop} {Q : FragS isa} {P : Prog}
    {sc : SetupCode} {D2 : Int} {ZU2 : Int64} {PostS : Ctl → Reg64s → Prop} {g0 : MainG} {x0 : BitVec 64}
    {k : StkKey} {fs : List TermRun.Frame} {Ab : FragS isa}
    (hB : MainBot (_root_.Executable.labels exe).label (ms []) R F sc D2 ZU2 PostS g0 x0 k fs)
    (hty : ∀ d, P[k.j]? = some d → d.retTy = .int)
    (hW : ∀ c0, k.G0 c0 → ∀ s c,
      ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs .int (fun _ _ _ => False) s c fs → W s c fs)
    (hAb : SegWS W K p lbl ms Ab Q)
    (h5 : SegWS W K p lbl ms
      ((At exe endPc R F (mainSR (_root_.Executable.labels exe).label sc (fun c v => UPostRF p lbl c [] v))).at [])
      Q) :
    SegWS W K p lbl ms (ExitStk p P lbl exe endPc k fs Ab) Q := by
  refine (SegWS.exists_pre (P := fun g : {c0 // k.G0 c0} =>
      ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp g.1 fs .int Ab)
    fun g => mainBot_segK hB (hW g.1 g.2) hAb h5).mono_pre ?_
  rintro s c fs' ⟨c0, ty, hG, ⟨d, hd, rfl⟩, hE⟩
  rw [hty d hd] at hE
  exact ⟨⟨c0, hG⟩, hE⟩

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainBot_ofGF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainBot_ofGF

/-- info: 'Spike.Lib.LowerX64.mainBot_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainBot_seg

/-- info: 'Spike.Lib.LowerX64.mainBot_segK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainBot_segK

/-- info: 'Spike.Lib.LowerX64.mainBot_exitStk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainBot_exitStk
