/-
**The setup function's return popped at a bottom key** (x86-64): the
step `setupBot_segM` (`Spike/Lib/LowerX64/SetupBotM.lean`) takes from the
setup function's exit to `scc_rt_main`'s node `mainS0`, as a statement of
its own: at a state of the key's exits (`ExitC2SL`'s return disjunct at a
`SetupBot` key), the key's frames are the setup call's one frame `fr`
(`CallTo` from the start control), the source pops it to a control `c''`
at no frame, and the same state is at `mainS0` at `c''` in `scc_rt_main`'s
region and frame condition. A `W2` at the popped pair (from `scc_rt_main`'s
segment) then gives the key's exits' `W2` (`w2_ofPopped`,
`Spike/Lib/LowerX64/W2Pop.lean`).

- `setupBot_popM`: the pop at a `SetupBot` key at any key memory side.

TODO: `setupBot_popM`'s proof duplicates `setupBot_segM`'s internals (and `rbp_retBotM`); factor the shared
return step out of both after the release.
-/
import Spike.Lib.LowerX64.SetupBotM

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (SetupCode mainSC mainS0 uN0 uNxS)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- `rbp` at the return to `mainS0` (a copy of `SetupBotM.lean`'s private
`rbp_retBotM`). -/
private theorem rbp_retBotP {rbpC rspC rbpR rspR : BitVec 64} (z : Int)
    (hb : rbpC = rspC + BitVec.ofInt 64 (-8 - (-8 - z - 8))) (hbR : rbpR = rbpC) (hspR : rspR = rspC + 8#64) :
    rbpR = rspR + BitVec.ofInt 64 (-8 - (-8 - z)) := by
  rw [hbR, hspR, hb]
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  bv_omega

/-- **The setup function's return popped at a `SetupBot` key** (at any key
memory side `ms0`): at a state `s` of the key's exits' return disjunct
(`hA`), the key's frames are one frame `fr` of the setup call from the
start control `g0.c0` (`CallTo`), the source runs from `(c, [fr])` to a
control `c''` at no frame (the pop `hPS` at `SRetR`), and `s` is at
`scc_rt_main`'s `mainS0` at `c''` in its region `R` and frame condition
`F` (`setupBot_segM`'s step to `h0`). -/
theorem setupBot_popM {sc : SetupCode} {ms0 : MemSide isa}
    {D1 : Int} {ZU1 : Int64} (hD10 : 0 ≤ D1) (hZ : 8 ≤ sc.Z.toInt) (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1)
    (hhi : 0 ≤ R.hi)
    {PostS : Ctl → Reg64s → Prop} {g0 : MainG} {x0 : BitVec 64} {ty : Ty} {k : StkKey}
    {fs : List TermRun.Frame} {c0 : Ctl}
    (hB : SetupBot p (_root_.Executable.labels exe).label ms0 R F sc D1 ZU1 g0 x0 k fs)
    (hPS : ∀ cE fr c rs, CallTo p g0.c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    {s : State} {c : Ctl}
    (hA : ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
      At exe endPc (rbR k.R) k.F ((retNSL p lbl k.fp k.ra c0' ty).withTp k.tp) s c) :
    ∃ cE fr c'', fs = [fr] ∧ CallTo p g0.c0 cE fr ∧ FrameRun p (c, [fr]) (c'', []) ∧
      At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g0 x0) s c'' := by
  obtain ⟨j, R', F', fp, ra, tp, G0⟩ := k
  obtain ⟨G, rfl, hR, hF, hfp, hra, htp, hbase⟩ := hB
  dsimp only at hR hF hfp hra htp hbase hA ⊢
  subst hR hF hfp hra htp
  let lab := (_root_.Executable.labels exe).label
  let FC := CallGF p R F (mainSC lab sc g0 x0) 0 (-D1) 8 (uN0 lab ms0 F sc.setup ZU1) G
  obtain ⟨c0', -, hA⟩ := hA
  have hA' := uPostSR_ret hbase rfl hA
  have hFC : FC s.st.1 := by
    obtain ⟨-, -, -, -, -, -, hF, -⟩ := hA'
    exact hF
  have hF : F s.st.1 := hFC.1
  have hCT : CallTo p g0.c0 G.2.2.2.1 G.2.2.2.2.1 := by
    obtain ⟨-, -, -, ⟨⟨hc, -⟩, -⟩, hCT, -⟩ := hFC
    exact hc ▸ hCT
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
      exact rbp_retBotP sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))
  obtain ⟨c'', hrun, hN⟩ := CallGF.ret (p := p) (exe := exe) (endPc := endPc) (R := R) (F := F)
    (N := fun _ : Unit => mainS0 lab sc PostS g0 x0) (E := fun e : Empty => e.elim)
    (nC := mainSC lab sc g0 x0) (e0 := 0) (lo' := -D1) (hi' := 8) (Ne := uN0 lab ms0 F sc.setup ZU1)
    (Ex := fun g (_ : Unit) => uNxS (SRetR lbl ty) g) (G := G) (x := ()) (fs := []) (F₂ := F) hret hA'' hF
  exact ⟨G.2.2.2.1, G.2.2.2.2.1, c'', rfl, hCT, hrun, hN.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim⟩

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.setupBot_popM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.setupBot_popM
