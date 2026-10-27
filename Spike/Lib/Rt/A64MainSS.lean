/-
**The AArch64 main thread `scc_rt_main` after a setup block, at depth**
(`mainS_segWS`): `mainS_segW` (`Spike/Lib/Rt/A64MainS.lean`) over segments
with frames (`SegWS`, `Spike/Lib/SegS.lean`), as `mainU_segWS`
(`Spike/Lib/Rt/A64SegsS.lean`) is `mainU_segW`'s, so that either callee may
itself call.

- **The callees are interfaces at depth** (`SetupCallWS`, `MainCallWS`):
  the setup block is an ordinary source call of `setupTerm`, its `SegWS` at
  the frame `[fr]` its call pushes (`CallTo`), its post `PostR` at its
  `ret`; the call is `call_ndS` (`mainSC_segWS`), the frame's pop from
  `PostR` to `PostS` a premise (`hPS`), as is `W` at the call node's pairs
  with the caller's control (`hWC`). The user function's `SegWS` is at `[]`
  (`main` is entered by a tail call).
- **The runtime's own pieces are the `SegW` ones, lifted** at `[]`
  (`SegWS.liftS`): the prologue, `bl setup` and the marshalling block, their
  obligations (`MainSW`) stated over `nilW W` under `ms []`. The user
  function's call is `call_nd_FWKS`, the `exit_group` tail `exitTail_segWS`.
- **`main`'s exit after its calls return** (`MainExitS`): as in
  `mainU_segWS`, `hexit` asks `main`'s exit after a frame run back to depth
  0, off an abort site; at one the `exit_group` is the abort's.
- **From `scc_rt_main`'s entry after the switch** (`mainES_segWS`): from
  `MainE` (`Spike/Lib/Rt/A64StartE.lean`, `startE_segWS`'s exit) at `[]`,
  `mainS_segWS` at every value of the new `sp`; from `_start` on
  (`startS_segWS`), `startE_segWS` then `mainES_segWS`.
-/
import Spike.Lib.Rt.A64MainS
import Spike.Lib.Rt.A64SegsS
import Spike.Lib.Rt.A64StartE

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## The interfaces at depth -/

/-- **The setup block called by `scc_rt_main`, as an interface at depth**:
`SetupCallW` with a segment with frames, the setup block an ordinary source
call (`setupTerm`'s `let r = call rodata … in …`): for every callee control
`g.c0` and frame `fr` the caller's control `c0` calls (`CallTo`), from its
entry to its return at the frames `[fr]`, its post `PostR` at the callee's
control there (the `ret` before the frame's pop). -/
def SetupCallWS (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isaLSE2)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (PostR : Ctl → Reg64s → Prop) (ra : BitVec 64) (c0 : Ctl)
    (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK → (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 →
    FStable (R.callee (-Z.toInt) (-D) 0) F' → (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
    ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ra → g.tp = tp → CallTo p c0 g.c0 fr →
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU g)).at [fr])
        ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (uNxS PostR g)).at [fr])

/-- **The user function called after the setup block, as an interface at
depth**: `MainCallW` with a segment with frames, from its entry to its
return at the empty frames. -/
def MainCallWS (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isaLSE2)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Pre : Ctl → Reg64s → Prop) (Post : Ctl → BitVec 64 → Prop)
    (ra : BitVec 64) (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK → (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 →
    FStable (R.callee (-Z.toInt) (-D) 0) F' → (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
    ∀ g : WcG, g.ra = ra → g.tp = tp →
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (uNM (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU Pre g)).at [])
        ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (uNx Post g)).at [])

/-- A call-free user interface is one at depth (lifted at `[]`). -/
theorem MainCallW.toS {W : FragS isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {Pre : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    {ra : BitVec 64} {tp : UInt64} (h : MainCallW (nilW W) K p lbl (ms []) exe endPc R F fn Z D ZU Pre Post ra tp) :
    MainCallWS W K p lbl ms exe endPc R F fn Z D ZU Pre Post ra tp :=
  fun F' hR hal hF hFF g hra htp => SegWS.liftS [] (h F' hR hal hF hFF g hra htp) fun _ _ h => h

/-! ## The segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`bl setup` as a source call, at depth** (the setup block an ordinary
call of `setupTerm`): from `mainSC` (at `setup`'s label, `x30` the return
address `sp0`, the caller's control `g.c0`) at the empty frames to `mainS0`
(back at `sp0`) there, by `call_ndS`: the callee's segment at the frame
`fr` the caller's control pushes (`hS`, its post `PostR` at the callee's
`ret`), the call a source call (`hcall`), the frame's pop from `PostR` to
`PostS` (`hPS`), `W` at the call node's pairs (`hWC`, the caller's control
at the callee's entry). -/
theorem mainSC_segWS {W : FragS isaLSE2} {K : State → State → Prop} {sc : SetupCode} {D1 : Int}
    (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) {ZU1 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo1 : R.lo ≤ -sc.Z.toInt - D1) (hhi : 0 ≤ R.hi) (g : MainG) (x0 : BitVec 64)
    (hlimS : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - sc.Z.toBitVec - ZU1.toBitVec))
    (hS : SetupCallWS W K p lbl ms exe endPc R F sc.setup sc.Z D1 ZU1 PostR
      ((_root_.Executable.labels exe).label sc.e0 + 4).toBitVec g.c0 g.tp)
    (hcall : ∃ cE fr, CallTo p g.c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p g.c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ s c, At exe endPc R F (mainSC (_root_.Executable.labels exe).label sc g x0) s c → W s c [])
    (esp0 : (_root_.Executable.labels exe).label sc.sp0 = (_root_.Executable.labels exe).label sc.e0 + 4) :
    SegWS W K p lbl ms ((At exe endPc R F (mainSC (_root_.Executable.labels exe).label sc g x0)).at [])
      ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g x0)).at []) := by
  let lab := (_root_.Executable.labels exe).label
  refine seg_oneWS (call_ndS (KC := False) (lo' := -D1) (hi' := 0) (M := fun _ => True)
    (Ne := uN0 lab (ms []) F exe endPc sc.setup ZU1) (Ex := fun g _ => uNxS PostR g)
    hR hal hF (by show R.lo ≤ -sc.Z.toInt + -D1; omega) (by omega) (by show -sc.Z.toInt < R.hi; omega)
    (by decide) (by show (-sc.Z.toInt) % 16 = 0; omega) (by omega) (by decide) (fun h => h.elim)
    (fun h => h.elim) (fun _ h _ => h) hWC
    (fun R' F' hR' hal' _ _ hF' _ hFF hR'e hcc g' fr hg' _ => by
      subst hR'e
      obtain ⟨σC, c, cE, ⟨⟨hc, -, htp, -⟩, h30⟩, hCT, ⟨⟨hc', -, h30', -, htp'⟩, -⟩⟩ := hg'
      subst hc hc'
      exact (hS F' hR' hal' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' fr (h30'.symm.trans h30)
        (htp'.symm.trans htp) hCT).mono_post fun _ _ _ h => ⟨⟨(), h.1, trivial⟩, h.2⟩)
    (fun _ => rfl) ?_ ?_)
  · rintro σC c ⟨⟨rfl, hsp, htp, -⟩, h30⟩
    obtain ⟨cE, fr, hCT⟩ := hcall
    refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, cE⟩, cE, fr, hCT, rfl,
      ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
    show LimOk (ms []) F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - ZU1.toBitVec)
    rw [hsp]; exact hlimS
  · rintro g' x σC c cE fr σx c' σR ⟨⟨rfl, hsp, htp, hsl⟩, h30⟩ hCT ⟨⟨-, -, h30', hsp', htp'⟩, -⟩
      ⟨hP, -, -, hspx, htpx⟩ hreg - hslot
    obtain ⟨c'', hrun, hP''⟩ := hPS cE fr c' σx.regs hCT hP
    refine ⟨c'', hrun, .inl ⟨(), ?_, by simp [SO.le, mainS0, mainSC, uNxS], ?_⟩⟩
    · show lab sc.sp0 = Int64.ofBitVec g'.ra
      rw [← h30']
      show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [h30, Spike.Lib.int64_ofBitVec_toBitVec]; exact esp0
    · show PostS c'' σR.regs ∧ σR.regs.SP.toBitVec = g.sp0 - sc.Z.toBitVec ∧ σR.regs.TPIDR_EL0 = g.tp ∧
        σR.slot (-sc.Z.toInt) = x0
      rw [hreg]
      refine ⟨hP'', hspx.trans (hsp'.symm.trans hsp), htpx.trans (htp'.symm.trans htp), ?_⟩
      · rw [hslot (-sc.Z.toInt) ⟨by omega, by omega, by omega⟩
          (by simp only [mainSC, Spike.Lib.Region.Off, Spike.Lib.Region.callee]; omega)]
        exact hsl

/-- **`scc_rt_main` from the setup block's return on, at depth** (the tail
of `mainS_segWS`): from `mainS0` (back past `bl setup`, `PostS` at the
source control) at the empty frames to nothing: the marshalling block and
`bl fn` (`SegW`, lifted at `[]`), the user function's call
(`call_nd_FWKS` at `hU`), the `exit_group` tail (`hexit` as
`mainS_segWS`'s). At any labels `lbl` and memory side `ms`: the segment
after a landing in the setup block resumes here at the landing's placement.
The code facts are `mainSIn`'s last three conjuncts. -/
theorem mainS0_segWS {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {sc : SetupCode}
    (hb1 : blockAt prog sc.sp0 0 (marshal sc.sw sc.fn) = true)
    (hg1 : labelGap prog sc.sp0 sc.sp1 (2 * sc.sw + 2) = true) (hex : exitIn prog sc.sp1 sc.k = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64}
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo2 : R.lo ≤ -sc.Z.toInt - D2) (hhi : 0 ≤ R.hi) (g : MainG) (x0 : BitVec 64)
    (hlimU : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - sc.Z.toBitVec - ZU2.toBitVec))
    (hU : MainCallWS W K p lbl ms exe endPc R F sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hW : MainSW (nilW W) K exe endPc R F (ms []) sc PostS Post g x0)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g x0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  have esp1 := label_labelGap hp hg1
  have hloZ : R.lo ≤ -sc.Z.toInt := by omega
  -- the marshalling block and `bl fn`
  have h3 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainS0 lab sc PostS g x0))
      (At exe endPc R F (mainSM lab sc PostS g x0)) := by
    refine seg_oneW (seg_ndW (by simp [marshal]) (okBlk_marshal (by omega) hsw _
        (fun i hi => by simp [Spike.Lib.offOk]; omega) (by simp [Spike.Lib.offOk]; omega))
      hF hR hal hloZ hhi (code_of hp hend hb1 (ofNat4_zero _)) hW.sp0
      fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [mainS0, mainSM]; rw [marshal_run]
    · dsimp only [mainS0, mainSM]; rw [marshal_run]; simp [SO.le]
    · dsimp only [mainS0, mainSM] at hJ ⊢; rw [marshal_run]
      obtain ⟨hP, hsp, htp, hsl⟩ := hJ
      obtain ⟨hr, hx⟩ := marshal_regs hsw (-sc.Z.toInt) (σ.slot) σ.regs
      refine ⟨⟨σ.regs, hP, fun i hi => ?_, ?_⟩, ?_, ?_, ?_⟩
      · simp only [Reg64s.getXReg_setXReg, argX_ne_X30 i (by omega), ite_false]; exact hr i hi
      · simp only [Reg64s.getXReg_setXReg, argX_ne_X30 _ (by omega : sc.sw < 8), ite_false, hx, hsl]
      · simp only [Reg64s.SP_setXReg, setWords_SP]; exact hsp
      · simp only [setXReg_TPIDR, setWords_TPIDR]; exact htp
      · simp only [Reg64s.X30_setXReg, ↓reduceIte, UInt64.toBitVec_ofBitVec]
        exact congrArg Int64.toBitVec esp1.symm
  -- the user function's call
  have h4 : SegWS W K p lbl ms ((At exe endPc R F (mainSM lab sc PostS g x0)).at [])
      ((At exe endPc R F (mainSR lab sc Post)).at []) := by
    refine seg_oneWS (call_nd_FWKS (KC := False) (lo' := -D2) (hi' := 0) (M := fun _ => True)
      (Ne := uNM lab (ms []) F exe endPc sc.fn ZU2 (SetupArgs PostS sc.sw x0)) (Ex := fun g _ => uNx Post g)
      hR hal hF (by show R.lo ≤ -sc.Z.toInt + -D2; omega) (by omega) (by show -sc.Z.toInt < R.hi; omega)
      (by decide) (by show (-sc.Z.toInt) % 16 = 0; omega) (by omega) (by decide) (fun h => h.elim)
      (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hal' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, htp, h30⟩, ⟨⟨-, -, h30', -, htp'⟩, -⟩⟩ := hg'
        exact (hU F' hR' hal' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' (h30'.symm.trans h30)
          (htp'.symm.trans htp)).mono_post fun _ _ _ h => ⟨⟨(), h.1, trivial⟩, h.2⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨hA, hsp, htp, -⟩
      refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, c⟩, rfl,
        ⟨hA, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk (ms []) F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - ZU2.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' x σC c σx c' σR ⟨-, -, -, h30⟩ ⟨⟨-, -, h30', -⟩, -⟩ ⟨hP, -, -⟩ hreg - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainSR, mainSM, uNx], ?_⟩
      · show lab sc.sp1 = Int64.ofBitVec g'.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, Spike.Lib.int64_ofBitVec_toBitVec]
      · show Post c' σR.regs.X0.toBitVec
        rw [hreg]; exact hP
  -- the exit: `exit_group(v)` after the source's frame run back to depth 0
  have h5 : SegWS W K p lbl ms ((At exe endPc R F (mainSR lab sc Post)).at []) (fun _ _ _ => False) := by
    simp only [exitIn, Bool.and_eq_true] at hex
    refine exitTail_segWS (n := mainSR lab sc Post) hK hF hR hal (lo := -sc.Z.toInt) (hi := 0)
      hloZ hhi hk (by show (-sc.Z.toInt) % 16 = 0; omega) (code_of hp hend hex.1 (ofNat4_zero _))
      (code_of hp hend hex.2 (by simp only [ofNat4_succ, ofNat4_zero]; try rfl)) hW.exit fun s c σ0 hJ hAt => ?_
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
    by_cases hab : (ms []).abortAt s
    · exact ⟨c, .refl _, SysOk.exitGroup_abort hab⟩
    · obtain ⟨c', hr, hx'⟩ := hexit s c _ hJ ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.X0.toBitVec = _; rw [hx]⟩ hab
      exact ⟨c', hr, SysOk.exitGroup_main (v := σ0.regs.X0.toBitVec.toNat) fun _ => hx'⟩
  exact (SegWS.liftS [] h3 fun _ _ h => h).seq (h4.seq (h5.mono_post fun _ _ _ h => h.elim))

/-- **`scc_rt_main` after a setup block does not return, at depth**
(`mainS_segW` with both callees interfaces at depth): its prologue, `bl
setup`, the marshalling block and the `exit_group` tail are `mainS_segW`'s,
lifted at the empty frames; the calls are `call_nd_FWKS`; `hexit` asks
`main`'s exit after a frame run back to depth 0 (`MainExitS`), off an abort
site. -/
theorem mainS_segWS {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {sc : SetupCode} (hin : mainSIn prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo1 : R.lo ≤ -sc.Z.toInt - D1) (hlo2 : R.lo ≤ -sc.Z.toInt - D2) (hhi : 0 ≤ R.hi) (g : MainG) (x0 : BitVec 64)
    (hlimM : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - sc.Z.toBitVec - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - sc.Z.toBitVec - ZU2.toBitVec))
    (hS : SetupCallWS W K p lbl ms exe endPc R F sc.setup sc.Z D1 ZU1 PostR
      ((_root_.Executable.labels exe).label sc.e0 + 4).toBitVec g.c0 g.tp)
    (hcall : ∃ cE fr, CallTo p g.c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p g.c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ s c, At exe endPc R F (mainSC (_root_.Executable.labels exe).label sc g x0) s c → W s c [])
    (hU : MainCallWS W K p lbl ms exe endPc R F sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hW : MainSW (nilW W) K exe endPc R F (ms []) sc PostS Post g x0)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((At exe endPc R F (mainSN0 (_root_.Executable.labels exe).label g x0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainSIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hpro, hb0⟩, hg0⟩, hb1⟩, hg1⟩, hex⟩ := hin
  have esp0 := label_labelGap hp hg0
  have hloZ : R.lo ≤ -sc.Z.toInt := by omega
  -- the prologue and `bl setup`
  have h1 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainSN0 lab g x0))
      (At exe endPc R F (mainSC lab sc g x0)) := by
    refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainS1 lab sc g x0) h16 hZ hF hR hal hloZ hhi
      (by simp [Spike.Lib.offOk]; omega) rfl (by simp [SO.le, oFr, mainS1]) hW.pro ?_) ?_
    · rintro σ c ⟨⟨rfl, hsp, htp⟩, hx⟩
      rw [tcbA_limA htp]
      refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr hs => ⟨rfl, ?_, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlimM.room v hv
      · rw [hr]; simp [frRegs, ldStep, chkRegs, hsp]
      · rw [hr]; simp [frRegs, ldStep, chkRegs, setXReg_TPIDR, htp]
      · rw [hs, hr]; simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, hx]
    · refine seg_oneW (seg_ndW (by simp) (okBlk_blD _ _ _ _) hF hR hal hloZ hhi
        (code_of hp hend hb0 (ofNat4_zero _)) hW.call0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
      · dsimp only [mainS1, mainSC]; rw [blD_run]
      · dsimp only [mainS1, mainSC]; rw [blD_run]; simp [SO.le]
      · dsimp only [mainS1, mainSC] at hJ ⊢; rw [blD_run]
        obtain ⟨rfl, hsp, htp, hsl⟩ := hJ
        exact ⟨⟨rfl, hsp, htp, hsl⟩, rfl⟩
  -- the setup block's call
  have h2 := mainSC_segWS (lbl := lbl) (ms := ms) hD10 hD18 h16 hZ hF hR hal hlo1 hhi g x0 hlimS hS hcall hPS hWC
    esp0
  exact (SegWS.liftS [] h1 fun _ _ h => h).seq (h2.seq (mainS0_segWS hp hend hb1 hg1 hex h16 hZ
    hsw hZw hk hD20 hD28 hK hF hR hal hlo2 hhi g x0 hlimU hU hexit hW))

/-- **From `scc_rt_main`'s entry after the switch, at depth** (`MainE`,
`Spike/Lib/Rt/A64StartE.lean`, to any fragment): `mainS_segWS` in the new
region of depth `L` at every value `v` of the new `sp`, under `swFSL`, the
ghosts the new stack's top `top`, the thread pointer `tcb` and the source
control `c0`, `x0` the thread pointer. The frame and either callee's fit in
the new region (`hL1`, `hL2`); the limit word is off it (`hfit`, `hout`);
the limit word's facts (`hlimM`, `hlimS`, `hlimU`) at any frame condition
(only their memory side's parts are used). -/
theorem mainES_segWS {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {sc : SetupCode} (hin : mainSIn prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop} {rS : Scc.Sem.Range} {L : Int}
    (hL1 : sc.Z.toInt + D1 ≤ L) (hL2 : sc.Z.toInt + D2 ≤ L)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec tcb)) (top - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec tcb)) (top - sc.Z.toBitVec - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec tcb)) (top - sc.Z.toBitVec - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWS W K p lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      sc.setup sc.Z D1 ZU1 PostR ((_root_.Executable.labels exe).label sc.e0 + 4).toBitVec c0 (UInt64.ofBitVec tcb))
    (hcall : ∃ cE fr, CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, At exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      (mainSC (_root_.Executable.labels exe).label sc ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb) s c → W s c [])
    (hU : ∀ v, MainCallWS W K p lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw tcb) Post ((_root_.Executable.labels exe).label sc.sp1).toBitVec
      (UInt64.ofBitVec tcb))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hW : ∀ v, MainSW (nilW W) K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) (ms [])
      sc PostS Post ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((MainE exe endPc rS tcb top c0 L).at []) Q := by
  let a := limA (UInt64.ofBitVec tcb)
  refine (SegWS.exists_pre (P := fun g : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK} =>
      (At exe endPc (swR g.1 (-L) 0) (swFSL L rS top a g.1)
        (mainSN0 (_root_.Executable.labels exe).label ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb)).at [])
    fun g => ?_).mono_pre fun _ _ _ ⟨⟨v, h1, h2, hA⟩, e⟩ => ⟨⟨v, h1, h2⟩, hA, e⟩
  obtain ⟨v, hv, hR⟩ := g
  have hF2 : FStable (swR v (-L) 0) (swFSL L rS top a v) := fun m m' h hd =>
    ⟨swF_stableL hfit hout m m' h.1 hd, stackOff_stable hfitS m m' h.2 hd⟩
  exact mainS_segWS hp hend hin h16 hZ hsw hZw hk hD10 hD18 hD20 hD28 hK hF2 hR hv
    (show -L ≤ -sc.Z.toInt - D1 by omega) (show -L ≤ -sc.Z.toInt - D2 by omega) (Int.le_refl _)
    ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb ⟨hlimM.rt, hlimM.mp, fun _ h => h.1.2, hlimM.room⟩
    ⟨hlimS.rt, hlimS.mp, fun _ h => h.1.2, hlimS.room⟩ ⟨hlimU.rt, hlimU.mp, fun _ h => h.1.2, hlimU.room⟩
    (hS v) hcall hPS (hWC v) (hU v) (fun s c x hP hAt => hexit _ _ s c x hP hAt) (hW v)

/-- **The program after a setup block never returns, at depth, from
`_start`** (`startE_segWS` then `mainES_segWS`): from `entryN` at the empty
frames to any fragment, the take its outside move; `startE_segWS`'s premises
(the runtime's code but `scc_rt_main`'s, `RtCodeIn0`) and `mainES_segWS`'s
at the new stack's top and the thread pointer `startE_segWS` reaches. -/
theorem startS_segWS {W : FragS isaLSE2} {rS : Scc.Sem.Range} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hc : RtCodeIn0 prog) {L : Int}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0)
      (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hk0 : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
    (h16t : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hWE : StartEW (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F rS n0 k0 c0 L)
    {sc : SetupCode} (hin : mainSIn prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hL1 : sc.Z.toInt + D1 ≤ L) (hL2 : sc.Z.toInt + D2 ≤ L) {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - sc.Z.toBitVec - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - sc.Z.toBitVec - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      (swR v (-L) 0) (swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v)
      sc.setup sc.Z D1 ZU1 PostR ((_root_.Executable.labels exe).label sc.e0 + 4).toBitVec c0
      (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
    (hcall : ∃ cE fr, CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, At exe endPc (swR v (-L) 0)
      (swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v)
      (mainSC (_root_.Executable.labels exe).label sc ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
        UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)) s c → W s c [])
    (hU : ∀ v, MainCallWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      (swR v (-L) 0) (swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (pinA (_root_.Executable.labels exe).label + n0 + 8#64)) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec
      (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hW : ∀ v, MainSW (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      (swR v (-L) 0) (swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v) (ms [])
      sc PostS Post ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
        UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
      (pinA (_root_.Executable.labels exe).label + n0 + 8#64))
    {Q : FragS isaLSE2} :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN (_root_.Executable.labels exe).label c0)).at []) Q :=
  (startE_segWS hp hend hc hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk0 hfld htk h16t hok hsub hfit hout hun hRS
    hfitS houtS hFt hWE).seq
    (mainES_segWS hp hend hin h16 hZ hsw hZw hk hD10 hD18 hD20 hD28 hL1 hL2 hK _ _ c0 hfitS hfit hout hlimM hlimS
      hlimU hS hcall hPS hWC hU hexit hW)

end Proof

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.mainSC_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSC_segWS

/-- info: 'Spike.Lib.A64.Rt.mainS0_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainS0_segWS

/-- info: 'Spike.Lib.A64.Rt.mainS_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainS_segWS

/-- info: 'Spike.Lib.A64.Rt.mainES_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainES_segWS

/-- info: 'Spike.Lib.A64.Rt.startS_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startS_segWS

end Spike.Lib.A64.Rt
