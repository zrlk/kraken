/-
**`scc_rt_main` after the setup block's return** (AArch64): the tail of
`mainS_segWSF` (`Spike/Lib/Rt/A64MainSSF.lean`) from the marshalling
block's node `mainS0` at the empty frames: the marshalling block, the user
function's call (`call_nd_FWKSF`, at `MainCallWSF`) and the `exit_group`
tail (`exitTail_segWSF`) at the frames of its return. The segment the setup
frame's bottom (`setupBot_seg`, `Spike/Lib/LowerA64/SetupBot.lean`) goes on
with after the setup call returns.

- `mainS0_segWSF`: from `mainS0` at `[]`, a segment to any `Q`.
-/
import Spike.Lib.Rt.A64MainSSF

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

set_option linter.unusedSimpArgs false

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from the marshalling block, at depth, its user function
returning at pending frames** (`mainS_segWSF`'s tail): the marshalling
block (`hsp0`, `MainSW.sp0`'s), `bl fn` at `MainCallWSF` (`hU`,
`call_nd_FWKSF`) and the `exit_group` tail at the frames `fs` of the return
(`hWx` at every `fs`, `hexit` asking `MainExitFA` from them). -/
theorem mainS0_segWSF {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {sc : SetupCode} (hin : mainSIn prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64}
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo2 : R.lo ≤ -sc.Z.toInt - D2) (hhi : 0 ≤ R.hi) (g : MainG) (x0 : BitVec 64)
    (hlimU : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - sc.Z.toBitVec - ZU2.toBitVec))
    (hU : MainCallWSF W K p lbl ms exe endPc R F sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec g.tp)
    (hexit : ∀ s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hsp0 : BlkW (nilW W) K exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g x0)
      (marshal sc.sw sc.fn))
    (hWx : ∀ fs, ExitW (fun s c => W s c fs) K exe endPc R F
      (mainSR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) sc.k)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g x0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainSIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hb1⟩, hg1⟩, hex⟩ := hin
  have esp1 := label_labelGap hp hg1
  have hloZ : R.lo ≤ -sc.Z.toInt := by omega
  -- the marshalling block and `bl fn`
  have h3 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainS0 lab sc PostS g x0))
      (At exe endPc R F (mainSM lab sc PostS g x0)) := by
    refine seg_oneW (seg_ndW (by simp [marshal]) (okBlk_marshal (by omega) hsw _
        (fun i hi => by simp [Spike.Lib.offOk]; omega) (by simp [Spike.Lib.offOk]; omega))
      hF hR hal hloZ hhi (code_of hp hend hb1 (ofNat4_zero _)) hsp0
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
  -- the user function's call, returning at the frames `fs` the source has there
  have h4 : SegWS W K p lbl ms ((At exe endPc R F (mainSM lab sc PostS g x0)).at [])
      (fun s c fs => At exe endPc R F (mainSR lab sc (fun c v => Post c fs v)) s c) := by
    refine (call_nd_FWKSF (KC := False) (lo' := -D2) (hi' := 0) (M := fun _ => True)
      (N := fun fs (_ : Unit) => mainSR lab sc (fun c v => Post c fs v)) (E := fun _ (e : Empty) => e.elim)
      (Ne := uNM lab (ms []) F exe endPc sc.fn ZU2 (SetupArgs PostS sc.sw x0))
      (Ex := fun g fs (_ : Unit) => uNx (fun c v => Post c fs v) g)
      hR hal hF (by show R.lo ≤ -sc.Z.toInt + -D2; omega) (by omega) (by show -sc.Z.toInt < R.hi; omega)
      (by decide) (by show (-sc.Z.toInt) % 16 = 0; omega) (by omega) (by decide) (fun h => h.elim)
      (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hal' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, htp, h30⟩, ⟨⟨-, -, h30', -, htp'⟩, -⟩⟩ := hg'
        exact (hU F' hR' hal' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' (h30'.symm.trans h30)
          (htp'.symm.trans htp)).mono_post fun _ _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_).mono_post fun _ _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    · rintro σC c ⟨hA, hsp, htp, -⟩
      refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, c⟩, rfl,
        ⟨hA, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk (ms []) F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - ZU2.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' fs' x σC c σx c' σR ⟨-, -, -, h30⟩ ⟨⟨-, -, h30', -⟩, -⟩ ⟨hP, -, -⟩ hreg - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainSR, mainSM, uNx], ?_⟩
      · show lab sc.sp1 = Int64.ofBitVec g'.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, Spike.Lib.int64_ofBitVec_toBitVec]
      · show Post c' fs' σR.regs.X0.toBitVec
        rw [hreg]; exact hP
  -- the exit: `exit_group(v)` after the source's frame run back to depth 0
  have h5 : SegWS W K p lbl ms (fun s c fs => At exe endPc R F (mainSR lab sc (fun c v => Post c fs v)) s c)
      (fun _ _ _ => False) := by
    simp only [exitIn, Bool.and_eq_true] at hex
    refine (SegWS.exists_pre (P := fun fs => (At exe endPc R F (mainSR lab sc (fun c v => Post c fs v))).at fs)
      fun fs => ?_).mono_pre fun _ _ fs h => ⟨fs, h, rfl⟩
    refine exitTail_segWSF (n := mainSR lab sc (fun c v => Post c fs v)) hK hF hR hal (lo := -sc.Z.toInt) (hi := 0)
      hloZ hhi hk (by show (-sc.Z.toInt) % 16 = 0; omega) (code_of hp hend hex.1 (ofNat4_zero _))
      (code_of hp hend hex.2 (by simp only [ofNat4_succ, ofNat4_zero]; try rfl)) (hWx fs)
      fun s c σ0 hJ hAt => ?_
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
    exact exitGroup_of_mainExitFA (v := σ0.regs.X0.toBitVec.toNat)
      (hexit s c fs _ hJ ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.X0.toBitVec = _; rw [hx]⟩)
  exact (SegWS.liftS [] h3 fun _ _ h => h).seq (h4.seq (h5.mono_post fun _ _ _ h => h.elim))

end Proof

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.mainS0_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainS0_segWSF

end Spike.Lib.A64.Rt
