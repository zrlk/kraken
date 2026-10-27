/-
**`scc_rt_main` after the setup block's return** (x86-64; the twin of
`Spike/Lib/Rt/A64MainS0.lean`): the tail of `mainS_segWSF`
(`Spike/Lib/Rt/X64MainSSF.lean`) from the marshalling block's node `mainS0`
at the empty frames: the marshalling block, the user function's call
(`call_nd_FWKSF`, at `MainCallWSF`) and the `exit_group` tail
(`xExitTail_segWSF`) at the frames of its return. The segment the setup
frame's bottom (`setupBot_seg`, `Spike/Lib/LowerX64/SetupBot.lean`) goes on
with after the setup call returns.

- `mainS0_segWSF`: from `mainS0` at `[]`, a segment to any `Q`.
-/
import Spike.Lib.Rt.X64MainSSF

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- `%rbp`'s offset moved by `8` with `%rsp`. -/
private theorem rbp_shiftS0 (r : BitVec 64) (z : Int) :
    r + BitVec.ofInt 64 (-8 - (-8 - z)) = r - 8#64 + BitVec.ofInt 64 (-8 - (-8 - z - 8)) := by
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  show r + y = r - 8#64 + (y + 8#64)
  bv_omega

/-- `%rbp` back at the saved `%rbp` after a call's return: the callee
restored `%rbp` and popped the return address. -/
private theorem rbp_retS0 {rbpC rspC rbpR rspR : BitVec 64} (z : Int)
    (hb : rbpC = rspC + BitVec.ofInt 64 (-8 - (-8 - z - 8))) (hbR : rbpR = rbpC) (hspR : rspR = rspC + 8#64) :
    rbpR = rspR + BitVec.ofInt 64 (-8 - (-8 - z)) := by
  rw [hbR, hspR, hb]
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  bv_omega

/-- **`scc_rt_main` from the marshalling block, at depth, its user function
returning at pending frames** (`mainS_segWSF`'s tail): the marshalling
block (`hsp0`, `MainSW.sp0`'s), `call fn` at `MainCallWSF` (`hU`,
`call_nd_FWKSF`) and the `exit_group` tail at the frames `fs` of the return
(`hWx` at every `fs`, `hexit` asking `MainExitFA` from them). -/
theorem mainS0_segWSF {W : FragS isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) {sc : SetupCode} (hin : mainSIn cells sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64}
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo2 : R.lo ≤ -8 - sc.Z.toInt - 8 - D2) (hhi : 0 ≤ R.hi)
    (g : MainG) (x0 : BitVec 64)
    (hlimU : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hU : MainCallWSF W K p lbl ms exe endPc R F sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec g.tp)
    (hexit : ∀ s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hsp0 : BlkW (nilW W) K exe endPc R F (mainS0R (_root_.Executable.labels exe).label sc PostS g x0)
      (marshal sc.sw sc.fn))
    (hWx : ∀ fs, XExitW (fun s c => W s c fs) K exe endPc R F
      (mainSRR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) (-8 - sc.Z.toInt) (-8) sc.k 4 4 5)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((At exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g x0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainSIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hb1⟩, hg1⟩, hex⟩ := hin
  have esp1 := label_labelGapB hp hg1
  have hloZ : R.lo ≤ -8 - sc.Z.toInt := by omega
  -- the marshalling block and `call fn`
  have h3 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainS0 lab sc PostS g x0))
      (At exe endPc R F (mainSM lab sc PostS g x0)) := by
    refine (seg_oneW (seg_ndW (n := mainS0R lab sc PostS g x0) (lo := -8 - sc.Z.toInt - 8) (hi := 0)
      (by simp [marshal, callB])
      (okBlk_marshal hsw _ (fun i hi => by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)) hF hR (by omega) hhi
      (code_field hp hend hb1 (ofNat_zero' _)) hsp0
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
        exact rbp_shiftS0 _ _
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
        exact rbp_retS0 sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))
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
  exact (SegWS.liftS [] h3 fun _ _ h => h).seq (h4.seq (h5.mono_post fun _ _ _ h => h.elim))

end Proof

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.mainS0_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainS0_segWSF

end Spike.Lib.X64.Rt
