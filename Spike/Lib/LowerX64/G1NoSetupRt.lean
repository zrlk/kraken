/-
**`scc_rt_main` without a setup block, at depth, its user function
returning at pending frames** (x86-64): `mainU_segWS`
(`Spike/Lib/Rt/X64SegsS.lean`) with the user function's return at whatever
frames the source has there, as `mainS_segWSF`
(`Spike/Lib/Rt/X64MainSSF.lean`) does after a setup block. A source held
back at a callee's `ret` (e.g. `print`'s `ret ()` at `[printFrame]`) is
still at depth when the machine returns from `main` and reaches
`exit_group`; the frame run back to depth 0 is taken by the `exit_group`
row (`xExitTail_segWSF`). The twin of `Spike/Lib/LowerA64/G1NoSetupRt.lean`.

- `UserCallWSF`: `UserCallWS` with its return at `NxF` (the entry at `[]`);
- `mainU_segWSF`: `mainU_segWS` at `UserCallWSF`; the user function's call
  is `call_nd_FWKSF`, the `exit_group` tail `xExitTail_segWSF` at the
  frames of the return, its obligation `hWx` at every frames; `hexit` asks
  `MainExitFA` from the frames;
- `mainEUF_segWSF`: from `MainEF` (`scc_rt_main`'s entry after the switch,
  in `call scc_rt_main`'s callee region, under the extra frame
  `Fw ∧ swFSL …`) on;
- `startUF_segWSF`: from `_start` (`startEF_segWS` then `mainEUF_segWSF`).

Where x86-64 differs from AArch64: `scc_rt_main` is entered by a `call`, so
its region is `MainEF`'s callee region of the switch region (`8` below the
new top, the caller's cells `CallerCells`) and its ghosts' `sp0` is
`top - 8`; the user function's callee region is `8` below the frame of `Z`
under the saved `%rbp`, the return address's cell included.
-/
import Spike.Lib.Rt.X64MainSSF
import Spike.Lib.Rt.X64StartEF

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The interface returning at pending frames -/

/-- **The user function called by `scc_rt_main` without a setup block,
returning at pending frames**: `UserCallWS` with its return at `NxF`. -/
def UserCallWSF (W : FragS isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isa)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Post : Ctl → List TermRun.Frame → BitVec 64 → Prop)
    (ra : BitVec 64) (c0 : Ctl) (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
    FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
    (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
    ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
          (uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g)).at [])
        (NxF exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' Post g)

/-! ## The segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- `%rbp`'s offset moved by `8` with `%rsp`. -/
private theorem rbp_shiftUF (r : BitVec 64) (z : Int) :
    r + BitVec.ofInt 64 (-8 - (-8 - z)) = r - 8#64 + BitVec.ofInt 64 (-8 - (-8 - z - 8)) := by
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  show r + y = r - 8#64 + (y + 8#64)
  bv_omega

/-- `%rbp` back at the saved `%rbp` after a call's return: the callee
restored `%rbp` and popped the return address. -/
private theorem rbp_retUF {rbpC rspC rbpR rspR : BitVec 64} (z : Int)
    (hb : rbpC = rspC + BitVec.ofInt 64 (-8 - (-8 - z - 8))) (hbR : rbpR = rbpC) (hspR : rspR = rspC + 8#64) :
    rbpR = rspR + BitVec.ofInt 64 (-8 - (-8 - z)) := by
  rw [hbR, hspR, hb]
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  bv_omega

/-- **`scc_rt_main` without a setup block does not return, at depth, its
user function returning at pending frames** (`mainU_segWS` at
`UserCallWSF`): its prologue and `call fn` are `mainU_segWS`'s; the user
function's call is `call_nd_FWKSF`, the `exit_group` tail
`xExitTail_segWSF` at the frames `fs` of the return (`hWx` at every `fs`);
`hexit` asks `MainExitFA` from those frames. -/
theorem mainU_segWSF {W : FragS isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) {mc : MainCode} (hin : mainUIn cells mc = true)
    (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - mc.Z.toInt - 8 - D) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - mc.Z.toBitVec - 8#64 - 8#64 - ZU.toBitVec))
    (hU : UserCallWSF W K p lbl ms exe endPc R F mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.sp0).toBitVec g.c0 g.tp)
    (hexit : ∀ s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        MainExitFA p (ms []) s c fs v.toNat)
    (hW : MainUW (nilW W) K exe endPc R F (ms []) mc (fun c v => Post c [] v) g)
    (hWx : ∀ fs, XExitW (fun s c => W s c fs) K exe endPc R F
      (mainURR (_root_.Executable.labels exe).label mc (fun c v => Post c fs v)) (-8 - mc.Z.toInt) (-8)
      mc.k mc.ze0 mc.ze1 mc.ze2)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainUIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hpro, hblk⟩, hgap⟩, hex⟩ := hin
  have esp0 := label_labelGapB hp hgap
  have hloZ : R.lo ≤ -8 - mc.Z.toInt := by omega
  -- the prologue and `call fn`
  have h1 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainN0 lab g)) (At exe endPc R F (mainUC lab mc g)) := by
    refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainU1 lab mc g) hZ hF hR hloZ hhi hps rfl
      (by simp [SO.le, lk, mainU1]) hW.pro ?_) ?_
    · -- the prologue
      rintro σ c ⟨rfl, hsp, htp⟩
      have ha : σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA g.tp := by rw [limA, htp]
      rw [ha]
      refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr _ => ⟨rfl, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlimM.room v hv
      · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
      · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
    · -- `call fn`
      refine (seg_oneW (seg_ndW (n := mainU1R lab mc g) (lo := -8 - mc.Z.toInt - 8) (hi := 0) (by simp [callB])
        (okBlk_callB _ (by simp [Spike.Lib.offOk, mainU1R]; omega)) hF hR (by omega) hhi
        (code_field hp hend hblk (ofNat_zero' _)) hW.call
          fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
        fun _ _ h => Ret0.At.rbp_get rfl h
      · dsimp only [mainU1R, mainUC]; rw [callB_run]
      · dsimp only [mainU1R, mainUC]; rw [callB_run]; simp [SO.le]
      · dsimp only [mainU1R, mainU1, mainUC] at hJ ⊢; rw [callB_run]
        obtain ⟨⟨rfl, hsp, htp⟩, hb⟩ := hJ
        refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
        · simp [Reg64s.set64, hsp]
        · simp [Reg64s.set64, htp]
        · simp only [Spike.Lib.upd_apply, ↓reduceIte]
          rw [show lab mc.sp0 = _ from esp0]; rfl
        · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]
          exact rbp_shiftUF _ _
  -- the user function's call, returning at the frames `fs` the source has there
  have h2 : SegWS W K p lbl ms ((At exe endPc R F (mainUC lab mc g)).at [])
      (fun s c fs => At exe endPc R F (mainUR lab mc (fun c v => Post c fs v)) s c) := by
    refine (call_nd_FWKSF (KC := False) (e0 := 0) (lo' := -D) (hi' := 8) (M := fun _ => True)
      (N := fun fs (_ : Unit) => mainUR lab mc (fun c v => Post c fs v)) (E := fun _ (e : Empty) => e.elim)
      (Ne := uN0 lab (ms []) F mc.fn ZU)
      (Ex := fun g fs (_ : Unit) => uNx (fun c v => Post c fs v) g)
      hR hF (by show R.lo ≤ -8 - mc.Z.toInt - 8 - 0 + -D; omega) (by omega)
      (by show -8 - mc.Z.toInt - 8 - 0 < R.hi; omega) (by show -8 - mc.Z.toInt - 8 - 0 + 8 ≤ R.hi; omega)
      (by show (-8 - mc.Z.toInt - 8 - 0) % 8 = 0; omega) (by omega) (by decide)
      (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨hc, -, htp⟩, hsl, -⟩, ⟨⟨hc', -, hra, -, htp'⟩, -⟩⟩ := hg'
        have hr : g'.ra = (lab mc.sp0).toBitVec := by
          rw [← hra, ← hsl]; show σC.slot (-8 - mc.Z.toInt - 8 - 0 + 0) = _; congr 1; omega
        exact (hU F' hR' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' hr (hc'.symm.trans hc)
          (htp'.symm.trans htp)).mono_post fun _ _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_).mono_post fun _ _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, -, -⟩
      refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-8 - mc.Z.toInt - 8 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk (ms []) F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - ZU.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' fs' x σC c σx c' σR ⟨-, hsl, hb⟩ ⟨⟨-, hfp, hra, hsp, -⟩, -⟩ ⟨hP, hb', hsp'⟩ hregs - - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainUR, mainUC, uNx], by rw [hregs]; exact hP, ?_⟩
      · show lab mc.sp0 = Int64.ofBitVec g'.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-8 - mc.Z.toInt - 8 - 0 + 0))
        rw [show -8 - mc.Z.toInt - 8 - 0 + 0 = -8 - mc.Z.toInt - 8 by omega, hsl, int64_ofBitVec_toBitVec]
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - mc.Z.toInt))
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        exact rbp_retUF mc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))
  -- the exit: `exit_group(v)` after the source's frame run back to depth 0, from the frames `fs` the
  -- source has at the return
  have h3 : SegWS W K p lbl ms (fun s c fs => At exe endPc R F (mainUR lab mc (fun c v => Post c fs v)) s c)
      (fun _ _ _ => False) := by
    simp only [exitIn, Bool.and_eq_true] at hex
    refine (SegWS.exists_pre (P := fun fs => (At exe endPc R F (mainURR lab mc (fun c v => Post c fs v))).at fs)
      fun fs => ?_).mono_pre fun _ _ fs h => ⟨fs, At.rbp h fun _ _ h => h.2, rfl⟩
    refine xExitTail_segWSF (lo := -8 - mc.Z.toInt) (hi := 0) (n := mainURR lab mc (fun c v => Post c fs v)) rfl hK
      hF hR hloZ hhi hk (code_field hp hend hex.1 (ofNat_zero' _))
      (code_field hp hend hex.2 (by rw [ofNat_add', ofNat_add']; rfl)) (hWx fs).w0 (hWx fs).w1
      fun s c σ0 hJ0 hs => ?_
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hs
    exact exitGroup_of_mainExitFA
      (hexit s c fs _ hJ0.1 ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.rdi.toBitVec = _; rw [hx]⟩)
  exact (SegWS.liftS [] h1 fun _ _ h => h).seq (h2.seq (h3.mono_post fun _ _ _ h => h.elim))

/-- **`scc_rt_main` without a setup block from its entry after the switch,
at depth, the user function returning at pending frames, with the extra
frame `Fw`** (`mainU_segWSF` at `MainEF`): for every value of the new
`%rsp`, in `call scc_rt_main`'s callee region inside the new region of
depth `L` (`mainEF_ok`), the ghosts `top - 8`, the thread pointer and `c0`;
the limit word's facts for any frame condition `F₀` (its unmapped clause
the switch's). -/
theorem mainEUF_segWSF {W : FragS isa} {K : State → State → Prop} {rS : Scc.Sem.Range} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {mc : MainCode} (hin : mainUIn cells mc = true)
    (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    {L : Int} (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    {Fw : _root_.Mem 64 → Prop}
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m))
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F₀ (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec - 8#64 - 8#64 - ZU.toBitVec))
    (hU : ∀ v, UserCallWSF W K p lbl ms exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      mc.fn mc.Z D ZU Post ((_root_.Executable.labels exe).label mc.sp0).toBitVec c0 (tpOf tcb))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainUW (nilW W) K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (ms []) mc (fun c v => Post c [] v) ⟨top - 8#64, tpOf tcb, c0⟩)
    (hWx : ∀ v fs, XExitW (fun s c => W s c fs) K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainURR (_root_.Executable.labels exe).label mc (fun c v => Post c fs v)) (-8 - mc.Z.toInt) (-8)
      mc.k mc.ze0 mc.ze1 mc.ze2)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((MainEF exe endPc Fw rS tcb top c0 L).at []) Q := by
  refine (SegWS.exists_pre (P := fun g : {v : BitVec 64 // (swR v (-L) 0).OK} =>
      (At exe endPc ((swR g.1 (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) g.1 m) ∧
          CallerCells (swR g.1 (-L) 0) (-8 - 0) (8 - L) 8 m)
        (mainN0 (_root_.Executable.labels exe).label ⟨top - 8#64, tpOf tcb, c0⟩)).at [])
    fun g => ?_).mono_pre fun _ _ _ ⟨⟨v, h1, he, hn, hdc, hpc, σ, hA, hD, hJ⟩, e⟩ =>
      ⟨⟨v, h1⟩, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ.1⟩, e⟩
  obtain ⟨v, hv⟩ := g
  obtain ⟨hR, hF⟩ := mainEF_ok (rS := rS) (tcb := tcb) (top := top) (by omega) hL8 hv (hFwS v)
  have hun : ∀ m, ((Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧
      CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
      Mem.loadInt m.dmem (limA (tpOf tcb)) 8 = none := fun _ h => h.1.2.1.2
  exact mainU_segWSF hp hend hin hZ hZ8 hps hk hD0 hD8 hK hF hR
    (show 8 - L ≤ -8 - mc.Z.toInt - 8 - D by omega) (show (0 : Int) ≤ 8 by decide) ⟨top - 8#64, tpOf tcb, c0⟩
    ⟨hlimM.rt, hlimM.mp, hun, hlimM.room⟩ ⟨hlimU.rt, hlimU.mp, hun, hlimU.room⟩ (hU v)
    (fun s c fs x hP hAt => hexit _ _ s c fs x hP hAt) (hW v) (hWx v)

/-- **The program without a setup block never returns, at depth, from
`_start`, the user function returning at pending frames, with the extra
frame `Fw` after the switch** (`startEF_segWS` then `mainEUF_segWSF`). -/
theorem startUF_segWSF {W : FragS isa} {rS : Scc.Sem.Range} {kp : Nat}
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
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    {Fw : _root_.Mem 64 → Prop} (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧
      swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m))
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hWE : StartEWF (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F Fw rS n0 k0 c0 L xr)
    {mc : MainCode} (hin : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F₀ (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec -
        8#64 - 8#64 - ZU.toBitVec))
    (hU : ∀ v, UserCallWSF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      mc.fn mc.Z D ZU Post ((_root_.Executable.labels exe).label mc.sp0).toBitVec c0
      (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainUW (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (ms [])
      mc (fun c v => Post c [] v) ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64,
        tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩)
    (hWx : ∀ v fs, XExitW (fun s c => W s c fs) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS)
      exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainURR (_root_.Executable.labels exe).label mc (fun c v => Post c fs v)) (-8 - mc.Z.toInt) (-8)
      mc.k mc.ze0 mc.ze1 mc.ze2)
    {Q : FragS isa} :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0)).at []) Q :=
  (startEF_segWS hp hend hc (by omega) hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk0 hfld htk hok hsub hun hFw
    hFwS hRS hfitS houtS hFt hWE).seq
    (mainEUF_segWSF hp hend hin hZ hZ8 hps hk hD0 hD8 hL hL8 hK _ _ c0 hFwS hlimM hlimU hU hexit hW hWx)

end Proof

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.mainU_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainU_segWSF

/-- info: 'Spike.Lib.X64.Rt.mainEUF_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainEUF_segWSF

/-- info: 'Spike.Lib.X64.Rt.startUF_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startUF_segWSF

end Spike.Lib.X64.Rt
