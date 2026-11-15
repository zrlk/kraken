/-
**`scc_rt_main` without a setup block, at depth, its user function
returning at pending frames** (AArch64): `mainU_segWS`
(`Spike/Lib/Rt/A64SegsS.lean`) with the user function's return at whatever
frames the source has there, as `mainS_segWSF`
(`Spike/Lib/Rt/A64MainSSF.lean`) does after a setup block. A source held
back at a callee's `ret` (e.g. `print`'s `ret ()` at `[printFrame]`) is
still at depth when the machine returns from `main` and reaches
`exit_group`; the frame run back to depth 0 is taken by the `exit_group`
row (`exitTail_segWSF`).

- `UserCallWSF`: `UserCallWS` with its return at `NxF` (the entry at `[]`);
- `mainU_segWSF`: `mainU_segWS` at `UserCallWSF`; the user function's call
  is `call_nd_FWKSF`, the `exit_group` tail `exitTail_segWSF` at the frames
  of the return, its obligation `hWx` at every frames; `hexit` asks
  `MainExitFA` from the frames;
- `mainEUF_segWSF`: from `MainEF` (`scc_rt_main`'s entry after the switch,
  under the extra frame `Fw ∧ swFSL …`) on;
- `startUF_segWSF`: from `_start` (`startEF_segWS` then `mainEUF_segWSF`).
-/
import Spike.Lib.Rt.A64MainSSF
import Spike.Lib.Rt.A64StartEF

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## The interface returning at pending frames -/

/-- **The user function called by `scc_rt_main` without a setup block,
returning at pending frames**: `UserCallWS` with its return at `NxF`. -/
def UserCallWSF (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isaLSE2)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Post : Ctl → List TermRun.Frame → BitVec 64 → Prop)
    (ra : BitVec 64) (c0 : Ctl) (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK → (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 →
    FStable (R.callee (-Z.toInt) (-D) 0) F' → (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
    ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU g)).at [])
        (NxF exe endPc (R.callee (-Z.toInt) (-D) 0) F' Post g)

/-! ## The segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_main` without a setup block does not return, at depth, its
user function returning at pending frames** (`mainU_segWS` at
`UserCallWSF`): its prologue and `bl fn` are `mainU_segWS`'s; the user
function's call is `call_nd_FWKSF`, the `exit_group` tail
`exitTail_segWSF` at the frames `fs` of the return (`hWx` at every `fs`);
`hexit` asks `MainExitFA` from those frames. -/
theorem mainU_segWSF {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {mc : MainCode} (hin : mainUIn prog mc = true)
    (h16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -mc.Z.toInt - D) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - mc.Z.toBitVec - ZU.toBitVec))
    (hU : UserCallWSF W K p lbl ms exe endPc R F mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec g.c0 g.tp)
    (hexit : ∀ s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : MainUW (nilW W) K exe endPc R F (ms []) mc (fun c v => Post c [] v) g)
    (hWx : ∀ fs, ExitW (fun s c => W s c fs) K exe endPc R F
      (mainUR (_root_.Executable.labels exe).label mc (fun c v => Post c fs v)) mc.k)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainUIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hpro, hblk⟩, hgap⟩, hex⟩ := hin
  have esp0 := label_labelGap hp hgap
  have hloZ : R.lo ≤ -mc.Z.toInt := by omega
  -- the prologue and `bl fn`
  have h1 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainN0 lab g)) (At exe endPc R F (mainUC lab mc g)) := by
    refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainU1 lab mc g) h16 hZ hF hR hal hloZ hhi
      (by simp [Spike.Lib.offOk]; omega) rfl (by simp [SO.le, oFr, mainU1]) hW.pro ?_) ?_
    · rintro σ c ⟨rfl, hsp, htp⟩
      rw [tcbA_limA htp]
      refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr _ => ⟨rfl, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlimM.room v hv
      · rw [hr]; simp [frRegs, ldStep, chkRegs, hsp]
      · rw [hr]; simp [frRegs, ldStep, chkRegs, setXReg_TPIDR, htp]
    · refine seg_oneW (seg_ndW (by simp) (okBlk_blD _ _ _ _) hF hR hal hloZ hhi
        (code_of hp hend hblk (ofNat4_zero _)) hW.call fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
      · dsimp only [mainU1, mainUC]; rw [blD_run]
      · dsimp only [mainU1, mainUC]; rw [blD_run]; simp [SO.le]
      · dsimp only [mainU1, mainUC] at hJ ⊢; rw [blD_run]
        obtain ⟨rfl, hsp, htp⟩ := hJ
        exact ⟨⟨rfl, hsp, htp⟩, rfl⟩
  -- the user function's call, returning at the frames `fs` the source has there
  have h2 : SegWS W K p lbl ms ((At exe endPc R F (mainUC lab mc g)).at [])
      (fun s c fs => At exe endPc R F (mainUR lab mc (fun c v => Post c fs v)) s c) := by
    refine (call_nd_FWKSF (KC := False) (lo' := -D) (hi' := 0) (M := fun _ => True)
      (N := fun fs (_ : Unit) => mainUR lab mc (fun c v => Post c fs v)) (E := fun _ (e : Empty) => e.elim)
      (Ne := uN0 lab (ms []) F exe endPc mc.fn ZU)
      (Ex := fun g fs (_ : Unit) => uNx (fun c v => Post c fs v) g)
      hR hal hF (by show R.lo ≤ -mc.Z.toInt + -D; omega) (by omega) (by show -mc.Z.toInt < R.hi; omega)
      (by decide) (by show (-mc.Z.toInt) % 16 = 0; omega) (by omega) (by decide) (fun h => h.elim)
      (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hal' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨hc, -, htp⟩, h30⟩, ⟨⟨hc', -, h30', -, htp'⟩, -⟩⟩ := hg'
        exact (hU F' hR' hal' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' (h30'.symm.trans h30)
          (hc'.symm.trans hc) (htp'.symm.trans htp)).mono_post fun _ _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_).mono_post fun _ _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, h30⟩
      refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk (ms []) F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - ZU.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' fs' x σC c σx c' σR ⟨⟨rfl, -, -⟩, h30⟩ ⟨⟨-, -, h30', -⟩, -⟩ ⟨hP, -, -⟩ hreg - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainUR, mainUC, uNx], ?_⟩
      · show lab mc.sp0 = Int64.ofBitVec g'.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, Spike.Lib.int64_ofBitVec_toBitVec]; exact esp0
      · show Post c' fs' σR.regs.X0.toBitVec
        rw [hreg]; exact hP
  -- the exit: `exit_group(v)` after the source's frame run back to depth 0, from the frames `fs` the
  -- source has at the return
  have h3 : SegWS W K p lbl ms (fun s c fs => At exe endPc R F (mainUR lab mc (fun c v => Post c fs v)) s c)
      (fun _ _ _ => False) := by
    simp only [exitIn, Bool.and_eq_true] at hex
    refine (SegWS.exists_pre (P := fun fs => (At exe endPc R F (mainUR lab mc (fun c v => Post c fs v))).at fs)
      fun fs => ?_).mono_pre fun _ _ fs h => ⟨fs, h, rfl⟩
    refine exitTail_segWSF (n := mainUR lab mc (fun c v => Post c fs v)) hK hF hR hal (lo := -mc.Z.toInt) (hi := 0)
      hloZ hhi hk (by show (-mc.Z.toInt) % 16 = 0; omega) (code_of hp hend hex.1 (ofNat4_zero _))
      (code_of hp hend hex.2 (by simp only [ofNat4_succ, ofNat4_zero]; try rfl)) (hWx fs)
      fun s c σ0 hJ hAt => ?_
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
    exact exitGroup_of_mainExitFA (v := σ0.regs.X0.toBitVec.toNat)
      (hexit s c fs _ hJ ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.X0.toBitVec = _; rw [hx]⟩)
  exact (SegWS.liftS [] h1 fun _ _ h => h).seq (h2.seq (h3.mono_post fun _ _ _ h => h.elim))

/-- **From `scc_rt_main`'s entry after the switch, without a setup block,
under the extra frame `Fw`** (`mainU_segWSF` in the new region of depth `L`
at every value `v` of the new `sp`, under `Fw ∧ swFSL …`, `FStable` by
`hFwS`). -/
theorem mainEUF_segWSF {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {mc : MainCode} (hin : mainUIn prog mc = true)
    (h16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    {rS : Scc.Sem.Range} {L : Int} (hL : mc.Z.toInt + D ≤ L)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    {Fw : _root_.Mem 64 → Prop}
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m))
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec - ZU.toBitVec))
    (hU : ∀ v, UserCallWSF W K p lbl ms exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
      mc.fn mc.Z D ZU Post ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec c0 (UInt64.ofBitVec tcb))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainUW (nilW W) K exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m) (ms [])
      mc (fun c v => Post c [] v) ⟨top, UInt64.ofBitVec tcb, c0⟩)
    (hWx : ∀ v fs, ExitW (fun s c => W s c fs) K exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
      (mainUR (_root_.Executable.labels exe).label mc (fun c v => Post c fs v)) mc.k)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((MainEF exe endPc rS Fw tcb top c0 L).at []) Q := by
  let a := limA (UInt64.ofBitVec tcb)
  refine (SegWS.exists_pre (P := fun g : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK} =>
      (At exe endPc (swR g.1 (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top a g.1 m)
        (mainN0 (_root_.Executable.labels exe).label ⟨top, UInt64.ofBitVec tcb, c0⟩)).at [])
    fun g => ?_).mono_pre fun _ _ _ ⟨⟨v, h1, h2, he, hn, hdc, hpc, σ, hA, hD, hJ⟩, e⟩ =>
      ⟨⟨v, h1, h2⟩, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ.1⟩, e⟩
  obtain ⟨v, hv, hR⟩ := g
  exact mainU_segWSF hp hend hin h16 hZ hk hD0 hD8 hK (hFwS v) hR hv (show -L ≤ -mc.Z.toInt - D by omega)
    (Int.le_refl _) ⟨top, UInt64.ofBitVec tcb, c0⟩ ⟨hlimM.rt, hlimM.mp, fun _ h => h.2.1.2, hlimM.room⟩
    ⟨hlimU.rt, hlimU.mp, fun _ h => h.2.1.2, hlimU.room⟩ (hU v) (fun s c fs x hP hAt => hexit _ _ s c fs x hP hAt)
    (hW v) (hWx v)

/-- **The program without a setup block never returns, at depth, from
`_start`, the user function returning at pending frames, with the extra
frame `Fw` after the switch** (`startEF_segWS` then `mainEUF_segWSF`). -/
theorem startUF_segWSF {W : FragS isaLSE2} {rS : Scc.Sem.Range} {Fw : _root_.Mem 64 → Prop} {kp : Nat}
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
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
      (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m))
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hWE : StartEWF (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F Fw rS n0 k0 c0 L)
    {mc : MainCode} (hin : mainUIn prog mc = true) (h16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hL : mc.Z.toInt + D ≤ L) {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - mc.Z.toBitVec - ZU.toBitVec))
    (hU : ∀ v, UserCallWSF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m)
      mc.fn mc.Z D ZU Post ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec c0
      (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainUW (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) (ms [])
      mc (fun c v => Post c [] v) ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
        UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩)
    (hWx : ∀ v fs, ExitW (fun s c => W s c fs) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS)
      exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m)
      (mainUR (_root_.Executable.labels exe).label mc (fun c v => Post c fs v)) mc.k)
    {Q : FragS isaLSE2} :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN (_root_.Executable.labels exe).label c0)).at []) Q :=
  (startEF_segWS hp hend hc hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk0 hfld htk h16t hok hsub hun hFw hFwS
    hRS hfitS houtS hFt hWE).seq
    (mainEUF_segWSF hp hend hin h16 hZ hk hD0 hD8 hL hK _ _ c0 hFwS hlimM hlimU hU hexit hW hWx)

end Proof

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.mainU_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainU_segWSF

/-- info: 'Spike.Lib.A64.Rt.mainEUF_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainEUF_segWSF

/-- info: 'Spike.Lib.A64.Rt.startUF_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startUF_segWSF

end Spike.Lib.A64.Rt
