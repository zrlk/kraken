/-
**`scc_rt_main` after a setup block, at depth, its user function returning
at pending frames** (AArch64; the twin of `Spike/Lib/Rt/X64MainSSF.lean`):
`mainS_segWS` (`Spike/Lib/Rt/A64MainSS.lean`) with the user function's
return at whatever frames the source has there. A source held back at a
callee's `ret` (e.g. `print`'s `ret ()` at `[printFrame]`) is still at depth
when the machine returns from `main` and reaches `exit_group`; the frame run
back to depth 0 is taken by the `exit_group` row (`exitTail_segWSF`,
`Spike/Lib/Rt/A64ExitF.lean`).

- `NxF`: the user function's return node `uNx` at the post `Post` of the
  control and the frames, at any frames;
- `MainCallWSF`: `MainCallWS` with its return at `NxF` (the entry at `[]`);
  `MainCallWS.toF`: an interface returning at `[]` is one at `NxF`;
- `mainS_segWSF`: `mainS_segWS` at `MainCallWSF`; the user function's call
  is `call_nd_FWKSF` (`Spike/Lib/A64CallSF.lean`), the `exit_group` tail
  `exitTail_segWSF` at the frames of the return, its obligation `hWx` at
  every frames (the runtime's states inside `W` there); `hexit` asks
  `MainExitFA` from the frames;
- `mainES_segWSF`, `startS_segWSF`: `mainES_segWS`, `startS_segWS` over it.
-/
import Spike.Lib.Rt.A64MainSS
import Spike.Lib.Rt.A64ExitF
import Spike.Lib.A64CallSF

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## The interface returning at pending frames -/

/-- **The user function's return at any frames**: `uNx` at the post of the
control and the frames the source has. -/
def NxF (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (Post : Ctl → List TermRun.Frame → BitVec 64 → Prop) (g : WcG) : FragS isaLSE2 :=
  fun s c fs => At exe endPc R F (uNx (fun c v => Post c fs v) g) s c

/-- **The user function called after the setup block, returning at pending
frames**: `MainCallWS` with its return at `NxF`, the source's frames free
there. -/
def MainCallWSF (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isaLSE2)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Pre : Ctl → Reg64s → Prop)
    (Post : Ctl → List TermRun.Frame → BitVec 64 → Prop) (ra : BitVec 64) (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK → (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 →
    FStable (R.callee (-Z.toInt) (-D) 0) F' → (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
    ∀ g : WcG, g.ra = ra → g.tp = tp →
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (uNM (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU Pre g)).at [])
        (NxF exe endPc (R.callee (-Z.toInt) (-D) 0) F' Post g)

/-- An interface returning at the empty frames returns at `NxF`, its post at
`[]` only. -/
theorem MainCallWS.toF {W : FragS isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {Pre : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    {ra : BitVec 64} {tp : UInt64} (h : MainCallWS W K p lbl ms exe endPc R F fn Z D ZU Pre Post ra tp) :
    MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre (fun c fs v => fs = [] ∧ Post c v) ra tp :=
  fun F' hR hal hF hFF g hra htp => (h F' hR hal hF hFF g hra htp).mono_post fun _ _ _ ⟨h, e⟩ => by
    subst e
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hP, hJ⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨rfl, hP⟩, hJ⟩

/-! ## The segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_main` after a setup block does not return, at depth, its user
function returning at pending frames** (`mainS_segWS` at `MainCallWSF`): its
prologue, `bl setup`, the setup block's call and the marshalling block are
`mainS_segWS`'s; the user function's call is `call_nd_FWKSF`, the
`exit_group` tail `exitTail_segWSF` at the frames `fs` of the return (`hWx`
at every `fs`); `hexit` asks `MainExitFA` from those frames. -/
theorem mainS_segWSF {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {sc : SetupCode} (hin : mainSIn prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
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
    (hU : MainCallWSF W K p lbl ms exe endPc R F sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec g.tp)
    (hexit : ∀ s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : MainSW (nilW W) K exe endPc R F (ms []) sc PostS (fun c v => Post c [] v) g x0)
    (hWx : ∀ fs, ExitW (fun s c => W s c fs) K exe endPc R F
      (mainSR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) sc.k)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((At exe endPc R F (mainSN0 (_root_.Executable.labels exe).label g x0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainSIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hpro, hb0⟩, hg0⟩, hb1⟩, hg1⟩, hex⟩ := hin
  have esp0 := label_labelGap hp hg0
  have esp1 := label_labelGap hp hg1
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
  -- the exit: `exit_group(v)` after the source's frame run back to depth 0, from the frames `fs` the
  -- source has at the return
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
  exact (SegWS.liftS [] h1 fun _ _ h => h).seq (h2.seq ((SegWS.liftS [] h3 fun _ _ h => h).seq
    (h4.seq (h5.mono_post fun _ _ _ h => h.elim))))

/-- **From `scc_rt_main`'s entry after the switch, at depth, the user
function returning at pending frames** (`mainES_segWS` over `mainS_segWSF`):
`mainS_segWSF` in the new region of depth `L` at every value `v` of the new
`sp`, under `swFSL`. -/
theorem mainES_segWSF {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {sc : SetupCode} (hin : mainSIn prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    {rS : Scc.Sem.Range} {L : Int}
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
    (hU : ∀ v, MainCallWSF W K p lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw tcb) Post ((_root_.Executable.labels exe).label sc.sp1).toBitVec
      (UInt64.ofBitVec tcb))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainSW (nilW W) K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) (ms [])
      sc PostS (fun c v => Post c [] v) ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb)
    (hWx : ∀ v fs, ExitW (fun s c => W s c fs) K exe endPc (swR v (-L) 0)
      (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      (mainSR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) sc.k)
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
  exact mainS_segWSF hp hend hin h16 hZ hsw hZw hk hD10 hD18 hD20 hD28 hK hF2 hR hv
    (show -L ≤ -sc.Z.toInt - D1 by omega) (show -L ≤ -sc.Z.toInt - D2 by omega) (Int.le_refl _)
    ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb ⟨hlimM.rt, hlimM.mp, fun _ h => h.1.2, hlimM.room⟩
    ⟨hlimS.rt, hlimS.mp, fun _ h => h.1.2, hlimS.room⟩ ⟨hlimU.rt, hlimU.mp, fun _ h => h.1.2, hlimU.room⟩
    (hS v) hcall hPS (hWC v) (hU v) (fun s c fs x hP hAt => hexit _ _ s c fs x hP hAt) (hW v) (hWx v)

/-- **The program after a setup block never returns, at depth, from
`_start`, the user function returning at pending frames** (`startE_segWS`
then `mainES_segWSF`). -/
theorem startS_segWSF {W : FragS isaLSE2} {rS : Scc.Sem.Range} {kp : Nat}
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
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
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
    (hU : ∀ v, MainCallWSF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      (swR v (-L) 0) (swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (pinA (_root_.Executable.labels exe).label + n0 + 8#64)) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec
      (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainSW (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      (swR v (-L) 0) (swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v) (ms [])
      sc PostS (fun c v => Post c [] v) ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
        UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
      (pinA (_root_.Executable.labels exe).label + n0 + 8#64))
    (hWx : ∀ v fs, ExitW (fun s c => W s c fs) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS)
      exe endPc (swR v (-L) 0) (swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v)
      (mainSR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) sc.k)
    {Q : FragS isaLSE2} :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN (_root_.Executable.labels exe).label c0)).at []) Q :=
  (startE_segWS hp hend hc hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk0 hfld htk h16t hok hsub hfit hout hun hRS
    hfitS houtS hFt hWE).seq
    (mainES_segWSF hp hend hin h16 hZ hsw hZw hk hD10 hD18 hD20 hD28 hL1 hL2 hK _ _ c0 hfitS hfit hout hlimM hlimS
      hlimU hS hcall hPS hWC hU hexit hW hWx)

end Proof

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.mainS_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainS_segWSF

/-- info: 'Spike.Lib.A64.Rt.mainES_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainES_segWSF

/-- info: 'Spike.Lib.A64.Rt.startS_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startS_segWSF

end Spike.Lib.A64.Rt
