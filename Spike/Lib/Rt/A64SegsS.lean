/-
**The runtime's start chain at depth** (H7a, calls): `mainU_segW`,
`startSwitchU_segW` and `startU_segW` (`Spike/Lib/Rt/A64Main.lean`,
`Spike/Lib/Rt/A64Segs.lean`) over segments with frames (`SegWS`,
`Spike/Lib/SegS.lean`), so that the user function called by `scc_rt_main`
may itself call (its segment a `SegWS`, the source's frames pushed and popped
inside it).

- **The user function is an interface at the empty frames**
  (`UserCallWS`): `UserCallW` with a `SegWS` from its entry to its return,
  both at `[]` (the main thread's source has no suspended frame at `main`'s
  call or return).
- **The runtime's own pieces are the `SegW` ones, lifted** at `[]`
  (`SegWS.liftS`): their states' obligations (`MainUW`, `Sp0W`, ...) are
  stated over `nilW W`, `W` at the empty frames, under the memory side
  `ms []`. Only the call of the user function is new (`call_nd_FWKS`).
- **`main`'s exit after its calls return** (`MainExitS`): the `hexit`
  obligation asks `main`'s exit after a frame run back to depth 0, since a
  source held back at the start returns from `main` only after its calls
  return; `exitTail_segWS` takes the `exit_group` row at the real pair
  (`OutS.pre`). `MainExit.toS` gives it from the call-free `MainExit`.
-/
import Spike.Lib.Rt.A64Segs
import Spike.Lib.A64CallS
import Spike.Lib.SegLagS

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

set_option linter.unusedSimpArgs false

/-- **`W` at the empty frames**, the fragment the runtime's own states'
obligations are stated over. -/
abbrev nilW (W : FragS isaLSE2) : Frag isaLSE2 := fun s c => W s c []

/-! ## Helpers over `SegWS` -/

section Helpers

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- `seg_oneW` at fixed frames: a single successor node. -/
theorem seg_oneWS {W : FragS isaLSE2} {K : State → State → Prop} {P : FragS isaLSE2} {n : ND}
    {fs : List TermRun.Frame}
    (h : SegWS W K p lbl ms P ((Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim)).at fs)) :
    SegWS W K p lbl ms P ((At exe endPc R F n).at fs) :=
  h.mono_post fun _ _ _ ⟨h, e⟩ => ⟨h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim, e⟩

/-- **Continuing after a switch** at fixed frames (`sw_segW` over
`SegWS`). -/
theorem sw_segWS {W : FragS isaLSE2} {K : State → State → Prop} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {X : FragS isaLSE2} {fs : List TermRun.Frame}
    (h : ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v lo hi).OK →
      SegWS W K p lbl ms ((At exe endPc (swR v lo hi) (F' v) n').at fs) X) :
    SegWS W K p lbl ms ((SwAt exe endPc lo hi F' n').at fs) X :=
  (SegWS.exists_pre (P := fun g : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v lo hi).OK} =>
      (At exe endPc (swR g.1 lo hi) (F' g.1) n').at fs) fun g => h g.1 g.2.1 g.2.2).mono_pre
    fun _ _ _ ⟨⟨v, h1, h2, hA⟩, e⟩ => ⟨⟨v, h1, h2⟩, hA, e⟩

/-- **The `exit_group` tail at depth 0, `main`'s exit after a frame run**
(`exitTail_segW` over `SegWS`): the block lifted at the empty frames; at the
`svc` the row is at the pair a frame run reaches back at depth 0 (`hok`,
`OutS.pre`; the call has no successor). -/
theorem exitTail_segWS {W : FragS isaLSE2} {K : State → State → Prop} {n : ND} {k : Int64} {Q : FragS isaLSE2}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : Spike.Lib.offOk lo hi (n.o.sp + k.toInt) = true)
    (h16 : n.o.sp % 16 = 0)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (exitTail k))
    (hcs : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (n.pc + 4 + 4 + 4) [svcDir])
    (hW : ExitW (nilW W) K exe endPc R F n k)
    (hok : ∀ s c σ0, n.J σ0 c →
      At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ _ => σ.regs.X0 = σ0.regs.X0⟩ s c →
      ∃ c', FrameRun p (c, []) (c', []) ∧ SysOk p (ms []) s c' (.exitGroup σ0.regs.X0.toNat)) :
    SegWS W K p lbl ms ((At exe endPc R F n).at []) Q := by
  refine (SegWS.liftS [] (Q₀ := At exe endPc R F (exitNx n)) ?_ fun _ _ h => h).seq ?_
  · refine (seg_ndW (N := fun _ : Unit => exitNx n) (E := fun e : Empty => e.elim) (by simp [exitTail])
      (exitTail_ok hk h16) hF hR hal hlo hhi hc hW.w0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    rw [exitTail_run]
    refine ⟨rfl, by simp [SO.le, exitNx], rfl, σ, hJ, ?_⟩
    show (σ.regs.setXReg .X8 94#64).X0 = σ.regs.X0
    rfl
  · refine SegWS.step (fun s c fs ⟨hA, e⟩ => by subst e; exact (hW.w1 s c hA).1)
      (fun s c fs ⟨hA, _⟩ => (hW.w1 s c hA).2) ?_
    rintro s c fs ⟨hAt, rfl⟩
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h8, σ0, hJ0, hx0⟩ := id hAt
    have hcell : CellAt s svcDir 4 := (hcs s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [exitNx])
    have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.a64 (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
        some (.exitGroup σ0.regs.X0.toNat) := by
      rw [← hx0, ← svcCall_exitGroup h8, svcCall, ← hA.regs]; rfl
    obtain ⟨c', hr, hok'⟩ := hok s c σ0 hJ0 ⟨he, hn, hdc, hpc, σ, hA, hD, hx0⟩
    exact .pre c' [] hr (.sys _ _ hK (Scc.Sem.A64.atSvc_of_cellAt hcell) hd hok' fun s' hs' => by
      rw [certSuccs_exitGroup] at hs'; cases hs')

end Helpers

/-! ## `scc_rt_main` with a calling user function -/

/-- **The user function called by `scc_rt_main`, as an interface at depth**:
`UserCallW` with a segment with frames, from its entry to its return at the
empty frames. -/
def UserCallWS (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isaLSE2)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) (ra : BitVec 64) (c0 : Ctl)
    (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK → (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 →
    FStable (R.callee (-Z.toInt) (-D) 0) F' → (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
    ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU g)).at [])
        ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (uNx Post g)).at [])

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_main` does not return, at depth** (`mainU_segW` with the user
function a `UserCallWS`): its prologue, `bl fn` and the `exit_group` tail are
`mainU_segW`'s, lifted at the empty frames; the call is `call_nd_FWKS`. -/
theorem mainU_segWS {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {mc : MainCode} (hin : mainUIn prog mc = true)
    (h16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -mc.Z.toInt - D) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F exe endPc (limA g.tp) (g.sp0 - mc.Z.toBitVec - ZU.toBitVec))
    (hU : UserCallWS W K p lbl ms exe endPc R F mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec g.c0 g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hW : MainUW (nilW W) K exe endPc R F (ms []) mc Post g)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainUIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hpro, hblk⟩, hgap⟩, hex⟩ := hin
  have esp0 := label_labelGap hp hgap
  have hloZ : R.lo ≤ -mc.Z.toInt := by omega
  have h1 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (mainN0 lab g)) (At exe endPc R F (mainUC lab mc g)) := by
    refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainU1 lab mc g) h16 hZ hF hR hal hloZ hhi
      (by simp [Spike.Lib.offOk]; omega) rfl (by simp [SO.le, oFr, mainU1]) hW.pro ?_) ?_
    · -- the prologue
      rintro σ c ⟨rfl, hsp, htp⟩
      rw [tcbA_limA htp]
      refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr _ => ⟨rfl, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlimM.room v hv
      · rw [hr]; simp [frRegs, ldStep, chkRegs, hsp]
      · rw [hr]; simp [frRegs, ldStep, chkRegs, setXReg_TPIDR, htp]
    · -- `bl fn`
      refine seg_oneW (seg_ndW (by simp) (okBlk_blD _ _ _ _) hF hR hal hloZ hhi
        (code_of hp hend hblk (ofNat4_zero _)) hW.call fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
      · dsimp only [mainU1, mainUC]; rw [blD_run]
      · dsimp only [mainU1, mainUC]; rw [blD_run]; simp [SO.le]
      · dsimp only [mainU1, mainUC] at hJ ⊢; rw [blD_run]
        obtain ⟨rfl, hsp, htp⟩ := hJ
        exact ⟨⟨rfl, hsp, htp⟩, rfl⟩
  have h3 : SegWS W K p lbl ms ((At exe endPc R F (mainUR lab mc Post)).at []) (fun _ _ _ => False) := by
    simp only [exitIn, Bool.and_eq_true] at hex
    refine exitTail_segWS (n := mainUR lab mc Post) hK hF hR hal (lo := -mc.Z.toInt) (hi := 0)
      hloZ hhi hk (by show (-mc.Z.toInt) % 16 = 0; omega) (code_of hp hend hex.1 (ofNat4_zero _))
      (code_of hp hend hex.2 (by simp only [ofNat4_succ, ofNat4_zero]; try rfl)) hW.exit fun s c σ0 hJ hAt => ?_
    -- the exit: `exit_group(v)` after the source's frame run back to depth 0
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
    by_cases hab : (ms []).abortAt s
    · exact ⟨c, .refl _, SysOk.exitGroup_abort hab⟩
    · obtain ⟨c', hr, hx'⟩ := hexit s c _ hJ ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.X0.toBitVec = _; rw [hx]⟩ hab
      exact ⟨c', hr, SysOk.exitGroup_main (v := σ0.regs.X0.toBitVec.toNat) fun _ => hx'⟩
  have h2 : SegWS W K p lbl ms ((At exe endPc R F (mainUC lab mc g)).at [])
      ((At exe endPc R F (mainUR lab mc Post)).at []) := by
    refine seg_oneWS (call_nd_FWKS (KC := False) (lo' := -D) (hi' := 0) (M := fun _ => True)
      (Ne := uN0 lab (ms []) F exe endPc mc.fn ZU) (Ex := fun g _ => uNx Post g)
      hR hal hF (by show R.lo ≤ -mc.Z.toInt + -D; omega) (by omega) (by show -mc.Z.toInt < R.hi; omega)
      (by decide) (by show (-mc.Z.toInt) % 16 = 0; omega) (by omega) (by decide) (fun h => h.elim)
      (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hal' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨hc, -, htp⟩, h30⟩, ⟨⟨hc', -, h30', -, htp'⟩, -⟩⟩ := hg'
        exact (hU F' hR' hal' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' (h30'.symm.trans h30)
          (hc'.symm.trans hc) (htp'.symm.trans htp)).mono_post fun _ _ _ h => ⟨⟨(), h.1, trivial⟩, h.2⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, h30⟩
      refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk (ms []) F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - ZU.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' x σC c σx c' σR ⟨⟨rfl, -, -⟩, h30⟩ ⟨⟨-, -, h30', -⟩, -⟩ ⟨hP, -, -⟩ hreg - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainUR, mainUC, uNx], ?_⟩
      · show lab mc.sp0 = Int64.ofBitVec g'.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, Spike.Lib.int64_ofBitVec_toBitVec]; exact esp0
      · show Post c' σR.regs.X0.toBitVec
        rw [hreg]; exact hP
  exact (SegWS.liftS [] h1 fun _ _ h => h).seq (h2.seq (h3.mono_post fun _ _ _ h => h.elim))

end Proof

/-! ## From the switch on -/

section SwitchU

/-- `scc_rt_main`'s own obligations under a weaker frame condition hold
under a stronger one. -/
theorem mainUW_monoS {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F' : MachineData → Prop} {ms : MemSide isaLSE2} {mc : MainCode}
    {Post : Ctl → BitVec 64 → Prop} {g : MainG} (h : MainUW W K exe endPc R F ms mc Post g)
    (hFF : ∀ m, F' m → F m) : MainUW W K exe endPc R F' ms mc Post g :=
  ⟨proW_mono h.pro hFF, blkW_mono h.call hFF, ⟨blkW_mono h.exit.w0 hFF, nodeW_mono h.exit.w1 hFF⟩⟩

/-- **The switch's and `scc_rt_main`'s states at depth** (`SwUW` with the
user function a `UserCallWS`): the runtime's own states inside `W` at the
empty frames; the user function's frame condition carries the private
memory's facts `U` from before the switch (e.g. the thread's words
unmapped). -/
structure SwUWS (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (ms : List TermRun.Frame → MemSide isaLSE2) (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int)
    (mc : MainCode) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) (U : _root_.Mem 64 → Prop) : Prop where
  sw : NodeW (nilW W) K exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW (nilW W) K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
    (startN6 (_root_.Executable.labels exe).label tcb top c0) startMain
  main : ∀ v, MainUW (nilW W) K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) (ms [])
    mc Post ⟨top, UInt64.ofBitVec tcb, c0⟩
  user : ∀ v, UserCallWS W K p lbl ms exe endPc (swR v (-L) 0)
    (fun m => swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m ∧ U m.dmem)
    mc.fn mc.Z D ZU Post ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec c0 (UInt64.ofBitVec tcb)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **From the switch on, at depth** (`startSwitchU_segW` with
`mainU_segWS`): the switch and `bl scc_rt_main` lifted at the empty
frames; the private memory's facts `U` from before the switch (`hUF`),
kept in the new region (`hUS`). -/
theorem startSwitchU_segWS {W : FragS isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hin : startTailIn prog = true)
    {mc : MainCode} (hmain : mainUIn prog mc = true) (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : mc.Z.toInt + D ≤ L)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hlimM : LimOk (ms []) F exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    {U : _root_.Mem 64 → Prop} (hUF : ∀ m, F m → U m.dmem) (hUS : FStable (swR top (-L) 0) fun m => U m.dmem)
    (hW : SwUWS W K p lbl exe endPc R F ms rS tcb top c0 L mc D ZU Post U)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((At exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (UInt64.ofBitVec tcb)
  have hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-L) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k := by
    intro m hD
    refine ⟨fun k => BitVec.ofInt 64 ((Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8).getD 0), fun k hk => ?_⟩
    obtain ⟨h8, ha, ha7⟩ := hsub k hk
    have h := hFS m hD _ h8 ha ha7
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, hj, by simp only [hj, Option.getD_some]⟩
  refine (SegWS.liftS [] (sw_ndW (n := startN5 lab tcb top c0) (lo := -L) (hi := 0) (F' := fun v m => swFSL L rS top a v m ∧ U m.dmem)
      (n' := startN6 lab tcb top c0)
      (p := p) (lbl := lbl) (ms := ms [])
      rfl (code_of hp hend hin.1.2 rfl) (ofNat4_succ' _ 5).symm rfl hW.sw fun m σ c _ hD hJ => ?_)
      fun _ _ h => h).seq (sw_segWS fun v hv hR => ?_)
  · obtain ⟨rfl, h9, htp, hx0⟩ := hJ
    obtain ⟨hsp, hx, htp'⟩ := swStep (startN5 lab tcb top c).o ((startN5 lab tcb top c).pc + Int64.ofNat 4) σ
    rw [hsp, h9]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨h16, hok, ⟨⟨⟨rfl, hlimM.unmapped m hD⟩, (hFS m hD).off⟩, hUF m hD⟩, sl, hsl, c, .refl c, rfl,
      hsp.trans h9, htp'.trans htp, (congrArg _ hx).trans hx0⟩
  · let g : MainG := ⟨top, UInt64.ofBitVec tcb, c0⟩
    have hF2 : FStable (swR v (-L) 0) (fun m => swFSL L rS top a v m ∧ U m.dmem) := fun m m' h hd => by
      have hvt : v = top := h.1.1.1
      subst hvt
      exact ⟨⟨swF_stableL hfit hout m m' h.1.1 hd, stackOff_stable hfitS m m' h.1.2 hd⟩, hUS m m' h.2 hd⟩
    refine (SegWS.liftS [] (Q₀ := At exe endPc (swR v (-L) 0) (fun m => swFSL L rS top a v m ∧ U m.dmem)
        (mainN0 lab g))
      (seg_oneW (seg_ndW (by simp [startMain]) (startMain_okL (-L) 0) hF2 hR hv (Int.le_refl _) (Int.le_refl _)
        (code_of hp hend hin.2 rfl) (blkW_mono (F' := fun m => swFSL L rS top a v m ∧ U m.dmem) (hW.blk v) fun _ h => h.1)
        fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      fun _ _ h => h).seq
      (mainU_segWS hp hend hmain hZ16 hZ hk hD0 hD8 hK hF2 hR hv (show -L ≤ -mc.Z.toInt - D by omega)
        (Int.le_refl _) g ⟨hlimM.rt, hlimM.mp, fun _ h => h.1.1.2, hlimM.room⟩
        ⟨hlimU.rt, hlimU.mp, fun _ h => h.1.1.2, hlimU.room⟩ (hW.user v)
        (fun s c x hP hAt => hexit _ _ s c x hP hAt) (mainUW_monoS (hW.main v) fun _ h => h.1))
    · dsimp only [startN6, mainN0]; rw [startMain_run]
    · dsimp only [startN6, mainN0]; rw [startMain_run]; rfl
    · dsimp only [startN6, mainN0] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp, -⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩ <;> simp_all [setXReg_TPIDR, Reg64s.setXReg_SP] <;> rfl

end SwitchU

/-! ## `scc_rt_start` whole -/

section StartU

/-- **`scc_rt_start`'s states at depth** (`StartAllUW` with `SwUWS`): the
runtime's own states inside `W` at the empty frames. -/
structure StartAllUWS (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : List TermRun.Frame → MemSide isaLSE2) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) (L : Int) (mc : MainCode) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop)
    (U : _root_.Mem 64 → Prop) : Prop where
  s1 : Sp0W (nilW W) K exe endPc R F n0 c0
  s2 : Sp2W (nilW W) K exe endPc R F rS n0 k0 c0
  s3 : SwUWS W K p lbl exe endPc R (fun m => F m ∧ StackM rS m) ms rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L mc D ZU Post U

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_start` never returns, at depth** (`startU_segW` with
`startSwitchU_segWS`): up to the switch lifted at the empty frames; the
private memory's facts `U` of the frame condition (`hUF`) kept in the new
stack's region (`hUS`). -/
theorem startU_segWS {W : FragS isaLSE2} {rS : Scc.Sem.Range} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hcall : startCallIn prog = true) (hstart : startIn prog = true)
    (hat : AllocTcb.allocTcbIn prog = true) (htail : startTailIn prog = true)
    (hti : ThreadInit.threadInitIn prog = true) (hsp : tiSpIn prog = true)
    (hst : StackTake.stackTakeIn prog = true)
    {mc : MainCode} (hmain : mainUIn prog mc = true) (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hkm : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : mc.Z.toInt + D ≤ L)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0)
      (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
    (h16 : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
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
    (hlimM : LimOk (ms []) F exe endPc
      (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F exe endPc
      (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - mc.Z.toBitVec - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    {U : _root_.Mem 64 → Prop} (hUF : ∀ m, F m → U m.dmem)
    (hUS : FStable (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0) fun m => U m.dmem)
    (hW : StartAllUWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl exe endPc R F ms
      rS n0 k0 c0 L mc D ZU Post U)
    {Q : FragS isaLSE2} :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)).at []) Q :=
  (SegWS.liftS []
    ((startSp2_segW (p := p) (lbl := lbl) (ms := ms []) hp hend hcall hstart hat hK hF hR hal (by omega) hhi n0 c0
      hn hhdr htcb hW.s1).seq
      (startSp2Sw_segW hp hend htail hti hsp hst hF hR hal hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS hfitS houtS hFt))
    fun _ _ h => h).seq
    (startSwitchU_segWS hp hend htail hmain hZ16 hZ hkm hD0 hD8 hL hK _ _ c0 h16 hok (fun _ h => h.2) hfitS hsub
      hfit hout (hlimM.mono fun _ h => h.1) (hlimU.mono fun _ h => h.1) hexit (fun m h => hUF m h.1) hUS hW.s3)

end StartU

end Spike.Lib.A64.Rt
