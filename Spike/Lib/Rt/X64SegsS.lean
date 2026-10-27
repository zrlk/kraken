/-
**The x86-64 runtime's start chain at depth** (H7a, calls): `mainU_segW`
(`Spike/Lib/Rt/X64Main.lean`), `startSwitchU_segW` and `startU_segW`
(`Spike/Lib/Rt/X64Segs.lean`) over segments with frames (`SegWS`,
`Spike/Lib/SegS.lean`), so that the user function called by `scc_rt_main`
may itself call (its segment a `SegWS`, the source's frames pushed and popped
inside it). The x86-64 twin of `Spike/Lib/Rt/A64SegsS.lean`.

- **The user function is an interface at the empty frames**
  (`UserCallWS`): `UserCallW` with a `SegWS` from its entry to its return,
  both at `[]` (the main thread's source has no suspended frame at `main`'s
  call or return).
- **The runtime's own pieces are the `SegW` ones, lifted** at `[]`
  (`SegWS.liftS`): their states' obligations (`MainUW`, `St0W`, ...) are
  stated over `nilW W`, `W` at the empty frames, under the memory side
  `ms []`. Only the calls are new (`call_nd_FWKS`).
- **`main`'s exit after its calls return** (`MainExitS`): the `hexit`
  obligation asks `main`'s exit after a frame run back to depth 0, since a
  source held back at the start returns from `main` only after its calls
  return; `xExitTail_segWS` takes the `exit_group` row at the real pair
  (`OutS.pre`). `MainExit.toS` gives it from the call-free `MainExit`.

Where x86-64 differs from AArch64: `scc_rt_main` is itself entered by a
`call` (`startSwitchU_segW`), so that call is a `call_nd_FWKS` too, its
callee `mainU_segWS`; the user function's interface is asked for every frame
condition stronger than the callee region's (`SwUWS.user`), as in `SwUW`;
`_start`'s call of `scc_rt_start` is a `call_nd_FWKS` (`KC := True`) at
`[]` too (`entry_segWS'`, the twin of `entry_segW'` in
`Spike/Lib/Rt/X64Entry.lean`).
-/
import Spike.Lib.Rt.X64Entry
import Spike.Lib.X64CallS
import Spike.Lib.SegLagS

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-- **`W` at the empty frames**, the fragment the runtime's own states'
obligations are stated over. -/
abbrev nilW (W : FragS isa) : Frag isa := fun s c => W s c []

/-! ## Helpers over `SegWS` -/

section Helpers

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- `seg_oneW` at fixed frames: a single successor node. -/
theorem seg_oneWS {W : FragS isa} {K : State → State → Prop} {P : FragS isa} {n : ND}
    {fs : List TermRun.Frame}
    (h : SegWS W K p lbl ms P ((Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim)).at fs)) :
    SegWS W K p lbl ms P ((At exe endPc R F n).at fs) :=
  h.mono_post fun _ _ _ ⟨h, e⟩ => ⟨h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim, e⟩

/-- **Continuing after a switch** at fixed frames (`sw_segW` over
`SegWS`). -/
theorem sw_segWS {W : FragS isa} {K : State → State → Prop} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {X : FragS isa} {fs : List TermRun.Frame}
    (h : ∀ v : BitVec 64, (swR v lo hi).OK → SegWS W K p lbl ms ((At exe endPc (swR v lo hi) (F' v) n').at fs) X) :
    SegWS W K p lbl ms ((SwAt exe endPc lo hi F' n').at fs) X :=
  (SegWS.exists_pre (P := fun g : {v : BitVec 64 // (swR v lo hi).OK} =>
      (At exe endPc (swR g.1 lo hi) (F' g.1) n').at fs) fun g => h g.1 g.2).mono_pre
    fun _ _ _ ⟨⟨v, h1, hA⟩, e⟩ => ⟨⟨v, h1⟩, hA, e⟩

/-- **The `exit_group` tail at depth 0, `main`'s exit after a frame run**
(`xExitTail_segW` over `SegWS`): the block lifted at the empty frames; at the
`syscall` the row is at the pair a frame run reaches back at depth 0 (`hok`,
`OutS.pre`; the call has no successor). -/
theorem xExitTail_segWS {W : FragS isa} {K : State → State → Prop} {n : ND} {Q : FragS isa} {sp b : Int}
    {k : Int64} {z0 z1 z2 z3 : Nat}
    (hno : n.o = ⟨sp, [(.rbp, b)]⟩) (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : offOk lo hi (b + k.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (xExit k z0 z1 z2))
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2) [(op64 .syscall, z3)])
    (hW : XExitW (nilW W) K exe endPc R F n sp b k z0 z1 z2)
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2,
      ⟨sp, [(.rbp, b)]⟩, fun σ _ => σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩ s c →
      ∃ c', FrameRun p (c, []) (c', []) ∧ SysOk p (ms []) s c' (.exitGroup σ0.regs.rax.toNat)) :
    SegWS W K p lbl ms ((At exe endPc R F n).at []) Q := by
  refine (SegWS.liftS [] (Q₀ := At exe endPc R F (xExitNx n sp b z0 z1 z2)) ?_ fun _ _ h => h).seq ?_
  · refine (seg_ndW (N := fun _ : Unit => xExitNx n sp b z0 z1 z2) (E := fun e : Empty => e.elim)
      (by simp [xExit]) (hno ▸ xExit_ok k z0 z1 z2 hk) hF hR hlo hhi hc0 hW.w0
      fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    obtain ⟨h1, h2, h3⟩ := xExit_run (Executable.labels exe).label n.pc sp b σ k z0 z1 z2
    rw [hno]
    refine ⟨h1, ?_, h2, σ, hJ, h3⟩
    simp only [xExit]; x64simp; simp [xExitNx, SO.le, lk]
  · refine SegWS.step (fun s c fs ⟨hA, e⟩ => by subst e; exact (hW.w1 s c hA).1)
      (fun s c fs ⟨hA, _⟩ => (hW.w1 s c hA).2) ?_
    rintro s c fs ⟨hAt, rfl⟩
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h231, σ0, hJ0, hx0⟩ := id hAt
    have hc : CellAt s (op64 .syscall) z3 := (hc1 s he hn).cell0 rfl rfl hpc
    have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.x64 (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
        some (.exitGroup σ0.regs.rax.toNat) := by
      have e : σ.regs.rdi.toNat = σ0.regs.rax.toNat := congrArg BitVec.toNat hx0
      rw [← e, ← syscallCall_exitGroup h231, syscallCall, ← hA.regs]; rfl
    obtain ⟨c', hr, hok'⟩ := hok s c σ0 hJ0 ⟨he, hn, hdc, hpc, σ, hA, hD, hx0⟩
    exact .pre c' [] hr (.sys _ _ hK (Scc.Sem.X64.atSyscall_of_cellAt hc) hd hok' fun s' hs' => by
      rw [certSuccs_exitGroup] at hs'; cases hs')

end Helpers

/-! ## `scc_rt_main` with a calling user function -/

/-- **The user function called by `scc_rt_main`, as an interface at depth**:
`UserCallW` with a segment with frames, from its entry to its return at the
empty frames. -/
def UserCallWS (W : FragS isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isa)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) (ra : BitVec 64) (c0 : Ctl)
    (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
    FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
    (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
    ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
          (uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g)).at [])
        ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' (uNx Post g)).at [])

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- `%rbp`'s offset moved by `8` with `%rsp`. -/
private theorem rbp_shiftS (r : BitVec 64) (z : Int) :
    r + BitVec.ofInt 64 (-8 - (-8 - z)) = r - 8#64 + BitVec.ofInt 64 (-8 - (-8 - z - 8)) := by
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  show r + y = r - 8#64 + (y + 8#64)
  bv_omega

/-- **`scc_rt_main` does not return, at depth** (`mainU_segW` with the user
function a `UserCallWS`): its prologue, `call fn` and the `exit_group` tail
are `mainU_segW`'s, lifted at the empty frames; the call is
`call_nd_FWKS`. -/
theorem mainU_segWS {W : FragS isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) {mc : MainCode} (hin : mainUIn cells mc = true)
    (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - mc.Z.toInt - 8 - D) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F (limA g.tp) (g.sp0 - 8#64 - mc.Z.toBitVec - 8#64 - 8#64 - ZU.toBitVec))
    (hU : UserCallWS W K p lbl ms exe endPc R F mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.sp0).toBitVec g.c0 g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hW : MainUW (nilW W) K exe endPc R F (ms []) mc Post g)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainUIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hpro, hblk⟩, hgap⟩, hex⟩ := hin
  have esp0 := label_labelGapB hp hgap
  have hloZ : R.lo ≤ -8 - mc.Z.toInt := by omega
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
          exact rbp_shiftS _ _
  have h3 : SegWS W K p lbl ms ((At exe endPc R F (mainUR lab mc Post)).at []) (fun _ _ _ => False) := by
    simp only [exitIn, Bool.and_eq_true] at hex
    refine (xExitTail_segWS (lo := -8 - mc.Z.toInt) (hi := 0) (n := mainURR lab mc Post) rfl hK hF hR hloZ hhi hk
        (code_field hp hend hex.1 (ofNat_zero' _)) (code_field hp hend hex.2 (by rw [ofNat_add', ofNat_add']; rfl))
        hW.exit fun s c σ0 hJ0 hs => ?_).mono_pre
      fun _ _ _ ⟨h, e⟩ => ⟨At.rbp h fun _ _ h => h.2, e⟩
    -- the exit: `exit_group(v)` after the source's frame run back to depth 0
    have hP := hJ0.1
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hs
    by_cases hab : (ms []).abortAt s
    · exact ⟨c, .refl _, SysOk.exitGroup_abort hab⟩
    · obtain ⟨c', hr, hx'⟩ := hexit s c _ hP ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.rdi.toBitVec = _; rw [hx]⟩ hab
      exact ⟨c', hr, SysOk.exitGroup_main (v := σ0.regs.rax.toBitVec.toNat) fun _ => hx'⟩
  have h2 : SegWS W K p lbl ms ((At exe endPc R F (mainUC lab mc g)).at [])
      ((At exe endPc R F (mainUR lab mc Post)).at []) := by
    refine seg_oneWS (call_nd_FWKS (KC := False) (e0 := 0) (lo' := -D) (hi' := 8) (M := fun _ => True)
      (Ne := uN0 lab (ms []) F mc.fn ZU) (Ex := fun g _ => uNx Post g)
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
          (htp'.symm.trans htp)).mono_post fun _ _ _ h => ⟨⟨(), h.1, trivial⟩, h.2⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, -, -⟩
      refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-8 - mc.Z.toInt - 8 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk (ms []) F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - ZU.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' x σC c σx c' σR ⟨⟨rfl, -, -⟩, hsl, hb⟩ ⟨⟨hc, hfp, hra, hsp, -⟩, -⟩ ⟨hP, hb', hsp'⟩ hregs
        - - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainUR, mainUC, uNx], by rw [hregs]; exact hP, ?_⟩
      · show lab mc.sp0 = Int64.ofBitVec g'.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-8 - mc.Z.toInt - 8 - 0 + 0))
        rw [show -8 - mc.Z.toInt - 8 - 0 + 0 = -8 - mc.Z.toInt - 8 by omega, hsl, int64_ofBitVec_toBitVec]
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - mc.Z.toInt))
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - (-8 - mc.Z.toInt))
        rw [hb]
        have := rbp_shiftS (σC.regs.rsp.toBitVec + 8#64) mc.Z.toInt
        rw [show σC.regs.rsp.toBitVec + 8#64 - 8#64 = σC.regs.rsp.toBitVec by bv_omega] at this
        exact this.symm
  exact (SegWS.liftS [] h1 fun _ _ h => h).seq (h2.seq (h3.mono_post fun _ _ _ h => h.elim))

end Proof

/-! ## From the switch on -/

section SwitchU

/-- **The switch's and `scc_rt_main`'s states at depth** (`SwUW` with the
user function a `UserCallWS`): the runtime's own states inside `W` at the
empty frames; the user function's frame conditions carry the private
memory's facts `U` from before the switch (e.g. the thread's words
unmapped). -/
structure SwUWS (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (ms : List TermRun.Frame → MemSide isa) (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int)
    (mc : MainCode) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) (U : _root_.Mem 64 → Prop) : Prop where
  sw : NodeW (nilW W) K exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)
  xor : ∀ v, NodeW (nilW W) K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (tpOf tcb)) v)
    (startN7 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW (nilW W) K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (tpOf tcb)) v)
    (startN8 (_root_.Executable.labels exe).label tcb top c0) startMain
  main : ∀ v, MainUW (nilW W) K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
    (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (ms []) mc
    Post ⟨top - 8#64, tpOf tcb, c0⟩
  user : ∀ v (F' : MachineData → Prop),
    (∀ m, F' m → (swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) ∧
      U m.dmem) →
    UserCallWS W K p lbl ms exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8) F' mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.sp0).toBitVec c0 (tpOf tcb)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **From the switch on, at depth** (`startSwitchU_segW` with
`mainU_segWS`): the switch, `xorl %ebp, %ebp` and the call block lifted at
the empty frames, then `call scc_rt_main` (`call_nd_FWKS`) with
`mainU_segWS` in the callee's region; the private memory's facts `U` from
before the switch (`hUF`), kept in the new region (`hUS`). -/
theorem startSwitchU_segWS {W : FragS isa} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : startTailIn cells = true)
    {mc : MainCode} (hmain : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hlimM : LimOk (ms []) F (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec - 8#64 - 8#64 - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    {U : _root_.Mem 64 → Prop} (hUF : ∀ m, F m → U m.dmem) (hUS : FStable (swR top (-L) 0) fun m => U m.dmem)
    (hW : SwUWS W K p lbl exe endPc R F ms rS tcb top c0 L mc D ZU Post U)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((At exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (tpOf tcb)
  have hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-L) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k := by
    intro m hD
    refine ⟨fun k => BitVec.ofInt 64 ((Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8).getD 0), fun k hk => ?_⟩
    obtain ⟨h8, ha, ha7⟩ := hsub k hk
    have h := hFS m hD _ h8 ha ha7
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, hj, by simp only [hj, Option.getD_some]⟩
  refine (SegWS.liftS [] (sw_ndW (n := startN6 lab tcb top c0) (lo := -L) (hi := 0)
      (F' := fun v m => swFSL L rS top a v m ∧ U m.dmem) (n' := startN7 lab tcb top c0)
      (p := p) (lbl := lbl) (ms := ms [])
      rfl (code_field hp hend hin.1.1.2 rfl) (ofNat_add' _ 28 3) rfl hW.sw fun m σ c _ hD hJ => ?_)
      fun _ _ h => h).seq (sw_segWS fun v hv => ?_)
  · obtain ⟨rfl, hax, htp, hdi⟩ := hJ
    obtain ⟨hsp, htp'⟩ := swStep (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3) σ
    have hdi' := (congrArg UInt64.toBitVec
      (swStep_rdi (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3) σ)).trans hdi
    have hsp2 : (AI.step (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3)
        (.reg .W64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64))))) σ).regs.get64 .rsp = top := by
      show (UInt64.toBitVec _) = _; rw [hsp]; exact hax
    rw [hsp2]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨hok, ⟨⟨⟨rfl, hlimM.unmapped m hD⟩, (hFS m hD).off⟩, hUF m hD⟩, sl, hsl, c, .refl c, rfl,
      by rw [hsp]; exact hax, htp'.trans htp, hdi'⟩
  · have hF2 : FStable (swR v (-L) 0) (fun m => swFSL L rS top a v m ∧ U m.dmem) := fun m m' h hd => by
      have hvt : v = top := h.1.1.1
      subst hvt
      exact ⟨⟨swF_stableL hfit hout m m' h.1.1 hd, stackOff_stable hfitS m m' h.1.2 hd⟩, hUS m m' h.2 hd⟩
    let g : MainG := ⟨top - 8#64, tpOf tcb, c0⟩
    refine (SegWS.liftS [] (Q₀ := At exe endPc (swR v (-L) 0) (fun m => swFSL L rS top a v m ∧ U m.dmem)
      (startNM lab tcb top c0))
      (SegW.seq (Q := At exe endPc (swR v (-L) 0) (fun m => swFSL L rS top a v m ∧ U m.dmem)
        (startN8 lab tcb top c0))
        (seg_oneW (flag_ndW (n := startN7 lab tcb top c0) (fi := .xor_rr32_self .rbp) rfl hF2
          (code_field hp hend hin.1.2 rfl) (nodeW_mono (hW.xor v) fun _ h => h.1)
          fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(),
            show lab x1L + Int64.ofNat 33 = lab x1L + Int64.ofNat 31 + Int64.ofNat 2 from ofNat_add' _ 31 2,
            by show SO.le SO.entry ((FI.xor_rr32_self .rbp).so SO.entry) = true; decide, ?_⟩⟩))
        (seg_oneW (seg_ndW (by simp [startMain]) (startMain_okL (by omega)) hF2 hv (Int.le_refl _) (Int.le_refl _)
          (code_field hp hend hin.2 rfl) (blkW_mono (hW.blk v) fun _ h => h.1)
          fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)))
      fun _ _ h => h).seq
      ((call_nd_FWKS (KC := False) (N := fun e : Empty => e.elim) (E := fun e : Empty => e.elim) (e0 := 0)
        (lo' := 8 - L) (hi' := 8) (M := fun _ => True) (fs := [])
        (nC := startNM lab tcb top c0) (exe := exe) (endPc := endPc)
        (F₂ := fun m => swFSL L rS top a v m ∧ U m.dmem)
        (Ne := fun _ : Unit => mainN0 lab g) (Ex := fun _ (e : Empty) => e.elim)
        hv hF2 (by show -L ≤ -8 - 0 + (8 - L); omega) (by omega) (by show (-8 : Int) - 0 < 0; decide)
        (by show (-8 : Int) - 0 + 8 ≤ 0; decide) (by show ((-8 : Int) - 0) % 8 = 0; decide) (by omega) (by decide)
        (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
        (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc _ _ _ => by
          subst hR'e
          exact mainU_segWS hp hend hmain hZ hZ8 hps hk hD0 hD8 hK hF' hR' (by omega) (by omega) g
            ⟨hlimM.rt, hlimM.mp, fun _ h => (hFF _ h).1.1.2, hlimM.room⟩
            ⟨hlimU.rt, hlimU.mp, fun _ h => (hFF _ h).1.1.2, hlimU.room⟩
            (hW.user v F' fun m h => ⟨⟨(hFF m h).1, hcc m h⟩, (hFF m h).2⟩)
            (fun s c x hP hAt => hexit _ _ s c x hP hAt)
            ((hW.main v).mono fun m h => ⟨(hFF m h).1, hcc m h⟩))
        (fun _ => rfl) (fun σC c hJ => ⟨(), rfl, hJ.1, hJ.2.1, hJ.2.2.1⟩) fun _ x => x.elim).mono_post
        fun _ _ _ h => h.1.elim (fun ⟨e, _⟩ => e.elim) fun ⟨e, _⟩ => e.elim)
    · dsimp only [startN7, startN8] at hJ ⊢
      obtain ⟨rfl, hsp, htp, hdi⟩ := hJ
      exact ⟨rfl, hsp, htp, hdi⟩
    · dsimp only [startN8, startNM]; rw [startMain_run]
    · dsimp only [startN8, startNM]; rw [startMain_run]; rfl
    · dsimp only [startN8, startNM] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp, hdi⟩ := hJ
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, hsp]
      · simp [Reg64s.set64, htp]
      · simp [Reg64s.set64, hdi]

end SwitchU

/-! ## `scc_rt_start` whole -/

section StartU

/-- **`scc_rt_start`'s states at depth** (`StartAllUW` with `SwUWS`): the
runtime's own states inside `W` at the empty frames. -/
structure StartAllUWS (W : FragS isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : List TermRun.Frame → MemSide isa) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) (L : Int) (mc : MainCode) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop)
    (U : _root_.Mem 64 → Prop) : Prop where
  s1 : St0W (nilW W) K exe endPc R F n0 c0
  s2 : X0W (nilW W) K exe endPc R F rS n0 k0 c0
  s3 : SwUWS W K p lbl exe endPc R (fun m => F m ∧ StackM rS m) ms rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L mc D ZU Post U

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_start` never returns, at depth** (`startU_segW` with
`startSwitchU_segWS`): up to the switch lifted at the empty frames; the
private memory's facts `U` of the frame condition (`hUF`) kept in the new
stack's region (`hUS`). -/
theorem startU_segWS {W : FragS isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hcall : startCallIn cells = true) (hstart : startIn cells = true)
    (hat : AllocTcb.allocTcbIn cells = true) (hcall2 : startCall2In cells = true)
    (htail : startTailIn cells = true) (hti : ThreadInit.threadInitIn cells = true)
    (hst : StackTake.stackTakeIn cells = true)
    {mc : MainCode} (hmain : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hkm : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hhdr : StOk (ms []) F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk (ms []) F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk (ms []) F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec -
        8#64 - 8#64 - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    {U : _root_.Mem 64 → Prop} (hUF : ∀ m, F m → U m.dmem)
    (hUS : FStable (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0) fun m => U m.dmem)
    (hW : StartAllUWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl exe endPc R F ms rS
      n0 k0 c0 L mc D ZU Post U)
    {Q : FragS isa} :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)).at []) Q :=
  (SegWS.liftS []
    ((startX0_segW (p := p) (lbl := lbl) (ms := ms []) hp hend hcall hstart hat hK hF hR (by omega) (by omega) n0 c0
      hn hhdr htcb hW.s1).seq
      (startX0Sw_segW hp hend hcall2 htail hti hst hK hF hR hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS hfitS houtS hFt))
    fun _ _ h => h).seq
    (startSwitchU_segWS hp hend htail hmain hZ hZ8 hps hkm hD0 hD8 hL hL8 hK _ _ c0 hok (fun _ h => h.2) hfitS
      hsub hfit hout (hlimM.mono fun _ h => h.1) (hlimU.mono fun _ h => h.1) hexit (fun m h => hUF m h.1) hUS hW.s3)

end StartU

/-! ## `_start` -/

section Entry

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **`_start` as one segment at depth** (`entry_segW'` over `SegWS`):
`xorl %ebp, %ebp`, `andq $-16, %rsp` and the call block lifted at the empty
frames, then the call of `scc_rt_start` (`call_nd_FWKS` with `KC := True`),
its callee's segment `hS` a `SegWS` at `[]` for every frame condition `F'`
stable in the callee's region, kept by `K` and implying `F`. -/
theorem entry_segWS' {W : FragS isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : Code.Start.entryIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -8 + -296) (hhi : 0 ≤ R.hi)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (c0 : Ctl) (hW : EntryW (nilW W) K exe endPc R F (_root_.Executable.labels exe).label c0) {Q : FragS isa}
    (hS : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' → KStable K F' →
      (∀ m, F' m → F m) → ∀ Q' : FragS isa,
      SegWS W K p lbl ms
        ((At exe endPc (R.callee (-8) (-296) 8) F' (startN0 (_root_.Executable.labels exe).label c0)).at []) Q') :
    SegWS W K p lbl ms ((At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0)).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [Code.Start.entryIn, Bool.and_eq_true] at hin
  obtain ⟨⟨hb0, hb1⟩, hb2⟩ := hin
  have h1 : SegW (nilW W) K p lbl (ms []) (At exe endPc R F (entryN0 lab c0)) (At exe endPc R F (entryNC lab c0)) := by
    refine (seg_oneW (flag_ndW (n := entryN0 lab c0) (N := fun _ : Unit => entryN1 lab c0)
      (E := fun e : Empty => e.elim) (fi := .xor_rr32_self .rbp) (z := 2) rfl hF
      (code_field hp hend hb0 (ofNat_zero' _)) hW.xor
      fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(), rfl, rfl, hJ⟩⟩)).seq ?_
    refine sw_seqW (lo := R.lo) (hi := R.hi) (F' := fun v m => v = R.base ∧ F m) (n' := entryN2 lab c0)
      (swand_ndW (k := -16) (z := 4) (n := entryN1 lab c0) (code_field hp hend hb1 rfl) rfl rfl hW.and
        fun m σ c hA hD hJ fl => ?_) fun v _ => ?_
    · have hsp : σ.regs.get64 .rsp = R.base := by
        rw [hA.so .rsp 0 rfl]; simp [Region.addr]
      have hv : (andRegs (-16) σ.regs).get64 .rsp = R.base := by
        simp only [andRegs, Reg64s.get64_set64_self]; rw [hsp]; exact and16 hal
      rw [hv]
      exact ⟨hR, ⟨rfl, hF _ _ hD fun _ _ _ => rfl⟩, σ.slot, fun k hk => hA.slot k hk, c, .refl c, hJ⟩
    refine SegW.mono_pre (P := At exe endPc R F (entryN2 lab c0)) ?_
      fun s c ⟨he, hn, hdc, hpc, σ, hA, ⟨hvb, hD⟩, hJ⟩ => ⟨he, hn, hdc, hpc, σ, by subst hvb; exact hA, hD, hJ⟩
    refine seg_oneW (seg_ndW (N := fun _ : Unit => entryNC lab c0) (E := fun e : Empty => e.elim)
      (by simp [Code.Start.entryCall]) entryCallB_ok hF hR (by omega) (by omega)
      (code_field hp hend hb2 (ofNat_add' _ 2 4)) hW.call
      fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · rw [show (entryN2 lab c0).o = SO.entry from rfl, entryCallB_run]; rfl
    · rw [show (entryN2 lab c0).o = SO.entry from rfl, entryCallB_run]; rfl
    · exact hJ
  exact (SegWS.liftS [] h1 fun _ _ h => h).seq
    ((call_nd_FWKS (KC := True) (nC := entryNC lab c0) (exe := exe) (endPc := endPc)
      (N := fun e : Empty => e.elim) (E := fun e : Empty => e.elim) (e0 := 0) (lo' := -296) (hi' := 8)
      (M := fun _ => True) (F₂ := F) (fs := [])
      (Ne := fun _ : Unit => startN0 lab c0) (Ex := fun _ (e : Empty) => e.elim)
      hR hF (by show R.lo ≤ -8 - 0 + -296; omega) (by decide)
      (by show (-8 : Int) - 0 < R.hi; omega) (by show (-8 : Int) - 0 + 8 ≤ R.hi; omega)
      (by show ((-8 : Int) - 0) % 8 = 0; decide) (by decide) (by decide)
      (fun _ => hFK)
      (fun _ s s' hk hFs k hk' _ => hKR s s' hk hFs k hk')
      (fun _ h _ => h)
      (fun R' F' _ _ _ hF' hK' hFF hR'e _ _ _ _ => by subst hR'e; exact hS F' hF' (hK' trivial) hFF _)
      (fun _ => rfl) (fun σC c hJ => ⟨(), rfl, hJ⟩) fun _ x => x.elim).mono_post
      fun _ _ _ h => h.1.elim (fun ⟨e, _⟩ => e.elim) fun ⟨e, _⟩ => e.elim)

end Entry

end Spike.Lib.X64.Rt
