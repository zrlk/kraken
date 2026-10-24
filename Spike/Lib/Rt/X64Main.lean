/-
**The x86-64 main thread `scc_rt_main`, parametric in the program**
(`mainU_segW`): the hand `main_segW` (`Spike/Lib/X64Ret0.lean`) with the
program's facts as parameters, so that it is proved once and not once per
program. The x86-64 twin of `Spike/Lib/Rt/A64Main.lean`.

- **What varies with the program** (`MainCode`): `scc_rt_main`'s frame `Z`
  (below the saved `%rbp`) and the spill offset `k` of the exit value (from
  `%rbp`), the user function it calls (`fn`), its labels (prologue check,
  grow stub, body entry, return point), and the cells' sizes the emitter
  chose (the prologue's, the parameters' stores `ps`, the exit tail's).
  Today's emitter (an entry with no argument and an integer result) emits
  exactly a stack-checked prologue, one `call fn`, and the `exit_group`
  tail; `mainUIn` is that code check, one boolean on the emitted cells.
- **The user function is an interface** (`UserCallW`), not a proof: from
  its entry (`uN0`: the caller's `%rbp`, the return address in the slot at
  `%rsp`, `%rsp`, the thread pointer and the source control as ghosts; the
  limit word's facts for a frame of `ZU`) a segment to its return (`uNx`: at
  the return address, `%rbp` restored, `%rsp` past the return address, and
  the post `Post` relating the source control and `%rax`), in the callee's
  region of depth `D` below the return address, for every frame condition
  that implies the caller's and the caller's cells outside the callee's
  region holding values.
- **The post is a relation** `Post : Ctl → BitVec 64 → Prop`, as on
  AArch64.
- **Oracle**: on `ret0`, `ret0MC` (frame 32, spill `-16`, `wc_main`) passes
  `mainUIn`, and the hand `wc_main` segment with its `W` obligations gives
  `UserCallW` at that `Post`, `ZU = 16`, `D = 24`
  (`Spike/Lib/Rt/X64MainRet0.lean`).

Where x86-64 differs from AArch64: the call pushes the return address (the
callee's region reaches `8` above the callee's entry `%rsp`, the call node's
offset `8` below the frame's base); the frame's base is `8 + Z` below the
entry `%rsp` (the saved `%rbp`); `%rbp`'s offset after the call is restored
from the invariant (`At.rbp`); the region need not be 16-aligned (the x86-64
call asks no alignment); the cells' sizes are parameters of the code.
-/
import Spike.Lib.Rt.X64Layout
import Spike.Lib.Rt.X64CodeIn

namespace Spike.Lib.X64

open Kraken Kraken.Promising Kraken.Promising.X64

/-! ## The call instruction -/

theorem classify_call (fn : Label) : classify (AI.call fn).toDir = some (.call fn) := rfl

/-- `call fn` from offsets `o`: covered when the return address's cell is. -/
theorem okBlk_callB {lo hi : Int} {o : SO} (fn : Label) (h : Spike.Lib.offOk lo hi (o.sp - 8) = true) :
    okBlk lo hi o (callB fn) = true := by
  simp [okBlk, callB, classify_call, AI.ok, h]

/-- **`call fn`'s run**: to `fn`'s label, the return address pushed. -/
theorem callB_run (lab : Label → Int64) (fn : Label) (pc : Int64) (sp : Int) (rs : List (Reg64 × Int)) (σ : AS) :
    arun lab (callB fn) ⟨pc, ⟨sp, rs⟩, σ⟩ = ⟨lab fn, ⟨sp - 8, rs⟩,
      { σ with regs := σ.regs.set64 .rsp (σ.regs.rsp.toBitVec - 8#64),
               slot := Spike.Lib.upd σ.slot (sp - 8) (pc.toBitVec + 5#64) }⟩ := by
  simp [arun, callB, dstep, classify_call, AI.so, AI.step, AI.tgt]

end Spike.Lib.X64

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (MainG mainN0 WcG LimOk limA seg_oneW CallerCells)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

/-- The hand `mainCall` is `call wc_main`. -/
example : Ret0.mainCall = callB "wc_main" := rfl

/-! ## Nodes -/

/-- The body's offsets: `%rsp` at the frame's base, `%rbp` at the saved
`%rbp`. -/
abbrev oU (Z : Int64) : SO := ⟨-8 - Z.toInt, [(.rbp, -8)]⟩

section Nodes

variable (lab : Label → Int64) (mc : MainCode)

/-- `scc_rt_main`'s body entry, the frame of `Z` set up. -/
def mainU1 (g : MainG) : ND := ⟨lab mc.e0, oU mc.Z, fun σ c =>
  c = g.c0 ∧ σ.regs.rsp.toBitVec = g.sp0 - 8#64 - mc.Z.toBitVec ∧ σ.regs.fsBase = g.tp⟩

/-- The body entry with `%rbp` claimed from its offset (`At.rbp_get`): the
node the call block runs from. -/
def mainU1R (g : MainG) : ND := ⟨lab mc.e0, oU mc.Z, fun σ c =>
  (mainU1 lab mc g).J σ c ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (oU mc.Z).sp)⟩

/-- The call node: at `fn`'s label, the return address `sp0` pushed. -/
def mainUC (g : MainG) : ND := ⟨lab mc.fn, ⟨-8 - mc.Z.toInt - 8, []⟩, fun σ c =>
  (c = g.c0 ∧ σ.regs.rsp.toBitVec = g.sp0 - 8#64 - mc.Z.toBitVec - 8#64 ∧ σ.regs.fsBase = g.tp) ∧
    σ.slot (-8 - mc.Z.toInt - 8) = (lab mc.sp0).toBitVec ∧
    σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - mc.Z.toInt - 8))⟩

/-- Back from `fn`, at `sp0`: the source control and the result in `%rax`
related by the post `Post`, `%rbp` at the saved `%rbp`. -/
def mainUR (Post : Ctl → BitVec 64 → Prop) : ND := ⟨lab mc.sp0, ⟨-8 - mc.Z.toInt, []⟩, fun σ c =>
  Post c σ.regs.rax.toBitVec ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - mc.Z.toInt))⟩

/-- Back from `fn` with `%rbp`'s offset fixed (`At.rbp`): the node the
`exit_group` tail runs from. -/
def mainURR (Post : Ctl → BitVec 64 → Prop) : ND :=
  ⟨lab mc.sp0, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, (mainUR lab mc Post).J⟩

/-- **The user function's entry**: the ghosts' registers and return
address, and the limit word's facts for a frame of `ZU` (`F` the caller's
frame condition). -/
def uN0 (ms : MemSide isa) (F : MachineData → Prop) (fn : Label) (ZU : Int64) (g : WcG) : ND :=
  ⟨lab fn, ⟨0, []⟩, fun σ c =>
    (c = g.c0 ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra ∧ σ.regs.rsp.toBitVec = g.sp ∧
      σ.regs.fsBase = g.tp) ∧ LimOk ms F (limA g.tp) (g.sp - 8#64 - ZU.toBitVec)⟩

end Nodes

/-- **The user function's return**: at the return address, the source
control and `%rax` related by `Post`, `%rbp` restored, `%rsp` past the
return address. -/
def uNx (Post : Ctl → BitVec 64 → Prop) (g : WcG) : ND := ⟨Int64.ofBitVec g.ra, ⟨8, []⟩, fun σ c =>
  Post c σ.regs.rax.toBitVec ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.regs.rsp.toBitVec = g.sp + 8#64⟩

/-! ## The interface and the obligations -/

/-- **The user function called by `scc_rt_main`, as an interface**: in the
callee's region at the call (`8` below the frame of `Z` under the saved
`%rbp`, depth `D` below the return address, the return address's cell
included), for every frame condition `F'` stable there that implies the
caller's `F` and the caller's cells outside the callee's region holding
values, and every ghost with the call's return address `ra`, source control
`c0` and thread pointer `tp`, a segment inside `W` from its entry `uN0`
(limit room `ZU`) to its return `uNx` with `Post` of the source control and
`%rax`. -/
def UserCallW (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) (ra : BitVec 64) (c0 : Ctl)
    (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
    FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
    (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
    ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      SegW W K p lbl ms
        (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
          (uN0 (_root_.Executable.labels exe).label ms F fn ZU g))
        (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' (uNx Post g))

/-- **`scc_rt_main`'s own states inside `W`**, none moved by `K`: its
prologue's, the call block's and the `exit_group` tail's. -/
structure MainUW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (mc : MainCode)
    (Post : Ctl → BitVec 64 → Prop) (g : MainG) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") mc.Z 8 mc.grow
    mc.zl mc.zf mc.z1 mc.z2 mc.zs mc.ps (mainN0 (_root_.Executable.labels exe).label g).J
  call : BlkW W K exe endPc R F (mainU1R (_root_.Executable.labels exe).label mc g) (callB mc.fn)
  exit : XExitW W K exe endPc R F (mainURR (_root_.Executable.labels exe).label mc Post) (-8 - mc.Z.toInt) (-8)
    mc.k mc.ze0 mc.ze1 mc.ze2

/-! ## The segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- `%rbp`'s offset moved by `8` with `%rsp`. -/
private theorem rbp_shift (r : BitVec 64) (z : Int) :
    r + BitVec.ofInt 64 (-8 - (-8 - z)) = r - 8#64 + BitVec.ofInt 64 (-8 - (-8 - z - 8)) := by
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  show r + y = r - 8#64 + (y + 8#64)
  bv_omega

/-- **`scc_rt_main` does not return, inside `W`**, in any valid layout of
any cells with `mainUIn`: from its entry (`%rsp` at offset 0 of a region
holding its frame, the return address it pushes and the callee's `D`) a
segment to any fragment, given the limit word's facts for its frame and the
callee's room `ZU`, the user function's interface `hU`, and that the
`exit_group` there off an abort site is `main`'s exit for every control and
value `Post` relates (`hexit`). The call asks no closure under `K` of the
callee (`call_nd_FWK` with `KC := False`). -/
theorem mainU_segW {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) {mc : MainCode} (hin : mainUIn cells mc = true)
    (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - mc.Z.toInt - 8 - D) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - mc.Z.toBitVec - 8#64 - 8#64 - ZU.toBitVec))
    (hU : UserCallW W K p lbl ms exe endPc R F mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.sp0).toBitVec g.c0 g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : MainUW W K exe endPc R F ms mc Post g)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainUIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hpro, hblk⟩, hgap⟩, hex⟩ := hin
  have esp0 := label_labelGapB hp hgap
  have hloZ : R.lo ≤ -8 - mc.Z.toInt := by omega
  refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainU1 lab mc g) hZ hF hR hloZ hhi hps rfl
    (by simp [SO.le, lk, mainU1]) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (mainUC lab mc g)) ?_
      (SegW.seq (Q := At exe endPc R F (mainUR lab mc Post)) ?_
        ((exitTail_seg_ofW (lo := -8 - mc.Z.toInt) (hi := 0) hp hend hex (n := mainURR lab mc Post) rfl rfl hK hF
            hR hloZ hhi hk hW.exit fun s c σ0 hJ0 hs => ?_).mono_pre
          fun _ _ h => At.rbp h fun _ _ h => h.2)))
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
        exact rbp_shift _ _
  · -- the call
    refine seg_oneW (call_nd_FWK (KC := False) (e0 := 0) (lo' := -D) (hi' := 8) (M := fun _ => True)
      (Ne := uN0 lab ms F mc.fn ZU) (Ex := fun g _ => uNx Post g)
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
          (htp'.symm.trans htp)).mono_post fun _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, -, -⟩
      refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-8 - mc.Z.toInt - 8 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - ZU.toBitVec)
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
        have := rbp_shift (σC.regs.rsp.toBitVec + 8#64) mc.Z.toInt
        rw [show σC.regs.rsp.toBitVec + 8#64 - 8#64 = σC.regs.rsp.toBitVec by bv_omega] at this
        exact this.symm
  · -- the exit: `exit_group(v)`
    have hP := hJ0.1
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hs
    exact SysOk.exitGroup_main (v := σ0.regs.rax.toBitVec.toNat)
      (hexit s c _ hP ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.rdi.toBitVec = _; rw [hx]⟩)

end Proof

end Spike.Lib.X64.Rt
