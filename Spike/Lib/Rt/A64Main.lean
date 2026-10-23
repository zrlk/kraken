/-
**The AArch64 main thread `scc_rt_main`, parametric in the program**
(`mainU_segW`): the hand `main_segW` (`Spike/Lib/A64Ret0.lean`) with the
program's facts as parameters, so that it is proved once and not once per
program.

- **What varies with the program** (`MainCode`): `scc_rt_main`'s frame `Z`
  and the spill offset `k` of the exit value (from the placement data),
  the user function it calls (`fn`), and its labels (prologue check, grow
  stub, body entry, return point). Today's emitter (`mainThreadF` for an
  entry with no argument and an integer result) emits exactly a
  stack-checked prologue saving `x0`, one `bl fn`, and the `exit_group`
  tail; `mainUIn` is that code check, one boolean on the emitted text.
- **The user function is an interface** (`UserCallW`), not a proof: from
  its entry (`uN0`: the caller's `x29`, the return address, `sp`, the
  thread pointer and the source control as ghosts; the limit word's facts
  for a frame of `ZU`) a segment to its return (`uNx`: at the return
  address, `x29`/`x30` restored, `sp` back, and the post `Post` relating
  the source control and `x0`), in the callee's region of depth `D` at the
  call, for every frame condition that implies the caller's and the
  caller's cells outside the callee's region holding values. This is the
  statement the program's own segments supply.
- **The post is a relation** `Post : Ctl → BitVec 64 → Prop`, so that a
  callee may leave the source control where it was (the hand `wc_main`
  does, `Post c v := c = c0 ∧ v = 42#64`) or run it on by local steps;
  `hexit` asks `main`'s exit for every control and value `Post` relates.
- **Oracle**: on `ret0`, `ret0MC` (frame 48, spill 8, `wc_main`) passes
  `mainUIn`, and the hand `wc_main` segment with its `W` obligations gives
  `UserCallW` at that `Post`, `ZU = D = 32` (`Spike/Lib/Rt/A64MainRet0.lean`).
-/
import Spike.Lib.Rt.A64Layout
import Spike.Lib.Rt.A64CodeIn

namespace Spike.Lib.A64.Flow

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64

/-! ## The call instruction -/

/-- `bl fn` at any offsets: covered. -/
theorem okBlk_blD (lo hi : Int) (o : SO) (fn : Label) : okBlk lo hi o [blD fn] = true := by
  simp [okBlk, blD, classify, AI.ok]

/-- **`bl fn`'s run**: to `fn`'s label, the return address in `x30`. -/
theorem blD_run (lab : Label → Int64) (fn : Label) (pc : Int64) (Z : Int) (σ : AS) :
    arun lab [blD fn] ⟨pc, ⟨Z, []⟩, σ⟩ =
      ⟨lab fn, ⟨Z, []⟩, { σ with regs := σ.regs.setXReg .X30 (pc + 4).toBitVec }⟩ := by
  simp [arun, blD, dstep, classify, AI.so, AI.step, AI.tgt, SO.kill, Spike.Lib.rm, Ret0.ofInt_bmod]
  rw [BitVec.ofInt_add]
  congr 1
  rw [show pc.toInt = pc.toBitVec.toInt from rfl, BitVec.ofInt_toInt]; rfl

end Spike.Lib.A64.Flow

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (MainG mainN0 WcG LimOk limA tcbA_limA setXReg_TPIDR ofInt_bmod seg_oneW
  CallerCells)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

/-- The hand `mainCall` is `bl wc_main`. -/
example : Ret0.mainCall = [blD "wc_main"] := rfl

/-! ## The program's facts

`MainCode` and `mainUIn` are in `Spike/Lib/Rt/A64CodeIn.lean`, so that the
placement check reads them without the proofs. -/

/-! ## Nodes -/

section Nodes

variable (lab : Label → Int64) (mc : MainCode)

/-- `scc_rt_main`'s body entry, the frame of `Z` set up. -/
def mainU1 (g : MainG) : ND := ⟨lab mc.e0, ⟨-mc.Z.toInt, []⟩, fun σ c =>
  c = g.c0 ∧ σ.regs.SP.toBitVec = g.sp0 - mc.Z.toBitVec ∧ σ.regs.TPIDR_EL0 = g.tp⟩

/-- The call node: at `fn`'s label, the return address `sp0`. -/
def mainUC (g : MainG) : ND := ⟨lab mc.fn, ⟨-mc.Z.toInt, []⟩, fun σ c =>
  (c = g.c0 ∧ σ.regs.SP.toBitVec = g.sp0 - mc.Z.toBitVec ∧ σ.regs.TPIDR_EL0 = g.tp) ∧
    σ.regs.X30.toBitVec = (lab mc.e0 + 4).toBitVec⟩

/-- Back from `fn`, at `sp0`: the source control and the result in `x0`
related by the post `Post`. -/
def mainUR (Post : Ctl → BitVec 64 → Prop) : ND := ⟨lab mc.sp0, ⟨-mc.Z.toInt, []⟩, fun σ c =>
  Post c σ.regs.X0.toBitVec⟩

/-- **The user function's entry**: the ghosts' registers, and the limit
word's facts for a frame of `ZU` (`F` the caller's frame condition). -/
def uN0 (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (fn : Label) (ZU : Int64) (g : WcG) : ND := ⟨lab fn, ⟨0, []⟩, fun σ c =>
  (c = g.c0 ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧ σ.regs.SP.toBitVec = g.sp ∧
    σ.regs.TPIDR_EL0 = g.tp) ∧ LimOk ms F exe endPc (limA g.tp) (g.sp - ZU.toBitVec)⟩

end Nodes

/-- **The user function's return**: at the return address, the source
control and `x0` related by `Post`, `x29`/`x30` restored, `sp` at the
entry's offset. -/
def uNx (Post : Ctl → BitVec 64 → Prop) (g : WcG) : ND := ⟨Int64.ofBitVec g.ra, ⟨0, []⟩, fun σ c =>
  Post c σ.regs.X0.toBitVec ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra⟩

/-! ## The interface and the obligations -/

/-- **The user function called by `scc_rt_main`, as an interface**: in the
callee's region at the call (depth `D` below the caller's frame of `Z`), for
every frame condition `F'` stable there that implies the caller's `F` and
the caller's cells outside the callee's region holding values, and every
ghost with the call's return address `ra`, source control `c0` and thread
pointer `tp`, a segment inside `W` from its entry `uN0` (limit room `ZU`) to
its return `uNx` with `Post` of the source control and `x0`. -/
def UserCallW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) (ra : BitVec 64) (c0 : Ctl)
    (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK → (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 →
    FStable (R.callee (-Z.toInt) (-D) 0) F' → (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
    ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      SegW W K p lbl ms
        (At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (uN0 (_root_.Executable.labels exe).label ms F exe endPc fn ZU g))
        (At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (uNx Post g))

/-- **`scc_rt_main`'s own states inside `W`**, none moved by `K`: its
prologue's, the call block's and the `exit_group` tail's. -/
structure MainUW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (mc : MainCode)
    (Post : Ctl → BitVec 64 → Prop) (g : MainG) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") mc.Z 8 mc.grow [(.X0, 0)]
    (mainN0 (_root_.Executable.labels exe).label g).J
  call : BlkW W K exe endPc R F (mainU1 (_root_.Executable.labels exe).label mc g) [blD mc.fn]
  exit : ExitW W K exe endPc R F (mainUR (_root_.Executable.labels exe).label mc Post) mc.k

/-! ## The segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_main` does not return, inside `W`**, in any valid layout of
any program with `mainUIn`: from its entry (`sp` at offset 0 of a region
holding its frame of `Z` and the callee's `D`) a segment to any fragment,
given the limit word's facts for its frame and the callee's room `ZU`, the
user function's interface `hU`, and that the `exit_group` there off an abort
site is `main`'s exit for every control and value `Post` relates (`hexit`). The call asks no
closure under `K` of the callee (`call_nd_FWK` with `KC := False`). -/
theorem mainU_segW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe prog)
    (hend : endPc = endOf exe prog) {mc : MainCode} (hin : mainUIn prog mc = true)
    (h16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -mc.Z.toInt - D) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk ms F exe endPc (limA g.tp) (g.sp0 - mc.Z.toBitVec))
    (hlimU : LimOk ms F exe endPc (limA g.tp) (g.sp0 - mc.Z.toBitVec - ZU.toBitVec))
    (hU : UserCallW W K p lbl ms exe endPc R F mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec g.c0 g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : MainUW W K exe endPc R F ms mc Post g)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainUIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hpro, hblk⟩, hgap⟩, hex⟩ := hin
  have esp0 := label_labelGap hp hgap
  have hloZ : R.lo ≤ -mc.Z.toInt := by omega
  refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainU1 lab mc g) h16 hZ hF hR hal hloZ hhi
    (by simp [Spike.Lib.offOk]; omega) rfl (by simp [SO.le, oFr, mainU1]) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (mainUC lab mc g)) ?_
      (SegW.seq (Q := At exe endPc R F (mainUR lab mc Post)) ?_
        (exitTail_seg_ofW hp hend hex (n := mainUR lab mc Post) rfl hK hF hR hal (lo := -mc.Z.toInt) (hi := 0)
          hloZ hhi hk (by show (-mc.Z.toInt) % 16 = 0; omega) hW.exit fun s c σ0 hJ hAt => ?_)))
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
  · -- the call
    refine seg_oneW (call_nd_FWK (KC := False) (lo' := -D) (hi' := 0) (M := fun _ => True)
      (Ne := uN0 lab ms F exe endPc mc.fn ZU) (Ex := fun g _ => uNx Post g)
      hR hal hF (by show R.lo ≤ -mc.Z.toInt + -D; omega) (by omega) (by show -mc.Z.toInt < R.hi; omega)
      (by decide) (by show (-mc.Z.toInt) % 16 = 0; omega) (by omega) (by decide) (fun h => h.elim)
      (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hal' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨hc, -, htp⟩, h30⟩, ⟨⟨hc', -, h30', -, htp'⟩, -⟩⟩ := hg'
        exact (hU F' hR' hal' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' (h30'.symm.trans h30)
          (hc'.symm.trans hc) (htp'.symm.trans htp)).mono_post fun _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, h30⟩
      refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - ZU.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' x σC c σx c' σR ⟨⟨rfl, -, -⟩, h30⟩ ⟨⟨-, -, h30', -⟩, -⟩ ⟨hP, -, -⟩ hreg - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainUR, mainUC, uNx], ?_⟩
      · show lab mc.sp0 = Int64.ofBitVec g'.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, Spike.Lib.int64_ofBitVec_toBitVec]; exact esp0
      · show Post c' σR.regs.X0.toBitVec
        rw [hreg]; exact hP
  · -- the exit: `exit_group(v)`
    have hP := hJ
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
    exact SysOk.exitGroup_main (v := σ0.regs.X0.toBitVec.toNat)
      (hexit s c _ hP ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.X0.toBitVec = _; rw [hx]⟩)

end Proof

end Spike.Lib.A64.Rt
