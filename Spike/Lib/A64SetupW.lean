/-
**A setup block on AArch64 from its call to its return, for any program**:
`scc_rt_main`'s first callee (the user's rodata function: buffer
allocations, lane stores and moves, no output) as the setup call's
interface `SetupCallW`. The prologue checks a frame of `ZU` bytes; the body
is a walk over the function's blocks, each step a segment to the next node
or to the heap abort; the thread pointer is kept across the whole call; a
heap abort does not return.

- `chainW`: steps `A k → A (k + 1)` for `k < n` and a last step `A n → Q`,
  every step free to leave to an exit `X`, compose to `A 0 → Q`;
- `entJ`, `sEn`: the body's entry after the prologue (the caller's frame
  record saved at `-16`, `-8`); `sRet`: the return at the caller's return
  address, `PostS` of the control and the registers, `x29`/`x30` restored;
  `sAb`: the heap abort at `allocAbortDepth fs` below the entry `sp`, `x0 =
  2`, the control as `Ab` has it;
- `blk_stepW`, `ret_stepW`, `alloc_stepW`, `lane_stepW`: the walk's steps (a
  straight block to a node; a block ending in `ret` to `sRet`;
  `NewBuf.newBuf_blkW` to the allocator's landing or `sAb`;
  `LaneStore.lane_storeW` to the node after the store);
- `callOK_tp`, `callOK_untp`, `limOk_tp`, `proW_tp`: the memory side's facts
  moved to a thread pointer (`tpXa`);
- `setup_callW`: the prologue, the body (a segment inside `NoMsrW W K` under
  `tpXa ms g.tp`), the heap abort, `sp` and the thread pointer restored: a
  segment from `uN0` to `uNxS PostS`;
- `setupCallW_intro`: `SetupCallW` from `setup_callW`'s premises for every
  callee frame condition and ghost, the callee's region reaching
  `allocAbortDepth ZU + 48` below the call.
-/
import Spike.Lib.A64Hello1RodataTP
import Spike.Lib.A64AbortHeapW
import Spike.Lib.A64NewBuf
import Spike.Lib.A64LaneStore
import Spike.Lib.Rt.A64MainS

namespace Spike.Lib.A64.Flow

namespace Setup

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap)
open Spike.Lib.A64.KeepTP (TP tpXa dNoMsr isMsr)
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk WcG limA tcbA_limA)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.A64.Rt (uN0 uNxS SetupCallW)
open NewBuf (allocAbortDepth allocFrame NBX nbX nbJc newBuf_blkW AllocCtx)

set_option linter.unusedSimpArgs false

/-! ## A chain of segments -/

/-- **A chain of segments**: from `A 0` through `A n` to `Q`, every step
free to leave to the exit `X`. -/
theorem chainW {I : ISA} {W : Frag I} {K : I.State → I.State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {A : Nat → Frag I} {Q X : Frag I} :
    ∀ n : Nat, (∀ k < n, SegW W K p lbl ms (A k) (fun s c => A (k + 1) s c ∨ X s c)) →
      SegW W K p lbl ms (A n) (fun s c => Q s c ∨ X s c) → SegW W K p lbl ms (A 0) (fun s c => Q s c ∨ X s c)
  | 0, _, h => h
  | n + 1, hs, h => chainW n (fun k hk => hs k (by omega))
      (((hs n (by omega)).seq_left h).mono_post fun _ _ h => h.elim id .inr)

/-! ## The nodes -/

section Nodes

variable (lab : Label → Int64)

/-- **The body's invariant after the prologue**: some entry state of `J0`
with the source control, its `x29` and `x30` saved at `-16` and `-8`. -/
def entJ (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J0 σe c ∧ σ.slot (-16) = σe.regs.X29.toBitVec ∧ σ.slot (-8) = σe.regs.X30.toBitVec

/-- **The body's entry**: the label `entry`, `sp` at `-ZU`. -/
def sEn (entry : Label) (ZU : Int64) (J0 : AS → Ctl → Prop) : ND := ⟨lab entry, ⟨-ZU.toInt, []⟩, entJ J0⟩

/-- **The return**: at the caller's return address, `PostS` of the control
and the registers, the frame record restored. -/
def sRet (PostS : Ctl → Reg64s → Prop) (g : WcG) : ND := ⟨Int64.ofBitVec g.ra, ⟨0, []⟩, fun σ c =>
  PostS c σ.regs ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra⟩

/-- **The heap abort** of an allocation in a frame of `fs` bytes: at
`scc_rt_abort`, `allocAbortDepth fs` below the entry `sp`, `x0 = 2`, the
control as `Ab` has it. -/
def sAb (fs : Int) (Ab : Ctl → Prop) : ND := ⟨lab "scc_rt_abort", ⟨-allocAbortDepth fs, []⟩, fun σ c =>
  σ.regs.X0 = 2 ∧ Ab c⟩

end Nodes

/-! ## The memory side with the allocation's landing at a thread pointer -/

section Tp

variable {ms : MemSide isaLSE2} {t : UInt64}

theorem callOK_tp {lab : Label → Int64} {q : Call} (h : q.OK ms lab) : q.OK (tpXa ms t) lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

theorem callOK_untp {lab : Label → Int64} {q : Call} (h : q.OK (tpXa ms t) lab) : q.OK ms lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

theorem limOk_tp {F : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64} {a Z : BitVec 64}
    (h : LimOk ms F exe endPc a Z) : LimOk (tpXa ms t) F exe endPc a Z :=
  ⟨h.rt, h.mp, h.unmapped, h.room⟩

theorem proW_tp {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : AS → Ctl → Prop} (h : ProW W K exe endPc R F ms pc0 Z lim L ps J) :
    ProW W K exe endPc R F (tpXa ms t) pc0 Z lim L ps J :=
  ⟨h.w0, h.w1, h.w2, h.w3⟩

end Tp

/-! ## The walk's steps -/

section Steps

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isaLSE2} {K : State → State → Prop}

/-- **A straight block to a node**: the block `blk` at node `n` to the node
`n'`, its end hitting `n'` after a local run of the source (`hedge`). -/
theorem blk_stepW {n n' : ND} {lo hi : Int} {blk : List Directive} (hne : blk ≠ [])
    (hok : okBlk lo hi n.o blk = true) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hW : BlkW W K exe endPc R F n blk)
    (hedge : ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧ Hit n' (arun (_root_.Executable.labels exe).label blk
      ⟨n.pc, n.o, σ⟩) c') :
    SegW W K p lbl ms (At exe endPc R F n) (At exe endPc R F n') := by
  refine (seg_ndW (N := fun _ : Unit => n') (E := fun e : Empty => e.elim) hne hok hF hR hal hlo hhi hc hW
    fun σ c hJ => ?_).mono_post fun s c h => ?_
  · obtain ⟨c', hr, hh⟩ := hedge σ c hJ
    exact ⟨c', hr, .inl ⟨(), hh⟩⟩
  · rcases h with ⟨_, h⟩ | ⟨x, _⟩
    · exact h
    · exact x.elim

/-- **The last block, ending in `ret`, to the return**: the block's end at
the caller's return address with `sp` at the entry's, `PostS` of the
registers there and the source after a local run, the frame record
restored (`hedge`). -/
theorem ret_stepW {n : ND} {lo hi : Int} {blk : List Directive} {PostS : Ctl → Reg64s → Prop} {g : WcG}
    (hne : blk ≠ []) (hok : okBlk lo hi n.o blk = true) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hW : BlkW W K exe endPc R F n blk)
    (hedge : ∀ σ c, n.J σ c →
      (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc = Int64.ofBitVec g.ra ∧
      (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).so.sp = 0 ∧
      ∃ c', LocalRun p c c' ∧ (sRet PostS g).J (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).σ c') :
    SegW W K p lbl ms (At exe endPc R F n) (At exe endPc R F (sRet PostS g)) := by
  refine blk_stepW hne hok hF hR hal hlo hhi hc hW fun σ c hJ => ?_
  obtain ⟨hpc, hsp, c', hr, hx⟩ := hedge σ c hJ
  refine ⟨c', hr, hpc.symm, ?_, hx⟩
  simp [SO.le, hsp, sRet]

/-- **A buffer allocation as a step** (`newBuf_blkW`): to the allocator's
landing `pcR` at an invariant `Jn` its return gives (`hret`), or to the heap
abort with `Ab` of the control its abort gives (`hab`); the allocator's
states asked in the call's context (`AllocCtx`). -/
theorem alloc_stepW [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {fs : Int} (hfs : fs % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth fs) (hkc : -fs < R.hi)
    {B : List Directive} {pc pcR : Int64} {lo hi : Int} {J J1 Jn : AS → Ctl → Prop} {Ab : Ctl → Prop}
    (hne : B ≠ []) (hok : okBlk lo hi ⟨-fs, []⟩ B = true) (hlo0 : R.lo ≤ lo) (hhi0 : hi ≤ R.hi)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc B)
    (ha : ∀ σ, (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).pc =
        (_root_.Executable.labels exe).label "scc_rt_alloc" ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).so = ⟨-fs, []⟩)
    (hloc : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X0.toBitVec = q.h ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X1.toBitVec = q.k ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X2.toBitVec = q.u ms)
    (hra : ∀ σ c, J1 σ c →
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X30.toBitVec = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs, []⟩ mC σC ∧
        nbJc (_root_.Executable.labels exe).label B pc ⟨-fs, []⟩ J1 σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs) σC) c ∧
        CKept R (-fs) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs) (-160) 0) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hWB : BlkW W K exe endPc R F ⟨pc, ⟨-fs, []⟩, J⟩ B)
    (hW : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs) (-160) 0) (fun m => F m ∧ CallerCells R (-fs) (-160) 0 m ∧
        AllocCtx ms (_root_.Executable.labels exe).label R fs (nbJc (_root_.Executable.labels exe).label B pc
          ⟨-fs, []⟩ J1) q m))
    (hret : ∀ σ c, (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR
      (nbJc (_root_.Executable.labels exe).label B pc ⟨-fs, []⟩ J1) .ret).J σ c → Jn σ c)
    (hab : ∀ c, (∃ q : {q : Call // q.OK ms (_root_.Executable.labels exe).label}, Jfull ms q.1 c ∧
      ∃ σC, nbJc (_root_.Executable.labels exe).label B pc ⟨-fs, []⟩ J1 σC q.1.c0) → Ab c) :
    SegW W K p lbl ms (At exe endPc R F ⟨pc, ⟨-fs, []⟩, J⟩)
      (fun s c => At exe endPc R F ⟨pcR, ⟨-fs, []⟩, Jn⟩ s c ∨
        At exe endPc R F (sAb (_root_.Executable.labels exe).label fs Ab) s c) := by
  refine (newBuf_blkW hp hend hprog hF hR hal hfs hlo hkc hne hok hlo0 hhi0 hc ha hloc hq hra hmem hxa hWB
    hW).mono_post fun s c ⟨x, h⟩ => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  cases x
  · exact .inl ⟨he, hn, hdc, hpc, σ, hA, hD, hret σ c hJ⟩
  · obtain ⟨h0, q, hf, σC, hJC, -⟩ := hJ
    exact .inr ⟨he, hn, hdc, hpc, σ, hA, hD, h0, hab c ⟨q, hf, σC, hJC⟩⟩

/-- **A lane store as a step** (`lane_storeW`), never to the exit. -/
theorem lane_stepW {X : Frag isaLSE2} {B1 B2 : List Directive}
    {pc pcL pcS : Int64} {o oL oS : SO} {lo hi : Int} {t b t' : XReg} {i : Int64}
    {w ov bn : String} {sg : Bool} {wd : Wd} {Kw : Nat} {i' : Nat} {e : Expr} {J J' : AS → Ctl → Prop}
    (h1ne : B1 ≠ []) (h2ne : B2 ≠ []) (hok1 : okBlk lo hi o B1 = true) (hok2 : okBlk lo hi (oL.kill t) B2 = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc B1)
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcL [ldrDir t b i])
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pcL + Int64.ofNat 4) B2)
    (hc4 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcS [strDir t' b i])
    (ha1 : ∀ σ, (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).pc = pcL ∧
      (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).so = oL)
    (ha2 : ∀ σ, (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat 4, oL.kill t, σ⟩).pc = pcS ∧
      (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat 4, oL.kill t, σ⟩).so = oS)
    (hle : SO.le oL oL = true ∧ SO.le (oL.kill t) (oL.kill t) = true ∧ SO.le oS oS = true)
    (hbw : bn ≠ w) (hK : Kw < 2 ^ 64)
    (ht : ∀ σ c, J σ c →
      c.term = .let_ w (.asLanes sg wd (.lit Kw)) (.let_ ov (.xchgAt (.var bn) (.lit i') (.var w)) e))
    (hsrc : ∀ σ c, J σ c → ∃ (ty : Ty) (pw : TermRun.Word) (μ : Mode) (l : WeakMem.AllocLabel) (A : Nat),
      TermRun.evalAt c.env (.var bn) = some (ty, [pw]) ∧ pw.val = .loc ⟨l, 0⟩ 0 ∧
      TermRun.bufElem ty = some (μ, .lanes sg wd) ∧ lbl l = some A ∧
      (rAddr (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ.regs b i).toNat = A + 8 * i' ∧
      (∀ m, F m → Mem.loadInt m.dmem (rAddr (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ.regs b i) 8
        = none) ∧
      ∀ r : BitVec 64,
        let σ1 := (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ
        let σ2 := (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat 4, oL.kill t, ldStep t r σ1⟩).σ
        rAddr σ2.regs b i = rAddr σ1.regs b i ∧
        ((σ2.regs.getRegOrZr (.low (.reg t') .W64)).setWidth 128).toNat = Kw ∧
        ∀ wold : TermRun.Word,
          J' σ2 ⟨e, (ov, .lanes sg wd, [wold]) :: (LaneStore.lsC1 w ov bn sg wd Kw i' e c).env, none⟩)
    (hW1 : BlkW W K exe endPc R F ⟨pc, o, J⟩ B1)
    (hWL : NodeW W K exe endPc R F
      (LaneStore.lsNL (_root_.Executable.labels exe).label B1 pc pcL o oL w ov bn sg wd Kw i' e J))
    (hW2 : BlkW W K exe endPc R F
      (LaneStore.lsNH (_root_.Executable.labels exe).label B1 pc pcL o oL t b i w ov bn sg wd Kw i' e J) B2)
    (hWS : NodeW W K exe endPc R F
      (LaneStore.lsNS (_root_.Executable.labels exe).label B1 B2 pc pcL pcS o oL oS t b i w ov bn sg wd Kw i' e J)) :
    SegW W K p lbl ms (At exe endPc R F ⟨pc, o, J⟩)
      (fun s c => At exe endPc R F ⟨pcS + Int64.ofNat 4, oS, J'⟩ s c ∨ X s c) :=
  (LaneStore.lane_storeW h1ne h2ne hok1 hok2 hF hR hal hlo hhi hc1 hc2 hc3 hc4 ha1 ha2 hle hbw hK ht hsrc
    hW1 hWL hW2 hWS).mono_post fun _ _ h => .inl h

end Steps

/-! ## The setup call -/

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **A setup block is one segment inside `W`** in any valid layout of a
program `prog`: from the setup call's entry `uN0` (the function `fn` with
the prologue of `prologueIn`, a frame of `ZU` bytes checked against the
limit word, no parameters) to its return `uNxS PostS` (`PostS` of the
control and the registers, the frame record, `sp` and the thread pointer as
at the call), in a region reaching `allocAbortDepth ZU + 48` below the
entry `sp` (the frame, the allocator's and the heap abort's). The
prologue's states lie in `W` (`hWpro`); the body, from `sEn` after the
prologue to the return or the heap abort, is a segment inside `NoMsrW W K`
under the memory side with allocations landing at the call's thread
pointer (`hbody`, a walk of `blk_stepW`, `alloc_stepW`, `lane_stepW` and
`ret_stepW` by `chainW`); the heap abort's path is given per caller's state
and control (`hstub`). -/
theorem setup_callW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hK : ms.K = some Scc.Sem.A64.abi)
    {fn sc entry L : Label} {ZU : Int64} (hin : prologueIn prog fn sc entry ZU 8 L [] = true)
    (h16 : ZU.toInt % 16 = 0) (hZ : 16 ≤ ZU.toInt)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -allocAbortDepth ZU.toInt - 48) (hhi : 0 ≤ R.hi)
    {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m) (g : WcG)
    {PostS : Ctl → Reg64s → Prop} {Ab : Ctl → Prop}
    (hWpro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) ZU 8 L []
      (uN0 (_root_.Executable.labels exe).label ms F0 exe endPc fn ZU g).J)
    (hbody : SegW (NoMsrW W K) K p lbl (tpXa ms g.tp)
      (At exe endPc R F (sEn (_root_.Executable.labels exe).label entry ZU
        (uN0 (_root_.Executable.labels exe).label ms F0 exe endPc fn ZU g).J))
      (fun s c => At exe endPc R F (sRet PostS g) s c ∨
        At exe endPc R F (sAb (_root_.Executable.labels exe).label ZU.toInt Ab) s c))
    (hstub : ∀ m0 σC c0, σC.regs.X0 = 2 → Ab c0 →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-allocAbortDepth ZU.toInt) (-48) 0)
        (fun m => F m ∧ CKept R (-allocAbortDepth ZU.toInt) (-48) 0 m0 m ∧
          Abs R ⟨-allocAbortDepth ZU.toInt, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (uN0 (_root_.Executable.labels exe).label ms F0 exe endPc fn ZU g))
      (At exe endPc R F (uNxS PostS g)) := by
  let lab := (_root_.Executable.labels exe).label
  let J0 := (uN0 lab ms F0 exe endPc fn ZU g).J
  let ms' := tpXa ms g.tp
  have hAD : allocAbortDepth ZU.toInt = ZU.toInt + 160 := rfl
  -- the prologue, inside `NoMsrW W K`
  have hpro : SegW (NoMsrW W K) K p lbl ms' (At exe endPc R F ⟨lab fn, ⟨0, []⟩, J0⟩)
      (At exe endPc R F (sEn lab entry ZU J0)) := by
    have hin' := hin
    simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin'
    obtain ⟨g0, b0, b1, b2, b3, -⟩ := hin'
    have e0 := label_labelGap hp g0
    rw [ofNat4_zero] at e0
    have hWN : ProW (NoMsrW W K) K exe endPc R F ms (lab fn) ZU 8 L [] J0 := by
      refine ProW.noMsr hWpro (code_of hp hend b0 ?_) (code_of hp hend b1 ?_) (code_of hp hend b2 ?_)
        (code_of hp hend b3 ?_) (by simp [chkHead, dNoMsr, isMsr]) (by simp [ldrDir, dNoMsr, isMsr])
        (by simp [chkBr, dNoMsr, isMsr]) (by simp [frameSet, frSetup, spStr, dNoMsr, isMsr])
      · rw [e0, ofNat4_zero]
      · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]; rfl
      · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]; rfl
      · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]; rfl
    refine prologue_seg_ofW hp hend hin h16 hZ hF hR hal (by simp only [hAD] at hlo; omega) hhi
      (by simp) rfl (by simp [SO.le, sEn, oFr]) (proW_tp hWN) ?_
    intro σ c hJ
    obtain ⟨⟨hc, h29, h30, hsp, htp⟩, hl⟩ := id hJ
    have hl' : LimOk ms' F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - ZU.toBitVec) := by
      rw [tcbA_limA htp, hsp]; exact limOk_tp (hl.mono hFF)
    refine ⟨hl'.rt, hl'.mp, hl'.unmapped, fun v hv => ⟨hl'.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs]
  have hB := SegW.keepTPN (t := g.tp) hK (hpro.seq hbody)
  -- the heap abort
  have hAb : SegW W K p lbl ms (At exe endPc R F (sAb lab ZU.toInt Ab)) (fun _ _ => False) := by
    refine Abort.Disp.seg_jabort2W rfl ?_ hF hR hal (by show R.lo ≤ -allocAbortDepth ZU.toInt - 48; exact hlo)
      (by show -allocAbortDepth ZU.toInt < R.hi; omega)
      (by show (-allocAbortDepth ZU.toInt) % 16 = 0; omega) hK ?_
    · rintro σ c ⟨h2, -⟩
      show σ.regs.X0.toNat = 2
      rw [h2]; rfl
    · rintro m0 σC c0 ⟨h2, hab⟩
      exact hstub m0 σC c0 h2 hab
  have hC := SegW.seq_left (hB.mono_post (Q' := fun s c => At exe endPc R F (sAb lab ZU.toInt Ab) s c ∨
    (At exe endPc R F (sRet PostS g) s c ∧ TP g.tp s)) fun s c ⟨h, ht⟩ =>
    h.elim (fun h => .inr ⟨h, ht⟩) fun h => .inl h) hAb
  refine (SegW.of_imp (L := R.addr 0 = g.sp) fun hL => (hC.mono_post fun s c h => ?_)).mono_pre
    fun s c h => ?_
  · rcases h with h | ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ, h29, h30⟩, ht⟩
    · exact h.elim
    refine ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, h29, h30, ?_, ?_⟩
    · have := hA.so .SP 0 rfl
      rw [← hL]; exact this
    · rw [← hA.regs]; exact ht
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨hc, h29, h30, hsp, htp⟩, hl⟩ := id h
    refine ⟨⟨h, ?_⟩, ?_⟩
    · show s.st.1.regs.TPIDR_EL0 = g.tp
      rw [hA.regs]; exact htp
    · rw [← hsp]; exact (hA.so .SP 0 rfl).symm

/-- **The setup call's interface from `setup_callW`**: in the callee's
region at the call (depth `D` below the caller's frame of `Z`, reaching
`allocAbortDepth ZU + 48`), for every callee frame condition and ghost with
the call's return address, source control and thread pointer, the
prologue's obligations, the body and the heap abort's paths. -/
theorem setupCallW_intro {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hK : ms.K = some Scc.Sem.A64.abi)
    {fn sc entry L : Label} {ZU Z : Int64} {D : Int} (hin : prologueIn prog fn sc entry ZU 8 L [] = true)
    (h16 : ZU.toInt % 16 = 0) (hZ : 16 ≤ ZU.toInt) (hD : allocAbortDepth ZU.toInt + 48 ≤ D)
    {PostS : Ctl → Reg64s → Prop} {ra : BitVec 64} {c0 : Ctl} {tp : UInt64} {Ab : WcG → Ctl → Prop}
    (hWpro : ∀ F' : MachineData → Prop, (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      ProW W K exe endPc (R.callee (-Z.toInt) (-D) 0) F' ms ((_root_.Executable.labels exe).label fn) ZU 8 L []
        (uN0 (_root_.Executable.labels exe).label ms F exe endPc fn ZU g).J)
    (hbody : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      SegW (NoMsrW W K) K p lbl (tpXa ms g.tp)
        (At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (sEn (_root_.Executable.labels exe).label entry ZU
          (uN0 (_root_.Executable.labels exe).label ms F exe endPc fn ZU g).J))
        (fun s c => At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (sRet PostS g) s c ∨
          At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
            (sAb (_root_.Executable.labels exe).label ZU.toInt (Ab g)) s c))
    (hstub : ∀ F' : MachineData → Prop, (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      ∀ m0 σC c, σC.regs.X0 = 2 → Ab g c →
      Abort.Disp.StubHW W K p lbl ms exe endPc
        ((R.callee (-Z.toInt) (-D) 0).callee (-allocAbortDepth ZU.toInt) (-48) 0)
        (fun m => F' m ∧ CKept (R.callee (-Z.toInt) (-D) 0) (-allocAbortDepth ZU.toInt) (-48) 0 m0 m ∧
          Abs (R.callee (-Z.toInt) (-D) 0) ⟨-allocAbortDepth ZU.toInt, []⟩ m0 σC) c) :
    SetupCallW W K p lbl ms exe endPc R F fn Z D ZU PostS ra c0 tp := by
  intro F' hR' hal' hF' hFF g hra hc0 htp
  exact setup_callW hp hend hK hin h16 hZ hF' hR' hal' (by show -D ≤ _; omega) (by show (0 : Int) ≤ 0; omega)
    (fun m h => (hFF m h).1) g (hWpro F' hFF g hra hc0 htp) (hbody F' hR' hal' hF' hFF g hra hc0 htp)
    (hstub F' hFF g hra hc0 htp)

end Call

end Setup

end Spike.Lib.A64.Flow
