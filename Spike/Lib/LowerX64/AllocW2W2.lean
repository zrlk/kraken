/-
**An allocation's caller blocks inside `W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/AllocW2W2.lean`): the parts of
`AllocW2` (`Spike/Lib/LowerX64/NewBufC2.lean`) at `W2`
(`Spike/Lib/LowerX64/SFactsX2.lean`) for the code predicate `CdCLE`
(`Spike/Lib/LowerX64/CdCLE.lean`) and the call predicate `BlC`, from the
covered block producers (`blkW_w2C`, `blkW_w2Call`,
`Spike/Lib/LowerX64/W2Body.lean`).

- `fallBlk_getOp`, `fallBlk_args3`, `noSlotWr_args3`, `endJ_of_fallBlk`:
  the arguments' loads are fall-throughs writing no slot, ending with
  neither a `jmp` nor a `ret`;
- `posOff_allocEntry`: the allocator's entry is a position off the write
  abort, in a layout with the allocator's code (`allocIn`);
- `allocArgs_w2`: the arguments' loads from the allocation's node
  (`laneJ`) inside `W2` (`AllocW2`'s first field);
- `allocBl_w2`: the `callq scc_rt_alloc` from the call's source relation
  (`nbJ1`) inside `W2` (`AllocW2`'s second field), the walk's facts at the
  allocation's `let` (free variables placed, register bases, immediates)
  premises;
- `fallBlk_stDir`, `endJ_stDir`: the returned base's store
  `movq %rax, off(%rbp)` is a fall-through, neither a `jmp` nor a `ret`;
- `allocStore_w2`: the returned base's store from the landing (`nbJS`)
  inside `W2` (`AllocW2`'s last field at `W₀ := W2`, `blkW_w2Pend`: its
  state placed with `x%n`'s slot at `%rax`, the AArch64 twin's
  `blkW_placedS_updX0` here `blkW_placedS_upd` at `.rax`);
- `CallMsOK`, `Call.OK.ofMs`: `Call.OK`'s memory side's fields, and
  `Call.OK` from them and the source's;
- `allocHq`: `AllocW2`'s `hq` at the call's source relation (`nbJ1` at the
  arguments `imm h`, `.imm kv`, `u`, in `%rdi`, `%rsi`, `%rdx`).

The controls of the nodes exclude `main`'s `ret` (`htr`, `hnr`) and `ZBad`
(`FrOk2` at the ghost, `hG0F`, kept by the local run).
-/
import Spike.Lib.LowerX64.NewBufC2
import Spike.Lib.LowerX64.CdCLE
import Spike.Lib.LowerX64.W2Body
import Spike.Lib.LowerX64.NoSlotWr
import Spike.Lib.Src.GroupPl
import Spike.Lib.Src.NJL

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun upd upd_apply)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (BlkW ND okBlk cellOff FStable AI)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad LocBaseRegAt ImmIn ofEnv2 SlotRepAt Fresh)
open Spike.Lib.Form (lookupS NodeJE)
open Scc.Emit.X64 (i64 rel)
open Scc.Lower.InvX64
open Scc.Lower.Inv (regName)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (newBufTy)
open Spike.Lib.X64.Flow.NewBuf (nbJc allocAbortDepth allocFrame)

/-! ## The arguments' loads -/

/-- **An operand's load is a fall-through** (a load from its slot or a
`mov` of an immediate). -/
theorem fallBlk_getOp {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {l : List Scc.Emit.X64.Item}
    (ha : getOp fr t a = .ok l) {zs : List Nat} (hz : zs.length = (dirs l).length) :
    fallBlk ((dirs l).zip zs) = true := by
  rcases getOp_cases ha with ⟨r, off, rfl, -, hl⟩ | ⟨v, rfl, hl⟩ <;> rw [hl] at hz ⊢ <;>
    obtain ⟨z, rfl⟩ := length_one hz
  · simp [fallBlk, Spike.Lib.X64.AI.toDir, Spike.Lib.X64.classify, fallI]
  · simp [fallBlk, i64, Scc.Emit.X64.op, Scc.Emit.X64.xr, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly, fallI]

/-- Two blocks of fall-throughs in a row are one. -/
theorem fallBlk_append {a b : List (Directive × Nat)} : fallBlk (a ++ b) = (fallBlk a && fallBlk b) := by
  simp [fallBlk, List.all_append]

/-- **The loads of three arguments are fall-throughs.** -/
theorem fallBlk_args3 {fr : Scc.Emit.X64.Frame} {a b c : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item}
    (h : getOps fr ([a, b, c].zip Scc.Emit.X64.argRegs) = .ok lw) {zs : List Nat}
    (hz : zs.length = (dirs lw).length) : fallBlk ((dirs lw).zip zs) = true := by
  obtain ⟨la, lb, lc, ha, hb, hc, rfl⟩ := getOps_three h
  obtain ⟨z1, z2, z3, rfl, hz1, hz2, hz3, hsp⟩ := args3_split ha hb hc hz
  rw [hsp, fallBlk_append, fallBlk_append, fallBlk_getOp ha hz1, fallBlk_getOp hb hz2, fallBlk_getOp hc hz3]
  rfl

/-- **The loads of three arguments write no slot** before their last. -/
theorem noSlotWr_args3 {fr : Scc.Emit.X64.Frame} {a b c : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item}
    (h : getOps fr ([a, b, c].zip Scc.Emit.X64.argRegs) = .ok lw) {zs : List Nat}
    (hz : zs.length = (dirs lw).length) : noSlotWr ((dirs lw).zip zs).dropLast = true := by
  refine noSlotWr_dropLast (noSlotWrD_dropLast ?_)
  rw [List.map_fst_zip (by omega)]
  exact noSlotWrD_getOps h

/-- **A block of fall-throughs ends with neither a `jmp` nor a `ret`.** -/
theorem endJ_of_fallBlk {blk : List (Directive × Nat)} (h : fallBlk blk = true) : endJ blk = false := by
  unfold endJ
  cases hl : (blk.map Prod.fst).getLast? with
  | none => rfl
  | some d =>
    obtain ⟨dz, hdz, rfl⟩ := List.mem_map.mp (List.mem_of_getLast? hl)
    have hd := List.all_eq_true.mp h dz hdz
    simp only [isJR]
    revert hd
    cases Spike.Lib.X64.classify dz.1 with
    | none => intro hd; cases hd
    | some a => cases a <;> simp [fallI]

/-- **The allocator's entry is a position off the write abort**, in a
layout with the allocator's code. -/
theorem posOff_allocEntry {cells : List (Directive × Nat)} {lab : Label → Int64}
    (h : Spike.Lib.X64.Alloc.allocIn cells = true) : PosOff cells lab (lab "scc_rt_alloc") := by
  obtain ⟨k, hk⟩ := Scc.Cert.Rt.X64.blockAt_of_blockAtB (Spike.Lib.X64.AllocG.allocIn_spec h).2.1
  simpa using posOff_of_blockAt (lab := lab) hk (by decide) (i := 0) (by decide)

/-! ## The returned base's store -/

/-- The returned base's store `movq %rax, off(%rbp)` is a fall-through. -/
theorem fallBlk_stDir (off : Int) (z : Nat) : fallBlk [(stDir off, z)] = true := by
  have hc : Spike.Lib.X64.classify (stDir off) = some (AI.st .rbp (Int64.ofInt off) .rax) := rfl
  simp [fallBlk, hc, fallI]

/-- The returned base's store `movq %rax, off(%rbp)` is neither a `jmp` nor
a `ret`. -/
theorem endJ_stDir (off : Int) (z : Nat) : endJ [(stDir off, z)] = false := by
  have hc : Spike.Lib.X64.classify (stDir off) = some (AI.st .rbp (Int64.ofInt off) .rax) := rfl
  simp [endJ, isJR, hc]

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}

/-- **The arguments' loads of an allocation inside `W2`** at the frames
`fs` (`AllocW2`'s first field, `blkW_w2C`): the loads `lw` of `a0`, `a1`,
`a2` into `%rdi`, `%rsi`, `%rdx` at `pc` a piece of the code at `CdCLE`
(`hcd`), from the allocation's node (`laneJ`, the immediates `Λ.imms`): the
loads are covered (`okBlk_args3`) fall-throughs (`fallBlk_args3`, so the
write abort's phase is kept, `blkW_abSt_fallL`, the pc after them off the
write abort by `CdCLE`) writing no slot; the node's controls placed in the
slot file (`slotRepAt_bodyN2`), excluding `main`'s `ret` (`htr`) and `ZBad`
(`hG0F`). -/
theorem allocArgs_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {pc : Int64} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (htr : ∀ a, t ≠ .ret a) (hG0F : FrOk2 c0 fs)
    {a0 a1 a2 : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item}
    (hlw : getOps fr ([a0, a1, a2].zip Scc.Emit.X64.argRegs) = .ok lw) {zs : List Nat}
    (hz : zs.length = (dirs lw).length) (hcd : CdCLE cells okPc ph lab ra0 pc ((dirs lw).zip zs)) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
      ⟨pc, oB fr, laneJ p lbl lsize Λ.imms fr fp ra tp c0 pc t env lits cs bufs⟩ ((dirs lw).zip zs) := by
  have hok := okBlk_args3 hf h1 hlw hz
  have hfb := fallBlk_args3 hlw hz
  have hend := hcd.2 (endJ_of_fallBlk hfb)
  refine blkW_w2C (n := ⟨pc, oB fr, laneJ p lbl lsize Λ.imms fr fp ra tp c0 pc t env lits cs bufs⟩) hI hR hR8
    hlo hhi hl hh hsub hfit hFO hFS hp (SubCd.whole hcd.toCdC) hok (noRetBlk_of_fallBlk hfb)
    (noSlotWr_args3 hlw hz)
    (blkW_abSt_fallL hI hpr hab (SubCd.whole hcd.toCdCL) hok hR hlo hhi hfb hend)
    (fun σ c h => slotRepAt_bodyN2 σ c h.1) hrs hfp (fun σ c h => ?_)
  obtain ⟨⟨L, sm, B, c', hr, hj, -⟩, -, hc0, -⟩ := h.1
  exact ⟨fun _ => noRet_of_run hr (by rw [hj.1]; exact htr),
    Spike.Lib.LowerNode.FrOk2.run hp (Spike.Lib.FrameRun.ofLocal hc0 fs) hG0F⟩

/-- **An allocation's `callq scc_rt_alloc` inside `W2`** at the frames `fs`
(`AllocW2`'s second field, `blkW_w2Call`): at `BlC` (`hbl`), from the
call's source relation (`nbJ1`), in a layout with the runtime's and the
allocator's code: the `callq`'s only target the allocator's entry, a
position off the write abort (`posOff_allocEntry`, so the write abort's
phase is kept, `blkW_abSt_pos`); the controls at the `let` `t` placed in
the slot file from the walk's facts there (`htot`, `hlb`, `himm`,
`SlotRepAt.of_nodeJE`), excluding `main`'s `ret` (`htr`) and `ZBad`
(`hG0F`). -/
theorem allocBl_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hprog : Spike.Lib.X64.Alloc.allocIn cells = true)
    {fr : Scc.Emit.X64.Frame} (h8 : (fr.size : Int) % 8 = 0) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    {pcB : Int64} {zc k : Nat} (hbl : BlC cells okPc ph lab fr ra0 pcB zc Scc.Lower.Names.alloc k)
    (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    (htr : ∀ a, t ≠ .ret a) (hG0F : FrOk2 c0 fs)
    (htot : ∀ y ∈ Scc.Sem.exprFv t, (lookupS (ofEnv2 env) y).isSome) (hlb : LocBaseRegAt (ofEnv2 env) t)
    (himm : ImmIn Λ.imms (ofEnv2 env) t) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
      ⟨pcB, oB fr, nbJ1 p lbl lsize fr R fp ra tp c0 t env lits cs bufs a0 a1 a2⟩
      [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] := by
  have hbl' := hbl
  obtain ⟨L, j, off, hpc, hb, -, hph, -⟩ := hbl'
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      Spike.Lib.X64.CodeAt s pcB [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
    rwa [hI.labOk, hpc] at this
  refine blkW_w2Call hI h8 hR hR8 hlo hhi hl hh hsub hfit hFO hFS hp rfl hbl ?_ (fun σ c h => ?_) hrs hfp
    (fun σ c h => ?_)
  · refine blkW_abSt_pos (lo := -(fr.size : Int) - 8) (hi := 16) hI hpr hab hcode
      (okBlk_callqC _ zc (by simp [offOk, oB]; omega)) hR hlo hhi hph (noRet_callq _ zc) ?_
    intro σ c _ k hk a ha t' ht
    obtain rfl : k = 0 := by simp at hk; omega
    have h0 : Spike.Lib.X64.classify (i64 (.call (rel Scc.Lower.Names.alloc))) =
      some (AI.call Scc.Lower.Names.alloc) := rfl
    simp only [List.getElem_cons_zero] at ha
    rw [h0] at ha
    cases ha
    simp only [aiTgts, List.mem_singleton] at ht
    subst ht
    exact .inl (posOff_allocEntry hprog)
  · obtain ⟨-, -, -, -, -, -, -, L', sm, B, hj, -⟩ := h
    exact SlotRepAt.of_nodeJE hj htot hlb himm
  · obtain ⟨-, -, -, -, -, -, hc0, L', sm, B, hj, -⟩ := h
    exact ⟨fun _ => by rw [hj.1]; exact htr,
      Spike.Lib.LowerNode.FrOk2.run hp (Spike.Lib.FrameRun.ofLocal hc0 fs) hG0F⟩

/-- **The returned base's store inside `W2`** at the placement `lbl`,
`lsize` and the frames `fs` (`AllocW2`'s last field at `W₀ := W2`,
`blkW_w2Pend`): the store `movq %rax, off(%rbp)` into `x%n`'s slot at
`pcB + zc` a piece of the code at `CdCLE` (`hcd`), from the landing (`nbJS`
at `lbl`, `lsize`, of the call node of `nbJ1` at the call's placement
`lbl0`, `lsize0` inside `lbl`, `hlbl`): a covered fall-through (the write
abort's phase kept, `blkW_abSt_fallL`); its state placed with `x%n`'s slot
at `%rax` (`blkW_placedS_upd`: the allocator keeps the frame's cells, the
source past its allocation at the label `%rax` represents,
`NodeJE.newBuf2`, the walk's facts at `e`, `hIt`, `hIc`, `hlb`); its
control past the allocation excluding `main`'s `ret` (`hnr`) and `ZBad`
(`hG0F` along the local run). -/
theorem allocStore_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -allocAbortDepth (fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ms0 : MemSide isa} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {x : String} {cn : At} {τ : Ty}
    {e : Expr} (he2 : Scc.Lower.elem2 τ = true) {env : Scc.Lower.Env} {n : Nat} (hfr : Fresh env n)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    {lbl0 : WeakMem.AllocLabel → Option Nat} {lsize0 : WeakMem.AllocLabel → Nat}
    (hlbl : ∀ l b, lbl0 l = some b → lbl l = some b)
    (hnr : fs = [] → ∀ a, e ≠ .ret a) (hG0F : FrOk2 c0 fs)
    {pcB : Int64} {zc z : Nat} {off : Int} (hoff : rsOf fr (regName x n) = some off)
    (hcd : CdCLE cells okPc ph lab ra0 (pcB + Int64.ofNat zc) [(stDir off, z)])
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, Spike.Lib.LowerShape.newBufTy τ,
      [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : ImmIn Λ.imms (ofEnv2 ((x, Spike.Lib.LowerShape.newBufTy τ,
      [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, Spike.Lib.LowerShape.newBufTy τ,
      [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
      ⟨pcB + Int64.ofNat zc, oB fr, nbJS ms0 (_root_.Executable.labels exe).label lbl lsize R fr.size tp
        (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)] pcB (oB fr)
          (nbJ1 p lbl0 lsize0 fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2))⟩
      [(stDir off, z)] := by
  have hlo0 : R.lo ≤ -(fr.size : Int) - 8 - 160 := by
    simp only [allocAbortDepth, allocFrame] at hlo; omega
  have hlo1 : R.lo ≤ -(fr.size : Int) := by omega
  have hok := okBlk_stDir hf h1 hoff z
  have hfb := fallBlk_stDir off z
  have hend := hcd.2 (endJ_stDir off z)
  rw [ofEnv2_cons (group_newBufTy τ _)] at hIt hIc hlb
  -- the frame's cells are kept by the allocator
  have hout : ∀ k : Int, k % 8 = 0 → -(fr.size : Int) ≤ k → k + 8 ≤ 16 →
      R.Off k ∧ ¬ (R.callee (-(fr.size : Int) - 8) (-160) 8).Off (k - (-(fr.size : Int) - 8)) :=
    fun k hk8 hk1 hk2 => frame_out hlo0 hhi (by decide) hk8 hk1 hk2
  refine blkW_w2Pend (k0 := off) hI hR hR8 hlo1 hhi hl hh hsub hfit hFO hFS hp
    (SubCd.whole hcd.toCdC) hok (noRetBlk_of_fallBlk hfb) (by simp)
    (blkW_abSt_fallL hI hpr hab (SubCd.whole hcd.toCdCL) hok hR hlo1 hhi hfb hend) ?_ hrs hfp ?_
  · rintro σ c ⟨⟨⟨c1, qx, qa, qτ, qe, qta, qws, qn, qh, qfp, qra⟩, hq⟩, ⟨σC, ⟨σ0, hJ1, hσC⟩, hsl⟩,
      l, ini, old, rfl, -, -, hvr, -, -⟩
    obtain ⟨-, -, -, -, -, -, -, L, sm, B, hj, -⟩ := hJ1
    have ht := hq.term
    rw [hj.1] at ht
    simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := ht
    have hsl' : ∀ k : Int, k % 8 = 0 → -(fr.size : Int) ≤ k → k + 8 ≤ 16 → σ.slot k = σ0.slot k := by
      intro k hk8 hk1 hk2
      obtain ⟨ho1, ho2⟩ := hout k hk8 hk1 hk2
      rw [hsl k ho1 ho2, hσC, arun_callq]
      simp only [upd_apply, oB]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    have hj' : NodeJE lbl (rsOf fr) (.let_ x (.newBuf cn τ) e) (ofEnv2 env) σ.slot c1 :=
      NodeJE.mono_lbl hlbl ⟨hj.1, hj.2.1, hj.2.2.congr fun _ _ _ _ o' _ => Spike.Lib.Form.opdVal_upd
        fun r k' _ hk' => by
          obtain ⟨hk8, hk1, hk2⟩ := rsOf_bounds hf hk'
          exact hsl' k' (by omega) (by omega) (by omega)⟩
    have hfr' : ∀ b ∈ ofEnv2 env, ∀ pl ∈ b.2.2, ∀ o' ∈ pl.opds, ∀ r k', o' = .reg r → rsOf fr r = some k' →
        k' ≠ off := fun b hb pl hpl o' ho' r k' hor hrk hk =>
      fresh_ofEnv2 hfr x b hb pl hpl o' ho' r hor (rsOf_inj hf hrk (hk ▸ hoff))
    have hvr' : ValRep lbl (.loc ⟨l, 0⟩ 0) (σ.regs.get64 .rax).toNat := hvr
    exact SlotRepAt.of_nodeJE (NodeJE.newBuf2 hj' he2 qn l ini hoff hfr' hvr') hIt hlb hIc
  · rintro σ c ⟨⟨⟨c1, qx, qa, qτ, qe, qta, qws, qn, qh, qfp, qra⟩, hq⟩, ⟨σC, ⟨σ0, hJ1, -⟩, -⟩,
      l, ini, old, rfl, -⟩
    obtain ⟨-, -, -, -, -, -, hr0, L, sm, B, hj, -⟩ := hJ1
    have hF := Spike.Lib.LowerNode.FrOk2.run hp (Spike.Lib.FrameRun.ofLocal hr0 fs) hG0F
    have ht := hq.term
    rw [hj.1] at ht
    simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := ht
    have hN := hF.1
    rw [hj.1] at hN
    exact ⟨fun h a => hnr h a, hN.2, hF.2⟩

end W

/-! ## The call's premises -/

section Hq

open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.LowerNode (GrpL InLits EnvLit IsNum sevalAt_ofEnv2G_one)
open Scc.Lower (LitV litAt)
open Scc.Lower.Inv (atomV)

/-- **The memory side's fields of `Call.OK`** (the counter's and the
arena's labels and bounds, the units and offset of the call's elements,
the runtime reads, maps and value invariant at the counter and the
headers). -/
structure CallMsOK (ms : MemSide isa) (lab : Label → Int64) (q : Call) : Prop where
  ctr : (lab "scc_rt_heap_use").toBitVec = BitVec.ofNat 64 ms.ctr
  heap : (lab "scc_rt_heap").toBitVec.toNat = ms.heap
  room : ms.heap + 2 ^ 46 ≤ 2 ^ 64
  cells : ms.cells = 4194304
  units : ms.units q.n q.τ < 2 ^ 63
  off : ms.off q.n q.τ = 8 * (q.n * (Spike.Lib.X64.Alloc.mOf q.h).toNat) + 8
  rt : ms.rt (BitVec.ofNat 64 ms.ctr).toNat
  mp : ms.mp (Spike.Lib.X64.ctrLoc ms) true
  grow : ∀ old : Val, ms.G (Spike.Lib.X64.ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells →
    ms.G (Spike.Lib.X64.ctrLoc ms) ((old.setWidth 64 + q.u ms).setWidth 128)
  hdr : ∀ o, o + ms.units q.n q.τ ≤ ms.cells →
    ms.rt (q.hdrAt ms o) ∧ ms.mp ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ true ∧
      ms.G ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ (q.hdr.setWidth 128)

/-- **`Call.OK` from its source's fields and `CallMsOK`.** -/
theorem Call.OK.ofMs {ms : MemSide isa} {lab : Label → Int64} {q : Call}
    (hterm : q.c0.term = .let_ q.x (.newBuf q.a q.τ) q.e) (hev : TermRun.evalAt q.c0.env q.a = some (q.ta, q.ws))
    (hnum : TermRun.numOf q.ws = some q.n) (hhold : q.c0.hold = none) (hlt : q.n < 2 ^ 64)
    (hacc : ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us) (h : CallMsOK ms lab q) : q.OK ms lab :=
  ⟨hterm, hev, hnum, hhold, hlt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, hacc, h.rt, h.mp, h.grow, h.hdr⟩

/-- **The call's arguments at the call's source relation** (`AllocW2`'s
`hq`, `nbJ1` at the header `imm h`, the count `.imm kv` and the units
operand `u`, in `%rdi`, `%rsi`, `%rdx`): the call `q` at the source's
control, its count `kv` (the count atom `cn` lowered to `kv`, `hcn`, in a
grouped environment, `hg`; its word a number, a leaf of the walk's
literals, `hsc`, `hleaf`, `EnvLit`), its header `h`, its units `u`'s
(`hu`); `Call.OK` from the element type's accesses (`hacc`) and the memory
side's fields (`hms`). -/
theorem allocHq {ms : MemSide isa} {L : Label → Int64} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {fr : Scc.Emit.X64.Frame} {R : Region} {fp ra : BitVec 64} {tp : UInt64}
    {c0 : Ctl} {x : String} {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env} {lits : List (String × LitV)}
    {cs bufs : List (String × Nat)} {h : Nat} {kv : UInt64} {u : Scc.IR.Operand} {tk : Ty}
    (hg : GrpL env) (hcn : atomV env cn = some (tk, [.imm kv])) (hsc : InLits lits cn)
    (hleaf : ∃ o, litAt lits cn = .leaf o)
    (hu : ∀ sl, Spike.Lib.Form.opdVal (rsOf fr) sl u = some (ms.units kv.toNat τ))
    (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us)
    (hms : ∀ q : Call, q.n = kv.toNat → q.τ = τ → q.h = BitVec.ofNat 64 h → CallMsOK ms L q) :
    ∀ σ c, nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
      (.imm kv) u σ c → ∃ q : Call, q.OK ms L ∧ q.c0 = c ∧
        σ.regs.rdi.toBitVec = q.h ∧ σ.regs.rsi.toBitVec = q.k ∧ σ.regs.rdx.toBitVec = q.u ms := by
  rintro σ c ⟨h0, h1, h2, -, -, -, -, L', sm, B, hj, hl, -⟩
  have hs := sevalAt_ofEnv2G_one hg hcn
  obtain ⟨t', ws, hev, -, hwr⟩ := hj.2.2.evalAt (fun _ => rfl) hs
  obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
    match ws, hwr with
    | [w], _ => exact ⟨w, rfl⟩
  obtain ⟨⟨v, hv, hvr⟩, -⟩ := hwr
  simp only [Spike.Lib.Form.opdVal_imm, Option.some.injEq] at hv
  subst hv
  obtain ⟨-, hnl⟩ := EnvLit.evalAt hl hsc hs hev
  obtain ⟨o, ho⟩ := hleaf
  obtain ⟨n, hn, -⟩ : IsNum w := hnl 0 w rfl (by rw [ho]; rfl)
  rw [hn] at hvr
  obtain ⟨-, rfl⟩ := hvr
  refine ⟨⟨c, x, cn, τ, e, t', [w], kv.toNat, BitVec.ofNat 64 h, 0, 0⟩,
    Call.OK.ofMs hj.1 hev (by simp [TermRun.numOf, hn]) hj.2.1 (UInt64.toNat_lt _) hacc (hms _ rfl rfl rfl),
    rfl, ?_, ?_, ?_⟩
  · refine BitVec.eq_of_toNat_eq ?_
    simp only [Scc.Lower.imm, Spike.Lib.Form.opdVal_imm, Option.some.injEq] at h0
    rw [show σ.regs.rdi.toBitVec = σ.regs.get64 .rdi from rfl, ← h0]; simp
  · refine BitVec.eq_of_toNat_eq ?_
    simp only [Spike.Lib.Form.opdVal_imm, Option.some.injEq] at h1
    rw [show σ.regs.rsi.toBitVec = σ.regs.get64 .rsi from rfl, ← h1]; simp [Spike.Lib.X64.Alloc.Call.k]
  · refine BitVec.eq_of_toNat_eq ?_
    rw [hu, Option.some.injEq] at h2
    simp only [Spike.Lib.X64.Alloc.Call.u, BitVec.toNat_ofNat]
    have hlt : ms.units kv.toNat τ < 2 ^ 64 := h2 ▸ BitVec.isLt _
    rw [show σ.regs.rdx.toBitVec = σ.regs.get64 .rdx from rfl, ← h2, Nat.mod_eq_of_lt hlt]

end Hq

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.allocStore_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocStore_w2

/-- info: 'Spike.Lib.LowerX64.endJ_of_fallBlk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.endJ_of_fallBlk

/-- info: 'Spike.Lib.LowerX64.posOff_allocEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.posOff_allocEntry

/-- info: 'Spike.Lib.LowerX64.allocArgs_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocArgs_w2

/-- info: 'Spike.Lib.LowerX64.allocBl_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocBl_w2

/-- info: 'Spike.Lib.LowerX64.allocHq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocHq
