/-
**An allocation's caller blocks inside `W2`** (AArch64): the parts of
`AllocW2` (`Spike/Lib/LowerA64/NewBufC2.lean`) at `W2`
(`Spike/Lib/LowerA64/SFactsA2.lean`) for the code predicate `CdCLE`
(`Spike/Lib/LowerA64/CdCLE.lean`) and the call predicate `BlC`, from the
covered block producers (`blkW_w2C`, `blkW_w2Call`,
`Spike/Lib/LowerA64/W2Body.lean`).

- `fallBlk_append`, `fallBlk_args3`, `noSlotWr_args3`, `endJ_of_fallBlk`:
  the arguments' loads are fall-throughs writing no slot, ending with
  neither a `b` nor a `ret`;
- `posOff_allocEntry`: the allocator's entry is a position off the write
  abort, in a program with the allocator's code (`allocIn`);
- `allocArgs_w2`: the arguments' loads `la` from the allocation's node
  (`laneJ`) inside `W2` (`AllocW2`'s first field);
- `allocBl_w2`: the `bl scc_rt_alloc` from the call's source relation
  (`nbJ1`) inside `W2` (`AllocW2`'s second field), the walk's facts at the
  allocation's `let` (free variables placed, register bases, immediates)
  premises;
- `CallMsOK`, `Call.OK.ofMs`: `Call.OK`'s memory side's fields, and
  `Call.OK` from them and the source's;
- `allocHq`: `AllocW2`'s `hq` at the call's source relation (`nbJ1` at the
  arguments `imm h`, `.imm kv`, `u`): the count atom `cn` lowered to the
  immediate `kv` (`atomV`, a grouped environment), a leaf of the walk's
  literals (so its word a number, `EnvLit`), the units operand `u` the
  memory side's units of `kv` elements (`hu`), the element type's accesses
  (`hacc`) and `CallMsOK` at every call of `kv` elements of `τ` with the
  header `h` (`hms`).

The controls of both nodes exclude `main`'s `ret` (their local run reaches
the term `t`, not a `ret`, `htr`) and `ZBad` (`FrOk2` at the ghost, `hG0F`,
kept by the local run).
-/
import Spike.Lib.LowerA64.NewBufC2
import Spike.Lib.LowerA64.CdCLE
import Spike.Lib.LowerA64.RetHeldAb
import Spike.Lib.LowerA64.NoSlotWr
import Spike.Lib.Src.GroupPl
import Spike.Lib.Src.NJL

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (FStable BlkW classify AI)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad LocBaseRegAt ImmIn ofEnv2 SlotRepAt)
open Spike.Lib.Form (lookupS)
open Scc.Emit.A64 (FnCtx directives)
open Scc.Lower.InvA64 (FrameOk)

/-! ## The arguments' loads -/

/-- Two blocks of fall-throughs in a row are one. -/
theorem fallBlk_append {a b : List Directive} : fallBlk (a ++ b) = (fallBlk a && fallBlk b) := by
  simp [fallBlk, List.all_append]

/-- **The loads of three arguments are fall-throughs.** -/
theorem fallBlk_args3 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {a b w : Scc.IR.Operand}
    {l : List Scc.Emit.A64.Item} (h : cx.getArgs [a, b, w] = .ok l) : fallBlk (directives l) = true := by
  rw [getArgs_three] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  obtain ⟨lb, hb, h⟩ := exc_bind_ok h
  obtain ⟨lw, hw, h⟩ := exc_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [directives_append, fallBlk_append, fallBlk_getOp hf h1 ha, fallBlk_getOp hf h1 hb,
    fallBlk_getOp hf h1 hw, Bool.and_self]

/-- **The loads of three arguments write no slot.** -/
theorem noSlotWr_args3 {cx : FnCtx} {a b w : Scc.IR.Operand} {l : List Scc.Emit.A64.Item}
    (h : cx.getArgs [a, b, w] = .ok l) : noSlotWr (directives l) = true := by
  rw [getArgs_three] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  obtain ⟨lb, hb, h⟩ := exc_bind_ok h
  obtain ⟨lw, hw, h⟩ := exc_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [directives_append, noSlotWr_append, noSlotWr_getOp ha, noSlotWr_getOp hb,
    noSlotWr_getOp hw, Bool.and_self]

/-- **A block of fall-throughs ends with neither a `b` nor a `ret`.** -/
theorem endJ_of_fallBlk {blk : List Directive} (h : fallBlk blk = true) : endJ blk = false := by
  unfold endJ
  cases hl : blk.getLast? with
  | none => rfl
  | some d =>
    have hd := List.all_eq_true.mp h d (List.mem_of_getLast? hl)
    simp only [isJR]
    revert hd
    cases classify d with
    | none => intro hd; cases hd
    | some a => cases a <;> simp [fallI]

/-- **The allocator's entry is a position off the write abort**, in a
program with the allocator's code. -/
theorem posOff_allocEntry {prog : List Directive} {lab : Label → Int64}
    (h : Spike.Lib.A64.Flow.allocIn prog = true) : PosOff prog lab (lab "scc_rt_alloc") :=
  ⟨"scc_rt_alloc", 0, Scc.Cert.Rt.A64.inRun_of_blockAt (Spike.Lib.A64.AllocG.allocIn_spec h).1 (i := 0)
    (by decide), by decide, Spike.Lib.A64.Flow.ofNat4_zero _⟩

/-! ## The returned base's store's placement -/

section Placed

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {Λ : Scc.Sem.Layout} {lbl : Lbl} {rs : Scc.IR.Reg → Option Int} {fs : List TermRun.Frame}
  {B : Nat → Prop}

/-- **A state placed at the returned base's store** (`placedS_of_abs_upd`
at `x0`): a control placed in the slot file with slot `k0` updated to
`x0`'s word is placed, slot `k0`'s words at `x0` and every other slot at
its cell (`hrs`), the suspended frames placed under the frame condition
(`hfp`). -/
theorem placedS_of_abs_updX0 {s : State} {o : Spike.Lib.A64.Flow.SO} {σ : Spike.Lib.A64.Flow.AS} {c : Ctl}
    {k0 : Int} (hA : Spike.Lib.A64.Flow.Abs R o s.st.1 σ)
    (h : SlotRepAt Λ.imms lbl rs (Spike.Lib.upd σ.slot k0 σ.regs.X0.toBitVec) c)
    (hrs : ∀ r k, rs r = some k → R.Off k) (hfp : FramesPlacedInI Λ lbl s fs B) : PlacedS Λ lbl s c fs := by
  refine PlacedS.ofFrames (placed_of_slotRep (pf := fun k => if k = k0 then .reg (.x 0) else
    .slot (R.addr k).toNat) h fun r' k hk => ?_) hfp.toFramesPlaced
  by_cases hk0 : k = k0
  · subst hk0
    simp only [Spike.Lib.upd_apply, ite_true]
    show some ((xRegs s.st.1.regs).getD 0 0).toBitVec.toNat = _
    rw [hA.regs]; rfl
  · simp only [hk0, Spike.Lib.upd_apply, ite_false]
    obtain ⟨j, hj, he⟩ := hA.slot k (hrs r' k hk)
    show (privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [privLoad, hj, Option.map_some, he]

/-- **A one-instruction block's state placed at the returned base's
store** (`placedS_of_abs_updX0` at the block's only state). -/
theorem blkW_placedS_updX0 (hFS : FStable R F) {n : Spike.Lib.A64.Flow.ND} {blk : List Directive} {k0 : Int}
    (h1 : blk.length ≤ 1)
    (hJ : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs (Spike.Lib.upd σ.slot k0 σ.regs.X0.toBitVec) c)
    (hrs : ∀ r k, rs r = some k → R.Off k) (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) :
    BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ hF hJn k hk m hA' hD
  refine ⟨?_, fun _ h => h⟩
  obtain rfl : k = 0 := by omega
  exact placedS_of_abs_updX0 (s := { s with st := (m, _) }) hA' (hJ σ c hJn) hrs
    (hfp _ (hFS _ _ hF hD)).choose_spec

end Placed

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}

/-- **The arguments' loads of an allocation inside `W2`** at the frames
`fs` (`AllocW2`'s first field, `blkW_w2C`): the loads `la` of `a0`, `a1`,
`a2` at `pc` a piece of the code at `CdCLE` (`hcd`), from the allocation's
node (`laneJ`, the immediates `Λ.imms`): the loads are covered
(`okBlk_args3`) fall-throughs (`fallBlk_args3`, so the write abort's phase
is kept, `blkW_abSt_fallL`, the pc after them off the write abort by
`CdCLE`) writing no slot; the node's controls placed in the slot file
(`slotRepAt_bodyN2`), excluding `main`'s `ret` (`htr`) and `ZBad`
(`hG0F`). -/
theorem allocArgs_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {pc : Int64} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (htr : ∀ a, t ≠ .ret a) (hG0F : FrOk2 c0 fs)
    {a0 a1 a2 : Scc.IR.Operand} {la : List Scc.Emit.A64.Item} (hla : cx.getArgs [a0, a1, a2] = .ok la)
    (hcd : CdCLE prog okPc ph lab ra0 pc (directives la)) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
      ⟨pc, oF cx, laneJ p lbl lsize Λ.imms cx fp ra tp c0 pc t env lits cs bufs⟩ (directives la) := by
  have hok := okBlk_args3 hf h1 h16 hla
  have hfb := fallBlk_args3 hf h1 hla
  have hend : PosOff prog lab (pc + Int64.ofNat (4 * (directives la).length)) := hcd.2 (endJ_of_fallBlk hfb)
  refine blkW_w2C (n := ⟨pc, oF cx, laneJ p lbl lsize Λ.imms cx fp ra tp c0 pc t env lits cs bufs⟩) hI hR hal
    hlo hhi hl hh hsub hfit hFO hFS hp (SubCd.whole hcd.toCdC) hok (noRetBlk_of_fallBlk hfb)
    (noSlotWr_dropLast (noSlotWr_args3 hla))
    (blkW_abSt_fallL hI hpr hab (SubCd.whole hcd.toCdCL) hok hR hal hlo hhi hfb hend)
    (fun σ c h => slotRepAt_bodyN2 σ c h.1) hrs hfp (fun σ c h => ?_)
  obtain ⟨⟨L, sm, B, c', hr, hj, -⟩, -, hc0, -⟩ := h.1
  exact ⟨fun _ => noRet_of_run hr (by rw [hj.1]; exact htr),
    Spike.Lib.LowerNode.FrOk2.run hp (Spike.Lib.FrameRun.ofLocal hc0 fs) hG0F⟩

/-- **An allocation's `bl scc_rt_alloc` inside `W2`** at the frames `fs`
(`AllocW2`'s second field, `blkW_w2Call`): at `BlC` (`hbl`), from the
call's source relation (`nbJ1`), in a program with the runtime's and the
allocator's code: the `bl`'s only target the allocator's entry, a
position off the write abort (`posOff_allocEntry`, so the write abort's
phase is kept, `blkW_abSt_pos`); the controls at the `let` `t` placed in
the slot file from the walk's facts there (`htot`, `hlb`, `himm`,
`SlotRepAt.of_nodeJE`), excluding `main`'s `ret` (`htr`) and `ZBad`
(`hG0F`). -/
theorem allocBl_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hprog : Spike.Lib.A64.Flow.allocIn prog = true)
    {cx : FnCtx} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    {pcB : Int64} {k : Nat} (hbl : BlC prog okPc ph lab cx ra0 pcB Scc.Lower.Names.alloc k)
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    (htr : ∀ a, t ≠ .ret a) (hG0F : FrOk2 c0 fs)
    (htot : ∀ y ∈ Scc.Sem.exprFv t, (lookupS (ofEnv2 env) y).isSome) (hlb : LocBaseRegAt (ofEnv2 env) t)
    (himm : ImmIn Λ.imms (ofEnv2 env) t) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
      ⟨pcB, oF cx, nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2⟩ [blD Scc.Lower.Names.alloc] := by
  have hbl' := hbl
  obtain ⟨L, j, hpc, hb, -, hph, -⟩ := hbl'
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := pcB) (by rw [hI.labOk]; exact hpc)
  refine blkW_w2Call hI hR hal hlo hhi hl hh hsub hfit hFO hFS hp hbl ?_ (fun σ c h => ?_) hrs hfp
    (fun σ c h => ?_)
  · refine blkW_abSt_pos (lo := -(cx.frame : Int)) (hi := 0) hI hpr hab hcode
      (Spike.Lib.A64.Flow.okBlk_blD _ _ _ _) hR hal hlo hhi hph (noRet_bl _) ?_
    intro σ c _ k hk a ha t' ht
    obtain rfl : k = 0 := by simp at hk; omega
    have h0 : classify (blD Scc.Lower.Names.alloc) = some (AI.bl Scc.Lower.Names.alloc) := rfl
    simp only [List.getElem_cons_zero] at ha
    rw [h0] at ha
    cases ha
    simp only [aiTgts, List.mem_singleton] at ht
    subst ht
    exact .inl (posOff_allocEntry hprog)
  · obtain ⟨-, -, -, -, -, -, L', sm, B, hj, -⟩ := h
    exact SlotRepAt.of_nodeJE hj htot hlb himm
  · obtain ⟨-, -, -, -, -, hc0, L', sm, B, hj, -⟩ := h
    exact ⟨fun _ => by rw [hj.1]; exact htr,
      Spike.Lib.LowerNode.FrOk2.run hp (Spike.Lib.FrameRun.ofLocal hc0 fs) hG0F⟩

open Spike.Lib.LowerNode Scc.Lower.InvA64 in
open Spike.Lib.A64.Flow (spStr blD_run) in
open Spike.Lib.Form (NodeJE opdVal_upd) in
/-- **The returned base's store inside `W2`** at the placement `lbl`,
`lsize` and the frames `fs` (`AllocW2`'s last field at `W₀ := W2`,
`blkW_w2CP`): the store `ls` of `x0` into `x%n`'s slot at `pcB + 4` a piece
of the code at `CdCLE` (`hcd`), from the landing (`nbJS` at `lbl`, `lsize`,
of the call node of `nbJ1` at the call's placement `lbl0`, `lsize0` inside
`lbl`, `hlbl`): a covered fall-through (the write abort's phase kept,
`blkW_abSt_fallL`); its state placed with `x%n`'s slot at `x0`
(`blkW_placedS_updX0`: the allocator keeps the frame's cells, the source
past its allocation at the label `x0` represents, `NodeJE.newBuf2`, the
walk's facts at `e`, `hIt`, `hIc`, `hlb`); its control past the allocation
excluding `main`'s `ret` (`hnr`) and `ZBad` (`hG0F` along the local run). -/
theorem allocStore_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -Spike.Lib.A64.Flow.NewBuf.allocAbortDepth (cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ms0 : MemSide isaLSE2} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {x : String} {cn : At} {τ : Ty}
    {e : Expr} (he2 : Scc.Lower.elem2 τ = true) {env : Scc.Lower.Env} {n : Nat} (hfr : Fresh env n)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    {lbl0 : WeakMem.AllocLabel → Option Nat} {lsize0 : WeakMem.AllocLabel → Nat}
    (hlbl : ∀ l b, lbl0 l = some b → lbl l = some b)
    (hnr : fs = [] → ∀ a, e ≠ .ret a) (hG0F : FrOk2 c0 fs)
    {pcB : Int64} {ls : List Scc.Emit.A64.Item} (hs : cx.setReg (Scc.Lower.Inv.regName x n) .X0 = .ok ls)
    (hcd : CdCLE prog okPc ph lab ra0 (pcB + 4) (directives ls))
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, Spike.Lib.LowerShape.newBufTy τ,
      [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : ImmIn Λ.imms (ofEnv2 ((x, Spike.Lib.LowerShape.newBufTy τ,
      [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, Spike.Lib.LowerShape.newBufTy τ,
      [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) e) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
      ⟨pcB + 4, oF cx, nbJS ms0 (_root_.Executable.labels exe).label lbl lsize R cx.frame tp
        (Spike.Lib.A64.Flow.NewBuf.nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB
          (oF cx) (nbJ1 p lbl0 lsize0 cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs a0 a1 a2))⟩
      (directives ls) := by
  have h16' := frame_ge16 hf
  have hlo0 : R.lo ≤ -(cx.frame : Int) - 160 := by
    simp only [Spike.Lib.A64.Flow.NewBuf.allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame] at hlo; omega
  have hlo1 : R.lo ≤ -(cx.frame : Int) := by omega
  have hok := okBlk_resStore hf h1 h16 hs
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  have hoff : rsOf cx (Scc.Lower.Inv.regName x n) = some (o - cx.frame) := by simp [rsOf, ho]
  have hls : directives ls = [spStr .X0 (Int64.ofInt o)] := by
    have hs' := hs
    rw [setReg_eq hf (by omega) ho] at hs'
    cases ok_inj hs'
    rfl
  have hfb : fallBlk (directives ls) = true := by
    rw [hls]; simp [fallBlk, spStr, Spike.Lib.A64.Flow.classify, fallI]
  have hend := hcd.2 (endJ_of_fallBlk hfb)
  rw [ofEnv2_cons (group_newBufTy τ _)] at hIt hIc hlb
  have hout : ∀ (r : Scc.IR.Reg) (k' : Int), rsOf cx r = some k' →
      R.Off k' ∧ ¬ (R.callee (-(cx.frame : Int)) (-160) 0).Off (k' - -(cx.frame : Int)) := by
    intro r k' hk'
    unfold rsOf at hk'
    split at hk'
    · rename_i o' ho'
      cases hk'
      obtain ⟨h0, h8, hle'⟩ := slotOff_bounds hf ho'
      exact frame_outC (by decide) hlo0 hhi (by omega) (by omega) (by omega)
    · cases hk'
  refine blkW_w2CP (n := ⟨pcB + 4, oF cx, _⟩) hI hR hal hlo1 hhi hl hh hsub hfit hFO hp
    (SubCd.whole hcd.toCdC) hok (noRetBlk_of_fallBlk hfb)
    (blkW_abSt_fallL hI hpr hab (SubCd.whole hcd.toCdCL) hok hR hal hlo1 hhi hfb hend)
    (blkW_placedS_updX0 (k0 := o - cx.frame) hFS (by rw [hls]; simp) ?_ hrs hfp) ?_
  · rintro σ c ⟨⟨⟨c1, qx, qa, qτ, qe, qta, qws, qn, qh, q29, qra⟩, hq⟩, ⟨σC, ⟨σ0, hJ1, hσC⟩, hsl⟩,
      l, ini, old, rfl, -, -, hvr, -, -⟩
    obtain ⟨-, -, -, -, -, -, L, sm, B, hj, -⟩ := hJ1
    have ht := hq.term
    rw [hj.1] at ht
    simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := ht
    have hσs : σC.slot = σ0.slot := by rw [hσC]; erw [blD_run]
    have hsl' : ∀ k', R.Off k' → ¬ (R.callee (-(cx.frame : Int)) (-160) 0).Off (k' - -(cx.frame : Int)) →
        σ.slot k' = σ0.slot k' := fun k' h1 h2 => (hsl k' h1 h2).trans (by rw [hσs])
    have hj' : NodeJE lbl (rsOf cx) (.let_ x (.newBuf cn τ) e) (ofEnv2 env) σ.slot c1 :=
      NodeJE.mono_lbl hlbl ⟨hj.1, hj.2.1, hj.2.2.congr fun _ _ _ _ o' _ => opdVal_upd fun r k' _ hk' =>
        hsl' k' (hout r k' hk').1 (hout r k' hk').2⟩
    have hfr' : ∀ b ∈ ofEnv2 env, ∀ pl ∈ b.2.2, ∀ o' ∈ pl.opds, ∀ r k', o' = .reg r → rsOf cx r = some k' →
        k' ≠ o - cx.frame := fun b hb pl hpl o' ho' r k' hor hrk hk =>
      Fresh.ofEnv2 hfr x b hb pl hpl o' ho' r hor (rsOf_inj hrk (hk ▸ hoff))
    have hvr' : ValRep lbl (.loc ⟨l, 0⟩ 0) σ.regs.X0.toBitVec.toNat := hvr
    exact SlotRepAt.of_nodeJE (NodeJE.newBuf2 hj' he2 qn l ini hoff hfr' hvr') hIt hlb hIc
  · rintro σ c ⟨⟨⟨c1, qx, qa, qτ, qe, qta, qws, qn, qh, q29, qra⟩, hq⟩, ⟨σC, ⟨σ0, hJ1, -⟩, -⟩,
      l, ini, old, rfl, -⟩
    obtain ⟨-, -, -, -, -, hr0, L, sm, B, hj, -⟩ := hJ1
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

open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.LowerNode (GrpL InLits EnvLit IsNum sevalAt_ofEnv2G_one)
open Scc.Lower (LitV litAt)
open Scc.Lower.Inv (atomV)

/-- **The memory side's fields of `Call.OK`** (the counter's and the
arena's labels and bounds, the units and offset of the call's elements,
the runtime reads, maps and value invariant at the counter and the
headers). -/
structure CallMsOK (ms : MemSide isaLSE2) (lab : Label → Int64) (q : Call) : Prop where
  ctr : (lab "scc_rt_heap_use").toBitVec = BitVec.ofNat 64 ms.ctr
  heap : (lab "scc_rt_heap").toBitVec.toNat = ms.heap
  room : ms.heap + 2 ^ 46 ≤ 2 ^ 64
  cells : ms.cells = 4194304
  units : ms.units q.n q.τ < 2 ^ 63
  off : ms.off q.n q.τ = 8 * (q.n * (Spike.Lib.A64.Alloc.mOf q.h).toNat) + 8
  rt : ms.rt (BitVec.ofNat 64 ms.ctr).toNat
  mp : ms.mp (Spike.Lib.A64.Flow.ctrLoc ms) true
  grow : ∀ old : Val, ms.G (Spike.Lib.A64.Flow.ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells →
    ms.G (Spike.Lib.A64.Flow.ctrLoc ms) ((old.setWidth 64 + q.u ms).setWidth 128)
  hdr : ∀ o, o + ms.units q.n q.τ ≤ ms.cells →
    ms.rt (q.hdrAt ms o) ∧ ms.mp ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ true ∧
      ms.G ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ (q.hdr.setWidth 128)

/-- **`Call.OK` from its source's fields and `CallMsOK`.** -/
theorem Call.OK.ofMs {ms : MemSide isaLSE2} {lab : Label → Int64} {q : Call}
    (hterm : q.c0.term = .let_ q.x (.newBuf q.a q.τ) q.e) (hev : TermRun.evalAt q.c0.env q.a = some (q.ta, q.ws))
    (hnum : TermRun.numOf q.ws = some q.n) (hhold : q.c0.hold = none) (hlt : q.n < 2 ^ 64)
    (hacc : ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us) (h : CallMsOK ms lab q) : q.OK ms lab :=
  ⟨hterm, hev, hnum, hhold, hlt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, hacc, h.rt, h.mp, h.grow, h.hdr⟩

/-- **The call's arguments at the call's source relation** (`AllocW2`'s
`hq`, `nbJ1` at the header `imm h`, the count `.imm kv` and the units
operand `u`): the call `q` at the source's control, its count `kv`
(the count atom `cn` lowered to `kv`, `hcn`, in a grouped environment,
`hg`; its word a number, a leaf of the walk's literals, `hsc`, `hleaf`,
`EnvLit`), its header `h`, its units `u`'s (`hu`); `Call.OK` from the
element type's accesses (`hacc`) and the memory side's fields (`hms`). -/
theorem allocHq {ms : MemSide isaLSE2} {L : Label → Int64} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {cx : FnCtx} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {x : String}
    {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env} {lits : List (String × LitV)} {cs bufs : List (String × Nat)}
    {h : Nat} {kv : UInt64} {u : Scc.IR.Operand} {tk : Ty}
    (hg : GrpL env) (hcn : atomV env cn = some (tk, [.imm kv])) (hsc : InLits lits cn)
    (hleaf : ∃ o, litAt lits cn = .leaf o)
    (hu : ∀ sl, Spike.Lib.Form.opdVal (rsOf cx) sl u = some (ms.units kv.toNat τ))
    (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us)
    (hms : ∀ q : Call, q.n = kv.toNat → q.τ = τ → q.h = BitVec.ofNat 64 h → CallMsOK ms L q) :
    ∀ σ c, nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv) u
      σ c → ∃ q : Call, q.OK ms L ∧ q.c0 = c ∧
        σ.regs.X0.toBitVec = q.h ∧ σ.regs.X1.toBitVec = q.k ∧ σ.regs.X2.toBitVec = q.u ms := by
  rintro σ c ⟨h0, h1, h2, -, -, -, L', sm, B, hj, hl, -⟩
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
    rw [← h0]; simp
  · refine BitVec.eq_of_toNat_eq ?_
    simp only [Spike.Lib.Form.opdVal_imm, Option.some.injEq] at h1
    rw [← h1]; simp [Call.k]
  · refine BitVec.eq_of_toNat_eq ?_
    rw [hu, Option.some.injEq] at h2
    simp only [Call.u, BitVec.toNat_ofNat]
    have hlt : ms.units kv.toNat τ < 2 ^ 64 := h2 ▸ BitVec.isLt _
    rw [← h2, Nat.mod_eq_of_lt hlt]

end Hq

/-- info: 'Spike.Lib.LowerA64.endJ_of_fallBlk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms endJ_of_fallBlk

/-- info: 'Spike.Lib.LowerA64.posOff_allocEntry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms posOff_allocEntry

/--
info: 'Spike.Lib.LowerA64.allocArgs_w2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocArgs_w2

/--
info: 'Spike.Lib.LowerA64.allocBl_w2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocBl_w2

/--
info: 'Spike.Lib.LowerA64.allocStore_w2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocStore_w2

/--
info: 'Spike.Lib.LowerA64.allocHq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocHq

end Spike.Lib.LowerA64
