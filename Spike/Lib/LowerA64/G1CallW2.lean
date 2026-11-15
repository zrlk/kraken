/-
**A plain call's blocks inside `W2` at placed nodes** (AArch64): the
premises `hWB`, `hWR`, `hWBl`, `hWC` of `CallC2FW`
(`Spike/Lib/LowerA64/G1CallWStmt.lean`) at the world `W2` with the write
abort `Ab lab` and the immediates `Λ.imms`, for a code predicate inside
`CdCLE` and a call predicate inside `BlC`, from the covered block
producers (`blkW_w2CP`, `blkW_w2Call`, `nodeW_w2CalleeEntry`,
`Spike/Lib/LowerA64/W2Body.lean`).

- `callBlk_facts`: a call's straight block (`CallBlk`: the argument's
  load, the result's store) is nonempty, covered at the frame's offsets,
  made of fall-throughs and writes no slot before its last instruction;
- `blkW_w2CallBlk`: a call's straight block of `CdCLE` inside `W2` given
  its states placed (the write abort's phase kept, `blkW_abSt_fallL`, the
  pc after it off the write abort by `CdCLE`);
- `fallBlk_chkHead`, `posOff_fnCode2`: the stack check's head is a
  fall-through, a compiled block's label a position off the write abort;
- `callW2_hWB`, `callW2_hWR`, `callW2_hWBl`, `callW2_hWC`: the four
  premises, the placement from the node's `SlotRepAt` (`blkW_placedS`, at
  the result's store with its slot at `x0`, `blkW_placedS_updX0`), `FrOk2`
  from the ghosts' (`hG0F`), the `bl`'s target a position off the write
  abort and the callee's prologue from its code facts (`FnCode2`,
  `ProPh`).
-/
import Spike.Lib.LowerA64.AllocW2W2
import Spike.Lib.LowerA64.G1CallWStmt
import Spike.Lib.LowerA64.ProgC2
import Spike.Lib.LowerA64.UserW

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (FStable BlkW ND classify AI okBlk)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)
open Scc.Emit.A64 (FnCtx directives)
open Scc.Lower.InvA64

/-- **A call's straight block** (`CallBlk`) is nonempty, covered at the
frame's offsets, made of fall-throughs, and writes no slot before its last
instruction. -/
theorem callBlk_facts {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {blk : List Directive} (hb : CallBlk cx blk) :
    blk ≠ [] ∧ okBlk (-(cx.frame : Int)) 0 (oF cx) blk = true ∧ fallBlk blk = true ∧
      noSlotWr blk.dropLast = true := by
  rcases hb with ⟨w, lw, hw, rfl⟩ | ⟨d, ls, hs, rfl⟩
  · exact ⟨getOp_ne_nil hf h1 hw, okBlk_argLoad hf h1 h16 hw, fallBlk_getOp hf h1 hw,
      noSlotWr_dropLast (noSlotWr_getOp hw)⟩
  · have hok := okBlk_resStore hf h1 h16 hs
    obtain ⟨o, ho, -⟩ := bind_eq_ok hs
    have hls : directives ls = [Spike.Lib.A64.Flow.spStr .X0 (Int64.ofInt o)] := by
      have hs' := hs
      rw [setReg_eq hf (by omega) ho] at hs'
      cases ok_inj hs'
      rfl
    refine ⟨by rw [hls]; simp, hok, ?_, by rw [hls]; rfl⟩
    rw [hls]; simp [fallBlk, Spike.Lib.A64.Flow.spStr, Spike.Lib.A64.Flow.classify, fallI]

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A call's straight block of the code inside `W2`** at the frames `fs`
(`blkW_w2CP`): a part of a piece at `CdCLE` (`hcd`) at a node with the
frame's offsets (`hno`), its states placed (`hP`), its controls off `main`'s
`ret` and free of `ZBad` (`hJ`): covered fall-throughs, so the write
abort's phase is kept (`blkW_abSt_fallL`, the pc after them off the write
abort, `posOff_end_subCdLE`). -/
theorem blkW_w2CallBlk {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra0 : Int64} {n : ND} {blk : List Directive}
    (hno : n.o = oF cx) (hcd : SubCd (CdCLE prog okPc ph lab ra0) n.pc blk) (hb : CallBlk cx blk)
    (hP : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n blk := by
  obtain ⟨hne, hok, hfb, -⟩ := callBlk_facts hf h1 h16 hb
  rw [← hno] at hok
  have hend := posOff_end_subCdLE hcd hne (endJ_of_fallBlk hfb)
  exact blkW_w2CP hI hR hal hlo hhi hl hh hsub hfit hFO hp (hcd.mono fun _ _ h => h.toCdC) hok
    (noRetBlk_of_fallBlk hfb)
    (blkW_abSt_fallL hI hpr hab (hcd.mono fun _ _ h => h.toCdCL) hok hR hal hlo hhi hfb hend) hP hJ

/-- The frame's register slots are cells of a region holding the frame. -/
theorem rsOf_off {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi) :
    ∀ r k, rsOf cx r = some k → R.Off k := fun r k hr => by
  unfold rsOf at hr
  split at hr
  · rename_i o ho
    cases hr
    obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho
    exact ⟨by omega, by omega, by omega⟩
  · cases hr

/-- **`CallC2FW`'s `hWB` at `W2`**: the argument's load (any call's
straight block) of `Cd` inside `CdCLE` (`hCd`), at a node placing its
controls in the slot file (`blkW_placedS`), `FrOk2` from the ghosts'
(`hG0F`). -/
theorem callW2_hWB {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) (hFS : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64} {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdCLE prog okPc ph lab ra0 pc blk) :
    ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt Λ.imms lbl (rsOf cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk cx blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n blk := by
  intro n blk hcd hno hJ hb
  exact blkW_w2CallBlk hI hpr hab hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hno (hcd.mono hCd) hb
    (blkW_placedS hFS (fun σ c h => (hJ σ c h).2.2.1) (rsOf_off hf h16 hlo hhi) hfp
      (callBlk_facts hf h1 h16 hb).2.2.2)
    fun σ c h => ⟨(hJ σ c h).2.2.2, hG0F c (hJ σ c h).1⟩

/-- **`CallC2FW`'s `hWR` at `W2`**: the result's store (any call's straight
block of at most one instruction) of `Cd` inside `CdCLE` (`hCd`), at a
node placing its controls in the slot file with the result's slot `k0` at
`x0`'s word (`blkW_placedS_updX0`), `FrOk2` from the ghosts' (`hG0F`). -/
theorem callW2_hWR {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) (hFS : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64} {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdCLE prog okPc ph lab ra0 pc blk) :
    ∀ (n : ND) blk (k0 : Int), SubCd Cd n.pc blk → n.o = oF cx → blk.length ≤ 1 →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt Λ.imms lbl (rsOf cx) (Spike.Lib.upd σ.slot k0 σ.regs.X0.toBitVec) c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk cx blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n blk := by
  intro n blk k0 hcd hno hb1 hJ hb
  exact blkW_w2CallBlk hI hpr hab hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hno (hcd.mono hCd) hb
    (blkW_placedS_updX0 (k0 := k0) hFS hb1 (fun σ c h => (hJ σ c h).2.2.1) (rsOf_off hf h16 hlo hhi) hfp)
    fun σ c h => ⟨(hJ σ c h).2.2.2, hG0F c (hJ σ c h).1⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- The stack check's head is a fall-through. -/
theorem fallBlk_chkHead (Z : Int64) : fallBlk (Spike.Lib.A64.Flow.chkHead Z) = true := by
  simp [fallBlk, Spike.Lib.A64.Flow.chkHead, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly, fallI]

/-- **A compiled block's label is a position off the write abort**: right
before its stack check's head (`c'.hpro`), whose label is none of the write
abort's (its function index none of the runtime's, `hfi`). -/
theorem posOff_fnCode2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {dg' : Decl}
    {RaOk : BitVec 64 → Prop} {Cd' : BitVec 64 → Int64 → List Directive → Prop}
    {i' : Expr → String → Nat → Option Nat} {T' : Expr → Prop} (c' : FnCode2 exe prog endPc RaOk Cd' i' T' dg')
    (hfi : c'.cx.fi ≠ 9 ∧ c'.cx.fi ≠ 12 ∧ c'.cx.fi ≠ 16) : PosOff prog lab (lab c'.fn) := by
  have hin := c'.hpro
  simp only [Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hgap, hb⟩, -⟩, -⟩, -⟩, -⟩ := hin
  have h0 := posOff_of_blockAt (lab := lab) hb (local_not_abLabs hfi "stack_check") (i := 0)
    (by simp [Spike.Lib.A64.Flow.chkHead])
  rw [show 0 + 0 = 0 from rfl, Spike.Lib.A64.Flow.ofNat4_zero] at h0
  rw [← hI.labOk] at h0 ⊢
  exact posOff_of_labelGap hI.lays hgap h0

/-- **`CallC2FW`'s `hWBl` at `W2`**: a call's `bl` to a callee `g` of `Bl`
inside `BlC` (`hBl`), its target `g`'s compiled block's label (`hcf`, as
`callW2_hWC`'s) a position off the write abort (`posOff_fnCode2`, so the
write abort's phase is kept, `blkW_abSt_pos`), at a node placing its
controls in the slot file (`blkW_w2Call`), `FrOk2` from the ghosts'
(`hG0F`). -/
theorem callW2_hWBl {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) (hFS : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64} {ra0 : Int64}
    {Bl : Int64 → Label → Nat → Prop} (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k)
    {lcx : Scc.Lower.Ctx} {T : Expr → Prop}
    (hcf : ∀ (g : String), Spike.Lib.LowerCall.Callee lcx g → (∃ x a e, T (.let_ x (.call g [] a []) e)) →
      ∃ (dg' : Decl) (RaOk : BitVec 64 → Prop) (Cd' : BitVec 64 → Int64 → List Directive → Prop)
        (i' : Expr → String → Nat → Option Nat) (T' : Expr → Prop) (c' : FnCode2 exe prog endPc RaOk Cd' i' T' dg'),
        dg'.name = g ∧ (c'.cx.fi ≠ 9 ∧ c'.cx.fi ≠ 12 ∧ c'.cx.fi ≠ 16) ∧
        ProPh okPc ph lab (c'.cx.local "stack_check") (Int64.ofInt c'.cx.frame) (proL c'.cx) c'.ps) :
    ∀ (n : ND) (g : String) k, Bl n.pc (Scc.Lower.Names.user g) k → Spike.Lib.LowerCall.Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt Λ.imms lbl (rsOf cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n
        [blD (Scc.Lower.Names.user g)] := by
  intro n g k hb hcl hT hno hJ
  have hT' : PosOff prog lab (lab (Scc.Lower.Names.user g)) := by
    obtain ⟨dg', RaOk, Cd', i', T', c', hnm, hfi, -⟩ := hcf g hcl hT
    have := posOff_fnCode2 hI c' hfi
    rwa [c'.hfn, hnm] at this
  have hbl := hBl _ _ _ hb
  have hbl' := hbl
  obtain ⟨L, j, hpc, hbk, -, hph, -⟩ := hbl'
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hbk (q := n.pc) (by rw [hI.labOk]; exact hpc)
  refine blkW_w2Call hI hR hal hlo hhi hl hh hsub hfit hFO hFS hp hbl ?_ (fun σ c h => (hJ σ c h).2.2.1)
    (rsOf_off hf h16 hlo hhi) hfp fun σ c h => ⟨(hJ σ c h).2.2.2, hG0F c (hJ σ c h).1⟩
  refine blkW_abSt_pos (lo := -(cx.frame : Int)) (hi := 0) hI hpr hab hcode
    (Spike.Lib.A64.Flow.okBlk_blD _ _ _ _) hR hal hlo hhi hph (noRet_bl _) ?_
  intro σ c _ k' hk a ha t' ht
  obtain rfl : k' = 0 := by simp at hk; omega
  have h0 : classify (blD (Scc.Lower.Names.user g)) = some (AI.bl (Scc.Lower.Names.user g)) := rfl
  simp only [List.getElem_cons_zero] at ha
  rw [h0] at ha
  cases ha
  simp only [aiTgts, List.mem_singleton] at ht
  subst ht
  exact .inl hT'

/-- **`CallC2FW`'s `hWC` at `W2`** (`nodeW_w2CalleeEntry`): for a callee
`g` of `p`, some compiled block named `g` whose code facts `c'` place its
prologue (`c'.hpro`: the label right before the stack check, the check's
head and its limit's load) with its function index none of the runtime's
and its prologue's phase facts (`hcf`, `ProOK`'s first two conjuncts); the
entry's write abort phase from the head's (`blkW_abSt_pos`: its
fall-throughs inside the head and at the limit's load, positions off the
write abort as the check label is none of its labels), the node's controls
placed in the slot file, `FrOk2` from the ghosts' (`hG0F`). -/
theorem callW2_hWC {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64} {lcx : Scc.Lower.Ctx}
    {T : Expr → Prop}
    (hcf : ∀ (g : String), Spike.Lib.LowerCall.Callee lcx g → (∃ x a e, T (.let_ x (.call g [] a []) e)) →
      ∃ (dg' : Decl) (RaOk : BitVec 64 → Prop) (Cd' : BitVec 64 → Int64 → List Directive → Prop)
        (i' : Expr → String → Nat → Option Nat) (T' : Expr → Prop) (c' : FnCode2 exe prog endPc RaOk Cd' i' T' dg'),
        dg'.name = g ∧ (c'.cx.fi ≠ 9 ∧ c'.cx.fi ≠ 12 ∧ c'.cx.fi ≠ 16) ∧
        ProPh okPc ph lab (c'.cx.local "stack_check") (Int64.ofInt c'.cx.frame) (proL c'.cx) c'.ps) :
    ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → Spike.Lib.LowerCall.Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt Λ.imms lbl (rsOf cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      ∀ s c, Spike.Lib.A64.Flow.At exe endPc R F n s c →
        W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs := by
  intro g dg hfd hcl hT n hpc hno hJ
  obtain ⟨dg', RaOk, Cd', i', T', c', hnm, hfi, hph⟩ := hcf g hcl hT
  have hin := c'.hpro
  simp only [Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hgap, hb⟩, hld⟩, -⟩, -⟩, -⟩ := hin
  have hpc' : n.pc = (_root_.Executable.labels exe).label c'.fn := by rw [hpc, c'.hfn, hnm]
  have he : lab (c'.cx.local "stack_check") + Int64.ofNat (4 * 0) = n.pc := by
    rw [hpc', ← hI.labOk, Scc.Cert.Rt.A64.label_labelGap hI.lays hgap, Spike.Lib.A64.Flow.ofNat4_zero,
      Spike.Lib.A64.Flow.ofNat4_zero]
  have hL := local_not_abLabs hfi "stack_check"
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  have hok : okBlk (-(cx.frame : Int)) 0 n.o (Spike.Lib.A64.Flow.chkHead (Int64.ofInt c'.cx.frame)) = true := by
    rw [hno]; exact okBlk_chkHead_at _ _ _ _
  have hph0 := hph.hd
  rw [he] at hph0
  have hfb := fallBlk_chkHead (Int64.ofInt c'.cx.frame)
  have HA : BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n
      (Spike.Lib.A64.Flow.chkHead (Int64.ofInt c'.cx.frame)) := by
    refine blkW_abSt_pos (lo := -(cx.frame : Int)) (hi := 0) hI hpr hab hcode hok hR hal hlo hhi hph0
      (Spike.Lib.A64.Rt.MainU.chkHead_noRet _) ?_
    intro σ c _ k hk a ha t ht
    have hfa := fallBlk_get hfb hk ha
    have htf : t = n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4 := by
      cases a <;> simp only [fallI, Bool.false_eq_true] at hfa <;>
        simp only [aiTgts, List.mem_singleton] at ht <;> exact ht
    subst htf
    rw [← he, Spike.Lib.A64.Flow.ofNat4_zero]
    have hk2 : k < 2 := by simpa [Spike.Lib.A64.Flow.chkHead] using hk
    refine .inl ?_
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · have := posOff_of_blockAt (lab := lab) hb hL (i := 1) (by simp [Spike.Lib.A64.Flow.chkHead])
      rw [Int64.add_assoc]
      exact this
    · have := posOff_of_blockAt (lab := lab) hld hL (i := 0) (by simp)
      rw [Int64.add_assoc]
      exact this
  intro s c hA
  exact (nodeW_w2CalleeEntry (rd := rd) (G := G) (ar := ar) (J := Jv) (lsize := lsize) hI hR hal hlo hhi hl hh
    hsub hfit hFO hp hgap hb hph.hd hpc' hno
    (BlkW.nodeW HA (by simp [Spike.Lib.A64.Flow.chkHead])) (fun σ c h => (hJ σ c h).2.2.1)
    (rsOf_off hf h16 hlo hhi) hfp (fun σ c h => ⟨(hJ σ c h).2.2.2, hG0F c (hJ σ c h).1⟩) s c hA).1

end W

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.callBlk_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callBlk_facts

/-- info: 'Spike.Lib.LowerA64.blkW_w2CallBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blkW_w2CallBlk

/-- info: 'Spike.Lib.LowerA64.callW2_hWB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callW2_hWB

/-- info: 'Spike.Lib.LowerA64.callW2_hWR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callW2_hWR

/-- info: 'Spike.Lib.LowerA64.callW2_hWBl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callW2_hWBl

/-- info: 'Spike.Lib.LowerA64.posOff_fnCode2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.posOff_fnCode2

/-- info: 'Spike.Lib.LowerA64.callW2_hWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callW2_hWC
