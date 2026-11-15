/-
**A plain call's blocks inside `W2` at placed nodes** (x86-64; the twin of
`Spike/Lib/LowerA64/G1CallW2.lean`): the premises `hWB`, `hWR`, `hWBl`,
`hWC` of `CallC2FW` (`Spike/Lib/LowerX64/G1CallWStmt.lean`) at the world
`W2` with the write abort `Ab lab` and the immediates `Λ.imms`, for a code
predicate inside `CdCLE` and a call predicate inside `BlC`, from the covered
block producers (`blkW_w2CP`, `blkW_w2Call`, `nodeW_w2CalleeEntry`,
`Spike/Lib/LowerX64/W2Body.lean`).

- `callBlk_facts`: a call's straight block (`CallBlk`: the argument's
  load, the result's store) is nonempty, covered at the frame's offsets,
  made of fall-throughs and writes no slot before its last instruction;
- `blkW_w2CallBlk`: a call's straight block of `CdCLE` inside `W2` given
  its states placed (the write abort's phase kept, `blkW_abSt_fallL`, the
  pc after it off the write abort by `CdCLE`);
- `rsOf_off`: the frame's register slots are cells of a region holding the
  frame;
- `posOff_fnCode2`: a compiled block's label is a position off the write
  abort (its prologue head's first cell);
- `callW2_hWB`, `callW2_hWR`, `callW2_hWBl`, `callW2_hWC`: the four
  premises, the placement from the node's `SlotRepAt` (`blkW_placedS`, at
  the result's store with its slot at `%rax`, `blkW_placedS_upd`), `FrOk2`
  from the ghosts' (`hG0F`), the `callq`'s target a position off the write
  abort and the callee's prologue head from its code facts (`FnCode2`,
  `ProPh`).
-/
import Spike.Lib.LowerX64.AllocW2W2
import Spike.Lib.LowerX64.G1CallW
import Spike.Lib.LowerX64.ProW2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND okBlk cellOff FStable AI CodeAt)
open Spike.Lib.X64.Flow (xHead xLea)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)
open Scc.Cert.Rt.X64 (blockAtB label_labelGapB)
open Scc.Emit.X64 (i64 rel)
open Scc.Lower.InvX64

/-- **A call's straight block** (`CallBlk`) is nonempty, covered at the
frame's offsets, made of fall-throughs, and writes no slot before its last
instruction. -/
theorem callBlk_facts {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {blk : List (Directive × Nat)} (hb : CallBlk fr blk) :
    blk ≠ [] ∧ okBlk (-(fr.size : Int)) 16 (oB fr) blk = true ∧ fallBlk blk = true ∧
      noSlotWr blk.dropLast = true := by
  rcases hb with ⟨w, lw, zs, hw, hz, rfl⟩ | ⟨r, off, z, hoff, rfl⟩
  · obtain ⟨dl, hdl⟩ := dirs_getOp hw
    refine ⟨zip_ne_nil hz (by rw [hdl]; simp), ?_, fallBlk_getOp hw hz, ?_⟩
    · have := okBlk_getOp hf h1 (by decide) (by decide) hw hz []
      rw [List.append_nil] at this
      rw [this]; rfl
    · refine noSlotWr_dropLast (noSlotWrD_dropLast ?_)
      rw [List.map_fst_zip (by omega)]
      exact noSlotWrD_getOp hw
  · exact ⟨by simp, okBlk_stDir hf h1 hoff z, fallBlk_stDir off z, rfl⟩

/-- The frame's register slots are cells of a region holding the frame. -/
theorem rsOf_off {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {R : Region} (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 0 ≤ R.hi) : ∀ r k, rsOf fr r = some k → R.Off k := fun _ _ hr => by
  obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr
  exact ⟨h2, by omega, by omega⟩

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A call's straight block of the code inside `W2`** at the frames `fs`
(`blkW_w2CP`): a part of a piece at `CdCLE` (`hcd`) at a node with the
frame's offsets (`hno`), its states placed (`hP`), its controls off `main`'s
`ret` and free of `ZBad` (`hJ`): covered fall-throughs, so the write
abort's phase is kept (`blkW_abSt_fallL`, the pc after them off the write
abort, `posOff_end_subCdLE`). -/
theorem blkW_w2CallBlk {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra0 : Int64} {n : ND}
    {blk : List (Directive × Nat)} (hno : n.o = oB fr) (hcd : SubCd (CdCLE cells okPc ph lab ra0) n.pc blk)
    (hb : CallBlk fr blk)
    (hP : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n blk := by
  obtain ⟨hne, hok, hfb, -⟩ := callBlk_facts hf h1 hb
  rw [← hno] at hok
  have hend := posOff_end_subCdLE hcd hne (endJ_of_fallBlk hfb)
  exact blkW_w2CP hI hR (by omega) hlo hhi hl hh hsub hfit hFO hp (hcd.mono fun _ _ h => h.toCdC) hok
    (noRetBlk_of_fallBlk hfb)
    (blkW_abSt_fallL hI hpr hab (hcd.mono fun _ _ h => h.toCdCL) hok hR hlo hhi hfb hend) hP hJ

/-- **`CallC2FW`'s `hWB` at `W2`**: the argument's load (any call's
straight block) of `Cd` inside `CdCLE` (`hCd`), at a node placing its
controls in the slot file (`blkW_placedS`), `FrOk2` from the ghosts'
(`hG0F`). -/
theorem callW2_hWB {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (hFS : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64} {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdCLE cells okPc ph lab ra0 pc blk) :
    ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt Λ.imms lbl (rsOf fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk fr blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n blk := by
  intro n blk hcd hno hJ hb
  exact blkW_w2CallBlk hI hpr hab hf h1 hR hal hlo hhi hl hh hsub hfit hFO hp hno (hcd.mono hCd) hb
    (blkW_placedS hFS (fun σ c h => (hJ σ c h).2.2.1) (rsOf_off hf hlo (by omega)) hfp
      (callBlk_facts hf h1 hb).2.2.2)
    fun σ c h => ⟨(hJ σ c h).2.2.2, hG0F c (hJ σ c h).1⟩

/-- **`CallC2FW`'s `hWR` at `W2`**: the result's store (any call's straight
block of at most one instruction) of `Cd` inside `CdCLE` (`hCd`), at a
node placing its controls in the slot file with the result's slot `k0` at
`%rax`'s word (`blkW_placedS_upd`), `FrOk2` from the ghosts' (`hG0F`). -/
theorem callW2_hWR {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (hFS : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64} {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdCLE cells okPc ph lab ra0 pc blk) :
    ∀ (n : ND) blk (k0 : Int), SubCd Cd n.pc blk → n.o = oB fr → blk.length ≤ 1 →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt Λ.imms lbl (rsOf fr) (Spike.Lib.upd σ.slot k0 (σ.regs.get64 .rax)) c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk fr blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n blk := by
  intro n blk k0 hcd hno hb1 hJ hb
  exact blkW_w2CallBlk hI hpr hab hf h1 hR hal hlo hhi hl hh hsub hfit hFO hp hno (hcd.mono hCd) hb
    (blkW_placedS_upd (k0 := k0) (r := .rax) hFS hb1 (fun σ c h => (hJ σ c h).2.2.1)
      (rsOf_off hf hlo (by omega)) hfp)
    fun σ c h => ⟨(hJ σ c h).2.2.2, hG0F c (hJ σ c h).1⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **A compiled block's label is a position off the write abort**: its
prologue head's first cell (`c'.hpro`), its label a user function's name
(`c'.hfn`), none of the write abort's. -/
theorem posOff_fnCode2 {dg' : Decl} {RaOk : BitVec 64 → Prop}
    {Cd' : BitVec 64 → Int64 → List (Directive × Nat) → Prop} {i' : Expr → String → Nat → Option Nat}
    {T' : Expr → Prop} (c' : FnCode2 exe cells endPc RaOk Cd' i' T' dg') : PosOff cells lab (lab c'.fn) := by
  have hin := c'.hpro
  simp only [Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨-, bHd⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hin
  have := posOff_blockAtB (lab := lab) (i := 0) bHd (by rw [c'.hfn]; exact user_not_abLabs _)
    (by simp [xHead])
  rwa [Spike.Lib.X64.cellOff_zero, show Int64.ofNat (0 + 0) = 0 from rfl, Int64.add_zero] at this

/-- **`CallC2FW`'s `hWBl` at `W2`**: a call's `callq` to a callee `g` of
`Bl` inside `BlC` (`hBl`), its target `g`'s compiled block's label (`hcf`,
as `callW2_hWC`'s) a position off the write abort (`posOff_fnCode2`, so the
write abort's phase is kept, `blkW_abSt_pos`), at a node placing its
controls in the slot file (`blkW_w2Call`), `FrOk2` from the ghosts'
(`hG0F`). -/
theorem callW2_hWBl {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h16 : fr.size % 16 = 0) (hFS : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64} {ra0 : Int64}
    {Bl : Int64 → Nat → Label → Nat → Prop} (hBl : ∀ pc zc g k, Bl pc zc g k → BlC cells okPc ph lab fr ra0 pc zc g k)
    {lcx : Scc.Lower.Ctx} {T : Expr → Prop}
    (hcf : ∀ (g : String), Spike.Lib.LowerCall.Callee lcx g → (∃ x a e, T (.let_ x (.call g [] a []) e)) →
      ∃ (dg' : Decl) (RaOk : BitVec 64 → Prop) (Cd' : BitVec 64 → Int64 → List (Directive × Nat) → Prop)
        (i' : Expr → String → Nat → Option Nat) (T' : Expr → Prop) (c' : FnCode2 exe cells endPc RaOk Cd' i' T' dg'),
        dg'.name = g ∧ c'.fr.fn = Scc.Lower.Names.user dg'.name ∧
        ProPh okPc ph lab c'.fn (Scc.Emit.X64.labelOf c'.fr.fn "chk") (Int64.ofInt c'.fr.size) (proL c'.fr)
          c'.zl c'.zf c'.z1 c'.z2 c'.zs c'.ps) :
    ∀ (n : ND) zc (g : String) k, Bl n.pc zc (Scc.Lower.Names.user g) k → Spike.Lib.LowerCall.Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → n.o = oB fr →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt Λ.imms lbl (rsOf fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n
        [(i64 (.call (rel (Scc.Lower.Names.user g))), zc)] := by
  intro n zc g k hb hcl hT hno hJ
  have hT' : PosOff cells lab (lab (Scc.Lower.Names.user g)) := by
    obtain ⟨dg', RaOk, Cd', i', T', c', hnm, -, -⟩ := hcf g hcl hT
    have := posOff_fnCode2 (lab := lab) c'
    rwa [c'.hfn, hnm] at this
  have hbl := hBl _ _ _ _ hb
  have hbl' := hbl
  obtain ⟨L, j, off, hpc, hbk, -, hph, -⟩ := hbl'
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [(i64 (.call (rel (Scc.Lower.Names.user g))), zc)] := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hbk
    rwa [hI.labOk, hpc] at this
  refine blkW_w2Call hI (by omega) hR (by omega) hlo hhi hl hh hsub hfit hFO hFS hp hno hbl ?_
    (fun σ c h => (hJ σ c h).2.2.1) (rsOf_off hf (by omega) (by omega)) hfp
    fun σ c h => ⟨(hJ σ c h).2.2.2, hG0F c (hJ σ c h).1⟩
  refine blkW_abSt_pos (lo := -(fr.size : Int) - 8) (hi := 16) hI hpr hab hcode
    (okBlk_callqC _ zc (by rw [hno]; simp [offOk, oB]; omega)) hR hlo hhi hph (noRet_callq _ zc) ?_
  intro σ c _ k' hk a ha t' ht
  obtain rfl : k' = 0 := by simp at hk; omega
  have h0 : Spike.Lib.X64.classify (i64 (.call (rel (Scc.Lower.Names.user g)))) =
    some (AI.call (Scc.Lower.Names.user g)) := rfl
  simp only [List.getElem_cons_zero] at ha
  rw [h0] at ha
  cases ha
  simp only [aiTgts, List.mem_singleton] at ht
  subst ht
  exact .inl hT'

/-- **`CallC2FW`'s `hWC` at `W2`** (`nodeW_w2CalleeEntry`): for a callee
`g` of `p`, some compiled block named `g` whose code facts `c'` place its
prologue (`c'.hpro`: its head right after its label, the check label `4`
bytes on) with its frame's function `g`'s and its prologue's phase facts
(`hcf`, `ProOK`'s first and third conjuncts); the entry's write abort
phase from the head's (`blkW_abSt_at`: two fall-throughs, the pc after them
the check's first cell, a position off the write abort as the check label
is none of its labels), the node's controls placed in the slot file,
`FrOk2` from the ghosts' (`hG0F`). -/
theorem callW2_hWC {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 16) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64} {lcx : Scc.Lower.Ctx}
    {T : Expr → Prop}
    (hcf : ∀ (g : String), Spike.Lib.LowerCall.Callee lcx g → (∃ x a e, T (.let_ x (.call g [] a []) e)) →
      ∃ (dg' : Decl) (RaOk : BitVec 64 → Prop) (Cd' : BitVec 64 → Int64 → List (Directive × Nat) → Prop)
        (i' : Expr → String → Nat → Option Nat) (T' : Expr → Prop) (c' : FnCode2 exe cells endPc RaOk Cd' i' T' dg'),
        dg'.name = g ∧ c'.fr.fn = Scc.Lower.Names.user dg'.name ∧
        ProPh okPc ph lab c'.fn (Scc.Emit.X64.labelOf c'.fr.fn "chk") (Int64.ofInt c'.fr.size) (proL c'.fr)
          c'.zl c'.zf c'.z1 c'.z2 c'.zs c'.ps) :
    ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → Spike.Lib.LowerCall.Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt Λ.imms lbl (rsOf fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      ∀ s c, Spike.Lib.X64.At exe endPc R F n s c →
        W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs := by
  intro g dg hfd hcl hT n hpc hno hJ
  obtain ⟨dg', RaOk, Cd', i', T', c', hnm, hfr, hph⟩ := hcf g hcl hT
  have hin := c'.hpro
  simp only [Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, -⟩, -⟩, -⟩, -⟩ := hin
  have hpc' : n.pc = (_root_.Executable.labels exe).label c'.fn := by rw [hpc, c'.hfn, hnm]
  have esc := label_labelGapB hI.lays hgap
  rw [hI.labOk] at esc
  have hsc : Scc.Emit.X64.labelOf c'.fr.fn "chk" ∉ X64.AllocG.abLabs := by
    rw [hfr]; exact labelOf_user_not_abLabs _ _
  have hfnL : c'.fn ∉ X64.AllocG.abLabs := by rw [c'.hfn]; exact user_not_abLabs _
  have he : lab c'.fn + Int64.ofNat 0 = n.pc := by
    rw [hpc', hI.labOk]; exact Spike.Lib.X64.Flow.ofNat_zero' _
  have h8 : (fr.size : Int) % 8 = 0 := by omega
  have hok : okBlk (-(fr.size : Int) - 16) 16 n.o xHead = true := by
    rw [hno]; exact okBlk_xHead_call fr (Int.le_refl _) h8 (by omega)
  have HA : BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n xHead := by
    refine blkW_abSt_at hI hpr hab bHd hfnL he hok hR hlo hhi hph.hd Spike.Lib.X64.Rt.MainU.xHead_noRet ?_
      (fun _ _ _ => htgt_fall fallBlk_xHead)
    have := posOff_blockAtB (lab := lab) (i := 0) bLea hsc (by simp [xLea])
    rwa [show lab (Scc.Emit.X64.labelOf c'.fr.fn "chk") +
        Int64.ofNat (0 + cellOff (xLea (Int64.ofInt c'.fr.size) c'.zl) 0) =
        lab c'.fn + Int64.ofNat (0 + cellOff xHead xHead.length) by rw [esc, Int64.add_assoc]; rfl] at this
  intro s c hA
  exact (nodeW_w2CalleeEntry (rd := rd) (G := G) (ar := ar) (J := Jv) (lsize := lsize) hI h8 hR (by omega) hlo hhi
    hl hh hsub hfit hFO hp bHd hph.hd hpc' hno (BlkW.nodeW HA (by simp [xHead]))
    (fun σ c h => (hJ σ c h).2.2.1) (rsOf_off hf (by omega) (by omega)) hfp
    (fun σ c h => ⟨(hJ σ c h).2.2.2, hG0F c (hJ σ c h).1⟩) s c hA).1

end W

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.callBlk_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callBlk_facts

/-- info: 'Spike.Lib.LowerX64.blkW_w2CallBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.blkW_w2CallBlk

/-- info: 'Spike.Lib.LowerX64.callW2_hWB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callW2_hWB

/-- info: 'Spike.Lib.LowerX64.callW2_hWR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callW2_hWR

/-- info: 'Spike.Lib.LowerX64.posOff_fnCode2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.posOff_fnCode2

/-- info: 'Spike.Lib.LowerX64.callW2_hWBl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callW2_hWBl

/-- info: 'Spike.Lib.LowerX64.callW2_hWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callW2_hWC
