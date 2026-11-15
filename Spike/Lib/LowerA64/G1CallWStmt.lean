/-
**The plain call of an `Accepted2` body with its blocks inside a fragment
that places the source** (AArch64): the statement `CallC2FW` of
`callC2_ofF` (`Spike/Lib/LowerA64/CallC2.lean`) with the call's blocks
asked inside the frame's fragment only at nodes whose controls the slot
file places (`SlotRepAt`), as a fragment like `W2` needs (`PlacedS`,
`blkW_w2C`, `blkW_w2Call`, `nodeW_w2CalleeEntry`).

`callC2_ofF`'s `hWB`, `hWBl`, `hWC` hold at every node whose controls are
in `G0` with the saved pair, which a fragment asking the source placed does
not give. Here each premise adds the node's placement and the `ret` guard
at no frames:

- `hWB`: the argument's load (a `CallBlk`), the controls placed in the slot
  file;
- `hWR`: the result's store (one instruction, a `CallBlk`), the controls
  placed in the slot file with the result's slot `k0` at `x0`'s word;
- `hWBl`: the call's `bl` to a callee of the lowering context called at a
  term of `T`, the controls placed in the slot file;
- `hWC`: the callee's entry at the caller's frame offsets, for a callee
  `g` of the lowering context called at a term of `T`, the controls placed
  in the slot file;
- `hTc`: only at a callee of the lowering context (`Callee`) are a call's
  indices and type arguments empty (an output call has one index).

The conclusion is `CallC2R` (`Spike/Lib/LowerA64/Body2SegHF.lean`): at no
frames the call is asked only where it does not continue with a bare `ret`
(`main`'s held calls are `HeldTailCX`'s).
-/
import Spike.Lib.LowerA64.CallC2
import Spike.Lib.LowerA64.Body2SegHF

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode (SlotRepAt)

/-- **`callC2_ofF` with its blocks asked at placed nodes** (see the module
docstring). -/
def CallC2FW : Prop :=
  ∀ {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isaLSE2} {W : FragS isaLSE2} {cx : FnCtx},
    FrameOk cx → cx.frame ≤ 4095 → cx.frame % 16 = 0 → ∀ {lcx : Scc.Lower.Ctx}, lcx.prog = p →
    FStable R F → R.OK → R.base.toNat % 16 = 0 → ∀ {D : Int}, 0 ≤ D → D % 8 = 0 →
    R.lo ≤ -(cx.frame : Int) - D → 0 ≤ R.hi →
    ∀ {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
      {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop},
    (∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) → (∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g]) →
    ∀ {G0 : Ctl → Prop}, (∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') →
    ∀ {i : Expr → String → Nat → Option Nat} {T : Expr → Prop},
    -- the argument's load
    (∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk cx blk → BlkW (fun s c => W s c fs) K exe endPc R F n blk) →
    -- the result's store
    (∀ (n : ND) blk (k0 : Int), SubCd Cd n.pc blk → n.o = oF cx → blk.length ≤ 1 →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt i lbl (rsOf cx) (Spike.Lib.upd σ.slot k0 σ.regs.X0.toBitVec) c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk cx blk → BlkW (fun s c => W s c fs) K exe endPc R F n blk) →
    -- the call's `bl`
    (∀ (n : ND) (g : String) k, Bl n.pc (Scc.Lower.Names.user g) k → Spike.Lib.LowerCall.Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      BlkW (fun s c => W s c fs) K exe endPc R F n [blD (Scc.Lower.Names.user g)]) →
    -- the callee's entry
    (∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → Spike.Lib.LowerCall.Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      ∀ s c, At exe endPc R F n s c → W s c fs) →
    (∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → Spike.Lib.LowerCall.Callee lcx g → is = [] ∧ ts = []) →
    ∀ {Ab : FragS isaLSE2} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop},
    (∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-(cx.frame : Int)) (-D) 0) F' → CalleeF2 p lbl lsize cx R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB k, Bl pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      CallSite2F p lbl lsize lcx cx Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q R D fp ra frm F' →
      SegWS W K p lbl ms ((At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty
          Ab)) →
    CallC2R p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk

end Spike.Lib.LowerA64
