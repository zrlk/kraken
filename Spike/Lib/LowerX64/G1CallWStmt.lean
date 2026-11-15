/-
**The plain call of an `Accepted2` body with its blocks inside a fragment
that places the source** (x86-64; the twin of
`Spike/Lib/LowerA64/G1CallWStmt.lean`): the statement `CallC2FW` of
`callC2_ofF` (`Spike/Lib/LowerX64/CallC2.lean`) with the call's blocks
asked inside the frame's fragment only at nodes whose controls the slot
file places (`SlotRepAt`), as a fragment like `W2` needs (`PlacedS`).

`callC2_ofF`'s `hWB`, `hWBl`, `hWC` hold at every node whose controls are
in `G0` with the saved pair, which a fragment asking the source placed does
not give. Here each premise adds the node's placement and the `ret` guard
at no frames:

- `hWB`: the argument's load (a call's straight block, `CallBlk`), the
  controls placed in the slot file;
- `hWR`: the result's store (a call's straight block of one instruction),
  the controls placed in the slot file with the result's slot `k0` at
  `%rax`'s word;
- `hWBl`: the call's `callq` to a callee `g` of the lowering context called
  at a term of `T`, the controls placed in the slot file;
- `hWC`: the callee's entry at the caller's frame offsets below the return
  address, for a callee `g` of the lowering context called at a term of
  `T`, the controls placed in the slot file;
- `hTc`: only at a callee of the lowering context (`Callee`) are a call's
  indices and type arguments empty (an output call has one index).

The conclusion is `CallC2R` (`Spike/Lib/LowerX64/Body2SegHF.lean`): at no
frames the call is asked only where it does not continue with a bare `ret`
(`main`'s held calls are `HeldTailCX`'s).

The region is the body's rebased one (its base 16-aligned, `CxCore2.hal`);
the callee's region `calleeR R fr.size D` is below the caller's frame, its
saved `%rbp` and the return address.
-/
import Spike.Lib.LowerX64.CallC2
import Spike.Lib.LowerX64.Body2SegHF

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.LowerNode (SlotRepAt)

/-- **A call's straight blocks**: `w`'s load into `%rdi` (its directives
with any sizes), or `%rax`'s store into a register's slot. -/
def CallBlk (fr : Scc.Emit.X64.Frame) (blk : List (Directive × Nat)) : Prop :=
  (∃ w lw zs, getOp fr .rdi w = .ok lw ∧ zs.length = (dirs lw).length ∧ blk = (dirs lw).zip zs) ∨
    ∃ r off z, rsOf fr r = some off ∧ blk = [(stDir off, z)]

/-- **`callC2_ofF` with its blocks asked at placed nodes** (see the module
docstring). -/
def CallC2FW : Prop :=
  ∀ {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isa} {W : FragS isa}
    {fr : Scc.Emit.X64.Frame},
    FrameOk fr → fr.size ≤ 2 ^ 31 → fr.size % 16 = 0 → ∀ {lcx : Scc.Lower.Ctx}, lcx.prog = p →
    FStable R F → R.OK → R.base.toNat % 16 = 0 → ∀ {D : Int}, 0 ≤ D → D % 8 = 0 →
    R.lo ≤ -(fr.size : Int) - 8 - D → 16 ≤ R.hi →
    ∀ {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
      {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop},
    (∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) →
    (∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)]) →
    ∀ {G0 : Ctl → Prop}, (∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') →
    ∀ {i : Expr → String → Nat → Option Nat} {T : Expr → Prop},
    -- the argument's load
    (∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk fr blk → BlkW (fun s c => W s c fs) K exe endPc R F n blk) →
    -- the result's store
    (∀ (n : ND) blk (k0 : Int), SubCd Cd n.pc blk → n.o = oB fr → blk.length ≤ 1 →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt i lbl (rsOf fr) (Spike.Lib.upd σ.slot k0 (σ.regs.get64 .rax)) c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk fr blk → BlkW (fun s c => W s c fs) K exe endPc R F n blk) →
    -- the call's `callq`
    (∀ (n : ND) zc (g : String) k, Bl n.pc zc (Scc.Lower.Names.user g) k → Spike.Lib.LowerCall.Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → n.o = oB fr →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      BlkW (fun s c => W s c fs) K exe endPc R F n [(i64 (.call (rel (Scc.Lower.Names.user g))), zc)]) →
    -- the callee's entry
    (∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → Spike.Lib.LowerCall.Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      ∀ s c, At exe endPc R F n s c → W s c fs) →
    (∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → Spike.Lib.LowerCall.Callee lcx g → is = [] ∧ ts = []) →
    ∀ {Ab : FragS isa} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop},
    (∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF2 p lbl lsize fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      CallSite2F p lbl lsize lcx fr Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q R D fp ra frm F' →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab)) →
    CallC2R p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk

end Spike.Lib.LowerX64
