/-
**The nodes of an `Accepted2` body** (x86-64): `bodyN`, `pendN`, `abortN`
and `retN` (`Node.lean`) at the node invariant with buffers and slices
(`NJB`, `Spike/Lib/Src/NJLB.lean`).

`bodyN`'s invariant `NJ` asks every bound word to be a number, which a
buffer's locative, a slice or a setup result is not. The nodes here carry
the walk's layouts `lits`, known values `cs` and buffers `bufs` (`litWalk2`,
`countsB`), with the source's labels, memory and label bound existential;
a symbolic environment of the lowering's is `ofEnv2` (words grouped per
source word).

- `bodyN2`, `pendN2`: a node of the body and a checked `+`'s pending store;
  besides the node invariant at the walk's term, the source control itself
  placed in the slots (`SlotRepAt`, `Spike/Lib/SlotRepAt.lean`), as the
  control may lag the node's term past `let`s without code whose bindings
  shadow variables it still reads;
- `AbJ2`, `abortN2`: the overflow abort label, the source at `AbSrcL`;
- `RetJ2`, `retN2`: the return's exit with any number of words, each
  represented by its result register (`RetJ.toJ2` on one word).
-/
import Spike.Lib.LowerX64.Node
import Spike.Lib.Src.NJLB
import Spike.Lib.Src.AbortImm2
import Spike.Lib.Src.LitPt2
import Spike.Lib.SlotRepAt

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.Form (SEnv)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Scc.Emit.X64 (labelOf)

/-! ## Nodes -/

/-- **A node of an `Accepted2` body** at `pc`, term `t`, symbolic
environment `s`, the walk's layouts `lits`, known values `cs` and buffers
`bufs`: the node invariant with buffers and slices (`NJB`) at some labels
`L`, source memory `sm` and label bound `B`; the saved pair; the source
control reached locally from the ghost `c0`, itself placed in the slots
with its immediates the table `i`'s (`SlotRepAt`). -/
def bodyN2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat)
    (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64) (c0 : Ctl) (pc : Int64) (t : Expr) (s : SEnv)
    (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) : ND :=
  ⟨pc, oB fr, fun σ c => (∃ L sm B, NJB p lbl (rsOf fr) lits cs bufs L sm lsize B t s σ.slot c) ∧ FrJ fp ra σ.slot ∧
    LocalRun p c0 c ∧ SlotRepAt i lbl (rsOf fr) σ.slot c⟩

/-- **The pending store** of a checked `+` (`pendN` at `NJB`): `x`'s cell
`k` valued by `%rax`, in the node invariant and in the control's
placement. -/
def pendN2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat)
    (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64) (c0 : Ctl) (pc : Int64) (t : Expr) (s : SEnv)
    (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (k : Int) : ND :=
  ⟨pc, oB fr, fun σ c =>
    (∃ L sm B, NJB p lbl (rsOf fr) lits cs bufs L sm lsize B t s (upd σ.slot k (σ.regs.get64 .rax)) c) ∧
    FrJ fp ra σ.slot ∧ LocalRun p c0 c ∧ SlotRepAt i lbl (rsOf fr) (upd σ.slot k (σ.regs.get64 .rax)) c⟩

/-- **The source at the overflow abort label** (`AbJ` at the walk's
layouts): `AbSrcL` in some symbolic environment and layouts, the
source's environment small (`EnvSmall`, the overflow abort's budget), the
immediates the table `i`'s and register bases for the locatives at the
source's term, the term satisfying `T`;
the saved pair. -/
def AbJ2 (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  (∃ s lits, AbSrcL lbl (rsOf fr) lits s σ.slot c ∧ EnvSmall c.env ∧ ImmIn i s c.term ∧
    LocBaseRegAt s c.term ∧ T c.term) ∧
    FrJ fp ra σ.slot

/-- **The overflow abort label** of an `Accepted2` body. -/
def abortN2 (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame) (lab : String → Int64) (fp ra : BitVec 64)
    (c0 : Ctl) : ND :=
  ⟨lab (ovfL fr), oB fr, fun σ c => AbJ2 i T lbl fr fp ra σ c ∧ LocalRun p c0 c⟩

/-- **The return's exit of any word count**: as `RetJ`, each of `a`'s
words represented by its result register (`%rax`, `%rdx`, …). -/
def RetJ2 (lbl : WeakMem.AllocLabel → Option Nat) (fp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  ∃ a t ws, c.term = .ret a ∧ c.hold = none ∧ TermRun.evalAt c.env a = some (t, ws) ∧
    ws.length ≤ Scc.Emit.X64.retRegs.length ∧
    (∀ j (hj : j < ws.length) (hr : j < Scc.Emit.X64.retRegs.length),
      ValRep lbl ws[j].val (σ.regs.get64 Scc.Emit.X64.retRegs[j]).toNat) ∧
    σ.regs.get64 .rbp = fp

theorem RetJ.toJ2 {lbl : WeakMem.AllocLabel → Option Nat} {fp : BitVec 64} {σ : AS} {c : Ctl}
    (h : RetJ lbl fp σ c) : RetJ2 lbl fp σ c := by
  obtain ⟨a, t, w, ht, hh, he, -, hv, hbp⟩ := h
  refine ⟨a, t, [w], ht, hh, he, by simp [Scc.Emit.X64.retRegs], fun j hj _ => ?_, hbp⟩
  match j, hj with
  | 0, _ => exact hv

/-- **The return's exit node of any word count**: `%rsp` past the popped
return address. -/
def retN2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (c0 : Ctl) : ND :=
  ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => RetJ2 lbl fp σ c ∧ LocalRun p c0 c⟩

end Spike.Lib.LowerX64
