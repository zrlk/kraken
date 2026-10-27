/-
**The callee's interface at a call** (AArch64): the callee's ghost at a
call (`CallG`), the callee's entry node at `g`'s label (`calleeN`), its
argument (`ArgV`), and its frame condition at the call (`CalleeF`, with
`.inF` and `.callerCells`), as the x86-64 `CalleeF`. A plain call's
segment (`bl g`, the callee by `call_ndSF`, the return) and the callees'
segments (`CalleeSegs`, `Spike/Lib/LowerA64/ProgCB.lean`) are stated with
them.
-/
import Spike.Lib.LowerA64.BodyC
import Spike.Lib.A64CallSA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep opdVal_upd)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Spike.Lib.A64.Flow.Ret0 (CallerCells)

/-! ## The callee's interface -/

/-- **The callee's ghost at a call**: the caller's frame pointer, the return
address, the argument in `x0`, the callee's entry control. -/
structure CallG where
  fp : BitVec 64
  ra : BitVec 64
  v : BitVec 64
  cE : Ctl

/-- **The callee's entry** at `g`'s label (`sp` at the callee's region's
base): the source at the callee's entry control, `x29`/`x30` the caller's
frame pointer and the return address, `x0` the argument, the thread pointer
`tp`. -/
def calleeN (lab : Label → Int64) (g : String) (tp : UInt64) (q : CallG) : ND :=
  ⟨lab (Scc.Lower.Names.user g), ⟨0, []⟩, fun σ c => c = q.cE ∧ σ.regs.X29.toBitVec = q.fp ∧
    σ.regs.X30.toBitVec = q.ra ∧ σ.regs.X0.toBitVec = q.v ∧ σ.regs.TPIDR_EL0 = tp⟩

/-- **The callee's argument**: the entry control binds one variable to one
word, a number below `2^64` represented by `x0`'s value `q.v`. -/
def ArgV (lbl : WeakMem.AllocLabel → Option Nat) (q : CallG) : Prop :=
  ∃ x t w, q.cE.env = [(x, t, [w])] ∧ ValRep lbl w.val q.v.toNat ∧ ∃ k, w.val = .num k ∧ k < 2 ^ 64

/-- **The callee's frame condition at a call** (`call_ndSF`'s): the
caller's `F`, the caller's cells outside the callee's region holding values
(`CallerCells`), and the caller's state at the call (`mC`, `σC` at the
frame's offsets, the cells outside the callee's region kept from `mC`), its
source control `c` calling `q.cE` with the frame `fr` pushed, at a term in
`T` whose environment `s` the frame's cells place, its words numbers
(`EnvNum`), the saved pair in its cells; the continuation's free variables
but the result bound in `s`, their immediates the table `i`'s at the
continuation (as the x86-64 `CalleeF`). -/
def CalleeF (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx) (R : Region)
    (F : MachineData → Prop) (D : Int) (fp ra : BitVec 64) (i : Expr → String → Nat → Option Nat)
    (T : Expr → Prop) (q : CallG) (fr : TermRun.Frame) (F' : MachineData → Prop) : Prop :=
  ∀ m, F' m → F m ∧ CallerCells R (-(cx.frame : Int)) (-D) 0 m ∧
    ∃ mC σC c t s, Abs R (oF cx) mC σC ∧ CKept R (-(cx.frame : Int)) (-D) 0 mC m ∧ CallTo p c q.cE fr ∧
      T t ∧ NodeJ lbl (rsOf cx) t s σC.slot c ∧ EnvNum c.env ∧ FrJ fp ra σC.slot ∧
      (∀ y ∈ Scc.Sem.exprFv fr.body, y ≠ fr.x → (lookupS s y).isSome) ∧
      ∀ y k v, y ≠ fr.x → (lookupS s y).bind (·.2[k]?) = some (.one (.imm v)) → i fr.body y k = some v.toNat

section CalleeF

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {cx : FnCtx} {R : Region}
  {F : MachineData → Prop} {D : Int} {fp ra : BitVec 64} {i : Expr → String → Nat → Option Nat}
  {T : Expr → Prop} {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop}

/-- The callee's frame condition is inside the caller's. -/
theorem CalleeF.inF (h : CalleeF p lbl cx R F D fp ra i T q frm F') : ∀ m, F' m → F m :=
  fun m hm => (h m hm).1

/-- The caller's cells outside the callee's region hold values. -/
theorem CalleeF.callerCells (h : CalleeF p lbl cx R F D fp ra i T q frm F') :
    ∀ m, F' m → CallerCells R (-(cx.frame : Int)) (-D) 0 m :=
  fun m hm => (h m hm).2.1

end CalleeF

end Spike.Lib.LowerA64
