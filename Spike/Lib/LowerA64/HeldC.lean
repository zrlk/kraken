/-
**The plain and the output call held at the callee's `ret`** (AArch64; the
noRet walk's option A; the twin of `Spike.Lib.LowerX64.HeldC`): `CallC2`
and `PrintCallC` (`Body2.lean`) end at
`ContC` with the callee's return taken by the source. Here the source pair
is kept at the callee's `ret a` at the callee's frame above `fs` (`HeldC`),
its return step landing at `ContC`; the walk holds the rest of `main` back
at those pairs (`SegWS.lagF`, `Spike/Lib/SegLagSF.lean`).

- `HeldC`, `HeldCtl`: the held pairs and their controls;
- `HeldC.lagF`: a held pair is `LagF`'s at `HeldCtl`;
- `CallC2H`, `PrintCallCH`: `CallC2`, `PrintCallC` with the post `HeldC` of
  `ContC` (or an abort); `PrintCallCH`'s held control is `print`'s `ret ()`.
-/
import Spike.Lib.LowerA64.Body2
import Spike.Lib.SegLagSF

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (lookupS)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (printInsts)
open Spike.Lib.LowerCall (Callee)
open Scc.Lower.Inv (atomV regName)

/-- **The source at a callee's `ret` one frame above `fs`**, its return step
landing at a pair `Q` holds at; the frame is the call's (`let x = call … in
e`): its result variable `x`, its continuation `e`. -/
def HeldC (p : Prog) (Q : FragS isaLSE2) (fs : List TermRun.Frame) (x : String) (e : Expr) : FragS isaLSE2 :=
  fun s c fs' =>
    ∃ a f cR, c.term = .ret a ∧ fs' = f :: fs ∧ f.x = x ∧ f.body = e ∧ FrameStep p (c, fs') (cR, fs) ∧ Q s cR fs

/-- The held controls of `HeldC`, as `LagF`'s `C`. -/
def HeldCtl (fs : List TermRun.Frame) (c : Ctl) (fs' : List TermRun.Frame) : Prop :=
  ∃ a f, c.term = .ret a ∧ fs' = f :: fs

/-- **A held pair is `LagF`'s** at `HeldCtl`: its return step is the frame
run to `Q`. -/
theorem HeldC.lagF {p : Prog} {Q : FragS isaLSE2} {fs : List TermRun.Frame} {x : String} {e : Expr} {s : State}
    {c : Ctl} {fs' : List TermRun.Frame} (h : HeldC p Q fs x e s c fs') : LagF p (HeldCtl fs) Q s c fs' := by
  obtain ⟨a, f, cR, ht, rfl, -, -, hst, hQ⟩ := h
  exact ⟨⟨a, f, ht, rfl⟩, cR, fs, hQ, .single hst⟩

section Held

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}

/-- **A plain call held at the callee's `ret`** (`CallC2` with the post
`HeldC` of `ContC`, or an abort). -/
def CallC2H (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2) (K : State → State → Prop)
    (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64) (fs : List TermRun.Frame)
    (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Ab : FragS isaLSE2)
    (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x g : String) (is : List String)
    (a : At) (ts : List Ty) (e : Expr) (t : Ty) (w : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    G0 c0 → T (.let_ x (.call g is a ts) e) → Fresh env n →
    LitPt (.let_ x (.call g is a ts) e, lits) → EnvTy2 (.let_ x (.call g is a ts) e, env, n) → GrpL env →
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.call g is a ts) e) = true →
    Spike.Lib.LowerCall.Callee lcx g → atomV env a = some (t, [w]) →
    InstsC2 cx Cd Bl kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] pc' →
    (∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome) →
    ImmIn i (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e →
    LocBaseRegAt (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e →
    PtC2 lcx cx Cd Bl (_root_.Executable.labels exe).label i T Lk kk pc env n lits cs bufs
      (.let_ x (.call g is a ts) e) →
    SegWS W K p lbl ms
      (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.call g is a ts) e) env lits cs bufs)
      (fun s c fs' => HeldC p (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs (fun _ _ _ => False) pc' e
        ((x, .int, [.reg (regName "r" n)]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
        (Scc.Lower.bufsAfter x cs bufs (.call g is a ts))) fs x e s c fs' ∨ Ab s c fs')

/-- **An output call held at `print`'s `ret ()`** (`PrintCallC` with the
post `HeldC` of `ContC` at the held control `ret ()`, or an abort). -/
def PrintCallCH (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2) (K : State → State → Prop)
    (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64) (fs : List TermRun.Frame)
    (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Ab : FragS isaLSE2) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x g : String) (is : List String)
    (a : At) (ts : List Ty) (e : Expr) (xe : String × Scc.Frontend.Extern) (dg : Decl) (t : Ty)
    (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    G0 c0 → T (.let_ x (.call g is a ts) e) → Fresh env n →
    LitPt (.let_ x (.call g is a ts) e, lits) → EnvTy2 (.let_ x (.call g is a ts) e, env, n) → GrpL env →
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.call g is a ts) e) = true →
    (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf dg.argTy →
    lcx.externs.find? (·.1 == g) = some xe → lcx.prog.find? (·.name == g) = some dg → dg.retTy = .unit →
    atomV env a = some (t, [b, .reg o, m, cw]) →
    InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
    (∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, .unit, []) :: env)) y).isSome) →
    ImmIn i (ofEnv2 ((x, .unit, []) :: env)) e →
    LocBaseRegAt (ofEnv2 ((x, .unit, []) :: env)) e →
    SegWS W K p lbl ms
      (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.call g is a ts) e) env lits cs bufs)
      (fun s c fs' => HeldC p (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs (fun _ _ _ => False) pc' e
        ((x, .unit, []) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
        (Scc.Lower.bufsAfter x cs bufs (.call g is a ts))) fs x e s c fs' ∧ c.term = .ret .unit ∨
        Ab s c fs')

end Held

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.HeldC.lagF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.HeldC.lagF
