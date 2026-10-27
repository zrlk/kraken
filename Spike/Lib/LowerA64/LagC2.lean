/-
**The non-call constructs' segments held back** (AArch64): the premises of
the body's induction (`Spike/Lib/LowerA64/Body2Seg.lean`) for `+`, `-`,
`if`, `ret` and the moves, with the source held back at the pairs of `C`
(`LagF`) under `SegWS.lagC`'s side conditions (`LagOk`,
`Spike/Lib/SegLagSC.lean`): the walk's lag over `main`'s last construct when
it is not a call, through its `ret` (the source held at the construct's
pair at depth 0, `HeldAt`, its runs `Quiet` at a quiet tail,
`quietFrom_heldAt`).

A lane store (`LaneC`) or an allocation (`NewBufC`) has no held-back form:
its source event (the exchange, the allocation) is taken with the target's
instruction, which a held-back source cannot (`not_quietFrom_newBuf`).

- `addC2_lag`, `subC2_lag`: `AddC2`, `SubC2` held back;
- `ifC2_lag`: `IfC2` held back, to either branch held back;
- `retC2_lag`: `RetC2` held back, to the body's exits held back;
- `pureMv2_lag`, `splitMv2_lag`, `unpackMv2_lag`: the moves held back;
- `contC_lag`: `ContC` held back, its node or its abort held back.
-/
import Spike.Lib.LowerA64.Body2Seg
import Spike.Lib.SegLagSC

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (isPure pureOp markR)
open Scc.Lower.Inv (atomV regName labName)

section LagC2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W W' : FragS isaLSE2} {K : State → State → Prop} {C : Ctl → List TermRun.Frame → Prop}
  {lcx : Scc.Lower.Ctx} {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
  {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {G0 : Ctl → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}

/-- **`ContC` held back**: the node at the continuation held back, or the
abort held back. -/
theorem contC_lag {c0 : Ctl} {pc' : Int64} {e : Expr} {env' : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {s : State} {c : Ctl}
    {fs' : List TermRun.Frame}
    (h : LagF p C (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e env' lits cs bufs) s c fs') :
    LagF p C (fun s c fs' => fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
      At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0' pc' e (ofEnv2 env') lits cs bufs).withTp tp) s c) s c fs' ∨
      LagF p C Ab s c fs' :=
  LagF.or h

/-- **A checked `+` held back.** -/
theorem addC2_lag (h : AddC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hL : LagOk p ms W W' C) {c0 : Ctl} {pc pc' : Int64} {kk : Nat} {env : Scc.Lower.Env} {n : Nat} {x : String}
    {a b : At} {e : Expr} {ta tb : Ty} {pa pb : Scc.IR.Operand} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)}
    (hpt : PtF lcx G0 i T c0 (.let_ x (.add a b) e) env n lits cs bufs)
    (ha : atomV env a = some (ta, [pa])) (hb : atomV env b = some (tb, [pb]))
    (hI : InstsC2 cx Cd Bl kk pc [.addChk (regName x n) pa pb] pc')
    (hc : ContF i e ((x, .int, [.reg (regName x n)]) :: env) (n + 1)) :
    SegWS W' K p lbl ms
      (LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.add a b) e) env lits cs bufs))
      (LagF p C (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e ((x, .int, [.reg (regName x n)]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.add a b)) :: lits) (Scc.Lower.csAfter x cs (.add a b))
        (Scc.Lower.bufsAfter x cs bufs (.add a b)))) :=
  hL.seg (h c0 pc pc' kk env n x a b e ta tb pa pb lits cs bufs hpt ha hb hI hc)

/-- **A saturating `-` held back.** -/
theorem subC2_lag (h : SubC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hL : LagOk p ms W W' C) {c0 : Ctl} {pc pc' : Int64} {kk : Nat} {env : Scc.Lower.Env} {n : Nat} {x : String}
    {a b : At} {e : Expr} {ta tb : Ty} {pa pb : Scc.IR.Operand} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)}
    (hpt : PtF lcx G0 i T c0 (.let_ x (.sub a b) e) env n lits cs bufs)
    (ha : atomV env a = some (ta, [pa])) (hb : atomV env b = some (tb, [pb]))
    (hI : InstsC2 cx Cd Bl kk pc [.subSat (regName x n) pa pb] pc')
    (hc : ContF i e ((x, .int, [.reg (regName x n)]) :: env) (n + 1)) :
    SegWS W' K p lbl ms
      (LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.sub a b) e) env lits cs bufs))
      (LagF p C (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e ((x, .int, [.reg (regName x n)]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.sub a b)) :: lits) (Scc.Lower.csAfter x cs (.sub a b))
        (Scc.Lower.bufsAfter x cs bufs (.sub a b)))) :=
  hL.seg (h c0 pc pc' kk env n x a b e ta tb pa pb lits cs bufs hpt ha hb hI hc)

/-- **An `if` held back**, to either branch's node held back. -/
theorem ifC2_lag (h : IfC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T)
    (hL : LagOk p ms W W' C) {c0 : Ctl} {pc : Int64} {kk : Nat} {env : Scc.Lower.Env} {n : Nat} {a b : At}
    {yes no : Expr} {ta tb : Ty} {pa pb : Scc.IR.Operand} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)}
    (hpt : PtF lcx G0 i T c0 (.ifeq a b yes no) env n lits cs bufs)
    (ha : atomV env a = some (ta, [pa])) (hb : atomV env b = some (tb, [pb]))
    (hcd : CodeC2 cx Cd Bl kk pc [] (.br .eq pa pb (labName "then" n) (labName "else" (n + 1))))
    {Ly Ln : Label} (hy : cx.blockLabel (labName "then" n) = .ok Ly)
    (hn : cx.blockLabel (labName "else" (n + 1)) = .ok Ln) :
    SegWS W' K p lbl ms
      (LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.ifeq a b yes no) env lits cs bufs))
      (fun s c fs' =>
        LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs ((_root_.Executable.labels exe).label Ly) yes
          env lits cs bufs) s c fs' ∨
        LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs ((_root_.Executable.labels exe).label Ln) no
          env lits cs bufs) s c fs') :=
  (hL.seg (h c0 pc kk env n a b yes no ta tb pa pb lits cs bufs hpt ha hb hcd Ly Ln hy hn)).mono_post
    fun _ _ _ hx => LagF.or hx

/-- **A `ret` held back**, to the body's exits held back. -/
theorem retC2_lag (h : RetC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hL : LagOk p ms W W' C) {c0 : Ctl} {pc : Int64} {kk : Nat} {env : Scc.Lower.Env} {n : Nat} {a : At} {t : Ty}
    {ws : List Scc.IR.Operand} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hpt : PtF lcx G0 i T c0 (.ret a) env n lits cs bufs) (hok : RetOk (.ret a, env, n))
    (ha : atomV env a = some (t, ws)) (hcd : CodeC2 cx Cd Bl kk pc [] (.ret ws)) :
    SegWS W' K p lbl ms (LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.ret a) env lits cs bufs))
      (LagF p C (ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab)) :=
  hL.seg (h c0 pc kk env n a t ws lits cs bufs hpt hok ha hcd)

/-- **A `let` without code held back.** -/
theorem pureMv2_lag (h : PureMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T) {c0 : Ctl} {pc : Int64}
    {env : Scc.Lower.Env} {n : Nat} {x : String} {op : Op} {e : Expr} {t : Ty} {ws : List Scc.IR.Operand}
    {sc hq : List Scc.IR.Reg} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hp : isPure op = true) (hpt : PtF lcx G0 i T c0 (.let_ x op e) env n lits cs bufs)
    (hb : ∀ y k, (∃ b, op = .pair (.var y) b) → bufs.lookup y = some k → k < 2 ^ 28)
    (ho : pureOp env op = some (t, ws)) (hm : markR t ws = some (sc, hq)) (hc : ContF i e ((x, t, ws) :: env) n)
    {s : State} {c : Ctl} {fs' : List TermRun.Frame}
    (hx : LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x op e) env lits cs bufs) s c fs') :
    LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e ((x, t, ws) :: env)
      ((x, Scc.Lower.opLit lcx.prog lits op) :: lits) (Scc.Lower.csAfter x cs op)
      (Scc.Lower.bufsAfter x cs bufs op)) s c fs' :=
  LagF.mono (h c0 pc env n x op e t ws sc hq lits cs bufs hp hpt hb ho hm hc) hx

/-- **A `split` held back.** -/
theorem splitMv2_lag (h : SplitMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T) {c0 : Ctl} {pc : Int64}
    {env : Scc.Lower.Env} {n : Nat} {a : At} {x y : String} {e : Expr} {t : Ty} {ws : List Scc.IR.Operand}
    {u w : Ty} {nu : Nat} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hpt : PtF lcx G0 i T c0 (.split a x y e) env n lits cs bufs) (ha : atomV env a = some (t, ws))
    (hpr : Scc.Lower.prodOf t = some (u, w)) (hnu : Scc.Obj.valWords u = some nu)
    (hc : ContF i e ((y, w, ws.drop nu) :: (x, u, ws.take nu) :: env) n)
    {s : State} {c : Ctl} {fs' : List TermRun.Frame}
    (hx : LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.split a x y e) env lits cs bufs) s c fs') :
    LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e
      ((y, w, ws.drop nu) :: (x, u, ws.take nu) :: env)
      (match Scc.Lower.litAt lits a with
        | .node l r => (y, r) :: (x, l) :: lits
        | _ => (y, .leaf none) :: (x, .leaf none) :: lits)
      (Scc.Lower.unbuf y (Scc.Lower.unbuf x cs)) (Scc.Lower.unbuf y (Scc.Lower.unbuf x bufs))) s c fs' :=
  LagF.mono (h c0 pc env n a x y e t ws u w nu lits cs bufs hpt ha hpr hnu hc) hx

/-- **An index unpack held back.** -/
theorem unpackMv2_lag (h : UnpackMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T) {c0 : Ctl}
    {pc : Int64} {env : Scc.Lower.Env} {n : Nat} {a : At} {i' x : String} {e : Expr} {b : Ty}
    {ws : List Scc.IR.Operand} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hpt : PtF lcx G0 i T c0 (.unpack a i' x e) env n lits cs bufs) (ha : atomV env a = some (.iex b, ws))
    (hc : ContF i e ((x, b, ws) :: env) n) {s : State} {c : Ctl} {fs' : List TermRun.Frame}
    (hx : LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.unpack a i' x e) env lits cs bufs)
      s c fs') :
    LagF p C (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e ((x, b, ws) :: env)
      ((x, Scc.Lower.litAt lits a) :: lits) (Scc.Lower.unbuf x (Scc.Lower.unbuf i' cs))
      (Scc.Lower.unbuf x (Scc.Lower.unbuf i' bufs))) s c fs' :=
  LagF.mono (h c0 pc env n a i' x e b ws lits cs bufs hpt ha hc) hx

end LagC2

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.addC2_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.addC2_lag

/-- info: 'Spike.Lib.LowerA64.ifC2_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.ifC2_lag

/-- info: 'Spike.Lib.LowerA64.retC2_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.retC2_lag
