/-
**A lowered `Accepted2` body is one segment** (AArch64): the induction over
`lowerC2`'s closed form (`Spike/Lib/LowerShapeC2.lean`), the twin of
`bodyC_segS` (`BodyC.lean`) at the nodes `bodyN2` (`Node2.lean`) and the
code `CodeC2` (`BlocksC2Code.lean`); the twin of the x86-64
`Spike/Lib/LowerX64/Body2Seg.lean`.

The induction is over per-construct premises (`body2_segS_of`), each in
`CallC2`'s shape: the construct's segment from the node at it to `ContC`
at its continuation, or a move between the nodes at the same code point
for a construct without code.

- `PtF`, `ContF`: the walk's facts at a construct and at its continuation,
  as the premises read them;
- `AddC2`, `SubC2`: a checked `+` and a saturating `-`;
- `PureMv2`, `SplitMv2`, `UnpackMv2`: the moves of a `let` without code, a
  `split` and an index unpack;
- `IfC2`: an `if`'s branch to its two blocks;
- `RetC2`: a `ret` to the body's exits (at most the argument registers'
  words, `RetOk`);
- `lowerC2_next_ge`: `lowerC2`'s counter does not decrease;
- `seg_cont`: a construct's segment, then the continuation's;
- `body2_segS_of`: the body's segment from the premises (with `CallC2`,
  `LaneC`, `NewBufC`, `PrintCallC`).
-/
import Spike.Lib.LowerA64.Body2
import Spike.Lib.LowerShapeC2Walk
import Spike.Lib.Src.LitPt2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC2 Res2 isPure pureOp markR lowerC2_add_inv lowerC2_sub_inv lowerC2_call_inv
  lowerC2_newBuf_inv lowerC2_xchg_inv lowerC2_pure_inv lowerC2_split_inv lowerC2_unpack_inv lowerC2_ifeq_inv
  lowerC2_ret_inv walk2_tail_add walk2_tail_sub walk2_tail_call walk2_tail_print walk2_tail_newBuf
  walk2_tail_xchg walk2_tail_pure walk2_tail_split walk2_tail_unpack walk2_tail_yes walk2_tail_no lowerC2_fv
  lowerC2_term_ne)
open Spike.Lib.LowerCall (Callee)
open Scc.Lower.Inv (atomV regName labName)
open Spike.Lib.Form (SEnv lookupS)

/-! ## The walk's facts -/

/-- **The walk's facts at a construct** `t` (environment `env`, counter
`n`, the walk's layouts `lits`, known values `cs`, buffers `bufs`): the
ghost in `G0`, the term in `T`, the environment fresh from `n`, the
literal walk's facts (`LitPt`), the lowering walk's (`EnvTy2`, `GrpL`),
the pairs paired (`countsB`), the immediates `i`'s, the free variables
bound. -/
def PtF (lcx : Scc.Lower.Ctx) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (c0 : Ctl) (t : Expr) (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)) : Prop :=
  G0 c0 ∧ T t ∧ Fresh env n ∧ LitPt (t, lits) ∧ EnvTy2 (t, env, n) ∧ GrpL env ∧
    Scc.Lower.countsB lcx.prog cs bufs lits t = true ∧ ImmIn i (ofEnv2 env) t ∧
    ∀ y ∈ Scc.Sem.exprFv t, (lookupS (ofEnv2 env) y).isSome

/-- **The walk's facts at a continuation** `e` (environment `env'`,
counter `n'`): the free variables bound, the immediates `i`'s, the
lowering walk's facts, the locatives' register bases. -/
def ContF (i : Expr → String → Nat → Option Nat) (e : Expr) (env' : Scc.Lower.Env) (n' : Nat) : Prop :=
  (∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 env') y).isSome) ∧ ImmIn i (ofEnv2 env') e ∧ GrpL env' ∧
    EnvTy2 (e, env', n') ∧ LocBaseRegAt (ofEnv2 env') e

theorem isSome_lookupS_ofEnv2 {env : Scc.Lower.Env} {y : String} (h : (env.find? (·.1 == y)).isSome) :
    (lookupS (ofEnv2 env) y).isSome := by
  rw [lookupS_ofEnv2]; simpa using h

section Body2Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

/-! ## The constructs' premises -/

/-- **A checked `+`** `let x = a + b`: `addChk x%n pa pb` (its pending
store included), to `x` bound to `x%n`, or the overflow abort (`Ab`). -/
def AddC2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Ab : FragS isaLSE2) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (a b : At)
    (e : Expr) (ta tb : Ty) (pa pb : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    PtF lcx G0 i T c0 (.let_ x (.add a b) e) env n lits cs bufs →
    atomV env a = some (ta, [pa]) → atomV env b = some (tb, [pb]) →
    InstsC2 cx Cd Bl kk pc [.addChk (regName x n) pa pb] pc' →
    ContF i e ((x, .int, [.reg (regName x n)]) :: env) (n + 1) →
    SegWS W K p lbl ms (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.add a b) e) env lits cs bufs)
      (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e ((x, .int, [.reg (regName x n)]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.add a b)) :: lits) (Scc.Lower.csAfter x cs (.add a b))
        (Scc.Lower.bufsAfter x cs bufs (.add a b)))

/-- **A saturating `-`** `let x = a - b`: `subSat x%n pa pb`. -/
def SubC2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Ab : FragS isaLSE2) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (a b : At)
    (e : Expr) (ta tb : Ty) (pa pb : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    PtF lcx G0 i T c0 (.let_ x (.sub a b) e) env n lits cs bufs →
    atomV env a = some (ta, [pa]) → atomV env b = some (tb, [pb]) →
    InstsC2 cx Cd Bl kk pc [.subSat (regName x n) pa pb] pc' →
    ContF i e ((x, .int, [.reg (regName x n)]) :: env) (n + 1) →
    SegWS W K p lbl ms (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.sub a b) e) env lits cs bufs)
      (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e ((x, .int, [.reg (regName x n)]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.sub a b)) :: lits) (Scc.Lower.csAfter x cs (.sub a b))
        (Scc.Lower.bufsAfter x cs bufs (.sub a b)))

/-- **A `let` without code** (`pureOp`, `isPure`): the node at the `let`
is the node at its continuation, `x` bound to the operation's words. -/
def PureMv2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (cx : FnCtx)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64)
    (tp : UInt64) (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat)
    (T : Expr → Prop) : Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (n : Nat) (x : String) (op : Op) (e : Expr) (t : Ty)
    (ws : List Scc.IR.Operand) (sc hq : List Scc.IR.Reg) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    isPure op = true → PtF lcx G0 i T c0 (.let_ x op e) env n lits cs bufs →
    (∀ y k, (∃ b, op = .pair (.var y) b) → bufs.lookup y = some k → k < 2 ^ 28) →
    pureOp env op = some (t, ws) → markR t ws = some (sc, hq) → ContF i e ((x, t, ws) :: env) n →
    ∀ s c fs', LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x op e) env lits cs bufs s c fs' →
      LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e ((x, t, ws) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits op) :: lits) (Scc.Lower.csAfter x cs op)
        (Scc.Lower.bufsAfter x cs bufs op) s c fs'

/-- **A `split`** `let (x, y) = a`: the node at it is the node at its
continuation, `x` bound to `a`'s first `nu` words, `y` to the rest, the
layouts `a`'s parts (`litWalk2`'s, `countsB`'s). -/
def SplitMv2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (cx : FnCtx)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64)
    (tp : UInt64) (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat)
    (T : Expr → Prop) : Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (n : Nat) (a : At) (x y : String) (e : Expr) (t : Ty)
    (ws : List Scc.IR.Operand) (u w : Ty) (nu : Nat) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    PtF lcx G0 i T c0 (.split a x y e) env n lits cs bufs →
    atomV env a = some (t, ws) → Scc.Lower.prodOf t = some (u, w) → Scc.Obj.valWords u = some nu →
    ContF i e ((y, w, ws.drop nu) :: (x, u, ws.take nu) :: env) n →
    ∀ s c fs', LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.split a x y e) env lits cs bufs s c fs' →
      LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e ((y, w, ws.drop nu) :: (x, u, ws.take nu) :: env)
        (match Scc.Lower.litAt lits a with
          | .node l r => (y, r) :: (x, l) :: lits
          | _ => (y, .leaf none) :: (x, .leaf none) :: lits)
        (Scc.Lower.unbuf y (Scc.Lower.unbuf x cs)) (Scc.Lower.unbuf y (Scc.Lower.unbuf x bufs)) s c fs'

/-- **An index unpack** `let ⟨i', x⟩ = a`: the node at it is the node at its
continuation, `x` bound to `a`'s words. -/
def UnpackMv2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (cx : FnCtx)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64)
    (tp : UInt64) (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat)
    (T : Expr → Prop) : Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (n : Nat) (a : At) (i' x : String) (e : Expr) (b : Ty)
    (ws : List Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
    PtF lcx G0 i T c0 (.unpack a i' x e) env n lits cs bufs →
    atomV env a = some (.iex b, ws) → ContF i e ((x, b, ws) :: env) n →
    ∀ s c fs', LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.unpack a i' x e) env lits cs bufs s c fs' →
      LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e ((x, b, ws) :: env)
        ((x, Scc.Lower.litAt lits a) :: lits) (Scc.Lower.unbuf x (Scc.Lower.unbuf i' cs))
        (Scc.Lower.unbuf x (Scc.Lower.unbuf i' bufs)) s c fs'

/-- **An `if`** `if a = b then yes else no` (the branch `br .eq pa pb` the
open block's terminator, `CodeC2` at `pc`; the blocks' assembler labels
`Ly`, `Ln`): to the node at `yes` at the `then` block's label or at `no` at
the `else` block's, the walk's state unchanged. -/
def IfC2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) :
    Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (a b : At) (yes no : Expr) (ta tb : Ty)
    (pa pb : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
    PtF lcx G0 i T c0 (.ifeq a b yes no) env n lits cs bufs →
    atomV env a = some (ta, [pa]) → atomV env b = some (tb, [pb]) →
    CodeC2 cx Cd Bl kk pc [] (.br .eq pa pb (labName "then" n) (labName "else" (n + 1))) →
    ∀ Ly Ln : Label, cx.blockLabel (labName "then" n) = .ok Ly → cx.blockLabel (labName "else" (n + 1)) = .ok Ln →
    SegWS W K p lbl ms (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.ifeq a b yes no) env lits cs bufs)
      (fun s c fs' =>
        LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs ((_root_.Executable.labels exe).label Ly) yes env lits cs
          bufs
          s c fs' ∨
        LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs ((_root_.Executable.labels exe).label Ln) no env lits cs
          bufs
          s c fs')

/-- **A `ret`** `ret a` (`a`'s words `ws`, at most eight, `RetOk`; `ret ws`
the open block's terminator): to the body's exits. -/
def RetC2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Ab : FragS isaLSE2) : Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (a : At) (t : Ty)
    (ws : List Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
    PtF lcx G0 i T c0 (.ret a) env n lits cs bufs → RetOk (.ret a, env, n) →
    atomV env a = some (t, ws) → CodeC2 cx Cd Bl kk pc [] (.ret ws) →
    SegWS W K p lbl ms (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.ret a) env lits cs bufs)
      (ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab)

/-! ## The induction -/

/-- **`lowerC2`'s counter does not decrease.** -/
theorem lowerC2_next_ge (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res2),
      lowerC2 cx env n l k e = some r → n ≤ r.next := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | add a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_add_inv hr; have := ih _ _ _ _ r' hr'; simp; omega
    | sub a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_sub_inv hr; have := ih _ _ _ _ r' hr'; simp; omega
    | call g is a ts =>
      rcases lowerC2_call_inv hr with ⟨_, _, _, r', -, -, -, -, hr', rfl⟩
          | ⟨_, _, _, _, _, _, _, r', -, -, -, -, hr', rfl⟩
      · have := ih _ _ _ _ r' hr'; simp; omega
      · have := ih _ _ _ _ r' hr'; simp; omega
    | newBuf c τ =>
      obtain ⟨_, _, _, _, _, _, _, r', -, -, -, -, -, hr', rfl⟩ := lowerC2_newBuf_inv hr
      have := ih _ _ _ _ r' hr'; simp; omega
    | xchgAt b i v =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r', -, -, -, -, -, -, -, -, hr', rfl⟩ :=
        lowerC2_xchg_inv hr
      have := ih _ _ _ _ r' hr'; simp; omega
    | _ =>
      first
      | (obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_pure_inv rfl hr
         exact ih _ _ _ _ r' hr')
      | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, _, -, -, -, hr'⟩ := lowerC2_split_inv hr
    exact ih _ _ _ _ _ hr'
  | unpack a i x e ih =>
    intro env n l k r hr
    obtain ⟨_, _, -, hr'⟩ := lowerC2_unpack_inv hr
    exact ih _ _ _ _ _ hr'
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, ry, rn, -, -, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    have h1 := ihy _ _ _ _ _ hy
    have h2 := ihn _ _ _ _ _ hn
    simp only
    omega
  | ret a =>
    intro env n l k r hr
    obtain ⟨_, _, -, rfl⟩ := lowerC2_ret_inv hr
    simp
  | _ => intro env n l k r hr; simp [lowerC2] at hr

/-- **A construct's segment, then its continuation's**: from the node at
the construct to `ContC` at `e`, and from the node at `e` to the body's
exits from every ghost in `G0` (closed under the frame runs at `fs`). -/
theorem seg_cont {cx : FnCtx} {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {i : Expr → String → Nat → Option Nat} {G0 : Ctl → Prop}
    (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') {Ab : FragS isaLSE2} {c0 : Ctl}
    (hG : G0 c0) {P : FragS isaLSE2} {pc' : Int64} {e : Expr} {env' : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hseg : SegWS W K p lbl ms P (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e env' lits cs bufs))
    (ih : ∀ c0', G0 c0' → SegWS W K p lbl ms
      (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0' fs pc' e env' lits cs bufs)
      (ExitC2 p lbl exe endPc R F fp ra tp c0' fs Ab)) :
    SegWS W K p lbl ms P (ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab) := by
  have ih' : ∀ g : {c0' // FrameRunM p (c0, fs) (c0', fs)},
      SegWS W K p lbl ms (LetAt p lbl lsize i cx exe endPc R F fp ra tp g.1 fs pc' e env' lits cs bufs)
        (ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab) := fun g =>
    (ih g.1 (hG0 _ _ hG g.2)).mono_post (ExitC2.trans g.2)
  refine (SegWS.seq_left (Q := fun s c fs' => fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
      At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0' pc' e (ofEnv2 env') lits cs bufs).withTp tp) s c) (E := Ab)
    hseg ((SegWS.exists_pre ih').mono_pre
      fun s c fs' ⟨he, c0', hrun, h⟩ => ⟨⟨c0', hrun⟩, h, he⟩)).mono_post fun s c fs' h => ?_
  rcases h with h | h
  · exact h
  · exact Or.inr h

/-- **A lowered `Accepted2` body is one segment at frames `fs`, from the
constructs' segments**: from the node at the body (`LetAt`: the lowering's
environment `env` grouped, `ofEnv2`; the walk's layouts `lits`, known
values `cs`, buffers `bufs`; the ghost `c0` in `G0`, closed under the
frame runs at `fs`, `hG0`) to the body's exits (`ExitC2`), given the
construct premises: plain calls (`CallC2`), lane stores (`LaneC`), buffer
allocations (`NewBufC`), output calls (`PrintCallC`), `+` (`AddC2`), `-`
(`SubC2`), the moves (`PureMv2`, `SplitMv2`, `UnpackMv2`), `if` (`IfC2`)
and `ret` (`RetC2`). The code: the open block's at `pc` (`CodeC2`), the
later blocks' at their labels (`BlocksCodeC2`); at each point of the
lowering's walk (`lowerEnvs2`) its immediates `i`'s, the point in `T`, a
`ret` of at most eight words (`RetOk`), the types (`EnvTy2`) and grouping
(`GrpL`); at each point of the literal walk (`litWalk2`) `LitPt` and the
calls' layouts (`CallLk`); the pairs paired (`countsB`); the lane stores in
range (`xchgsB`). The lowering's calls plain (`hfrm`). -/
theorem body2_segS_of {cx : FnCtx} {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} {fs : List TermRun.Frame}
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64}
    (hcall : CallC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hlane : LaneC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hprint : PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hadd : AddC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hsub : SubC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hpure : PureMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T)
    (hsplit : SplitMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T)
    (hunpack : UnpackMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T)
    (hif : IfC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T)
    (hret : RetC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res2) (kk : Nat) (pc : Int64)
      (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
      lowerC2 lcx env n l k e = some r → Fresh env n →
      CodeC2 cx Cd Bl kk pc r.insts r.term →
      BlocksCodeC2 cx Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ RetOk q ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits e, LitPt q ∧ CallLk lcx.prog q) →
      Scc.Lower.countsB lcx.prog cs bufs lits e = true → xchgsB cs bufs e = true →
      ∀ c0, G0 c0 → SegWS W K p lbl ms (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e env lits cs bufs)
        (ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab) := by
  -- the walk's facts at the head, and at a continuation from the walk's tail
  have hpt : ∀ {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat} {r : Res2}
      {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)},
      G0 c0 → lowerC2 lcx env n l k t = some r → Fresh env n →
      (∀ q ∈ lowerEnvs2 lcx env n t, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ RetOk q ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits t, LitPt q ∧ CallLk lcx.prog q) →
      Scc.Lower.countsB lcx.prog cs bufs lits t = true → PtF lcx G0 i T c0 t env n lits cs bufs := by
    intro c0 t env n l k r lits cs bufs hG hr hfr hW hL hC
    have hh := walk2_head hW
    refine ⟨hG, hh.2.1, hfr, (hL _ ?_).1, hh.2.2.2.1, hh.2.2.2.2.1, hC, hh.1,
      fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx t env n l k r hr y hy)⟩
    cases t <;> simp [Scc.Lower.litWalk2]
  have hcf : ∀ {e : Expr} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat} {r : Res2},
      lowerC2 lcx env n l k e = some r →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ RetOk q ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      ContF i e env n := by
    intro e env n l k r hr hW
    have hh := walk2_head hW
    exact ⟨fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx e env n l k r hr y hy), hh.1, hh.2.2.2.2.1,
      hh.2.2.2.1, hh.2.2.2.2.2⟩
  -- the literal walk and `countsB` past a `let`
  have hlitL : ∀ {lits : List (String × Scc.Lower.LitV)} {x : String} {op : Op} {e : Expr},
      (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits (.let_ x op e), LitPt q ∧ CallLk lcx.prog q) →
      ∀ q ∈ Scc.Lower.litWalk2 lcx.prog ((x, Scc.Lower.opLit lcx.prog lits op) :: lits) e,
        LitPt q ∧ CallLk lcx.prog q :=
    fun hL q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq)
  have hcntL : ∀ {cs bufs : List (String × Nat)} {lits : List (String × Scc.Lower.LitV)} {x : String} {op : Op}
      {e : Expr}, Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x op e) = true →
      Scc.Lower.countsB lcx.prog (Scc.Lower.csAfter x cs op) (Scc.Lower.bufsAfter x cs bufs op)
        ((x, Scc.Lower.opLit lcx.prog lits op) :: lits) e = true := by
    intro cs bufs lits x op e h
    simp only [Scc.Lower.countsB, Bool.and_eq_true] at h
    exact h.2
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    by_cases hp : isPure op = true
    · obtain ⟨t, ws, sc, hq, r', hpo, hm, hr', rfl⟩ := lowerC2_pure_inv hp hr
      have hW' := walk2_tail_pure hp hpo hm hW
      exact (ih _ n l k r' kk pc _ _ _ hr' (hfr.pure hpo x) hcode hbl hW' (hlitL hL) (hcntL hC)
        (xchgsB_tail hX) c0 hG).mono_pre
        (hpure c0 pc env n x op e t ws sc hq lits cs bufs hp hP (pairSmall_head hX) hpo hm (hcf hr' hW'))
    cases op with
    | add a b =>
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC2_add_inv hr
      obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
      have hW' := walk2_tail_add ha hb hW
      exact seg_cont hG0 hG (hadd c0 pc pc' kk env n x a b e ta tb pa pb lits cs bufs hP ha hb hi (hcf hr' hW'))
        fun c0' hG' => ih _ (n + 1) l (k + 1) r' _ pc' _ _ _ hr' (hfr.add x) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) c0' hG'
    | sub a b =>
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC2_sub_inv hr
      obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
      have hW' := walk2_tail_sub ha hb hW
      exact seg_cont hG0 hG (hsub c0 pc pc' kk env n x a b e ta tb pa pb lits cs bufs hP ha hb hi (hcf hr' hW'))
        fun c0' hG' => ih _ (n + 1) l (k + 1) r' _ pc' _ _ _ hr' (hfr.add x) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) c0' hG'
    | call g is a ts =>
      rcases lowerC2_call_inv hr with ⟨dg, t, w, r', hx, hdg, hrt, ha, hr', rfl⟩
          | ⟨xe, dg, t, b, o, m, cw, r', hx, hdg, hrt, ha, hr', rfl⟩
      · obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
        have hW' := walk2_tail_call hfrm hx hdg hrt ha hW
        have hF := hcf hr' hW'
        exact seg_cont hG0 hG (hcall c0 pc pc' kk env n x g is a ts e t w lits cs bufs hG hP.2.1 hfr hP.2.2.2.1
            hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC ⟨hx, dg, hdg, hrt⟩ ha hi hF.1 hF.2.1 hF.2.2.2.2
            ⟨l, k, _, hr, hcode, hbl,
            fun q hq =>
              ⟨(hW q hq).1, (hW q hq).2.1, (hW q hq).2.2.2.1, (hW q hq).2.2.2.2.1, (hW q hq).2.2.2.2.2⟩,
              fun q hq => ⟨(hL q hq).1, (hL q hq).2, trivial⟩, hC, hX⟩)
          fun c0' hG' => ih _ (n + 1) l (k + 1) r' _ pc' _ _ _ hr' (Fresh.callC1 hfr x) hrest hbl hW' (hlitL hL)
            (hcntL hC) (xchgsB_tail hX) c0' hG'
      · obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts _ kk pc).1 hcode
        have hW' := walk2_tail_print hx hdg hrt ha hW
        have hF := hcf hr' hW'
        exact seg_cont hG0 hG (hprint c0 pc pc' kk env n x g is a ts e xe dg t b o m cw lits cs bufs hG hP.2.1
            hfr hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC
            (by
              rw [← argShape_of_find hdg]
              exact (hL (.let_ x (.call g is a ts) e, lits) (by simp [Scc.Lower.litWalk2])).2 x g is a ts e rfl)
            hx hdg hrt ha hi hF.1 hF.2.1 hF.2.2.2.2)
          fun c0' hG' => ih _ (n + 4) l (k + 5) r' _ pc' _ _ _ hr' (hfr.print x) hrest hbl hW' (hlitL hL)
            (hcntL hC) (xchgsB_tail hX) c0' hG'
    | newBuf cn τ =>
      obtain ⟨tk, kv, en, em, h, sc, hq, r', ha, hc, hh, hw, hm, hr', rfl⟩ := lowerC2_newBuf_inv hr
      obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
      have hW' := walk2_tail_newBuf ha hc hh hw hm hW
      have hF := hcf hr' hW'
      exact seg_cont hG0 hG (hbuf c0 pc pc' kk env n x cn τ e tk kv en em h lits cs bufs hG hP.2.1 hfr
          hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC ha hc hh hw hi hF.1 hF.2.1 hF.2.2.2.2
          ⟨l, k, _, hr, hcode, hbl,
            fun q hq =>
              ⟨(hW q hq).1, (hW q hq).2.1, (hW q hq).2.2.2.1, (hW q hq).2.2.2.2.1, (hW q hq).2.2.2.2.2⟩,
            fun q hq => ⟨(hL q hq).1, (hL q hq).2, trivial⟩, hC, hX⟩)
        fun c0' hG' => ih _ (n + 1) l (k + 1) r' _ pc' _ _ _ hr' (hfr.newBuf x τ) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) c0' hG'
    | xchgAt b j v =>
      obtain ⟨t, bw, rb, o, tj, iv, μ, u, nu, mu, tv, w, s1, sc, hq, r', hb, hrf, hj, he, hg, hv, hs, hm, hr', rfl⟩ :=
        lowerC2_xchg_inv hr
      obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_, _] kk pc).1 hcode
      have hW' := walk2_tail_xchg hb hrf hj he hg hv hs hm hW
      have hF := hcf hr' hW'
      exact seg_cont hG0 hG (hlane c0 pc pc' kk env n x b j v e t bw rb o tj iv μ u nu mu tv w s1 lits cs bufs
          hG hP.2.1 hfr hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC (xchgB_of_ok hX) hb hrf hj he hg hv hs hi
          hF.1 hF.2.1 hF.2.2.2.2
          hP.2.2.2.2.2.2.2.2 hP.2.2.2.2.2.2.2.1 (walk2_head hW).2.2.2.2.2)
        fun c0' hG' => ih _ (n + 1) l (k + 2) r' _ pc' _ _ _ hr' (hfr.xchg x u) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) c0' hG'
    | _ => first | exact absurd rfl hp | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    obtain ⟨t, ws, u, w, nu, ha, hpr, hv, hr'⟩ := lowerC2_split_inv hr
    have hW' := walk2_tail_split ha hpr hv hW
    have hL' : ∀ q ∈ Scc.Lower.litWalk2 lcx.prog (match Scc.Lower.litAt lits a with
          | .node l r => (y, r) :: (x, l) :: lits
          | _ => (y, .leaf none) :: (x, .leaf none) :: lits) e, LitPt q ∧ CallLk lcx.prog q :=
      fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq)
    have hC' : Scc.Lower.countsB lcx.prog (Scc.Lower.unbuf y (Scc.Lower.unbuf x cs))
        (Scc.Lower.unbuf y (Scc.Lower.unbuf x bufs)) (match Scc.Lower.litAt lits a with
          | .node l r => (y, r) :: (x, l) :: lits
          | _ => (y, .leaf none) :: (x, .leaf none) :: lits) e = true := by
      simp only [Scc.Lower.countsB] at hC; exact hC
    exact (ih _ n l k r kk pc _ _ _ hr' (hfr.split ha x y u w nu) hcode hbl hW' hL' hC'
      (by simpa only [xchgsB] using hX) c0 hG).mono_pre
      (hsplit c0 pc env n a x y e t ws u w nu lits cs bufs hP ha hpr hv (hcf hr' hW'))
  | unpack a i' x e ih =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    obtain ⟨b, ws, ha, hr'⟩ := lowerC2_unpack_inv hr
    have hW' := walk2_tail_unpack ha hW
    have hL' : ∀ q ∈ Scc.Lower.litWalk2 lcx.prog ((x, Scc.Lower.litAt lits a) :: lits) e,
        LitPt q ∧ CallLk lcx.prog q :=
      fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq)
    have hC' : Scc.Lower.countsB lcx.prog (Scc.Lower.unbuf x (Scc.Lower.unbuf i' cs))
        (Scc.Lower.unbuf x (Scc.Lower.unbuf i' bufs)) ((x, Scc.Lower.litAt lits a) :: lits) e = true := by
      simp only [Scc.Lower.countsB] at hC; exact hC
    exact (ih _ n l k r kk pc _ _ _ hr' (hfr.unpack ha x) hcode hbl hW' hL' hC'
      (by simpa only [xchgsB] using hX) c0 hG).mono_pre
      (hunpack c0 pc env n a i' x e b ws lits cs bufs hP ha (hcf hr' hW'))
  | ifeq a b yes no ihy ihn =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    obtain ⟨ta, pa, tb, pb, ry, rn, ha, hb, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    have hmy : (⟨labName "then" n, ry.insts, ry.term⟩ : Scc.IR.Block) ∈
        ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
          ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks := by simp
    have hmn : (⟨labName "else" (n + 1), rn.insts, rn.term⟩ : Scc.IR.Block) ∈
        ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
          ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks := by simp
    obtain ⟨Ly, ky, hLy, hcy⟩ := hbl _ hmy (lowerC2_term_ne lcx _ _ _ _ _ _ hy)
    obtain ⟨Ln, kn, hLn, hcn⟩ := hbl _ hmn (lowerC2_term_ne lcx _ _ _ _ _ _ hn)
    have hnext := lowerC2_next_ge lcx yes env (n + 2) _ 0 ry hy
    simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC
    simp only [xchgsB, Bool.and_eq_true] at hX
    have segy := ihy env (n + 2) _ 0 ry ky _ lits cs bufs hy (hfr.mono (by omega)) hcy
      (fun b hb => hbl b (by simp [hb])) (walk2_tail_yes ha hb hW)
      (fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq)))
      hC.1 hX.1 c0 hG
    have segn := ihn env ry.next _ 0 rn kn _ lits cs bufs hn (hfr.mono (by omega)) hcn
      (fun b hb => hbl b (by simp [hb])) (walk2_tail_no hfrm ha hb hy hW)
      (fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq)))
      hC.2 hX.2 c0 hG
    exact (hif c0 pc kk env n a b yes no ta tb pa pb lits cs bufs hP ha hb hcode Ly Ln hLy hLn).seq
      (SegWS.or_pre segy segn)
  | ret a =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    obtain ⟨t, ws, ha, rfl⟩ := lowerC2_ret_inv hr
    exact hret c0 pc kk env n a t ws lits cs bufs hP (walk2_head hW).2.2.1 ha hcode
  | _ => intro env n l k r kk pc lits cs bufs hr; simp [lowerC2] at hr

end Body2Seg

end Spike.Lib.LowerA64
