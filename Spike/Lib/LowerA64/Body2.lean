/-
**A lowered `Accepted2` body is one segment at the caller's frames**
(AArch64): the premises of `body2_segS`, the `Accepted2` twin of
`Spike/Lib/LowerA64/BodyC.lean`'s `bodyC_segS` (the statement and its proof
to come), the twin of the x86-64 `Spike/Lib/LowerX64/Body2.lean`.

- `RetOk`, `ExitC2`: `RetOne` and `ExitC` for a `ret` of any number of
  words (at most the argument registers), at `retN2`
  (`Spike/Lib/LowerA64/Node2.lean`; `ExitC.toC2`, `ExitC2.trans`).
- `ContC`, `LetAt`: a construct's exit and entry at `bodyN2`, the
  environment grouped (`ofEnv2`), with the walk's layouts, known values and
  buffers.
- `CallC2`, `NewBufC`, `LaneC`, `PrintCallC`: `CallC`'s shape at `bodyN2`
  for a user call, `newBuf`'s call of `scc_rt_alloc`, `xchg b[i] v`'s load
  and store and the output extern's block (`printInsts`): from the node at
  the `let` (the construct's code first, `InstsC2`, from `pc` to `pc'`) to
  the node at the continuation at `pc'` with the walk's next layouts
  (`opLit`), known values (`csAfter`) and buffers (`bufsAfter`), the ghost
  re-anchored by a frame run; or to an abort (`Ab`). Each takes the closed
  form's data (`lowerC2_call_inv`, `lowerC2_newBuf_inv`, `lowerC2_xchg_inv`)
  and the walk's facts at the `let` (`Fresh`, `LitPt`, `EnvTy2`, `countsB`)
  as premises.
-/
import Spike.Lib.LowerA64.BodyC
import Spike.Lib.LowerA64.BlocksC2Code
import Spike.Lib.Src.LowerEnvImm2Of
import Spike.Lib.LowerA64.Node2
import Spike.Lib.FrameRunM
import Spike.Lib.Src.XchgB

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (newBufCall newBufTy unitsOf countsO refO slotAddr xchgLoad xchgStore printInsts)
open Scc.Lower.Inv (atomV regName)

/-! ## A `ret` of any number of words -/

/-- **A `ret` of at most the argument registers' words**: at a point of
the walk at `ret a`, `a`'s words fit `x0`–`x7`, each word one source word
(`group` places them one by one, no locative), as the return's exit
(`RetJ2`) puts word `j` in argument register `j`. -/
def RetOk (q : Expr × Scc.Lower.Env × Nat) : Prop :=
  ∀ a, q.1 = .ret a → ∃ t ws, atomV q.2.1 a = some (t, ws) ∧ ws.length ≤ argRegs.length ∧
    Spike.Lib.Form.group t ws = some (ws.map .one)

/-- **A `ret` of one word, placed as one, is of at most the argument
registers' words.** -/
theorem RetOne.toOk {q : Expr × Scc.Lower.Env × Nat} (h : RetOne q)
    (hg : ∀ a t w, q.1 = .ret a → atomV q.2.1 a = some (t, [w]) → Spike.Lib.Form.group t [w] = some [.one w]) :
    RetOk q := fun a ha => by
  obtain ⟨t, w, hw⟩ := h a ha
  exact ⟨t, [w], hw, by simp only [List.length_singleton]; decide, hg a t w ha hw⟩

section Body2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

/-- **The body's exits at the frames `fs`** for `ret`s of any number of
words: `ExitC` at `retN2`. -/
def ExitC2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (Ab : FragS isaLSE2) : FragS isaLSE2 := fun s c fs' =>
  (fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧ At exe endPc R F ((retN2 p lbl fp ra c0').withTp tp) s c) ∨
    Ab s c fs'

/-- **`ExitC` is an `ExitC2`.** -/
theorem ExitC.toC2 {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame} {Ab : FragS isaLSE2}
    {s : State} {c : Ctl} {fs' : List TermRun.Frame} (h : ExitC p lbl exe endPc R F fp ra tp c0 fs Ab s c fs') :
    ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' := by
  rcases h with ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, ⟨hJ, hL⟩, htp⟩ | h
  · exact .inl ⟨e, c0', hr.toM, he, hn, hd, hpc, σ, hA, hFm, ⟨hJ.toJ2, hL⟩, htp⟩
  · exact .inr h

/-- **`ExitC2` re-anchored by a frame run** of the ghost. -/
theorem ExitC2.trans {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {fs : List TermRun.Frame}
    {Ab : FragS isaLSE2} (hr : FrameRunM p (c0, fs) (c0', fs)) :
    ∀ s c fs', ExitC2 p lbl exe endPc R F fp ra tp c0' fs Ab s c fs' →
      ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' :=
  fun _ _ _ h => h.imp_left fun ⟨e, c1, hr', h⟩ => ⟨e, c1, hr.trans hr', h⟩

/-- **The exit of a construct's segment** at the frames `fs` (immediates
table `i`): the node at `e` at `pc'` in `env'` (grouped, `ofEnv2`) with the
walk's next layouts, known values and buffers, the ghost `c0` run to `c0'`
at `fs`; or an abort. -/
def ContC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat)
    (cx : FnCtx) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame) (Ab : FragS isaLSE2) (pc' : Int64)
    (e : Expr) (env' : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) :
    FragS isaLSE2 := fun s c fs' =>
  (fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
    At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0' pc' e (ofEnv2 env') lits cs bufs).withTp tp) s c) ∨ Ab s c fs'

/-- **The node at a `let` of an `Accepted2` body** (`bodyN2` at `ofEnv2`,
the thread pointer `tp`, at the frames `fs`). -/
abbrev LetAt (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat)
    (cx : FnCtx) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame) (pc : Int64) (t : Expr)
    (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) : FragS isaLSE2 :=
  (At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0 pc t (ofEnv2 env) lits cs bufs).withTp tp)).at fs

/-! ## The constructs' segments

Each is a premise of the body's induction in `CallC`'s shape: from the node
at `let x = op in e` (the construct's instructions first in the code, from
`pc` numbered `kk` to `pc'`, `InstsC2`; the ghost `c0` in `G0`, the term in
`T`, the walk's facts at the `let`) to `ContC` at `e` with `x` bound, the
walk's next layouts (`opLit`), known values (`csAfter`) and buffers
(`bufsAfter`). -/

/-- **A plain call's resumption facts** at the `let` `t` at `pc` (label
counter `kk`): its closed form from `env` and counter `n` with its code and
its later blocks' (labels at `lab`), the lowering walk's facts (immediates
`i`, the term in `T`, types, grouping, register bases), the literal walk's
(`LitPt`, the calls' layouts `CallLk`, `Lk`), the pairs' counts and the
lane stores' range at the known values `cs` and buffers `bufs`. The data a
suspended caller resumes from (`BodyPtW`). -/
def PtC2 (lcx : Scc.Lower.Ctx) (cx : FnCtx) (Cd : Int64 → List Directive → Prop)
    (Bl : Int64 → Label → Nat → Prop) (lab : Label → Int64) (i : Expr → String → Nat → Option Nat)
    (T : Expr → Prop) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) (kk : Nat) (pc : Int64)
    (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
    (t : Expr) : Prop :=
  ∃ l k r, Spike.Lib.LowerShape.lowerC2 lcx env n l k t = some r ∧ CodeC2 cx Cd Bl kk pc r.insts r.term ∧
    BlocksCodeC2 cx Cd Bl lab r.blocks ∧
    (∀ q ∈ lowerEnvs2 lcx env n t, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
      LocBaseRegAt (ofEnv2 q.2.1) q.1) ∧
    (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits t, LitPt q ∧ CallLk lcx.prog q ∧ Lk q) ∧
    Scc.Lower.countsB lcx.prog cs bufs lits t = true ∧ xchgsB cs bufs t = true

/-- **A plain call** `let x = g(a)` (`CallC` at `bodyN2`): `call [r%n] g [w]`;
the call's resumption facts at the `let` (`PtC2`, the literal walk's facts
with `Lk`). -/
def CallC2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
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
      (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e ((x, .int, [.reg (regName "r" n)]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
        (Scc.Lower.bufsAfter x cs bufs (.call g is a ts)))

/-- **A lane store** `let x = xchg b[j] v`: the load of the slot into `x%n`
and the store of `v`'s word `w` (`lowerC2_xchg_inv`'s data); the walk's
facts at the continuation and at the `let` itself (free variables placed,
immediates, register bases). -/
def LaneC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2) (K : State → State → Prop)
    (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64) (fs : List TermRun.Frame)
    (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Ab : FragS isaLSE2) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (b j v : At) (e : Expr)
    (t : Ty) (bw : List Scc.IR.Operand) (rb : Scc.IR.Reg) (o : UInt64) (tj : Ty) (iv : UInt64) (μ : Mode) (u : Ty)
    (nu mu : Nat) (tv : Ty) (w : Scc.IR.Operand) (s1 : Bool × Nat) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    G0 c0 → T (.let_ x (.xchgAt b j v) e) → Fresh env n →
    LitPt (.let_ x (.xchgAt b j v) e, lits) → EnvTy2 (.let_ x (.xchgAt b j v) e, env, n) → GrpL env →
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.xchgAt b j v) e) = true →
    XchgB bufs b j →
    atomV env b = some (t, bw) → refO bw = some (.reg rb, .imm o) → atomV env j = some (tj, [.imm iv]) →
    Scc.Lower.bufElem t = some (μ, u) → Scc.Obj.regOf u = some (nu, mu) → atomV env v = some (tv, [w]) →
    Scc.Obj.slots u 0 0 = some [s1] →
    InstsC2 cx Cd Bl kk pc
      [xchgLoad (regName x n) (slotAddr lcx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1),
       xchgStore (slotAddr lcx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1) w] pc' →
    (∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, u, [.reg (regName x n)]) :: env)) y).isSome) →
    ImmIn i (ofEnv2 ((x, u, [.reg (regName x n)]) :: env)) e →
    LocBaseRegAt (ofEnv2 ((x, u, [.reg (regName x n)]) :: env)) e →
    (∀ y ∈ Scc.Sem.exprFv (.let_ x (.xchgAt b j v) e), (lookupS (ofEnv2 env) y).isSome) →
    ImmIn i (ofEnv2 env) (.let_ x (.xchgAt b j v) e) → LocBaseRegAt (ofEnv2 env) (.let_ x (.xchgAt b j v) e) →
    SegWS W K p lbl ms
      (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.xchgAt b j v) e) env lits cs bufs)
      (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e ((x, u, [.reg (regName x n)]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.xchgAt b j v)) :: lits) (Scc.Lower.csAfter x cs (.xchgAt b j v))
        (Scc.Lower.bufsAfter x cs bufs (.xchgAt b j v)))

/-- **A buffer allocation** `let x = newBuf[τ] cn`: the allocator's call
into `x%n` (`newBufCall`, `lowerC2_newBuf_inv`'s data), the buffer's words
`[x%n, 0]` (`newBufTy τ`); the allocation's resumption facts at the `let`
(`PtC2`, the literal walk's facts with `Lk`: the allocator's landing packs
the allocating frame's resumption point, `landStk_hxa`). -/
def NewBufC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2) (K : State → State → Prop)
    (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64) (fs : List TermRun.Frame)
    (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Ab : FragS isaLSE2)
    (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (cn : At) (τ : Ty)
    (e : Expr) (tk : Ty) (kv : UInt64) (en em h : Nat) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    G0 c0 → T (.let_ x (.newBuf cn τ) e) → Fresh env n →
    LitPt (.let_ x (.newBuf cn τ) e, lits) → EnvTy2 (.let_ x (.newBuf cn τ) e, env, n) → GrpL env →
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.newBuf cn τ) e) = true →
    atomV env cn = some (tk, [.imm kv]) → countsO lcx.obj τ = some (en, em) →
    Scc.Obj.header0 lcx.obj .array en em = some h → en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em) →
    InstsC2 cx Cd Bl kk pc [newBufCall (regName x n) h kv (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)]
      pc' →
    (∀ y ∈ Scc.Sem.exprFv e,
      (lookupS (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome) →
    ImmIn i (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e →
    LocBaseRegAt (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e →
    PtC2 lcx cx Cd Bl (_root_.Executable.labels exe).label i T Lk kk pc env n lits cs bufs
      (.let_ x (.newBuf cn τ) e) →
    SegWS W K p lbl ms
      (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.newBuf cn τ) e) env lits cs bufs)
      (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e
        ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
        (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ)))

/-- **An output call** `let x = g(a)`, `g` an extern returning `Unit`:
`printInsts` from counter `n` (`lowerC2_call_inv`'s second case; `a`'s
words a slice `[b, o, m, cw]`, its offset word `o` a register, its layout
erased `g`'s parameter's, `callsOk2`), `x` of no words. -/
def PrintCallC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
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
      (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 fs Ab pc' e ((x, .unit, []) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
        (Scc.Lower.bufsAfter x cs bufs (.call g is a ts)))

end Body2

end Spike.Lib.LowerA64
