/-
**A compiled block's body segment from any of its resumption points**
(AArch64): `BodyAt2` (`Spike/Lib/LowerA64/ProgC2.lean`) generalised from the
body's entry node to any point of the body's lowering walk at which the
code facts hold (`BodyPt`), so that a body suspended at a call or a buffer
allocation resumes as one segment to its exits (`ExitC2SL`).

- `BodyPt`: a resumption point of compiled block `c` at return address
  `ra`: the term `t`'s closed form from `env` and counter `n` (fresh), its
  code at `pc` and its later blocks', its lowering and literal walks inside
  the body's (so `c`'s walk facts hold at it), its pairs' counts and lane
  stores' range.
- `BodyPtW`: a resumption point with `c`'s walk facts at its walks stated
  directly (in place of the inclusions); `BodyPt.toW`.
- `bodyPt_entry`, `bodyPtW_entry`: the body's entry is one.
- `BodyPt.call`, `BodyPt.newBuf`: past a plain call / a buffer allocation,
  `CallC2`'s / `NewBufC`'s premise data at the point and the continuation a
  resumption point at their `ContC` arguments; `BodyPtW.call`,
  `BodyPtW.newBuf` at `BodyPtW`.
- `bodyAtPt2`: the body's segment from any resumption point
  (`body2_segS_ofSL` at `t`); `bodyAtPt2W` from a `BodyPtW`.
-/
import Spike.Lib.LowerA64.ProgC2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC2 Res2 lowerC2_call_inv lowerC2_newBuf_inv walk2_tail_call walk2_tail_newBuf
  newBufCall newBufTy unitsOf countsO)
open Scc.Lower.Inv (atomV regName)

section BodyPt2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
  {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}

/-- **A resumption point of compiled block `c` at return address `ra`**:
the term `t` at `pc` from the environment `env` and counter `n` (fresh),
with its closed form `r`'s code at `pc` (label counter `kk`) and its later
blocks', its lowering and literal walks (from `lits`) inside the body's,
its pairs' counts and lane stores' range at the known values `cs` and
buffers `bufs`. -/
def BodyPt (c : FnCode2 exe prog endPc RaOk Cd i T d) (ra : BitVec 64) (pc : Int64) (t : Expr)
    (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) :
    Prop :=
  ∃ l k r kk, lowerC2 c.lcx env n l k t = some r ∧ Fresh env n ∧
    CodeC2 c.cx (Cd ra) (c.Bl ra) kk pc r.insts r.term ∧
    BlocksCodeC2 c.cx (Cd ra) (c.Bl ra) (_root_.Executable.labels exe).label r.blocks ∧
    (∀ q ∈ lowerEnvs2 c.lcx env n t, q ∈ lowerEnvs2 c.lcx c.env 0 d.body) ∧
    (∀ q ∈ Scc.Lower.litWalk2 c.lcx.prog lits t, q ∈ Scc.Lower.litWalk2 c.lcx.prog c.lits d.body) ∧
    Scc.Lower.countsB c.lcx.prog cs bufs lits t = true ∧ xchgsB cs bufs t = true

/-- **A resumption point with the walk facts stated directly** (`BodyPt`
with its lowering and literal walks' inclusions in the body's replaced by
the facts `c` gives there: `FnCode2.hWk`'s at the lowering walk, `hlit`,
`hcallL`, `hretL` (`RetLk`) at the literal walk). -/
def BodyPtW (c : FnCode2 exe prog endPc RaOk Cd i T d) (ra : BitVec 64) (pc : Int64) (t : Expr)
    (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) :
    Prop :=
  ∃ l k r kk, lowerC2 c.lcx env n l k t = some r ∧ Fresh env n ∧
    CodeC2 c.cx (Cd ra) (c.Bl ra) kk pc r.insts r.term ∧
    BlocksCodeC2 c.cx (Cd ra) (c.Bl ra) (_root_.Executable.labels exe).label r.blocks ∧
    (∀ q ∈ lowerEnvs2 c.lcx env n t, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
      LocBaseRegAt (ofEnv2 q.2.1) q.1) ∧
    (∀ q ∈ Scc.Lower.litWalk2 c.lcx.prog lits t, LitPt q ∧ CallLk c.lcx.prog q ∧ RetLk d.retTy q) ∧
    Scc.Lower.countsB c.lcx.prog cs bufs lits t = true ∧ xchgsB cs bufs t = true

omit [Kraken.Executable.ValidLayout exe] in
/-- **The body's entry is a resumption point** (at a return address of
`RaOk`). -/
theorem bodyPt_entry (c : FnCode2 exe prog endPc RaOk Cd i T d) {ra : BitVec 64} (hra : RaOk ra) :
    BodyPt c ra ((_root_.Executable.labels exe).label c.entry) d.body c.env 0 c.lits [] [] :=
  ⟨"entry", 0, c.r, 0, c.hr, c.hfr, c.hcode ra hra, c.hbl ra hra, fun _ h => h, fun _ h => h, c.hcnt, c.hxchg⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **Past a plain call**: at a resumption point at `let x = g(a)`, `g` no
extern, the callee `dg` of return type `int`, `a` one word `w`, the call's
code from `pc` to `pc'` (`CallC2`'s premises), and the continuation `e` a
resumption point at `pc'` at `CallC2`'s `ContC` arguments (counter
`n + 1`). -/
theorem BodyPt.call {c : FnCode2 exe prog endPc RaOk Cd i T d} {ra : BitVec 64} {pc : Int64} {x g : String}
    {is : List String} {a : At} {ts : List Ty} {e : Expr} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (h : BodyPt c ra pc (.let_ x (.call g is a ts) e) env n lits cs bufs)
    (hx : c.lcx.externs.find? (·.1 == g) = none) :
    ∃ (dg : Decl) (t : Ty) (w : Scc.IR.Operand) (kk : Nat) (pc' : Int64),
      c.lcx.prog.find? (·.name == g) = some dg ∧ dg.retTy = .int ∧ atomV env a = some (t, [w]) ∧
      InstsC2 c.cx (Cd ra) (c.Bl ra) kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] pc' ∧
      BodyPt c ra pc' e ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1)
        ((x, Scc.Lower.opLit c.lcx.prog lits (.call g is a ts)) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
        (Scc.Lower.bufsAfter x cs bufs (.call g is a ts)) := by
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := h
  rcases lowerC2_call_inv hr with ⟨dg, t, w, r', -, hdg, hrt, ha, hr', rfl⟩
      | ⟨xe, -, -, -, -, -, -, r', hx', -⟩
  · obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
    simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC
    exact ⟨dg, t, w, kk, pc', hdg, hrt, ha, hi, l, k + 1, r', _, hr', Fresh.callC1 hfr x, hrest, hbl,
      walk2_tail_call c.hfrm hx hdg hrt ha hWs,
      fun q hq => hLs q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq), hC.2,
      xchgsB_tail hX⟩
  · rw [hx] at hx'; cases hx'

omit [Kraken.Executable.ValidLayout exe] in
/-- **Past a buffer allocation**: at a resumption point at
`let x = newBuf[τ] cn`, `NewBufC`'s premise data (`cn`'s immediate `kv`,
the counts, the header, the words' bound, the allocator call's code from
`pc` to `pc'`), and the continuation `e` a resumption point at `pc'` at
`NewBufC`'s `ContC` arguments (counter `n + 1`). -/
theorem BodyPt.newBuf {c : FnCode2 exe prog endPc RaOk Cd i T d} {ra : BitVec 64} {pc : Int64} {x : String}
    {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (h : BodyPt c ra pc (.let_ x (.newBuf cn τ) e) env n lits cs bufs) :
    ∃ (tk : Ty) (kv : UInt64) (en em hh kk : Nat) (pc' : Int64),
      atomV env cn = some (tk, [.imm kv]) ∧ countsO c.lcx.obj τ = some (en, em) ∧
      Scc.Obj.header0 c.lcx.obj .array en em = some hh ∧ en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em) ∧
      InstsC2 c.cx (Cd ra) (c.Bl ra) kk pc
        [newBufCall (regName x n) hh kv (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)] pc' ∧
      BodyPt c ra pc' e ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env) (n + 1)
        ((x, Scc.Lower.opLit c.lcx.prog lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
        (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ)) := by
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := h
  obtain ⟨tk, kv, en, em, hh, sc, hq, r', ha, hc, hhd, hw, hm, hr', rfl⟩ := lowerC2_newBuf_inv hr
  obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
  simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC
  exact ⟨tk, kv, en, em, hh, kk, pc', ha, hc, hhd, hw, hi, l, k + 1, r', _, hr', hfr.newBuf x τ, hrest, hbl,
    walk2_tail_newBuf ha hc hhd hw hm hWs,
    fun q hq => hLs q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq), hC.2,
    xchgsB_tail hX⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **A compiled block's body segment from any resumption point**
(`BodyAt2` at a `BodyPt`): from the node at the point (`LetAt`) at the
frames `fs` (any ghost `c0` in `G0`, the thread pointer `tp`), given
`BodyAt2`'s premises at `ra` and the context's construct premises
(`bodySpecC2_of`'s `hcon` at the context), to the body's exits by
placements with `RetL` at its return type (`ExitC2SL`). `c`'s walk facts
hold at the point's walks (`BodyPt`'s inclusions). -/
theorem bodyAtPt2 (c : FnCode2 exe prog endPc RaOk Cd i T d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    {W₀ : Frag isaLSE2} {c0 : Ctl} (hra : RaOk ra)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(c.cx.frame : Int))
    (hhi : 0 ≤ R.hi) (hW₀ : ∀ s c, W₀ s c → W s c fs)
    (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs k) blk)
    (hab : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN2 i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs)
    (hcon : CallC2 p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      LaneC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab ∧
      NewBufC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      PrintCallC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    {pc : Int64} {t : Expr} {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} (hpt : BodyPt c ra pc t env n lits cs bufs) (hg0 : G0 c0) :
    SegWS W K p lbl ms (LetAt p lbl lsize i c.cx exe endPc R F fp ra tp c0 fs pc t env lits cs bufs)
      (ExitC2SL p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab) := by
  obtain ⟨hcall, hlane, hbuf, hprint⟩ := hcon
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := hpt
  have hCd := c.hCd ra hra
  exact body2_segS_ofSL c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hG0 hW c.hfrm d.retTy hcall hlane hbuf hprint
    (addC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW hWp hab c.lcx tp)
    (subC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW hWp c.lcx tp)
    (pureMv2_of c.lcx tp) (splitMv2_of c.lcx tp) (unpackMv2_of c.lcx tp)
    (ifC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW c.lcx tp)
    t env n l k r kk pc lits cs bufs hr hfr hcode hbl (fun q hq => c.hWk q (hWs q hq))
    (fun q hq => ⟨c.hlit q (hLs q hq), c.hcallL q (hLs q hq)⟩) (fun a lits' hq => c.hretL a lits' (hLs _ hq))
    hC hX c0 hg0

omit [Kraken.Executable.ValidLayout exe] in
/-- **A resumption point has the walk facts** (`BodyPt` to `BodyPtW`): `c`'s
walk facts (`hWk`, `hlit`, `hcallL`, `hretL`) at the point's walks through
their inclusions in the body's. -/
theorem BodyPt.toW {c : FnCode2 exe prog endPc RaOk Cd i T d} {ra : BitVec 64} {pc : Int64} {t : Expr}
    {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (h : BodyPt c ra pc t env n lits cs bufs) : BodyPtW c ra pc t env n lits cs bufs := by
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := h
  refine ⟨l, k, r, kk, hr, hfr, hcode, hbl, fun q hq => c.hWk q (hWs q hq),
    fun q hq => ⟨c.hlit q (hLs q hq), c.hcallL q (hLs q hq), fun a ha => ?_⟩, hC, hX⟩
  obtain ⟨q1, q2⟩ := q
  cases ha
  exact c.hretL a q2 (hLs _ hq)

omit [Kraken.Executable.ValidLayout exe] in
/-- **The body's entry is a resumption point with the walk facts**
(`bodyPt_entry`, `BodyPt.toW`). -/
theorem bodyPtW_entry (c : FnCode2 exe prog endPc RaOk Cd i T d) {ra : BitVec 64} (hra : RaOk ra) :
    BodyPtW c ra ((_root_.Executable.labels exe).label c.entry) d.body c.env 0 c.lits [] [] :=
  (bodyPt_entry c hra).toW

omit [Kraken.Executable.ValidLayout exe] in
/-- **Past a plain call** at a `BodyPtW` (`BodyPt.call`): the walk facts
pass to the continuation's walks (`walk2_tail_call`, the literal walk's
tail). -/
theorem BodyPtW.call {c : FnCode2 exe prog endPc RaOk Cd i T d} {ra : BitVec 64} {pc : Int64} {x g : String}
    {is : List String} {a : At} {ts : List Ty} {e : Expr} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (h : BodyPtW c ra pc (.let_ x (.call g is a ts) e) env n lits cs bufs)
    (hx : c.lcx.externs.find? (·.1 == g) = none) :
    ∃ (dg : Decl) (t : Ty) (w : Scc.IR.Operand) (kk : Nat) (pc' : Int64),
      c.lcx.prog.find? (·.name == g) = some dg ∧ dg.retTy = .int ∧ atomV env a = some (t, [w]) ∧
      InstsC2 c.cx (Cd ra) (c.Bl ra) kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] pc' ∧
      BodyPtW c ra pc' e ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1)
        ((x, Scc.Lower.opLit c.lcx.prog lits (.call g is a ts)) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
        (Scc.Lower.bufsAfter x cs bufs (.call g is a ts)) := by
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := h
  rcases lowerC2_call_inv hr with ⟨dg, t, w, r', -, hdg, hrt, ha, hr', rfl⟩
      | ⟨xe, -, -, -, -, -, -, r', hx', -⟩
  · obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
    simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC
    exact ⟨dg, t, w, kk, pc', hdg, hrt, ha, hi, l, k + 1, r', _, hr', Fresh.callC1 hfr x, hrest, hbl,
      walk2_tail_call c.hfrm hx hdg hrt ha hWs,
      fun q hq => hLs q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq), hC.2,
      xchgsB_tail hX⟩
  · rw [hx] at hx'; cases hx'

omit [Kraken.Executable.ValidLayout exe] in
/-- **Past a buffer allocation** at a `BodyPtW` (`BodyPt.newBuf`): the
walk facts pass to the continuation's walks (`walk2_tail_newBuf`, the
literal walk's tail). -/
theorem BodyPtW.newBuf {c : FnCode2 exe prog endPc RaOk Cd i T d} {ra : BitVec 64} {pc : Int64} {x : String}
    {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (h : BodyPtW c ra pc (.let_ x (.newBuf cn τ) e) env n lits cs bufs) :
    ∃ (tk : Ty) (kv : UInt64) (en em hh kk : Nat) (pc' : Int64),
      atomV env cn = some (tk, [.imm kv]) ∧ countsO c.lcx.obj τ = some (en, em) ∧
      Scc.Obj.header0 c.lcx.obj .array en em = some hh ∧ en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em) ∧
      InstsC2 c.cx (Cd ra) (c.Bl ra) kk pc
        [newBufCall (regName x n) hh kv (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)] pc' ∧
      BodyPtW c ra pc' e ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env) (n + 1)
        ((x, Scc.Lower.opLit c.lcx.prog lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
        (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ)) := by
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := h
  obtain ⟨tk, kv, en, em, hh, sc, hq, r', ha, hc, hhd, hw, hm, hr', rfl⟩ := lowerC2_newBuf_inv hr
  obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
  simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC
  exact ⟨tk, kv, en, em, hh, kk, pc', ha, hc, hhd, hw, hi, l, k + 1, r', _, hr', hfr.newBuf x τ, hrest, hbl,
    walk2_tail_newBuf ha hc hhd hw hm hWs,
    fun q hq => hLs q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq), hC.2,
    xchgsB_tail hX⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **A compiled block's body segment from any `BodyPtW`** (`bodyAtPt2`
with the walk facts given directly to `body2_segS_ofSL`; `RetLk` is its
`hretL` argument). -/
theorem bodyAtPt2W (c : FnCode2 exe prog endPc RaOk Cd i T d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    {W₀ : Frag isaLSE2} {c0 : Ctl} (hra : RaOk ra)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(c.cx.frame : Int))
    (hhi : 0 ≤ R.hi) (hW₀ : ∀ s c, W₀ s c → W s c fs)
    (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs k) blk)
    (hab : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN2 i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs)
    (hcon : CallC2 p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      LaneC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab ∧
      NewBufC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      PrintCallC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    {pc : Int64} {t : Expr} {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} (hpt : BodyPtW c ra pc t env n lits cs bufs) (hg0 : G0 c0) :
    SegWS W K p lbl ms (LetAt p lbl lsize i c.cx exe endPc R F fp ra tp c0 fs pc t env lits cs bufs)
      (ExitC2SL p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab) := by
  obtain ⟨hcall, hlane, hbuf, hprint⟩ := hcon
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := hpt
  have hCd := c.hCd ra hra
  exact body2_segS_ofSL c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hG0 hW c.hfrm d.retTy hcall hlane hbuf hprint
    (addC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW hWp hab c.lcx tp)
    (subC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW hWp c.lcx tp)
    (pureMv2_of c.lcx tp) (splitMv2_of c.lcx tp) (unpackMv2_of c.lcx tp)
    (ifC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW c.lcx tp)
    t env n l k r kk pc lits cs bufs hr hfr hcode hbl hWs
    (fun q hq => ⟨(hLs q hq).1, (hLs q hq).2.1⟩) (fun a lits' hq => (hLs _ hq).2.2 a rfl)
    hC hX c0 hg0

end BodyPt2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.BodyPt.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BodyPt.call

/-- info: 'Spike.Lib.LowerA64.BodyPt.newBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BodyPt.newBuf

/-- info: 'Spike.Lib.LowerA64.bodyAtPt2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bodyAtPt2

/-- info: 'Spike.Lib.LowerA64.BodyPt.toW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BodyPt.toW

/-- info: 'Spike.Lib.LowerA64.bodyPtW_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bodyPtW_entry

/-- info: 'Spike.Lib.LowerA64.BodyPtW.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BodyPtW.call

/-- info: 'Spike.Lib.LowerA64.BodyPtW.newBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BodyPtW.newBuf

/-- info: 'Spike.Lib.LowerA64.bodyAtPt2W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bodyAtPt2W

end Spike.Lib.LowerA64
