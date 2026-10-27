/-
**The plain call of an `Accepted2` body** (AArch64): the construct
obligation `CallC2` (`Body2.lean`) at the node with buffers and slices
(`bodyN2`), from the call's code, its blocks inside the frame's fragment
and the callee's segment; `CallC.lean`'s `callC_of` at `NJB`. The twin of
`Spike/Lib/LowerX64/CallC2.lean`.

`callC_of`'s nodes ask every bound word to be a number (`EnvNum`), which a
buffer's locative or a slice is not. The nodes here carry the caller's
facts against the walk (`EnvQ`: `EnvLit`, `EnvB`, `MemB`) instead, and the
callee's frame condition the caller's (`CalleeF2`). The argument is a
number below `2^64`: its one operand is one placement (`GrpL`,
`sevalAt_ofEnv2_one`), so its layout is a leaf (`NJB.litMask_one`). The
result is a number below `2^64` by the callee's exit (`RetL`, `retNB`).
At the landing node the source control is placed in the slots
(`SlotRepAt.of_nodeJE`).

- `csN2`, `retCN2`, `exN2`, `CalleeF2`: the nodes and the callee's frame
  condition (`bl` keeps the frame's offsets, so one call-site node shape
  serves before and after it, as `csN`);
- `CallSite2`: the call site's data handed to the callee's segment (`hcal`);
- `CallerAt2`, `CallSite2F`, `CallSite2F.toCallSite2`: the caller pinned at
  the call site's data, for its resumption (`Resume2.lean`), and the call
  site with it;
- `instsC2_call`: `InstsC2`'s plain-call arm;
- `argC_seg2`, `blC_seg2`, `calleeC_seg2`, `resC_seg2`: the argument's
  load, `bl g`, the callee, the result's store (`calleeC_seg2G`: the
  callee's segment given the pinned caller);
- `callC2_of`, `callC2_ofF` (the callee's segment from `CallSite2F`).
-/
import Spike.Lib.LowerA64.CallC
import Spike.Lib.LowerA64.RetNB
import Spike.Lib.Src.GroupOpds

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv sevalAt lookupS WordPl SRep opdVal_upd)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Spike.Lib.A64.Flow.Ret0 (CallerCells setXReg_TPIDR)
open Scc.Lower.Inv (regName labName atomV)
open Spike.Lib.LowerCall (Callee)

set_option linter.unusedSimpArgs false

/-! ## The nodes -/

/-- **A node of a call of an `Accepted2` body** at `pc` (`csN` at `Q` for
`EnvNum`): the source exactly at `t`, the facts `Q` of its control (the
caller's against the walk, `EnvQ`), the saved pair, the source control in
`Rn`, the thread pointer `tp`, the call's own facts `P`. -/
def csN2 (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx) (fp ra : BitVec 64) (tp : UInt64)
    (Q Rn : Ctl → Prop) (pc : Int64) (t : Expr) (s : SEnv) (P : AS → Prop) : ND :=
  ⟨pc, oF cx, fun σ c => NodeJE lbl (rsOf cx) t s σ.slot c ∧ Q c ∧ FrJ fp ra σ.slot ∧ Rn c ∧
    σ.regs.TPIDR_EL0 = tp ∧ P σ⟩

/-- **Back from the callee** (`retCN` at `Q`). -/
def retCN2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx) (fp ra : BitVec 64) (tp : UInt64)
    (c0 : Ctl) (fs : List TermRun.Frame) (Q : Ctl → Prop) (pc : Int64) (e : Expr) (s : SEnv) (off : Int) : ND :=
  ⟨pc, oF cx, fun σ c => NodeJE lbl (rsOf cx) e s (upd σ.slot off σ.regs.X0.toBitVec) c ∧ Q c ∧
    FrJ fp ra σ.slot ∧ FrameRunM p (c0, fs) (c, fs) ∧ σ.regs.TPIDR_EL0 = tp⟩

/-- **The callee's exit** (`exN` at `retNB`, the frame's type). -/
def exN2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (tp : UInt64) (fs : List TermRun.Frame) (q : CallG)
    (frm : TermRun.Frame) (c0' : Ctl) : ND :=
  ⟨Int64.ofBitVec q.ra, ⟨0, []⟩, fun σ c => FrameRunM p (q.cE, frm :: fs) (c0', frm :: fs) ∧
    ((retNB p lbl q.fp q.ra c0' frm.ty).withTp tp).J σ c⟩

/-- **The callee's frame condition at a call of an `Accepted2` body**
(`CalleeF` with the caller's facts against its walk, `EnvQ`, for
`EnvNum`; the continuation's locatives with register bases, so that the
caller's frame is placed with its buffers, `framesPlaced_calleeF2`). -/
def CalleeF2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cx : FnCtx)
    (R : Region)
    (F : MachineData → Prop) (D : Int) (fp ra : BitVec 64) (i : Expr → String → Nat → Option Nat)
    (T : Expr → Prop) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop) : Prop :=
  ∀ m, F' m → F m ∧ CallerCells R (-(cx.frame : Int)) (-D) 0 m ∧
    ∃ mC σC c t s, Abs R (oF cx) mC σC ∧ CKept R (-(cx.frame : Int)) (-D) 0 mC m ∧ CallTo p c q.cE frm ∧
      T t ∧ NodeJE lbl (rsOf cx) t s σC.slot c ∧ (∃ lits cs bufs, EnvQ lits cs bufs lsize c.env) ∧ FrJ fp ra σC.slot ∧
      (∀ y ∈ Scc.Sem.exprFv frm.body, y ≠ frm.x → (lookupS s y).isSome) ∧
      (∀ y ∈ Scc.Sem.exprFv frm.body, y ≠ frm.x → ∀ ty pls, lookupS s y = some (ty, pls) →
        ∀ b o, WordPl.loc b o ∈ pls → ∃ r, b = .reg r) ∧
      ∀ y k v, y ≠ frm.x → (lookupS s y).bind (·.2[k]?) = some (.one (.imm v)) → i frm.body y k = some v.toNat

/-- **The call site of a plain call `let x = g(a)` returning to `q.ra`**
(the data `CallC2` gives at the call, for the callee's segment, `hcal`):
the ghost `c0` in `G0`, the term in `T`, the walk's facts at the `let`
(`Fresh`, `LitPt`, `EnvTy2`, `GrpL`, `countsB`), the callee, the argument's
word `w`, the call's code (`InstsC2`) with `w`'s load `lw`, the return
address after its `bl g`, and the call's resumption facts at the `let`
(`PtC2`, labels at `lab`, immediates `i`, the literal walk's facts with
`Lk`). -/
def CallSite2 (lcx : Scc.Lower.Ctx) (cx : FnCtx) (Cd : Int64 → List Directive → Prop)
    (Bl : Int64 → Label → Nat → Prop) (G0 : Ctl → Prop) (T : Expr → Prop) (lab : Label → Int64)
    (i : Expr → String → Nat → Option Nat) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) (g : String)
    (q : CallG) : Prop :=
  ∃ (c0 : Ctl) (pc pc' : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (a : At) (e : Expr)
    (t : Ty) (w : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
    (lw : List Item),
    G0 c0 ∧ T (.let_ x (.call g [] a []) e) ∧ Fresh env n ∧ LitPt (.let_ x (.call g [] a []) e, lits) ∧
    EnvTy2 (.let_ x (.call g [] a []) e, env, n) ∧ GrpL env ∧
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.call g [] a []) e) = true ∧
    Spike.Lib.LowerCall.Callee lcx g ∧ atomV env a = some (t, [w]) ∧
    InstsC2 cx Cd Bl kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] pc' ∧
    cx.getOp .X0 w = .ok lw ∧ q.ra = (pc + Int64.ofNat (4 * (directives lw).length) + 4).toBitVec ∧
    PtC2 lcx cx Cd Bl lab i T Lk kk pc env n lits cs bufs (.let_ x (.call g [] a []) e)

/-- **The caller at a plain call, pinned to the call site** (the callee's
frame condition `F'` with the caller's state at the call site's own data,
for the caller's resumption after the return): every memory of `F'` keeps
the cells of a caller's state `σC` outside the callee's region at room `D`,
`σC` holds a control `c` calling into `q.cE` with the frame `frm`, at the
call term `t` placed by `env` (`ofEnv2`), its facts against the walk
(`EnvQ`) at `lits`, `cs`, `bufs`, the saved pair, and `c` reached locally
from the ghost `c0`. `CalleeF2` with its existentials fixed. -/
def CallerAt2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cx : FnCtx)
    (R : Region) (D : Int) (fp ra : BitVec 64) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop)
    (c0 : Ctl) (t : Expr) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)) : Prop :=
  ∀ m, F' m → ∃ mC σC c, Abs R (oF cx) mC σC ∧ CKept R (-(cx.frame : Int)) (-D) 0 mC m ∧ CallTo p c q.cE frm ∧
    NodeJE lbl (rsOf cx) t (ofEnv2 env) σC.slot c ∧ EnvQ lits cs bufs lsize c.env ∧ FrJ fp ra σC.slot ∧
    LocalRun p c0 c

/-- **The call site with the caller pinned** (`CallSite2` and, at its own
data, `CallerAt2`: the callee's frame condition `F'` at the frame `frm`
keeps the caller's state at the call site, region `R`, room `D`, saved
pair `fp`/`ra`). -/
def CallSite2F (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (cx : FnCtx) (Cd : Int64 → List Directive → Prop)
    (Bl : Int64 → Label → Nat → Prop) (G0 : Ctl → Prop) (T : Expr → Prop) (lab : Label → Int64)
    (i : Expr → String → Nat → Option Nat) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) (g : String)
    (q : CallG) (R : Region) (D : Int) (fp ra : BitVec 64) (frm : TermRun.Frame) (F' : MachineData → Prop) :
    Prop :=
  ∃ (c0 : Ctl) (pc pc' : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (a : At) (e : Expr)
    (t : Ty) (w : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
    (lw : List Item),
    G0 c0 ∧ T (.let_ x (.call g [] a []) e) ∧ Fresh env n ∧ LitPt (.let_ x (.call g [] a []) e, lits) ∧
    EnvTy2 (.let_ x (.call g [] a []) e, env, n) ∧ GrpL env ∧
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.call g [] a []) e) = true ∧
    Spike.Lib.LowerCall.Callee lcx g ∧ atomV env a = some (t, [w]) ∧
    InstsC2 cx Cd Bl kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] pc' ∧
    cx.getOp .X0 w = .ok lw ∧ q.ra = (pc + Int64.ofNat (4 * (directives lw).length) + 4).toBitVec ∧
    PtC2 lcx cx Cd Bl lab i T Lk kk pc env n lits cs bufs (.let_ x (.call g [] a []) e) ∧
    CallerAt2 p lbl lsize cx R D fp ra q frm F' c0 (.let_ x (.call g [] a []) e) env lits cs bufs

/-- The call site of a pinned call site (`CallerAt2` dropped). -/
theorem CallSite2F.toCallSite2 {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {lcx : Scc.Lower.Ctx} {cx : FnCtx} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} {G0 : Ctl → Prop} {T : Expr → Prop} {lab : Label → Int64}
    {i : Expr → String → Nat → Option Nat} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop} {g : String}
    {q : CallG} {R : Region} {D : Int} {fp ra : BitVec 64} {frm : TermRun.Frame} {F' : MachineData → Prop}
    (h : CallSite2F p lbl lsize lcx cx Cd Bl G0 T lab i Lk g q R D fp ra frm F') :
    CallSite2 lcx cx Cd Bl G0 T lab i Lk g q :=
  let ⟨c0, pc, pc', kk, env, n, x, a, e, t, w, lits, cs, bufs, lw, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, _⟩ := h
  ⟨c0, pc, pc', kk, env, n, x, a, e, t, w, lits, cs, bufs, lw, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13⟩

/-! ## The code -/

/-- **`InstsC2`'s plain-call arm**: `w`'s load into `x0` at `pc`, `bl g`
after it (`Bl`), the result's store; the pc after it. -/
theorem instsC2_call {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    {k : Nat} {pc pc' : Int64} {d : Scc.IR.Reg} {g : String} {w : Scc.IR.Operand}
    (h : InstsC2 cx Cd Bl k pc [.call [d] (Scc.Lower.Names.user g) [w]] pc') :
    ∃ lw ls, cx.getOp .X0 w = .ok lw ∧ cx.setReg d .X0 = .ok ls ∧ Cd pc (directives lw) ∧
      Bl (pc + Int64.ofNat (4 * (directives lw).length)) (Scc.Lower.Names.user g) k ∧
      Cd (pc + Int64.ofNat (4 * (directives lw).length) + 4) (directives ls) ∧
      pc' = pc + Int64.ofNat (4 * (directives lw).length) + 4 + Int64.ofNat (4 * (directives ls).length) := by
  rcases h with ⟨hc, -⟩ | ⟨d', g', w', lw, ls, he, hw, hs, h1, h2, h3, hp⟩ |
      ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  · simp [Spike.Lib.LowerShape.isCall] at hc
  · simp only [Scc.IR.Inst.call.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, hg, rfl⟩ := he
    rw [← hg] at h2
    exact ⟨lw, ls, hw, hs, h1, h2, h3, hp⟩
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-! ## The argument's load and `bl g` -/

/-- **The argument's load into `x0`** from the node with buffers and
slices (`argC_seg` at `bodyN2`): the source's local run taken to the call
exactly, its facts against the walk (`EnvQ`) carried. -/
theorem argC_seg2 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW W₀ K exe endPc R F n blk)
    {w : Scc.IR.Operand} {lw : List Item} (hw : cx.getOp .X0 w = .ok lw) {pc : Int64}
    (hc : Cd pc (directives lw)) {i : Expr → String → Nat → Option Nat} {t : Expr} {s : SEnv}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} :
    SegW W₀ K p lbl ms0 (At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp))
      (At exe endPc R F (csN2 lbl cx fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        (pc + Int64.ofNat (4 * (directives lw).length)) t s
        fun σ => opdVal (rsOf cx) σ.slot w = some σ.regs.X0.toBitVec.toNat)) := by
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi (hCd _ _ hc)
    (hWB _ _ (SubCd.whole hc) rfl (fun σ c h => ⟨hG c h.1.2.2.1, h.1.2.1⟩) (.inl ⟨w, lw, hw, rfl⟩))
    (getOp_ne_nil hf h1 hw) (okBlk_argLoad hf h1 h16 hw) ?_
  rintro σ c ⟨⟨⟨L, sm, B, c', hr, hj, hn, hb, hm, hS⟩, hfj, hc0, -⟩, htp⟩
  refine ⟨c', hr, ?_⟩
  obtain ⟨v, hv, hrr⟩ := arun_getOp hf h1 hw (_root_.Executable.labels exe).label pc σ
  show Hit _ (arun _ _ ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c'
  rw [hrr]
  refine ⟨rfl, so_le_refl _ rfl, hj, ⟨hn, hS, L, sm, B, hb, hm⟩, hfj, hc0.trans hr, ?_, ?_⟩
  · show (σ.regs.setXReg .X0 v).TPIDR_EL0 = tp
    rw [setXReg_TPIDR]; exact htp
  · show opdVal (rsOf cx) σ.slot w = some (σ.regs.setXReg .X0 v).X0.toBitVec.toNat
    simpa [Reg64s.setXReg] using hv

/-- **`bl g` is one segment** (`blC_seg` at `csN2`). -/
theorem blC_seg2 {cx : FnCtx} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2}
    {fp ra : BitVec 64} {tp : UInt64} {Bl : Int64 → Label → Nat → Prop}
    (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {G0 Q Rn : Ctl → Prop} (hG : ∀ c, Rn c → G0 c)
    (hWBl : ∀ (n : ND) g k, Bl n.pc g k → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW W₀ K exe endPc R F n [blD g])
    {pc : Int64} {g : Label} {k : Nat} (hb : Bl pc g k) {t : Expr} {s : SEnv} {P P' : AS → Prop}
    (hP : ∀ σ, P σ → P' { σ with regs := σ.regs.setXReg .X30 (pc + 4).toBitVec }) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (csN2 lbl cx fp ra tp Q Rn pc t s P))
      (At exe endPc R F (csN2 lbl cx fp ra tp Q Rn ((_root_.Executable.labels exe).label g) t s P')) := by
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi (hBl _ _ _ hb)
    (hWBl _ _ _ hb rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) (by simp) (okBlk_blD _ _ _ g)
    fun σ c hJ => ⟨c, .refl c, ?_⟩
  show Hit (csN2 lbl cx fp ra tp Q Rn ((_root_.Executable.labels exe).label g) t s P')
    (arun (_root_.Executable.labels exe).label [blD g] ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c
  erw [blD_run]
  obtain ⟨hj, hq, hfj, hr, htp, hp⟩ := hJ
  refine ⟨rfl, so_le_refl _ rfl, hj, hq, hfj, hr, ?_, hP σ hp⟩
  show (σ.regs.setXReg .X30 _).TPIDR_EL0 = tp
  rw [setXReg_TPIDR]; exact htp

/-! ## The callee -/

/-- **The callee inside a plain call of an `Accepted2` body is one
segment** (`calleeC_seg` at `csN2`, `retCN2`): the argument a number by its
leaf layout (`hsc`, `hlit`, `GrpL`), the result by the callee's exit
(`ExitC2B` at the frame's type, `RetL.int`); the caller's facts against the
walk (`EnvQ`) extended by the result at the walk's binding. The callee's
segment (`hcal`, at the call's `g`) gets the return address after the
call's `bl` and the caller pinned at the call site (`CallerAt2`). -/
theorem calleeC_seg2G {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {D : Int}
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isaLSE2}
    {W : FragS isaLSE2} {Bl : Int64 → Label → Nat → Prop}
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → ∀ s c, At exe endPc R F n s c → W s c fs)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    {x g : String} {a : At} {e : Expr} (hT : T (.let_ x (.call g [] a []) e)) (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {t : Ty} {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) (hg : GrpL env)
    {n : Nat} (hfresh : Fresh env n) {off : Int} (hoff : rsOf cx (regName "r" n) = some off)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} (hsc : InLits lits a)
    (hlit : ∀ k, a = .lit k → k < 2 ^ 64)
    {pcB : Int64} {k : Nat} (hb : Bl pcB (Scc.Lower.Names.user g) k)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hcal : ∀ (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-(cx.frame : Int)) (-D) 0) F' → CalleeF2 p lbl lsize cx R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB k, Bl pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      q.ra = (pcB + 4).toBitVec →
      CallerAt2 p lbl lsize cx R D fp ra q frm F' c0 (.let_ x (.call g [] a []) e) env lits cs bufs →
      SegWS W K p lbl ms ((At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty
          Ab)) :
    SegWS W K p lbl ms ((At exe endPc R F (csN2 lbl cx fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv2 env) (callP cx w (pcB + 4)))).at fs)
      (fun s c fs' => (At exe endPc R F (retCN2 p lbl cx fp ra tp c0 fs
          (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
            (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
          (pcB + 4) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)).at fs s c fs' ∨
        Ab s c fs') := by
  have h16' := frame_ge16 hf
  obtain ⟨-, dd, hfd0, hretTy⟩ := hcl
  have hfd := hfd0
  rw [hprog] at hfd
  have hop : Scc.Lower.opLit lcx.prog lits (.call g [] a []) = .leaf none := by
    simp only [Scc.Lower.opLit, retShape_of_find hfd0, hretTy]; rfl
  have hgr : Spike.Lib.Form.group .int [.reg (regName "r" n)] = some [.one (.reg (regName "r" n))] := rfl
  have hsa := sevalAt_ofEnv2_one hg ha
  -- the frame's cells are kept by the callee
  have hout : ∀ (r : Scc.IR.Reg) (k' : Int), rsOf cx r = some k' →
      R.Off k' ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (k' - -(cx.frame : Int)) := by
    intro r k' hk'
    unfold rsOf at hk'
    split at hk'
    · rename_i o ho
      cases hk'
      obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho
      exact frame_outC hD0 hlo hhi (by omega) (by omega) (by omega)
    · cases hk'
  have houtA : R.Off (-16) ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (-16 - -(cx.frame : Int)) :=
    frame_outC hD0 hlo hhi (by decide) (by omega) (by omega)
  have houtB : R.Off (-8) ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (-8 - -(cx.frame : Int)) :=
    frame_outC hD0 hlo hhi (by decide) (by omega) (by omega)
  refine (call_ndSF (KC := False) (W := W) (K := K) (M := fun _ => True) (F₂ := F)
    (nC := csN2 lbl cx fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
      ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g))
      (.let_ x (.call g [] a []) e) (ofEnv2 env) (callP cx w (pcB + 4)))
    (γ := CallG) (κ' := Ctl) (lo' := -D) (hi' := 0)
    (Ne := fun q _ => calleeN (_root_.Executable.labels exe).label g tp q)
    (Ex := fun q frm c0' => exN2 p lbl tp fs q frm c0')
    (N := fun _ : Unit => retCN2 p lbl cx fp ra tp c0 fs
      (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
        (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
      (pcB + 4) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)
    (E := fun e : Empty => e.elim)
    (fs := fs) (Ab := Ab) hR hal hF
    (by show R.lo ≤ -(cx.frame : Int) + -D; omega) (by omega)
    (by show -(cx.frame : Int) < R.hi; omega) (Int.le_refl 0)
    (by show (-(cx.frame : Int)) % 16 = 0; omega) (by omega) (by decide)
    (fun h => h.elim) (fun h => h.elim) (fun _ hm _ => hm)
    (hWC g dd hfd _ rfl rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) ?_ (fun _ _ => rfl) ?_ ?_).mono_post ?_
  · -- the callee's segment, from `hcal`
    intro R' F' _ _ _ _ hFS _ hF'F hR'eq hcells q frm hex hall
    subst hR'eq
    have hra : q.ra = (pcB + 4).toBitVec := by
      obtain ⟨σC, c, cE, hJ, -, hNe⟩ := hex
      rw [← hNe.2.2.1]
      exact hJ.2.2.2.2.2.2
    refine (hcal q frm F' hFS ?_ ?_ ?_ ?_ hra ?_).mono_post ?_
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, -, -, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      refine ⟨hF'F m hm, hcells m hm, mC, σC, c, _, _, hA, hkept, hct, hT, hj, ⟨lits, cs, bufs, hen⟩, hfj, ?_⟩
      obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, -, -, hfr1⟩ := id hct
      rw [hj.1] at ht1
      cases ht1
      subst hfr1
      have hne : ∀ y, y ≠ x →
          ((x, Ty.int, [Spike.Lib.Form.WordPl.one (.reg (regName "r" n))]).1 == y) = false := by
        intro y hy; simp only [beq_eq_false_iff_ne]; exact fun h => hy h.symm
      refine ⟨fun y hy hyx => ?_, fun y hy hyx ty pls hl => ?_, fun y kk v hy hl => ?_⟩
      · have := hIt y hy
        rw [ofEnv2_cons hgr] at this
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using this
      · apply hlb y hy ty pls
        rw [ofEnv2_cons hgr]
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using hl
      · apply hIc y kk v
        rw [ofEnv2_cons hgr]
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hy] using hl
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      have hcE : cE = q.cE := hNe.1
      subst hcE
      exact ⟨c, x, a, e, hG c hJ.2.2.2.1, hT, hJ.1.1, hct⟩
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      obtain ⟨hj, hen, -, -, -, hP1, -⟩ := hJ
      obtain ⟨hl, hS, L, sm, B, hbB, hmB⟩ := hen
      have hm1 := NJB.litMask_one (NJB.of_nodeJE (p := p) (B := B) hj hl hbB hmB hS) hsa hsc
      obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, hev1, hcE1, -⟩ := hct
      rw [hj.1] at ht1
      cases ht1
      obtain ⟨_, ws', hev', -, hwr⟩ := hj.2.2.evalAt (fun _ => rfl) hsa
      rw [hev1] at hev'
      cases hev'
      match ws1, hwr, hev1, hcE1 with
      | [w'], ⟨⟨v, hv, hvr⟩, _⟩, hev1, hcE1 =>
        have hv' : v = q.v.toNat := by
          rw [hP1] at hv
          cases hv
          rw [← hNe.2.2.2.1]; rfl
        obtain ⟨kk, hkk, hlt⟩ := NumL.one (hl.evalAt' hsc hlit hev1).2 hm1
        exact ⟨d1.arg, d1.argTy, w', by rw [← hNe.1, hcE1], hv' ▸ hvr, kk, hkk, hlt⟩
    · exact ⟨pcB, k, hb, hra⟩
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, hr, -, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      exact ⟨mC, σC, c, hA, hkept, hct, hj, hen, hfj, hr⟩
    · rintro s c fs' (⟨rfl, c0', hrun, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩⟩ | hab)
      · exact .inl ⟨⟨c0', ⟨he, hn, hdc, hpc, σ, hA, hD, hrun, hJ⟩, trivial⟩, rfl⟩
      · exact .inr hab
  · -- the source's call and the callee's entry
    intro σC c hJ
    obtain ⟨hj, -, -, -, htp, -⟩ := hJ
    obtain ⟨ta, ws', hev, -⟩ := hj.2.2.evalAt (fun _ => rfl) hsa
    exact ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.X0.toBitVec,
      ⟨dd.body, [(dd.arg, dd.argTy, ws')], none⟩⟩, _, ⟨x, e, c.env, [], dd.retTy⟩,
      ⟨x, g, a, e, dd, ta, ws', hj.1, hfd, hev, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, htp⟩
  · -- the return: the source returns into `x`, the caller's cells kept
    intro q c0' σC c cE frm σx c' σR hJ hct hNe hEx hregs _ hsl
    obtain ⟨hj, hen, hfj, hr, -, -, hP2⟩ := hJ
    obtain ⟨hrun, ⟨⟨⟨a', t', ws', hta, -, hev', -, hvr, -, -⟩, hlr⟩, hRL⟩, htpx⟩ := hEx
    have hcE : cE = q.cE := hNe.1
    subst hcE
    have hct' := hct
    obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, hfd1, -, -, hfr1⟩ := hct'
    rw [hj.1] at ht1
    cases ht1
    rw [hfd] at hfd1
    cases hfd1
    subst hfr1
    have hRL' : RetL .int c' := by rw [← hretTy]; exact hRL
    obtain ⟨a2, t2, w2, ht2, he2, hnum⟩ := RetL.int hRL'
    rw [hta] at ht2
    cases ht2
    rw [hev'] at he2
    simp only [Option.some.injEq, Prod.mk.injEq] at he2
    obtain ⟨rfl, rfl⟩ := he2
    have hstep : FrameStep p (c', ⟨x, e, c.env, [], dd.retTy⟩ :: fs)
        (⟨e, (x, dd.retTy, [w2]) :: c.env, none⟩, fs) := .ret hta rfl hev'
    have hvr' : ValRep lbl w2.val σR.regs.X0.toBitVec.toNat := by
      rw [hregs]; exact hvr 0 (by simp) (by decide)
    refine ⟨⟨e, (x, dd.retTy, [w2]) :: c.env, none⟩, .single hstep, .inl ⟨(), ?_, ?_, ?_⟩⟩
    · show pcB + 4 = Int64.ofBitVec q.ra
      rw [← hNe.2.2.1]
      show _ = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [hP2, Int64.ofBitVec_toBitVec]
    · show SO.le ⟨-(cx.frame : Int), []⟩ ⟨-(cx.frame : Int) + 0, []⟩ = true
      simp [SO.le]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨rfl, rfl, ?_⟩
        show Spike.Lib.Form.SRepE lbl _ (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
          ((x, dd.retTy, [w2]) :: c.env)
        rw [ofEnv2_cons hgr, hretTy]
        refine (hj.2.2.congr fun b hb pl hpl o ho => opdVal_upd fun r k' hr' hk' => ?_).bind x rfl
          ⟨⟨_, by simp [opdVal, hoff, upd_apply], hvr'⟩, trivial⟩
        have hne := Fresh.ofEnv2 hfresh "r" b hb pl hpl o ho r hr'
        rw [upd_apply]
        split
        · next hk => subst hk; exact absurd (rsOf_inj hk' hoff) hne
        exact hsl k' (hout r k' hk').1 (hout r k' hk').2
      · obtain ⟨hl, hS, L, sm, B, hbB, hmB⟩ := hen
        refine ⟨?_, EnvSmall.cons hS (WordsSmall.isNum hnum), L, sm, B, ?_, hmB⟩
        · show EnvLit _ ((x, dd.retTy, [w2]) :: c.env)
          rw [hop, hretTy]
          refine hl.cons rfl (NumL.of_all fun w hw => ?_)
          simp only [List.mem_singleton] at hw
          subst hw; exact hnum
        · show EnvB _ _ _ L sm lsize ((x, dd.retTy, [w2]) :: c.env)
          rw [hop]
          exact hbB.cons (SliceL.leaf none [w2]) (fun a h => by rcases h with h | h <;> cases h)
            (fun n τ h => by cases h)
      · exact ⟨(hsl _ houtA.1 houtA.2).trans hfj.1, (hsl _ houtB.1 houtB.2).trans hfj.2⟩
      · exact (FrameRunM.ofLocal hr fs).trans (.step (.frame (hct.step fs))
          (hrun.trans ((FrameRunM.ofLocal hlr _).trans (.single (.frame hstep)))))
      · rw [hregs]; exact htpx
  · rintro s c fs' (⟨h, rfl⟩ | hab)
    · exact .inl (h.elim (fun ⟨_, h⟩ => ⟨h, rfl⟩) fun ⟨e, _⟩ => e.elim)
    · exact .inr hab

/-- **The callee inside a plain call of an `Accepted2` body is one
segment** (`calleeC_seg` at `csN2`, `retCN2`): the argument a number by its
leaf layout (`hsc`, `hlit`, `GrpL`), the result by the callee's exit
(`ExitC2B` at the frame's type, `RetL.int`); the caller's facts against the
walk (`EnvQ`) extended by the result at the walk's binding (`calleeC_seg2G`). -/
theorem calleeC_seg2 {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {D : Int}
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isaLSE2}
    {W : FragS isaLSE2} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → ∀ s c, At exe endPc R F n s c → W s c fs)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-(cx.frame : Int)) (-D) 0) F' → CalleeF2 p lbl lsize cx R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB k, Bl pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      CallSite2 lcx cx Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q →
      SegWS W K p lbl ms ((At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty
          Ab))
    {x g : String} {a : At} {e : Expr} (hT : T (.let_ x (.call g [] a []) e)) (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {t : Ty} {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) (hg : GrpL env)
    {n : Nat} (hfresh : Fresh env n) {off : Int} (hoff : rsOf cx (regName "r" n) = some off)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} (hsc : InLits lits a)
    (hlit : ∀ k, a = .lit k → k < 2 ^ 64)
    {pcB : Int64} {k : Nat} (hb : Bl pcB (Scc.Lower.Names.user g) k)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hsite : ∀ q : CallG, q.ra = (pcB + 4).toBitVec →
      CallSite2 lcx cx Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q) :
    SegWS W K p lbl ms ((At exe endPc R F (csN2 lbl cx fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv2 env) (callP cx w (pcB + 4)))).at fs)
      (fun s c fs' => (At exe endPc R F (retCN2 p lbl cx fp ra tp c0 fs
          (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
            (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
          (pcB + 4) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)).at fs s c fs' ∨
        Ab s c fs') :=
  calleeC_seg2G hf h16 hprog hF hR hal hD0 hD8 hlo hhi hG hWC hT hcl ha hg hfresh hoff hsc hlit hb hIt hIc hlb
    fun q frm F' hFS hCF hex hav hbl hq _ => hcal g q frm F' hFS hCF hex hav hbl (hsite q hq)

/-! ## The result's store -/

/-- **The result's store into `r%n`** from the return address (`resC_seg`
at `retCN2`, `csN2`). -/
theorem resC_seg2 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 Q : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW W₀ K exe endPc R F n blk)
    {d : Scc.IR.Reg} {ls : List Item} (hs : cx.setReg d .X0 = .ok ls) {off : Int}
    (hoff : rsOf cx d = some off) {pcR : Int64} (hc : Cd pcR (directives ls)) {e : Expr} {s : SEnv} :
    SegW W₀ K p lbl ms0 (At exe endPc R F (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off))
      (At exe endPc R F (csN2 lbl cx fp ra tp Q (fun c => FrameRunM p (c0, fs) (c, fs))
        (pcR + Int64.ofNat (4 * (directives ls).length)) e s fun _ => True)) := by
  have hok := okBlk_resStore hf h1 h16 hs
  have hW := hWB ⟨pcR, oF cx, (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off).J⟩ _ (SubCd.whole hc) rfl
    (fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) (.inr ⟨d, ls, hs, rfl⟩)
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  rw [setReg_eq hf (by omega) ho] at hs
  cases ok_inj hs
  have hoo : off = o - cx.frame := by
    simp only [rsOf, ho, Option.some.injEq] at hoff; exact hoff.symm
  subst hoo
  have hds : directives [ins (.STR (rz .W64 .X0) ⟨spW64, .imm ⟨i64 o, none⟩⟩)] =
      [spStr .X0 (Int64.ofInt o)] := rfl
  rw [hds] at hc hok hW ⊢
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi (hCd _ _ hc) hW (by simp) hok
    fun σ c hJ => ⟨c, .refl c, ?_⟩
  show Hit _ (arun _ _ ⟨pcR, ⟨-(cx.frame : Int), []⟩, σ⟩) c
  rw [arun_spStr1, ofs_eq hf h1 ho]
  obtain ⟨hj, hq, hfj, hr, htp⟩ := hJ
  exact ⟨rfl, so_le_refl _ rfl, hj, hq, frJ_upd hfj (ofs_le hf ho) _, hr, htp, trivial⟩

/-! ## The plain call -/

/-- **A plain call of an `Accepted2` body** (`CallC2`; `callC_of` at
`bodyN2`): `callC_of`'s premises, the source's controls in `G0` closed
under the frame runs with memory (`FrameRunM`) at `fs`, and the callee's
segment from `CalleeF2` to its exits at the frame's type (`ExitC2B`), given
the call site with the caller pinned (`CallSite2F`). -/
theorem callC2_ofF {ms : List TermRun.Frame → MemSide isaLSE2} {W : FragS isaLSE2} {cx : FnCtx}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {D : Int}
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW (fun s c => W s c fs) K exe endPc R F n blk)
    (hWBl : ∀ (n : ND) g k, Bl n.pc g k → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW (fun s c => W s c fs) K exe endPc R F n [blD g])
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → ∀ s c, At exe endPc R F n s c → W s c fs)
    {T : Expr → Prop} (hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = [])
    {i : Expr → String → Nat → Option Nat} {Ab : FragS isaLSE2} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-(cx.frame : Int)) (-D) 0) F' → CalleeF2 p lbl lsize cx R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB k, Bl pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      CallSite2F p lbl lsize lcx cx Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q R D fp ra frm F' →
      SegWS W K p lbl ms ((At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty
          Ab)) :
    CallC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk := by
  intro c0 pc pc' kk env n x g is a ts e t w lits cs bufs hc0 hT hfresh hlp hty hg hcnt hcl ha hcode hIt hIc hlb
    hpt
  obtain ⟨rfl, rfl⟩ := hTc _ _ _ _ _ _ hT
  have hG : ∀ c, LocalRun p c0 c → G0 c := fun c h => hG0 c0 c hc0 (FrameRunM.ofLocal h fs)
  have hGR : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c := fun c h => hG0 c0 c hc0 h
  have hlo0 : R.lo ≤ -(cx.frame : Int) := by omega
  have hsc : InLits lits a := hlp.1 a (by simp [headAtoms])
  have hlit : ∀ k, a = .lit k → k < 2 ^ 64 := fun k hk => hlp.2.2.2 k (by subst hk; simp [headAtoms])
  obtain ⟨lw, ls, hw, hs, hcw, hb, hcs, hp⟩ := instsC2_call hcode
  subst hp
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  have hoff : rsOf cx (regName "r" n) = some (o - cx.frame) := by simp [rsOf, ho]
  -- `w`'s load into `x0`
  have sA := argC_seg2 (p := p) (lbl := lbl) (lsize := lsize) (K := K) (ms0 := ms fs) (tp := tp) (i := i)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (lits := lits) (cs := cs) (bufs := bufs)
    hf h1 h16 hF hR hal hlo0 hhi hCd hG hWB hw hcw
  -- `bl g`
  have sB := blC_seg2 (p := p) (lbl := lbl) (K := K) (ms0 := ms fs) (tp := tp) (cx := cx)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (Q := fun c => EnvQ lits cs bufs lsize c.env)
    (Rn := LocalRun p c0)
    (P' := callP cx w (pc + Int64.ofNat (4 * (directives lw).length) + 4))
    hF hR hal hlo0 hhi hBl hG hWBl hb fun σ hp => by
      refine ⟨?_, ?_⟩
      · show opdVal (rsOf cx) σ.slot w = some (σ.regs.setXReg .X30 _).X0.toBitVec.toNat
        simpa [Reg64s.setXReg] using hp
      · simp [Reg64s.setXReg]
  have sW := SegWS.liftS (W := W) fs (sA.seq sB) (fun _ _ h => h)
  -- the callee
  have sCal := calleeC_seg2G (p := p) (lbl := lbl) (exe := exe) (endPc := endPc) (K := K) (ms := ms) (W := W)
    (fp := fp) (ra := ra) (tp := tp) (fs := fs) (c0 := c0) (Ab := Ab) (lits := lits) (cs := cs) (bufs := bufs)
    hf h16 hprog hF hR hal hD0 hD8 hlo hhi hG hWC hT hcl ha hg hfresh hoff hsc hlit hb hIt hIc hlb
    fun q frm F' hFS hCF hex hav hbl hq hpin => hcal g q frm F' hFS hCF hex hav hbl
      ⟨c0, pc, _, kk, env, n, x, a, e, t, w, lits, cs, bufs, lw, hc0, hT, hfresh, hlp, hty, hg,
        hcnt, hcl, ha, hcode, hw, hq, hpt, hpin⟩
  -- the result's store
  have sR := SegWS.liftS (W := W) fs (resC_seg2 (p := p) (lbl := lbl) (K := K) (ms0 := ms fs) (fp := fp)
    (ra := ra) (tp := tp) (e := e) (s := ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
    (Q := fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
      (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
    hf h1 h16 hF hR hal hlo0 hhi hCd hGR hWB hs hoff hcs) (fun _ _ h => h)
  refine (sW.seq (SegWS.seq_left sCal sR)).mono_post ?_
  rintro s c fs' (⟨⟨he, hn, hdc, hpc, σ, hA, hD, hj, ⟨hl, hS, L, sm, B, hbB, hmB⟩, hfj, hr, htp, -⟩, rfl⟩ | hab)
  · exact .inl ⟨rfl, c, hr, he, hn, hdc, hpc, σ, hA, hD,
      ⟨⟨L, sm, B, NJB.of_nodeJE hj hl hbB hmB hS⟩, hfj, .refl c, SlotRepAt.of_nodeJE hj hIt hlb hIc⟩, htp⟩
  · exact .inr hab

/-- **A plain call of an `Accepted2` body** (`CallC2`; `callC_of` at
`bodyN2`): `callC_of`'s premises, the source's controls in `G0` closed
under the frame runs with memory (`FrameRunM`) at `fs`, and the callee's
segment from `CalleeF2` to its exits at the frame's type (`ExitC2B`)
(`callC2_ofF`). -/
theorem callC2_of {ms : List TermRun.Frame → MemSide isaLSE2} {W : FragS isaLSE2} {cx : FnCtx}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {D : Int}
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW (fun s c => W s c fs) K exe endPc R F n blk)
    (hWBl : ∀ (n : ND) g k, Bl n.pc g k → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW (fun s c => W s c fs) K exe endPc R F n [blD g])
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → ∀ s c, At exe endPc R F n s c → W s c fs)
    {T : Expr → Prop} (hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = [])
    {i : Expr → String → Nat → Option Nat} {Ab : FragS isaLSE2} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-(cx.frame : Int)) (-D) 0) F' → CalleeF2 p lbl lsize cx R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB k, Bl pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      CallSite2 lcx cx Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q →
      SegWS W K p lbl ms ((At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty
          Ab)) :
    CallC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk :=
  callC2_ofF hf h1 h16 hprog hF hR hal hD0 hD8 hlo hhi hCd hBl hG0 hWB hWBl hWC hTc
    fun g q frm F' hFS hCF hex hav hbl hs => hcal g q frm F' hFS hCF hex hav hbl hs.toCallSite2

end Call

/-- info: 'Spike.Lib.LowerA64.instsC2_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.instsC2_call

/-- info: 'Spike.Lib.LowerA64.argC_seg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.argC_seg2

/-- info: 'Spike.Lib.LowerA64.blC_seg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blC_seg2

/-- info: 'Spike.Lib.LowerA64.calleeC_seg2G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.calleeC_seg2G

/-- info: 'Spike.Lib.LowerA64.calleeC_seg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.calleeC_seg2

/-- info: 'Spike.Lib.LowerA64.resC_seg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.resC_seg2

/-- info: 'Spike.Lib.LowerA64.callC2_ofF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callC2_ofF

/-- info: 'Spike.Lib.LowerA64.callC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callC2_of

end Spike.Lib.LowerA64
