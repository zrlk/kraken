/-
**A plain call of an `Accepted2` body** (x86-64): `callC2_of`, the call's
obligation `CallC2` (`Body2.lean`) at the node with buffers and slices
(`bodyN2`), from the call's code, its blocks inside the frame's fragment
and the callee's segment; `CallC.lean`'s `callC_of` at `NJB`.

`callC_of`'s nodes ask every bound word to be a number (`EnvNum`), which a
buffer's locative or a slice is not. The nodes here carry the caller's
facts against the walk (`EnvQ`: `EnvLit`, `EnvB`, `MemB`) instead, and the
callee's frame condition the caller's (`CalleeF2`). The argument is a
number below `2^64`: its one operand is one placement (`GrpL`,
`sevalAt_ofEnv2_one`), so its layout is a leaf (`NJB.litMask_one`). The
result is a number below `2^64` by the callee's exit (`RetL`, `retNB`).

- `brN2`, `callN2`, `retCP2`, `exN2`, `CalleeF2`: the nodes and the
  callee's frame condition (`EnvQ` in `Spike.Lib.Src.GroupOpds`);
- `CallSite2`: the call site's data handed to the callee's segment (`hcal`);
- `CallerAt2`, `CallSite2F`, `CallSite2F.toCallSite2`: the caller pinned at
  the call site's data, for its resumption (`Resume2.lean`), and the call
  site with it;
- `instsC2_call`: `InstsC2`'s plain-call arm;
- `argP_seg2`, `callq_seg2`, `calleeP_seg2`, `retP_seg2`: the argument's
  load, `callq g`, the callee, the result's store (`calleeP_seg2G`: the
  callee's segment given the pinned caller);
- `callC2_of`, `callC2_ofF` (the callee's segment from `CallSite2F`).
-/
import Spike.Lib.LowerX64.CallC
import Spike.Lib.LowerX64.RetNB
import Spike.Lib.Src.GroupOpds

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (labelOf i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv opdVal_upd WordsRep SRep sevalAt lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName labName atomV)
open Scc.Sem (ValRep)
open Spike.Lib.LowerCall (Callee)
open Spike.Lib.X64Consumer (noRetBlk)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)

set_option linter.unusedSimpArgs false

/-! ## The nodes -/

/-- **A node of the call's bracket** (`brN` at `Q` for `EnvNum`). -/
def brN2 (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (Q Rn : Ctl → Prop) (pc : Int64) (t : Expr) (s : SEnv) (P : AS → Prop) : ND :=
  ⟨pc, oB fr, fun σ c => NodeJE lbl (rsOf fr) t s σ.slot c ∧ Q c ∧ FrJ fp ra σ.slot ∧ Rn c ∧
    σ.regs.fsBase = tp ∧ P σ⟩

/-- **The call node** (`callN` at `Q`). -/
def callN2 (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (Q Rn : Ctl → Prop) (pc : Int64) (t : Expr) (s : SEnv) (P : AS → Prop) : ND :=
  ⟨pc, { oB fr with sp := (oB fr).sp - 8 }, fun σ c => NodeJE lbl (rsOf fr) t s σ.slot c ∧ Q c ∧
    FrJ fp ra σ.slot ∧ Rn c ∧ σ.regs.fsBase = tp ∧ P σ⟩

/-- **Back from the callee** (`retCP` at `Q`). -/
def retCP2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (R : Region) (fr : Scc.Emit.X64.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame) (Q : Ctl → Prop) (pc : Int64)
    (e : Expr) (s : SEnv) (off : Int) : ND :=
  ⟨pc, ⟨-(fr.size : Int), []⟩, fun σ c => NodeJE lbl (rsOf fr) e s (upd σ.slot off (σ.regs.get64 .rax)) c ∧
    Q c ∧ FrJ fp ra σ.slot ∧ FrameRunM p (c0, fs) (c, fs) ∧ σ.regs.fsBase = tp ∧
    σ.regs.get64 .rbp = R.addr 0⟩

/-- **The callee's exit seen from its region** (`exN` at `retNB`). -/
def exN2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (tp : UInt64) (fs : List TermRun.Frame) (q : CallG)
    (frm : TermRun.Frame) (c0' : Ctl) : ND :=
  ⟨Int64.ofBitVec q.ra, ⟨8, []⟩, fun σ c => FrameRunM p (q.cE, frm :: fs) (c0', frm :: fs) ∧
    ((retNB p lbl q.fp q.ra c0' frm.ty).withTp tp).J { σ with slot := shSl σ.slot } c⟩

/-- **The callee's frame condition at a call of an `Accepted2` body**
(`CalleeF` with the caller's facts against its walk, `EnvQ`, for
`EnvNum`). -/
def CalleeF2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (fr : Scc.Emit.X64.Frame) (R : Region)
    (F : MachineData → Prop) (D : Int) (fp ra : BitVec 64) (i : Expr → String → Nat → Option Nat)
    (T : Expr → Prop) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop) : Prop :=
  ∀ m, F' m → F m ∧ CallerCells R (-(fr.size : Int) - 8) (-D) 8 m ∧
    ∃ mC σC c t s, Abs R { oB fr with sp := (oB fr).sp - 8 } mC σC ∧ CKept R (-(fr.size : Int) - 8) (-D) 8 mC m ∧
      CallTo p c q.cE frm ∧ T t ∧ NodeJE lbl (rsOf fr) t s σC.slot c ∧ (∃ lits cs bufs, EnvQ lits cs bufs lsize c.env) ∧
      FrJ fp ra σC.slot ∧
      (∀ y ∈ Scc.Sem.exprFv frm.body, y ≠ frm.x → (Spike.Lib.Form.lookupS s y).isSome) ∧
      (∀ y ∈ Scc.Sem.exprFv frm.body, y ≠ frm.x → ∀ ty pls, Spike.Lib.Form.lookupS s y = some (ty, pls) →
        ∀ b o, Spike.Lib.Form.WordPl.loc b o ∈ pls → ∃ r, b = .reg r) ∧
      ∀ y k v, y ≠ frm.x → (Spike.Lib.Form.lookupS s y).bind (·.2[k]?) = some (.one (.imm v)) →
        i frm.body y k = some v.toNat

/-- **The call site of a plain call `let x = g(a)` returning to `q.ra`**
(the data `CallC2` gives at the call, for the callee's segment, `hcal`):
the ghost `c0` in `G0`, the term in `T`, the walk's facts at the `let`
(`Fresh`, `LitPt`, `EnvTy2`, `GrpL`, `countsB`), the callee, the argument's
word `w`, the call's code (`InstsC2`) with `w`'s load `lw` (its sizes `zs`)
and `callq g` (its size `zc`), the return address after the `callq`, and
the call's resumption facts at the `let` (`PtC2`, labels at `lab`,
immediates `i`, the literal walk's facts with `Lk`). -/
def CallSite2 (lcx : Scc.Lower.Ctx) (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (G0 : Ctl → Prop) (T : Expr → Prop) (lab : Label → Int64)
    (i : Expr → String → Nat → Option Nat) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) (g : String)
    (q : CallG) : Prop :=
  ∃ (c0 : Ctl) (pc pc' : Int64) (kk kk' : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (a : At) (e : Expr)
    (t : Ty) (w : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
    (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc : Nat),
    G0 c0 ∧ T (.let_ x (.call g [] a []) e) ∧ Fresh env n ∧ LitPt (.let_ x (.call g [] a []) e, lits) ∧
    EnvTy2 (.let_ x (.call g [] a []) e, env, n) ∧ GrpL env ∧
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.call g [] a []) e) = true ∧
    Callee lcx g ∧ atomV env a = some (t, [w]) ∧
    InstsC2 fr Cd Bl kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] kk' pc' ∧
    getOp fr .rdi w = .ok lw ∧ zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
    Bl (pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) kk ∧
    q.ra = (pc + Int64.ofNat zs.sum + Int64.ofNat zc).toBitVec ∧
    PtC2 lcx fr Cd Bl lab i T Lk kk pc env n lits cs bufs (.let_ x (.call g [] a []) e)

/-- **The caller at a plain call, pinned to the call site** (the callee's
frame condition `F'` with the caller's state at the call site's own data,
for the caller's resumption after the return): every memory of `F'` keeps
the cells of a caller's state `σC` (at the call node's offsets) outside the
callee's region at room `D`, `σC` holds a control `c` calling into `q.cE`
with the frame `frm`, at the call term `t` placed by `env` (`ofEnv2`), its
facts against the walk (`EnvQ`) at `lits`, `cs`, `bufs`, the saved pair,
`c` reached locally from the ghost `c0`; the callee's saved `%rbp` the
region's frame record. `CalleeF2` with its existentials fixed. -/
def CallerAt2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (fr : Scc.Emit.X64.Frame) (R : Region) (D : Int) (fp ra : BitVec 64) (q : CallG) (frm : TermRun.Frame)
    (F' : MachineData → Prop) (c0 : Ctl) (t : Expr) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)) : Prop :=
  ∀ m, F' m → ∃ mC σC c, Abs R { oB fr with sp := (oB fr).sp - 8 } mC σC ∧
    CKept R (-(fr.size : Int) - 8) (-D) 8 mC m ∧ CallTo p c q.cE frm ∧
    NodeJE lbl (rsOf fr) t (ofEnv2 env) σC.slot c ∧ EnvQ lits cs bufs lsize c.env ∧ FrJ fp ra σC.slot ∧
    LocalRun p c0 c ∧ q.fp = R.addr 0

/-- **The call site with the caller pinned** (`CallSite2` and, at its own
data, `CallerAt2`: the callee's frame condition `F'` at the frame `frm`
keeps the caller's state at the call site, region `R`, room `D`, saved
pair `fp`/`ra`). -/
def CallSite2F (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (G0 : Ctl → Prop) (T : Expr → Prop) (lab : Label → Int64)
    (i : Expr → String → Nat → Option Nat) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) (g : String)
    (q : CallG) (R : Region) (D : Int) (fp ra : BitVec 64) (frm : TermRun.Frame) (F' : MachineData → Prop) :
    Prop :=
  ∃ (c0 : Ctl) (pc pc' : Int64) (kk kk' : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (a : At) (e : Expr)
    (t : Ty) (w : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
    (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc : Nat),
    G0 c0 ∧ T (.let_ x (.call g [] a []) e) ∧ Fresh env n ∧ LitPt (.let_ x (.call g [] a []) e, lits) ∧
    EnvTy2 (.let_ x (.call g [] a []) e, env, n) ∧ GrpL env ∧
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.call g [] a []) e) = true ∧
    Callee lcx g ∧ atomV env a = some (t, [w]) ∧
    InstsC2 fr Cd Bl kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] kk' pc' ∧
    getOp fr .rdi w = .ok lw ∧ zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
    Bl (pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) kk ∧
    q.ra = (pc + Int64.ofNat zs.sum + Int64.ofNat zc).toBitVec ∧
    PtC2 lcx fr Cd Bl lab i T Lk kk pc env n lits cs bufs (.let_ x (.call g [] a []) e) ∧
    CallerAt2 p lbl lsize fr R D fp ra q frm F' c0 (.let_ x (.call g [] a []) e) env lits cs bufs

/-- The call site of a pinned call site (`CallerAt2` dropped). -/
theorem CallSite2F.toCallSite2 {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {lcx : Scc.Lower.Ctx} {fr : Scc.Emit.X64.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop} {G0 : Ctl → Prop}
    {T : Expr → Prop} {lab : Label → Int64} {i : Expr → String → Nat → Option Nat}
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop} {g : String} {q : CallG} {R : Region} {D : Int}
    {fp ra : BitVec 64} {frm : TermRun.Frame} {F' : MachineData → Prop}
    (h : CallSite2F p lbl lsize lcx fr Cd Bl G0 T lab i Lk g q R D fp ra frm F') :
    CallSite2 lcx fr Cd Bl G0 T lab i Lk g q :=
  let ⟨c0, pc, pc', kk, kk', env, n, x, a, e, t, w, lits, cs, bufs, lw, zs, zc, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10, h11, h12, h13, h14, h15, h16, _⟩ := h
  ⟨c0, pc, pc', kk, kk', env, n, x, a, e, t, w, lits, cs, bufs, lw, zs, zc, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16⟩

/-! ## The code -/

/-- **`InstsC2`'s plain-call arm**: `w`'s load into `%rdi` at `pc`, `callq
g` with the return label after it (`Bl`), the result's store; the counter
and pc after it. -/
theorem instsC2_call {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {k k' : Nat} {pc pc' : Int64} {d : Scc.IR.Reg} {g : String}
    {w : Scc.IR.Operand} (h : InstsC2 fr Cd Bl k pc [.call [d] (Scc.Lower.Names.user g) [w]] k' pc') :
    ∃ lw off zs zc z, getOp fr .rdi w = .ok lw ∧ rsOf fr d = some off ∧ zs.length = (dirs lw).length ∧
      Cd pc ((dirs lw).zip zs) ∧ Bl (pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) k ∧
      Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)] ∧ k' = k + 1 ∧
      pc' = pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z := by
  have hua : Scc.Lower.Names.user g ≠ Scc.Lower.Names.alloc := by
    intro h
    have := congrArg (fun s : String => s.toList.head?) h
    simp [Scc.Lower.Names.user, Scc.Lower.Names.alloc, String.toList_append] at this
  have hup : Scc.Lower.Names.user g ≠ Scc.Lower.Names.print := by
    intro h
    have := congrArg (fun s : String => s.toList.head?) h
    simp [Scc.Lower.Names.user, Scc.Lower.Names.print, String.toList_append] at this
  rcases h with ⟨hc, -⟩ | ⟨d', g', w', lw, off, zs, zc, z, he, hw, hd, hz, h1, h2, h3, ⟨hk, hp⟩⟩ |
      ⟨d', ws, -, -, -, -, -, he, -⟩ | ⟨ws, -, -, -, he, -⟩
  · simp [Spike.Lib.LowerShape.isCall] at hc
  · simp only [Scc.IR.Inst.call.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, hg, rfl⟩ := he
    rw [← hg] at h2
    exact ⟨lw, off, zs, zc, z, hw, hd, hz, h1, h2, h3, hk, hp⟩
  · simp only [Scc.IR.Inst.call.injEq, List.cons.injEq] at he
    exact absurd he.2.1 hua
  · simp only [Scc.IR.Inst.call.injEq] at he
    cases he.1

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-! ## The bracket's segments -/

/-- **The argument's load into `%rdi`** from the node with buffers and
slices (`argP_seg` at `bodyN2`): the source's local run taken to the call
exactly, its facts against the walk (`EnvQ`) carried. -/
theorem argP_seg2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc R F n blk)
    {w : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item} (hlw : getOp fr .rdi w = .ok lw)
    {zs : List Nat} (hz : zs.length = (dirs lw).length) {pc : Int64} (hc : Cd pc ((dirs lw).zip zs))
    {t : Expr} {s : SEnv} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {i : Expr → String → Nat → Option Nat} :
    SegW W₀ K p lbl ms0 (At exe endPc R F ((bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs).withTp tp))
      (At exe endPc R F (brN2 lbl fr fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        (pc + Int64.ofNat zs.sum) t s fun σ => opdVal (rsOf fr) σ.slot w = some (σ.regs.get64 .rdi).toNat)) := by
  obtain ⟨dl, hdl⟩ := dirs_getOp hlw
  have hok : okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs lw).zip zs) = true := by
    have := okBlk_getOp hf h1 (by decide) (by decide) hlw hz []
    rw [List.append_nil] at this
    rw [this]; rfl
  refine seg_blk1 hF hR hlo hhi (hCd _ _ hc)
    (hWB _ _ (SubCd.whole hc) rfl hok (noRet_argLoadC hlw hz) fun σ c h => ⟨hG c h.1.2.2.1, h.1.2.1⟩)
    (zip_ne_nil hz (by rw [hdl]; simp)) hok ?_
  rintro σ c ⟨⟨⟨L, sm, B, c', hr, hj, hn, hb, hm, hS⟩, hfj, hc0, -⟩, htp⟩
  refine ⟨c', hr, ?_⟩
  obtain ⟨v, hv, hrr⟩ := arun_getOp hf h1 (by decide) hlw (_root_.Executable.labels exe).label pc σ hz
  show Hit _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  rw [hrr]
  refine ⟨rfl, so_le_oB fr, hj, ⟨hn, hS, L, sm, B, hb, hm⟩, hfj, hc0.trans hr, ?_, ?_⟩
  · show (σ.regs.set64 .rdi v).fsBase = tp
    rw [Reg64s.set64_fsBase]; exact htp
  · show opdVal (rsOf fr) σ.slot w = some ((σ.regs.set64 .rdi v).get64 .rdi).toNat
    rw [Reg64s.get64_set64_self]; exact hv

/-- **`callq g` is one segment** (`callq_seg` at `brN2`, `callN2`). -/
theorem callq_seg2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {Bl : Int64 → Nat → Label → Nat → Prop}
    (hBl : ∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    {G0 Q Rn : Ctl → Prop} (hG : ∀ c, Rn c → G0 c)
    (hWBl : ∀ (n : ND) zc g k, Bl n.pc zc g k → n.o = oB fr → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW W₀ K exe endPc R F n [(i64 (.call (rel g)), zc)])
    {pc : Int64} {zc : Nat} {g : Label} {k : Nat} (hb : Bl pc zc g k) {t : Expr} {s : SEnv} {P P' : AS → Prop}
    (hP : ∀ σ, P σ → P'
      { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp - 8#64),
               slot := upd σ.slot (-(fr.size : Int) - 8) (pc + Int64.ofNat zc).toBitVec }) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (brN2 lbl fr fp ra tp Q Rn pc t s P))
      (At exe endPc R F (callN2 lbl fr fp ra tp Q Rn ((_root_.Executable.labels exe).label g) t s P')) := by
  have h8 := frame_mod8B hf
  refine seg_blk1 (lo := -(fr.size : Int) - 8) (hi := 16) hF hR hlo hhi (hBl _ _ _ _ hb)
    (hWBl _ _ _ _ hb rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) (by simp)
    (okBlk_callq _ _ (by simp [offOk, brN2, oB]; omega)) fun σ c hJ => ⟨c, .refl c, ?_⟩
  show Hit _ (arun _ _ ⟨pc, oB fr, σ⟩) c
  rw [arun_callq]
  obtain ⟨hj, hn, hfj, hr, htp, hp⟩ := hJ
  have hk : (oB fr).sp - 8 = -(fr.size : Int) - 8 := rfl
  refine ⟨rfl, so_le_oB8 fr, ?_, hn, ?_, hr, ?_, ?_⟩
  · show NodeJE _ _ _ _ (upd _ ((oB fr).sp - 8) _) c
    rw [hk]
    exact ⟨hj.1, hj.2.1, hj.2.2.congr fun _ _ _ _ o _ => opdVal_upd_out hf (by omega) _ _ o⟩
  · show FrJ _ _ (upd _ ((oB fr).sp - 8) _)
    rw [hk]; exact frJ_upd_out hfj (by omega) _
  · show (σ.regs.set64 .rsp _).fsBase = tp
    rw [Reg64s.set64_fsBase]; exact htp
  · show P' { σ with regs := _, slot := upd _ ((oB fr).sp - 8) _ }
    rw [hk]; exact hP σ hp

/-- **A bracket node's `%rbp`** at its offset `0` (`at_brN_rbp` at `brN2`). -/
theorem at_brN2_rbp {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {tp : UInt64} {Q Rn : Ctl → Prop} {pc : Int64}
    {t : Expr} {s : SEnv} {P : AS → Prop} {st : State} {c : Ctl}
    (h : At exe endPc R F (brN2 lbl fr fp ra tp Q Rn pc t s P) st c) :
    At exe endPc R F (brN2 lbl fr fp ra tp Q Rn pc t s fun σ => P σ ∧ σ.regs.get64 .rbp = R.addr 0) st c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hj, hen, hfj, hr, htp, hp⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, hj, hen, hfj, hr, htp, hp, hA.so .rbp 0 (by simp [brN2, oB, SO.get, lk])⟩

/-- **The result's store into `r%n`** after the return (`retP_seg` at
`retCP2`, `brN2`). -/
theorem retP_seg2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 Q : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc R F n blk)
    {e : Expr} {s : SEnv} {off : Int} {r : Scc.IR.Reg} (hoff : rsOf fr r = some off)
    {pcR : Int64} {z : Nat} (hc : Cd pcR [(stDir off, z)]) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off))
      (At exe endPc R F (brN2 lbl fr fp ra tp Q (fun c => FrameRunM p (c0, fs) (c, fs)) (pcR + Int64.ofNat z) e s
        fun _ => True)) := by
  let n0 : ND := ⟨pcR, oB fr, (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off).J⟩
  have s0 : SegW W₀ K p lbl ms0 (At exe endPc R F n0)
      (At exe endPc R F (brN2 lbl fr fp ra tp Q (fun c => FrameRunM p (c0, fs) (c, fs)) (pcR + Int64.ofNat z) e s
        fun _ => True)) := by
    refine seg_blk1 hF hR hlo hhi (hCd _ _ hc)
      (hWB n0 _ (SubCd.whole hc) rfl (okBlk_stDir hf h1 hoff z) rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩)
      (by simp) (okBlk_stDir hf h1 hoff z) fun σ c hJ => ⟨c, .refl c, ?_⟩
    show Hit _ (arun _ _ ⟨pcR, oB fr, σ⟩) c
    rw [arun_stDir hf h1 hoff]
    obtain ⟨hj, hen, hfj, hr, htp, -⟩ := hJ
    exact ⟨rfl, so_le_oB fr, hj, hen, frJ_upd hf hfj hoff _, hr, htp, trivial⟩
  exact s0.mono_pre fun st c h => at_rbp_addr (k := 0) h fun σ c hJ => hJ.2.2.2.2.2

/-! ## The callee -/

/-- **The callee inside a plain call of an `Accepted2` body is one
segment** (`calleeP_seg` at `callN2`, `retCP2`): the argument a number by
its leaf layout (`hsc`, `hlit`, `GrpL`), the result by the callee's exit
(`ExitC2B` at the frame's type, `RetL.int`); the caller's facts against the
walk (`EnvQ`) extended by the result at the walk's binding. The callee's
segment (`hcal`, at the call's `g`) gets the return address after the
call's `callq` and the caller pinned at the call site (`CallerAt2`). -/
theorem calleeP_seg2G {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    (hF : FStable R F) (hR : R.OK) {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isa}
    {W : FragS isa} {Bl : Int64 → Nat → Label → Nat → Prop}
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWC : ∀ (n : ND) g dg, p.find? (·.name == g) = some dg →
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    {x g : String} {a : At} {e : Expr} (hT : T (.let_ x (.call g [] a []) e)) (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {t : Ty} {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) (hg : GrpL env)
    {n : Nat} (hfresh : Fresh env n) {off : Int} (hoff : rsOf fr (regName "r" n) = some off)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} (hsc : InLits lits a)
    (hlit : ∀ k, a = .lit k → k < 2 ^ 64)
    {pcB : Int64} {zc k : Nat} (hb : Bl pcB zc (Scc.Lower.Names.user g) k)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (Spike.Lib.Form.lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hLb : LocBaseRegAt (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hcal : ∀ (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF2 p lbl lsize fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      q.ra = (pcB + Int64.ofNat zc).toBitVec →
      CallerAt2 p lbl lsize fr R D fp ra q frm F' c0 (.let_ x (.call g [] a []) e) env lits cs bufs →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab)) :
    SegWS W K p lbl ms
      ((At exe endPc R F (callN2 lbl fr fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv2 env) (callPP fr R w (pcB + Int64.ofNat zc)))).at fs)
      (fun s c fs' => (At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs
          (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
            (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
          (pcB + Int64.ofNat zc) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)).at fs s c fs' ∨
        Ab s c fs') := by
  have h8 := frame_mod8B hf
  have hsp : ((oB fr).sp - 8) - 0 = -(fr.size : Int) - 8 := by simp [oB]
  have hRc : R.callee (((oB fr).sp - 8) - 0) (-D) 8 = calleeR R fr.size D := by rw [hsp]; rfl
  have hsp0 : ((oB fr).sp - 8) - 0 + 0 = -(fr.size : Int) - 8 := by simp [oB]
  obtain ⟨-, dd, hfd0, hretTy⟩ := hcl
  have hfd := hfd0
  rw [hprog] at hfd
  have hop : Scc.Lower.opLit lcx.prog lits (.call g [] a []) = .leaf none := by
    simp only [Scc.Lower.opLit, retShape_of_find hfd0, hretTy]; rfl
  have hgr : Spike.Lib.Form.group .int [.reg (regName "r" n)] = some [.one (.reg (regName "r" n))] := rfl
  have hsa := sevalAt_ofEnv2_one hg ha
  -- the frame's cells are kept by the callee
  have hout : ∀ (r : Scc.IR.Reg) (k' : Int), rsOf fr r = some k' →
      R.Off k' ∧ ¬ (R.callee (((oB fr).sp - 8) - 0) (-D) 8).Off (k' - (((oB fr).sp - 8) - 0)) := by
    intro r k' hk'
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hk'
    rw [hsp]
    exact frame_out hlo hhi hD0 hk2 (by omega) (by omega)
  have hout0 : R.Off 0 ∧ ¬ (R.callee (((oB fr).sp - 8) - 0) (-D) 8).Off (0 - (((oB fr).sp - 8) - 0)) := by
    rw [hsp]; exact frame_out hlo hhi hD0 (by decide) (by omega) (by omega)
  have hout8 : R.Off 8 ∧ ¬ (R.callee (((oB fr).sp - 8) - 0) (-D) 8).Off (8 - (((oB fr).sp - 8) - 0)) := by
    rw [hsp]; exact frame_out hlo hhi hD0 (by decide) (by omega) (by omega)
  refine (call_ndSF (KC := False) (W := W) (K := K) (M := fun _ => True) (F₂ := F)
    (nC := callN2 lbl fr fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
      ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g))
      (.let_ x (.call g [] a []) e) (ofEnv2 env) (callPP fr R w (pcB + Int64.ofNat zc)))
    (γ := CallG) (κ' := Ctl) (e0 := 0) (lo' := -D) (hi' := 8)
    (Ne := fun q _ => calleeN (_root_.Executable.labels exe).label g tp q)
    (Ex := fun q frm c0' => exN2 p lbl tp fs q frm c0')
    (N := fun _ : Unit => retCP2 p lbl R fr fp ra tp c0 fs
      (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
        (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
      (pcB + Int64.ofNat zc) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)
    (E := fun e : Empty => e.elim)
    (fs := fs) (Ab := Ab) hR hF
    (by show R.lo ≤ ((oB fr).sp - 8) - 0 + -D; rw [hsp]; omega) (by omega)
    (by show ((oB fr).sp - 8) - 0 < R.hi; rw [hsp]; omega)
    (by show ((oB fr).sp - 8) - 0 + 8 ≤ R.hi; rw [hsp]; omega)
    (by show (((oB fr).sp - 8) - 0) % 8 = 0; rw [hsp]; omega) (by omega) (by decide)
    (fun h => h.elim) (fun h => h.elim) (fun _ hm _ => hm)
    (hWC _ g dd hfd rfl rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) ?_ (fun _ _ => rfl) ?_ ?_).mono_post ?_
  · -- the callee's segment, from `hcal`
    intro R' F' _ _ _ hFS _ hF'F hR'eq hcells q frm hex hall
    have hR' : R' = calleeR R fr.size D := hR'eq.trans hRc
    subst hR'
    have hra : q.ra = (pcB + Int64.ofNat zc).toBitVec := by
      obtain ⟨σC, c, cE, hJ, -, hNe⟩ := hex
      rw [← hNe.2.2.1]
      show σC.slot ((oB fr).sp - 8 - 0 + 0) = _
      rw [hsp0]; exact hJ.2.2.2.2.2.2.2
    refine (hcal q frm F' hFS ?_ ?_ ?_ ?_ hra ?_).mono_post ?_
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, -, -, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      refine ⟨hF'F m hm, fun k hk hn => hcells m hm k hk ?_, mC, σC, c, _, _, hA, fun k hk hn => hkept k hk ?_,
        hct, hT, hj, ⟨lits, cs, bufs, hen⟩, hfj, ?_⟩
      · show ¬ (calleeR R fr.size D).Off (k - ((oB fr).sp - 8 - 0)); rw [hsp]; exact hn
      · show ¬ (calleeR R fr.size D).Off (k - ((oB fr).sp - 8 - 0)); rw [hsp]; exact hn
      · obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, -, -, hfr1⟩ := id hct
        rw [hj.1] at ht1
        cases ht1
        subst hfr1
        have hne : ∀ y, y ≠ x →
            ((x, Ty.int, [Spike.Lib.Form.WordPl.one (.reg (regName "r" n))]).1 == y) = false := by
          intro y hy; simp only [beq_eq_false_iff_ne]; exact fun h => hy h.symm
        refine ⟨fun y hy hyx => ?_, fun y hy hyx ty pls hl b o hb => ?_, fun y kk v hy hl => ?_⟩
        · have := hIt y hy
          rw [ofEnv2_cons hgr] at this
          simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using this
        · refine hLb y hy ty pls ?_ b o hb
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
      obtain ⟨hj, hen, -, -, -, hP2, -, -⟩ := hJ
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
          rw [hP2] at hv
          cases hv
          rw [← hNe.2.2.2.1]; rfl
        obtain ⟨kk, hkk, hlt⟩ := NumL.one (hl.evalAt' hsc hlit hev1).2 hm1
        exact ⟨d1.arg, d1.argTy, w', by rw [← hNe.1, hcE1], hv' ▸ hvr, kk, hkk, hlt⟩
    · exact ⟨pcB, zc, k, hb, hra⟩
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, hr, -, -, hP3, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      refine ⟨mC, σC, c, hA, fun k hk hn => hkept k hk ?_, hct, hj, hen, hfj, hr, hNe.2.1.symm.trans hP3⟩
      show ¬ (calleeR R fr.size D).Off (k - ((oB fr).sp - 8 - 0)); rw [hsp]; exact hn
    · rintro s c fs' (⟨rfl, c0', hrun, hat⟩ | hab)
      · exact .inl ⟨⟨c0', at_of_rbR (fun σ c h => ⟨hrun, h⟩) hat, trivial⟩, rfl⟩
      · exact .inr hab
  · -- the source's call and the callee's entry
    intro σC c hJ
    obtain ⟨hj, -, -, -, htp, -⟩ := hJ
    obtain ⟨ta, ws', hev, -⟩ := hj.2.2.evalAt (fun _ => rfl) hsa
    exact ⟨⟨σC.regs.rbp.toBitVec, σC.slot ((oB fr).sp - 8 - 0 + 0), σC.regs.rdi.toBitVec,
      ⟨dd.body, [(dd.arg, dd.argTy, ws')], none⟩⟩, _, ⟨x, e, c.env, [], dd.retTy⟩,
      ⟨x, g, a, e, dd, ta, ws', hj.1, hfd, hev, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, htp⟩
  · -- the return: the source returns into `x`, the caller's cells kept
    intro q c0' σC c cE frm σx c' σR hJ hct hNe hEx hregs _ _ hsl
    obtain ⟨hj, hen, hfj, hr, -, -, hP3, hP4⟩ := hJ
    obtain ⟨hrun, ⟨⟨⟨a', t', ws', hta, -, hev', -, hvr, hrbp⟩, hlr⟩, hRL⟩, htpx⟩ := hEx
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
    have hvr' : ValRep lbl w2.val (σR.regs.get64 .rax).toNat := by
      rw [hregs]; exact hvr 0 (by simp) (by simp [Scc.Emit.X64.retRegs])
    refine ⟨⟨e, (x, dd.retTy, [w2]) :: c.env, none⟩, .single hstep, .inl ⟨(), ?_, ?_, ?_⟩⟩
    · show pcB + Int64.ofNat zc = Int64.ofBitVec q.ra
      rw [← hNe.2.2.1]
      show _ = Int64.ofBitVec (σC.slot ((oB fr).sp - 8 - 0 + 0))
      rw [hsp0, hP4, Int64.ofBitVec_toBitVec]
    · show SO.le ⟨-(fr.size : Int), []⟩ ⟨(oB fr).sp - 8 - 0 + 8, []⟩ = true
      simp [SO.le, oB]
    · refine ⟨⟨rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · show Spike.Lib.Form.SRepE lbl _ (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
          ((x, dd.retTy, [w2]) :: c.env)
        rw [ofEnv2_cons hgr, hretTy]
        refine (hj.2.2.congr fun b hb pl hpl o ho => opdVal_upd fun r k' hr' hk' => ?_).bind x rfl
          ⟨⟨_, by simp [opdVal, hoff, upd_apply], hvr'⟩, trivial⟩
        have hne := Fresh.ofEnv2 hfresh "r" b hb pl hpl o ho r hr'
        rw [upd_apply]
        split
        · next hk => subst hk; exact absurd (rsOf_inj hf hk' hoff) hne
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
      · exact ⟨(hsl 0 hout0.1 hout0.2).trans hfj.1, (hsl 8 hout8.1 hout8.2).trans hfj.2⟩
      · exact (FrameRunM.ofLocal hr fs).trans (.step (.frame (hct.step fs))
          (hrun.trans ((FrameRunM.ofLocal hlr _).trans (.single (.frame hstep)))))
      · rw [hregs]; exact htpx
      · rw [hregs]; exact hrbp.trans (hNe.2.1.symm.trans hP3)
  · rintro s c fs' (⟨h, rfl⟩ | hab)
    · exact .inl (h.elim (fun ⟨_, h⟩ => ⟨h, rfl⟩) fun ⟨e, _⟩ => e.elim)
    · exact .inr hab

/-- **The callee inside a plain call of an `Accepted2` body is one
segment** (`calleeP_seg` at `callN2`, `retCP2`): the argument a number by
its leaf layout (`hsc`, `hlit`, `GrpL`), the result by the callee's exit
(`ExitC2B` at the frame's type, `RetL.int`); the caller's facts against the
walk (`EnvQ`) extended by the result at the walk's binding (`calleeP_seg2G`). -/
theorem calleeP_seg2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    (hF : FStable R F) (hR : R.OK) {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isa}
    {W : FragS isa} {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWC : ∀ (n : ND) g dg, p.find? (·.name == g) = some dg →
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF2 p lbl lsize fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      CallSite2 lcx fr Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab))
    {x g : String} {a : At} {e : Expr} (hT : T (.let_ x (.call g [] a []) e)) (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {t : Ty} {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) (hg : GrpL env)
    {n : Nat} (hfresh : Fresh env n) {off : Int} (hoff : rsOf fr (regName "r" n) = some off)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} (hsc : InLits lits a)
    (hlit : ∀ k, a = .lit k → k < 2 ^ 64)
    {pcB : Int64} {zc k : Nat} (hb : Bl pcB zc (Scc.Lower.Names.user g) k)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (Spike.Lib.Form.lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hLb : LocBaseRegAt (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hsite : ∀ q : CallG, q.ra = (pcB + Int64.ofNat zc).toBitVec →
      CallSite2 lcx fr Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q) :
    SegWS W K p lbl ms
      ((At exe endPc R F (callN2 lbl fr fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv2 env) (callPP fr R w (pcB + Int64.ofNat zc)))).at fs)
      (fun s c fs' => (At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs
          (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
            (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
          (pcB + Int64.ofNat zc) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)).at fs s c fs' ∨
        Ab s c fs') :=
  calleeP_seg2G hf hprog hF hR hD0 hD8 hlo hhi hG hWC hT hcl ha hg hfresh hoff hsc hlit hb hIt hIc hLb
    fun q frm F' hFS hCF hex hav hbl hq _ => hcal g q frm F' hFS hCF hex hav hbl (hsite q hq)

/-! ## The call -/

/-- **A plain call of an `Accepted2` body** (`CallC2`; `callC_of` at
`bodyN2`): `callC_of`'s premises, the source's controls in `G0` closed
under the frame runs with memory (`FrameRunM`) at `fs`, and the callee's
segment from `CalleeF2` to its exits at the frame's type (`ExitC2B`), given
the call site with the caller pinned (`CallSite2F`). -/
theorem callC2_ofF {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {W : FragS isa} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    (hF : FStable R F) (hR : R.OK) {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc R F n blk)
    (hWBl : ∀ (n : ND) zc g k, Bl n.pc zc g k → n.o = oB fr → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW W₀ K exe endPc R F n [(i64 (.call (rel g)), zc)])
    (hWC : ∀ (n : ND) g dg, p.find? (·.name == g) = some dg →
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {T : Expr → Prop} (hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = [])
    {i : Expr → String → Nat → Option Nat} {Ab : FragS isa} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF2 p lbl lsize fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      CallSite2F p lbl lsize lcx fr Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q R D fp ra frm F' →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab)) :
    CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk := by
  intro c0 pc pc' kk kk' env n x g is a ts e t w lits cs bufs hc0 hT hfresh hlp hty hg hcnt hcl ha hcode hIt hIc
    hLb hpt
  obtain ⟨rfl, rfl⟩ := hTc _ _ _ _ _ _ hT
  have hG : ∀ c, LocalRun p c0 c → G0 c := fun c h => hG0 c0 c hc0 (FrameRunM.ofLocal h fs)
  have hGR : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c := fun c h => hG0 c0 c hc0 h
  have hlo0 : R.lo ≤ -(fr.size : Int) := by omega
  have hsc : InLits lits a := hlp.1 a (by simp [headAtoms])
  have hlit : ∀ k, a = .lit k → k < 2 ^ 64 := fun k hk => hlp.2.2.2 k (by subst hk; simp [headAtoms])
  obtain ⟨lw, off, zs, zc, z, hlw, hoff, hz, hc1, hb, hc3, -, hp⟩ := instsC2_call hcode
  subst hp
  -- `w`'s load into `%rdi`
  have sA := argP_seg2 (p := p) (lbl := lbl) (lsize := lsize) (K := K) (W₀ := W₀) (ms0 := ms fs) (tp := tp)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (lits := lits) (cs := cs) (bufs := bufs) (i := i)
    hf h1 hF hR hlo0 hhi hCd hG hWB hlw hz hc1
  -- `callq g`
  have sQ := callq_seg2 (p := p) (lbl := lbl) (K := K) (W₀ := W₀) (ms0 := ms fs) (fp := fp) (ra := ra) (tp := tp)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (Q := fun c => EnvQ lits cs bufs lsize c.env)
    (Rn := LocalRun p c0)
    (P := fun σ => opdVal (rsOf fr) σ.slot w = some (σ.regs.get64 .rdi).toNat ∧ σ.regs.get64 .rbp = R.addr 0)
    (P' := callPP fr R w (pc + Int64.ofNat zs.sum + Int64.ofNat zc))
    hf hF hR (by omega) hhi hBl hG hWBl hb fun σ ⟨hp2, hp3⟩ => by
      refine ⟨?_, ?_, ?_⟩
      · show opdVal (rsOf fr) (upd _ _ _) w = some ((σ.regs.set64 .rsp _).get64 .rdi).toNat
        rw [opdVal_upd_out hf (by omega), Reg64s.get64_set64_ne _ (by decide)]; exact hp2
      · show (σ.regs.set64 .rsp _).get64 .rbp = _
        rw [Reg64s.get64_set64_ne _ (by decide)]; exact hp3
      · show upd _ _ _ _ = _
        rw [upd_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have sW := SegWS.liftS (W := W) fs ((sA.mono_post fun _ _ h => at_brN2_rbp h).seq sQ) hW₀
  -- the callee
  have sCal := calleeP_seg2G (p := p) (lbl := lbl) (exe := exe) (endPc := endPc) (K := K) (ms := ms) (W := W)
    (fp := fp) (ra := ra) (tp := tp) (fs := fs) (c0 := c0) (Ab := Ab) (lits := lits) (cs := cs) (bufs := bufs)
    hf hprog hF hR hD0 hD8 hlo hhi hG hWC hT hcl ha hg hfresh hoff hsc hlit hb hIt hIc hLb
    fun q frm F' hFS hCF hex hav hbl hq hpin => hcal g q frm F' hFS hCF hex hav hbl
      ⟨c0, pc, _, kk, kk', env, n, x, a, e, t, w, lits, cs, bufs, lw, zs, zc, hc0, hT, hfresh, hlp,
        hty, hg, hcnt, hcl, ha, hcode, hlw, hz, hc1, hb, hq, hpt, hpin⟩
  -- the result's store
  have sR := SegWS.liftS (W := W) fs (retP_seg2 (p := p) (lbl := lbl) (K := K) (W₀ := W₀) (ms0 := ms fs)
    (fp := fp) (ra := ra) (tp := tp) (e := e) (s := ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
    (Q := fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
      (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
    hf h1 hF hR hlo0 hhi hCd hGR hWB hoff hc3) hW₀
  refine (sW.seq (SegWS.seq_left sCal sR)).mono_post ?_
  rintro s c fs' (⟨⟨he, hn, hdc, hpc, σ, hA, hD, hj, ⟨hl, hS, L, sm, B, hbB, hmB⟩, hfj, hr, htp, -⟩, rfl⟩ | hab)
  · exact .inl ⟨rfl, c, hr, he, hn, hdc, hpc, σ, hA, hD,
      ⟨⟨L, sm, B, NJB.of_nodeJE hj hl hbB hmB hS⟩, hfj, .refl c, SlotRepAt.of_nodeJE hj hIt hLb hIc⟩, htp⟩
  · exact .inr hab

/-- **A plain call of an `Accepted2` body** (`CallC2`; `callC_of` at
`bodyN2`): `callC_of`'s premises, the source's controls in `G0` closed
under the frame runs with memory (`FrameRunM`) at `fs`, and the callee's
segment from `CalleeF2` to its exits at the frame's type (`ExitC2B`)
(`callC2_ofF`). -/
theorem callC2_of {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {W : FragS isa} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    (hF : FStable R F) (hR : R.OK) {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc R F n blk)
    (hWBl : ∀ (n : ND) zc g k, Bl n.pc zc g k → n.o = oB fr → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW W₀ K exe endPc R F n [(i64 (.call (rel g)), zc)])
    (hWC : ∀ (n : ND) g dg, p.find? (·.name == g) = some dg →
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {T : Expr → Prop} (hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = [])
    {i : Expr → String → Nat → Option Nat} {Ab : FragS isa} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF2 p lbl lsize fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      CallSite2 lcx fr Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab)) :
    CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk :=
  callC2_ofF hf h1 hprog hF hR hD0 hD8 hlo hhi hCd hBl hW₀ hG0 hWB hWBl hWC hTc
    fun g q frm F' hFS hCF hex hav hbl hs => hcal g q frm F' hFS hCF hex hav hbl hs.toCallSite2

end Call

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.calleeP_seg2G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.calleeP_seg2G

/-- info: 'Spike.Lib.LowerX64.calleeP_seg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.calleeP_seg2

/-- info: 'Spike.Lib.LowerX64.callC2_ofF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callC2_ofF

/-- info: 'Spike.Lib.LowerX64.callC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callC2_of
