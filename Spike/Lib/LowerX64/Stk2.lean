/-
**The suspended frames of an `Accepted2` program** (x86-64; the twin of
`Spike/Lib/LowerA64/Stk2.lean`): the static stack invariant of the levels
(`nodes2_of_starts`' `h1`): at a landing, besides the running code's
context, each suspended frame `f` of the source's frames `fs` has a record
`StkFr` of its caller's context at the call, so that it resumes from its
return node as a segment of its body (from `BodyPt`'s continuation). No
coinduction: the records are static data, threaded by depth.

- `StkFr`: one suspended caller: its compiled block `j`, its context
  (region `R`, frame condition `F`, saved pair `fp`/`ra`, thread pointer
  `tp`, ghosts `G0`, aborts `Ab`), its ghost `c0`, the call's ghost `q`
  (`q.ra` the return site), the callee's room `D`, and its resumption point
  at the call (`pc`, the call term `t`, `env`, `n`, `lits`, `cs`, `bufs`;
  `BodyPt`'s arguments).
- `StkFrOk`: a record's facts at the frame above's region and frame
  condition (the key `(R', F')`): the caller's context in `CxOk j`, `RaOk`
  of its return address, its ghost in `G0`, the call a resumption point of
  its block, the frame above in the callee's region below the caller's
  frame and the return address at room `D` (`calleeR (rbR R) frame D`:
  `R` the caller's context's entry region, its body's the rebased `rbR R`),
  its frame condition the caller's at the call (`CalleeF2` in `rbR R`), the
  return site after the call's `callq`.
- `StkKey`, `StkFr.key`, `StkLink`: a running frame's key (block, region,
  frame condition, saved pair, thread pointer, ghosts); the frame above a
  record linked to it (the call's pair, ghosts from the call's entry
  control, `int` return), `StkFrOk.link`.
- `StkOk`: `StkOkB StkFrOk` (`Spike/Lib/Src/Stk2.lean`): the records
  aligned with `fs` above some bottom frames `Bot`, chained by the records'
  own keys.
- `CxOkS`: a context with its suspended frames: `CxOk` and some `StkOk` at
  its key; `CxOkS.bot`: no records at the bottom frames; `CxOkS.cx`,
  `CxOkS.call`: a call pushes the caller's record; `CxOkS.callSite`: the record pushed at a
  plain call's site (`CallSite2F`); `StkOk.uncons`, `StkFrOk.cx`: a return
  pops it; `StkFrOk.pin`: a record's resumption data (`callC2_resume`'s
  premises).
- `StkRoomX`, `stkRoomX_of_le`, `limOk_callee_ofStk`: the stack-depth bound
  `lim ≤ (rsp − 8 − fsz).toNat` (at `lim = stacksA + 4096`
  `limOk_callee_ofPlaceOK`'s `hZ`) from `lim + 8 + fsz ≤ rsp.toNat`.
- `hlim_ofStk`, `proEdge2_ofCallee_ofStk`: a callee's prologue edge at any
  depth, its limit facts from the stack-depth bound at its entry states, the
  frame condition within `rtF` and the call's thread pointer the first
  thread's.
-/
import Spike.Lib.Src.Stk2
import Spike.Lib.LowerX64.BodyPt2
import Spike.Lib.LowerX64.CallC2
import Spike.Lib.LowerX64.LimOk0
import Spike.Lib.LowerX64.ProEdge2Callee

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.LowerNode

/-! ## The records -/

/-- **A suspended caller's record** (see the module docstring): its
compiled block `j`, its context at the call, its ghost `c0`, the call's
ghost `q`, the callee's room `D`, its resumption point at the call. -/
structure StkFr where
  j : Nat
  R : Region
  F : MachineData → Prop
  fp : BitVec 64
  ra : BitVec 64
  tp : UInt64
  G0 : Ctl → Prop
  Ab : FragS isa
  c0 : Ctl
  q : CallG
  D : Int
  pc : Int64
  t : Expr
  env : Scc.Lower.Env
  n : Nat
  lits : List (String × Scc.Lower.LitV)
  cs : List (String × Nat)
  bufs : List (String × Nat)

/-- **A running frame's key**: its compiled block `j`, region `R` (its
context's entry region), frame condition `F`, saved pair `fp`/`ra`, thread
pointer `tp` and ghosts `G0` (the record above it is checked against it:
`StkFrOk`). -/
structure StkKey where
  j : Nat
  R : Region
  F : MachineData → Prop
  fp : BitVec 64
  ra : BitVec 64
  tp : UInt64
  G0 : Ctl → Prop

/-- The key a record's frame runs at (the key of the frames below it). -/
def StkFr.key (a : StkFr) : StkKey := ⟨a.j, a.R, a.F, a.fp, a.ra, a.tp, a.G0⟩

section Stk

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}

/-- **The frame above linked to a record** (`callC2_resume`'s callee
segment from the frame above's exits): the frame above saved the call's
pair (`q.fp`, `q.ra`) at the record's thread pointer, its ghosts reached
from the call's entry control `q.cE` by a frame run at `f :: fs`, its block
(in `P`) returning `int` as the frame `f` does. -/
def StkLink (p P : Prog) (k : StkKey) (a : StkFr) (f : TermRun.Frame) (fs : List TermRun.Frame) : Prop :=
  k.fp = a.q.fp ∧ k.ra = a.q.ra ∧ k.tp = a.tp ∧
    (∀ c, k.G0 c → FrameRunM p (a.q.cE, f :: fs) (c, f :: fs)) ∧
    (∃ dg, P[k.j]? = some dg ∧ dg.retTy = .int) ∧ f.ty = .int

/-- **A record's facts** at the frame above's key `k` (its region `k.R`
and frame condition `k.F`), for the frame `f` it suspends and the frames `fs` below:
the caller's context (`CxOk j` at `fs`), its return address, its ghost, the
call a resumption point of its block `hcode j d hd`, the frame above in the
callee's region at room `D` (`calleeR` of the caller's body's rebased region
`rbR a.R`, `a.R` its context's entry region), under the caller's frame
condition at the call (`CalleeF2` in `rbR a.R`, with `f` the call's frame), the return site after
the call's `callq`, and the call term's: a plain call `let x = g(b)`
whose argument's word `w` loads into `%rdi` by `lw` (its sizes `zs`), the
`callq g` (its size `zc`) after it, the return site past both
(`CallSite2`'s). The resumption point states the body's walk facts at it
(`BodyPtW`). Last, the callee a code block (`Callee`), the caller pinned
at the record's data (`CallerAt2`), for the caller's resumption
(`callC2_resume`), and the frame above linked to the record (`StkLink`). -/
def StkFrOk (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop)
    (k : StkKey) (a : StkFr) (f : TermRun.Frame) (fs : List TermRun.Frame) : Prop :=
  ∃ (d : Decl) (hd : P[a.j]? = some d),
    CxOk a.j a.R a.F fs a.fp a.ra a.tp a.G0 a.Ab ∧ RaOk a.ra ∧ a.G0 a.c0 ∧
    BodyPtW (hcode a.j d hd) a.ra a.pc a.t a.env a.n a.lits a.cs a.bufs ∧
    0 ≤ a.D ∧ a.D % 8 = 0 ∧ (rbR a.R).lo ≤ -((hcode a.j d hd).fr.size : Int) - 8 - a.D ∧
    k.R = calleeR (rbR a.R) (hcode a.j d hd).fr.size a.D ∧ FStable k.R k.F ∧
    CalleeF2 p lbl lsize (hcode a.j d hd).fr (rbR a.R) a.F a.D a.fp a.ra i (T a.j) a.q f k.F ∧
    (∃ pcB zc kk g, (hcode a.j d hd).Bl a.ra pcB zc (Scc.Lower.Names.user g) kk ∧
      a.q.ra = (pcB + Int64.ofNat zc).toBitVec) ∧
    (∃ (x g : String) (b : At) (e : Expr) (t : Ty) (w : Scc.IR.Operand) (lw : List Scc.Emit.X64.Item)
      (zs : List Nat) (zc kk : Nat),
      a.t = .let_ x (.call g [] b []) e ∧ Scc.Lower.Inv.atomV a.env b = some (t, [w]) ∧
      getOp (hcode a.j d hd).fr .rdi w = .ok lw ∧ zs.length = (dirs lw).length ∧
      Cd a.ra a.pc ((dirs lw).zip zs) ∧
      (hcode a.j d hd).Bl a.ra (a.pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) kk ∧
      a.q.ra = (a.pc + Int64.ofNat zs.sum + Int64.ofNat zc).toBitVec) ∧
    (∀ x g b e, a.t = .let_ x (.call g [] b []) e → Spike.Lib.LowerCall.Callee (hcode a.j d hd).lcx g) ∧
    CallerAt2 p lbl lsize (hcode a.j d hd).fr (rbR a.R) a.D a.fp a.ra a.q f k.F a.c0 a.t a.env a.lits a.cs a.bufs ∧
    StkLink p P k a f fs

/-- **The suspended frames' records** at the running frame's key `k`:
`StkFrOk` aligned with `fs` above some bottom frames (`Bot` at the last
key), chained by the records' keys. -/
def StkOk (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop)
    (Bot : StkKey → List TermRun.Frame → Prop) (k : StkKey) (st : List StkFr) (fs : List TermRun.Frame) : Prop :=
  StkOkB (StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk) StkFr.key Bot k st fs

/-- **A context with its suspended frames**: `CxOk j` and records of the
frames `fs` at its region and frame condition. The shape of `FnSpecC2`'s
context argument. -/
def CxOkS (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop) (Bot : StkKey → List TermRun.Frame → Prop) (j : Nat)
    (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isa) : Prop :=
  CxOk j R F fs fp ra tp G0 Ab ∧
    ∃ st, StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot ⟨j, R, F, fp, ra, tp, G0⟩ st fs

variable {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
  {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop}

/-- **At the bottom frames, no records**: a context whose frames are the
bottom ones at its key (`Bot`; at no frames the depth-`0` context; at the
setup wrapper's frame, `main` under the setup block). -/
theorem CxOkS.bot {j : Nat} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64}
    {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa} (h : CxOk j R F fs fp ra tp G0 Ab)
    (hB : Bot ⟨j, R, F, fp, ra, tp, G0⟩ fs) :
    CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j R F fs fp ra tp G0 Ab :=
  ⟨h, [], StkOkB.bot hB⟩

/-- A context with its suspended frames is a context. -/
theorem CxOkS.cx {j : Nat} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64}
    {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (h : CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j R F fs fp ra tp G0 Ab) :
    CxOk j R F fs fp ra tp G0 Ab := h.1

/-- **A call pushes the caller's record**: from the caller's records at
its own key (`a.key`) and the record's facts at the callee's key, the
callee's context `CxOk j'` at `f :: fs` has the records `a :: st`. -/
theorem CxOkS.call {a : StkFr} {st : List StkFr} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (hst : StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot a.key st fs)
    {j' : Nat} {R' : Region} {F' : MachineData → Prop} {fp' ra' : BitVec 64} {tp' : UInt64}
    {G0' : Ctl → Prop} {Ab' : FragS isa}
    (ha : StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk ⟨j', R', F', fp', ra', tp', G0'⟩ a f fs)
    (hc : CxOk j' R' F' (f :: fs) fp' ra' tp' G0' Ab') :
    CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j' R' F' (f :: fs) fp' ra' tp' G0' Ab' :=
  ⟨hc, a :: st, StkOkB.cons ha hst⟩

/-- **The callee's context with its suspended frames at a plain call**
(`CxOkS.call` at the call site's record): from the caller's context with
its records (`CxOkS j` at `fs`, `RaOk ra`), the call site of `g` returning
to `q.ra` in block `j` (`CallSite2F` at the block's code facts, the literal
walk's facts with `RetLk` at the block's return type, in the body's
rebased region `rbR R`), the callee's room `D`, its frame condition `F'`
the caller's at the call (`CalleeF2` in `rbR R`, stable in the callee's
region `calleeR (rbR R) frame D`) and the return site after the call's `callq`, the
callee's context `CxOk j'` at `f :: fs` has records: the caller's record at
the call pushed (its resumption point `BodyPtW` from `PtC2`, the ra link
from the argument's load and the `callq`, the pinned caller from
`CallSite2F`), linked to the callee's key (`StkLink`: the call's saved
pair, the thread pointer, the callee's ghosts from the call's entry
control, an `int` block and frame). -/
theorem CxOkS.callSite {j : Nat} {d : Decl} (hd : P[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hcx : CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j R F fs fp ra tp G0 Ab) (hra : RaOk ra)
    {g : String} {q : CallG}
    {D : Int} {f : TermRun.Frame} {F' : MachineData → Prop}
    (hs : CallSite2F p lbl lsize (hcode j d hd).lcx (hcode j d hd).fr (Cd ra) ((hcode j d hd).Bl ra) G0 (T j)
      (_root_.Executable.labels exe).label i (RetLk d.retTy) g q (rbR R) D fp ra f F')
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : (rbR R).lo ≤ -((hcode j d hd).fr.size : Int) - 8 - D)
    (hF' : FStable (calleeR (rbR R) (hcode j d hd).fr.size D) F')
    (hCF : CalleeF2 p lbl lsize (hcode j d hd).fr (rbR R) F D fp ra i (T j) q f F')
    (hbl : ∃ pcB zc kk, (hcode j d hd).Bl ra pcB zc (Scc.Lower.Names.user g) kk ∧
      q.ra = (pcB + Int64.ofNat zc).toBitVec)
    {j' : Nat} {fp' ra' : BitVec 64} {tp' : UInt64} {G0' : Ctl → Prop} {Ab' : FragS isa}
    (hc : CxOk j' (calleeR (rbR R) (hcode j d hd).fr.size D) F' (f :: fs) fp' ra' tp' G0' Ab')
    (hfp : fp' = q.fp) (hra' : ra' = q.ra) (htp : tp' = tp)
    (hG0' : ∀ c, G0' c → FrameRunM p (q.cE, f :: fs) (c, f :: fs))
    (hj' : ∃ dg, P[j']? = some dg ∧ dg.retTy = .int) (hfty : f.ty = .int) :
    CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j' (calleeR (rbR R) (hcode j d hd).fr.size D)
      F' (f :: fs) fp' ra' tp' G0' Ab' := by
  obtain ⟨hcj, st, hst⟩ := hcx
  obtain ⟨c0, pc, pc', kk, kk', env, n, x, a, e, t, w, lits, cs, bufs, lw, zs, zc, hc0, -, hfr, -, -, -, -, hcl,
    ha, -, hlw, hz, hc1, hb, hq, ⟨l, k, r, hr, hcode', hblk, hW, hL, hC, hX⟩, hpin⟩ := hs
  obtain ⟨pcB, zcB, kB, hB, hqB⟩ := hbl
  let rec_ : StkFr := ⟨j, R, F, fp, ra, tp, G0, Ab, c0, q, D, pc, .let_ x (.call g [] a []) e, env, n, lits, cs,
    bufs⟩
  exact CxOkS.call (a := rec_) hst
    ⟨d, hd, hcj, hra, hc0, ⟨l, k, r, kk, hr, hfr, hcode', hblk, hW, hL, hC, hX⟩, hD0, hD8, hlo, rfl, hF', hCF,
      ⟨pcB, zcB, kB, g, hB, hqB⟩, ⟨x, g, a, e, t, w, lw, zs, zc, kk, rfl, ha, hlw, hz, hc1, hb, hq⟩,
      fun _ _ _ _ he => by cases he; exact hcl, hpin, hfp, hra', htp, hG0', hj', hfty⟩ hc

/-- **A return pops the record**: the top record's facts at the running
frame's key and the caller's records at the record's. -/
theorem StkOk.uncons {k : StkKey} {a : StkFr} {st : List StkFr} {f : TermRun.Frame}
    {fs : List TermRun.Frame}
    (h : StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot k (a :: st) (f :: fs)) :
    StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk k a f fs ∧
      StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot a.key st fs := h

/-- **The suspended caller's context** of a record. -/
theorem StkFrOk.cx {k : StkKey} {a : StkFr} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (h : StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk k a f fs) :
    CxOk a.j a.R a.F fs a.fp a.ra a.tp a.G0 a.Ab ∧ RaOk a.ra := by
  obtain ⟨_, _, hc, hra, -⟩ := h
  exact ⟨hc, hra⟩

/-- **A record's resumption data** (`callC2_resume`'s premises at the
record): the call term `let x = g(b)` at the resumption point (`BodyPtW`),
`g` a callee, `b`'s word `w` loaded by `lw` of sizes `zs`, the `callq` of
size `zc`, the return address after it, the frame above's frame condition
inside the caller's (`CalleeF2`) and the caller pinned at the record's data
(`CallerAt2`). -/
theorem StkFrOk.pin {k : StkKey} {a : StkFr} {f : TermRun.Frame}
    {fs : List TermRun.Frame} (h : StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk k a f fs) :
    ∃ (d : Decl) (hd : P[a.j]? = some d) (x g : String) (b : At) (e : Expr) (t : Ty) (w : Scc.IR.Operand)
      (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc kk : Nat), a.t = .let_ x (.call g [] b []) e ∧
      BodyPtW (hcode a.j d hd) a.ra a.pc a.t a.env a.n a.lits a.cs a.bufs ∧
      0 ≤ a.D ∧ (rbR a.R).lo ≤ -((hcode a.j d hd).fr.size : Int) - 8 - a.D ∧
      k.R = calleeR (rbR a.R) (hcode a.j d hd).fr.size a.D ∧
      Spike.Lib.LowerCall.Callee (hcode a.j d hd).lcx g ∧ Scc.Lower.Inv.atomV a.env b = some (t, [w]) ∧
      getOp (hcode a.j d hd).fr .rdi w = .ok lw ∧ zs.length = (dirs lw).length ∧
      Cd a.ra a.pc ((dirs lw).zip zs) ∧
      (hcode a.j d hd).Bl a.ra (a.pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) kk ∧
      a.q.ra = (a.pc + Int64.ofNat zs.sum + Int64.ofNat zc).toBitVec ∧
      (∀ m, k.F m → a.F m) ∧
      CallerAt2 p lbl lsize (hcode a.j d hd).fr (rbR a.R) a.D a.fp a.ra a.q f k.F a.c0 a.t a.env a.lits a.cs
        a.bufs := by
  obtain ⟨d, hd, -, -, -, hb, h0, -, hlo, hk, -, hcal, -, ⟨x, g, b, e, t, w, lw, zs, zc, kk, ht, ha, hw, hz, hc1, hbl,
    hq⟩, hcl, hpin, -⟩ := h
  exact ⟨d, hd, x, g, b, e, t, w, lw, zs, zc, kk, ht, hb, h0, hlo, hk, hcl x g b e ht, ha, hw, hz, hc1, hbl, hq,
    fun m hm => (hcal m hm).1, hpin⟩

/-- **The frame above linked to a record** (`StkLink`). -/
theorem StkFrOk.link {k : StkKey} {a : StkFr} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (h : StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk k a f fs) : StkLink p P k a f fs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hl⟩ := h
  exact hl

end Stk

/-! ## The stack-depth bound -/

/-- **The stack-depth bound** at a state: the new frame's `%rsp` (`%rsp`
less the return address and the frame `fsz`) at least `lim`
(`limOk_callee_ofPlaceOK`'s `hZ` at `lim = stacksA + 4096`). -/
def StkRoomX (lim : Nat) (σ : AS) (fsz : Int) : Prop :=
  lim ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fsz).toBitVec).toNat

/-- **The bound from room below `%rsp`**: a frame `0 ≤ fsz < 2^63` and
`lim + 8 + fsz ≤ rsp`. -/
theorem stkRoomX_of_le {lim : Nat} {σ : AS} {fsz : Int} (h0 : 0 ≤ fsz) (h1 : fsz < 2 ^ 63)
    (h : lim + 8 + fsz.toNat ≤ σ.regs.rsp.toBitVec.toNat) : StkRoomX lim σ fsz := by
  unfold StkRoomX
  have he : (Int64.ofInt fsz).toBitVec.toNat = fsz.toNat := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    have : fsz % (2 ^ 64 : Nat) = fsz := Int.emod_eq_of_lt h0 (by omega)
    rw [this]
  have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hs1 : (σ.regs.rsp.toBitVec - 8#64).toNat = σ.regs.rsp.toBitVec.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h8]; omega), h8]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, he, hs1]; omega), he, hs1]
  omega

section Place

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
  {labelOffs : List (String × Nat)}

open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64ConsumerS (msOfS)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (μ)

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.X64.PhRec.GOf (Ly h) (Spike.Lib.X64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) (G0 h)
  (fun s _ => Spike.Lib.X64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The first thread's pointer. -/
local notation "TP0" h:max => tpOf (Ret0.pinA (_root_.Executable.labels (Ly h).exe).label + 0#64 + 8#64)

/-- **A callee's prologue limit facts at any depth** (`limOk_callee_ofPlaceOK`
at `StkRoomX`): at the first thread, under a frame condition within `rtF`,
at a state with the stack-depth bound at the first stack's limit. -/
theorem limOk_callee_ofStk {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly h) (Ly h).Λ.static (fun _ => 0))
    {F : MachineData → Prop} (hF : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly h) m) (fs : List TermRun.Frame)
    {σ : AS} (hfs : σ.regs.fsBase = TP0 h) {fsz : Int}
    (hZ : StkRoomX ((Ly h).stacksA.toNat + 4096) σ fsz) :
    Ret0.LimOk ((MSS h) fs) F (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fsz).toBitVec) :=
  limOk_callee_ofPlaceOK h hfree hF fs hfs hZ

/-- **`proEdge2_ofCallee`'s limit facts at any depth** (`hlim` from
`limOk_callee_ofStk`): at the placement's memory side at the frames `fs`,
under a frame condition within `rtF` (`hF`), the call's thread pointer the
first thread's (`htp`), every entry state of `J` (within the callee's entry
`calleeN`, `hJ`) with the stack-depth bound for the callee's frame
(`hZ`). -/
theorem hlim_ofStk {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly h) (Ly h).Λ.static (fun _ => 0))
    {F : MachineData → Prop} (hF : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly h) m) (fs : List TermRun.Frame)
    {exe : _root_.Executable} {g : String} {tp : UInt64} {q : CallG} (htp : tp = TP0 h)
    {J : AS → Ctl → Prop} (hJ : ∀ σ c', J σ c' → (calleeN (_root_.Executable.labels exe).label g tp q).J σ c')
    {fsz : Int} (hZ : ∀ σ c', J σ c' → StkRoomX ((Ly h).stacksA.toNat + 4096) σ fsz) :
    ∀ σ c', J σ c' →
      Ret0.LimOk ((MSS h) fs) F (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec)
        (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fsz).toBitVec) := fun σ c' hσ => by
  obtain ⟨-, -, -, -, hfs⟩ := hJ σ c' hσ
  exact limOk_callee_ofStk h hfree hF fs (hfs.trans htp) (hZ σ c' hσ)

/-- **A callee's prologue edge at any depth** (`proEdge2_ofCallee` at
`hlim_ofStk`): its premises, with the limit facts from the stack-depth
bound at the entry states (`hZ`), the frame condition within `rtF` (`hF`)
and the call's thread pointer the first thread's (`htp`). -/
theorem proEdge2_ofCallee_ofStk {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly h) (Ly h).Λ.static (fun _ => 0))
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (hint : d.argTy = .int)
    (henv : c.env = Spike.Lib.LowerShape.env2 d 1)
    (hlits : c.lits = (Scc.Lower.params2 d).map (·, Scc.Lower.shapeOf d.argTy)) {zs : List Nat}
    (hs : Scc.Cert.Code1X64.spills c.fr (Spike.Lib.LowerShape.paramsR d 1) zs = some c.ps)
    {g : String} {tp : UInt64} {q : CallG} (harg : ArgV lbl q) {ws : List TermRun.Word}
    (hcE : q.cE = ⟨d.body, [(d.arg, d.argTy, ws)], none⟩)
    {F : MachineData → Prop} (hF : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly h) m) (fs : List TermRun.Frame)
    (htp : tp = TP0 h) {J : AS → Ctl → Prop}
    (hJ : ∀ σ c', J σ c' → (calleeN (_root_.Executable.labels exe).label g tp q).J σ c')
    (hZ : ∀ σ c', J σ c' → StkRoomX ((Ly h).stacksA.toNat + 4096) σ c.fr.size) :
    ProEdge2 p lbl lsize ((MSS h) fs) F c q.fp q.ra tp q.cE J :=
  proEdge2_ofCallee c hint henv hlits hs harg hcE hJ (hlim_ofStk h hfree hF fs htp hJ hZ)

end Place

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.CxOkS.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CxOkS.call

/-- info: 'Spike.Lib.LowerX64.CxOkS.bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CxOkS.bot

/-- info: 'Spike.Lib.LowerX64.CxOkS.callSite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CxOkS.callSite

/-- info: 'Spike.Lib.LowerX64.StkFrOk.pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.StkFrOk.pin

/-- info: 'Spike.Lib.LowerX64.stkRoomX_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stkRoomX_of_le

/-- info: 'Spike.Lib.LowerX64.limOk_callee_ofStk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.limOk_callee_ofStk
/-- info: 'Spike.Lib.LowerX64.hlim_ofStk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hlim_ofStk

/-- info: 'Spike.Lib.LowerX64.proEdge2_ofCallee_ofStk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proEdge2_ofCallee_ofStk
