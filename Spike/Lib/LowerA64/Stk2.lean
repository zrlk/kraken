/-
**The suspended frames of an `Accepted2` program** (AArch64): the static
stack invariant of the levels (`nodes2_of_starts`' `h1`, design A): at a
landing, besides the running code's context, each suspended frame `f` of
the source's frames `fs` has a record `StkFr` of its caller's context at
the call, so that it resumes from its return node (`retCN2`) as a segment
of its body (`bodyAtPt2` from `BodyPt.call`'s continuation). No
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
  frame at room `D` (`R.callee (-frame) (-D) 0`), its frame condition the
  caller's at the call (`CalleeF2`), the return site after the call's `bl`
  and after the call term's argument load (the ra link); the resumption
  point with its walk facts stated (`BodyPtW`).
- `StkKey`, `StkFr.key`, `StkLink`: a running frame's key (block, region,
  frame condition, saved pair, thread pointer, ghosts); the frame above a
  record linked to it (the call's pair, ghosts from the call's entry
  control, `int` return), `StkFrOk.link`.
- `StkOk`: `StkOkB StkFrOk` (`Spike/Lib/Src/Stk2.lean`): the records
  aligned with `fs` above some bottom frames `Bot`, chained by the records'
  own keys.
- `CxOkS`: a context with its suspended frames: `CxOk` and some `StkOk` at
  its key; `CxOkS.bot`: no records at the bottom frames; `CxOkS.cx`, `CxOkS.call`: a call pushes
  the caller's record (the callee's stack is the return site's record on
  the caller's); `CxOkS.callSite`: the record pushed at a plain call's
  site (`CallSite2F`, `PtC2`); `StkFrOk.pin`: a record's resumption data
  (`callC2_resume`'s premises).
- `StkRoomA`, `stkRoomA_of_le`, `limOk_callee_ofStk`: the stack-depth bound
  `lim ≤ (SP − fsz).toNat` (at `lim = stacksA + 4096`
  `limOk_callee_ofPlaceOK`'s `hZ`) from `lim + fsz ≤ SP.toNat`.

The x64 twin (`Spike/Lib/LowerX64/Stk2.lean`) has the same shape with the
return address slot: the bound is `lim ≤ (rsp − 8 − fsz).toNat`, the
thread pointer `fsBase`.
-/
import Spike.Lib.Src.Stk2
import Spike.Lib.LowerA64.BodyPt2
import Spike.Lib.LowerA64.CallC2
import Spike.Lib.LowerA64.LimOk0

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
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
  Ab : FragS isaLSE2
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

/-- **A running frame's key**: its compiled block `j`, region `R`, frame
condition `F`, saved pair `fp`/`ra`, thread pointer `tp` and ghosts `G0`
(the record above it is checked against it: `StkFrOk`). -/
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
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
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

/-- **A record's facts** at the frame above's region and frame condition
`k = (R', F')`, for the frame `f` it suspends and the frames `fs` below:
the caller's context (`CxOk j` at `fs`), its return address, its ghost, the
call a resumption point of its block `hcode j d hd`, the frame above in the
callee's region at room `D`, under the caller's frame condition at the call
(`CalleeF2`, with `f` the call's frame), the return site after the call's
`bl`, and the call term's: a plain call `let x = g(b)` whose argument's word
`w` loads into `x0` by `lw`, the return site `lw`'s length past `pc`
(`CallSite2`'s). The resumption point states the body's walk facts at it
(`BodyPtW`). Last, the callee a code block (`Callee`) and the caller pinned
at the record's data (`CallerAt2`), for the caller's resumption
(`callC2_resume`). -/
def StkFrOk (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop)
    (k : StkKey) (a : StkFr) (f : TermRun.Frame) (fs : List TermRun.Frame) : Prop :=
  ∃ (d : Decl) (hd : P[a.j]? = some d),
    CxOk a.j a.R a.F fs a.fp a.ra a.tp a.G0 a.Ab ∧ RaOk a.ra ∧ a.G0 a.c0 ∧
    BodyPtW (hcode a.j d hd) a.ra a.pc a.t a.env a.n a.lits a.cs a.bufs ∧
    0 ≤ a.D ∧ a.D % 8 = 0 ∧ a.R.lo ≤ -((hcode a.j d hd).cx.frame : Int) - a.D ∧
    k.R = a.R.callee (-((hcode a.j d hd).cx.frame : Int)) (-a.D) 0 ∧ FStable k.R k.F ∧
    CalleeF2 p lbl lsize (hcode a.j d hd).cx a.R a.F a.D a.fp a.ra i (T a.j) a.q f k.F ∧
    (∃ pcB kk g, (hcode a.j d hd).Bl a.ra pcB (Scc.Lower.Names.user g) kk ∧ a.q.ra = (pcB + 4).toBitVec) ∧
    (∃ (x g : String) (b : At) (e : Expr) (t : Ty) (w : Scc.IR.Operand) (lw : List Item),
      a.t = .let_ x (.call g [] b []) e ∧ Scc.Lower.Inv.atomV a.env b = some (t, [w]) ∧
      (hcode a.j d hd).cx.getOp .X0 w = .ok lw ∧
      a.q.ra = (a.pc + Int64.ofNat (4 * (directives lw).length) + 4).toBitVec) ∧
    (∀ x g b e, a.t = .let_ x (.call g [] b []) e → Spike.Lib.LowerCall.Callee (hcode a.j d hd).lcx g) ∧
    CallerAt2 p lbl lsize (hcode a.j d hd).cx a.R a.D a.fp a.ra a.q f k.F a.c0 a.t a.env a.lits a.cs a.bufs ∧
    StkLink p P k a f fs

/-- **The suspended frames' records** at the running frame's region and
frame condition `k`: `StkFrOk` aligned with `fs`, chained by the records'
keys. -/
def StkOk (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop)
    (Bot : StkKey → List TermRun.Frame → Prop) (k : StkKey) (st : List StkFr) (fs : List TermRun.Frame) : Prop :=
  StkOkB (StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk) StkFr.key Bot k st fs

/-- **A context with its suspended frames**: `CxOk j` and records of the
frames `fs` at its region and frame condition. The shape of `FnSpecC2`'s
context argument. -/
def CxOkS (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop) (Bot : StkKey → List TermRun.Frame → Prop) (j : Nat)
    (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isaLSE2) : Prop :=
  CxOk j R F fs fp ra tp G0 Ab ∧
    ∃ st, StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot ⟨j, R, F, fp, ra, tp, G0⟩ st fs

variable {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
  {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop}

/-- **At the bottom frames, no records**: a context whose frames are the
bottom ones at its key (`Bot`; at no frames the depth-`0` context,
`mainCtxB`'s; at the setup wrapper's frame, `main` under the setup block). -/
theorem CxOkS.bot {j : Nat} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64}
    {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2} (h : CxOk j R F fs fp ra tp G0 Ab)
    (hB : Bot ⟨j, R, F, fp, ra, tp, G0⟩ fs) :
    CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j R F fs fp ra tp G0 Ab :=
  ⟨h, [], StkOkB.bot hB⟩

/-- A context with its suspended frames is a context. -/
theorem CxOkS.cx {j : Nat} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64}
    {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (h : CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j R F fs fp ra tp G0 Ab) :
    CxOk j R F fs fp ra tp G0 Ab := h.1

/-- **A call pushes the caller's record**: from the caller's records at
its own region and frame condition (`a.key`) and the record's facts at the
callee's key, the callee's context `CxOk j'` at `f :: fs` has the records
`a :: st`. -/
theorem CxOkS.call {a : StkFr} {st : List StkFr} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (hst : StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot a.key st fs)
    {j' : Nat} {R' : Region} {F' : MachineData → Prop} {fp' ra' : BitVec 64} {tp' : UInt64}
    {G0' : Ctl → Prop} {Ab' : FragS isaLSE2}
    (ha : StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk ⟨j', R', F', fp', ra', tp', G0'⟩ a f fs)
    (hc : CxOk j' R' F' (f :: fs) fp' ra' tp' G0' Ab') :
    CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j' R' F' (f :: fs) fp' ra' tp' G0' Ab' :=
  ⟨hc, a :: st, StkOkB.cons ha hst⟩

/-- **The callee's context with its suspended frames at a plain call**
(`CxOkS.call` at the call site's record): from the caller's context with
its records (`CxOkS j` at `fs`, `RaOk ra`), the call site of `g` returning
to `q.ra` in block `j` (`CallSite2F` at the block's code facts, the literal
walk's facts with `RetLk` at the block's return type), the callee's room
`D`, its frame condition `F'` the caller's at the call (`CalleeF2`, stable
in the callee's region) and the return site after the call's `bl`, the
callee's context `CxOk j'` at `f :: fs` has records: the caller's record at
the call pushed (its resumption point `BodyPtW` from `PtC2`, the ra link
from the argument's load, the pinned caller from `CallSite2F`), linked to
the callee's key (`StkLink`: the call's saved pair, the thread pointer, the
callee's ghosts from the call's entry control, an `int` block and frame). -/
theorem CxOkS.callSite {j : Nat} {d : Decl} (hd : P[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hcx : CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j R F fs fp ra tp G0 Ab) (hra : RaOk ra)
    {g : String} {q : CallG}
    {D : Int} {f : TermRun.Frame} {F' : MachineData → Prop}
    (hs : CallSite2F p lbl lsize (hcode j d hd).lcx (hcode j d hd).cx (Cd ra) ((hcode j d hd).Bl ra) G0 (T j)
      (_root_.Executable.labels exe).label i (RetLk d.retTy) g q R D fp ra f F')
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -((hcode j d hd).cx.frame : Int) - D)
    (hF' : FStable (R.callee (-((hcode j d hd).cx.frame : Int)) (-D) 0) F')
    (hCF : CalleeF2 p lbl lsize (hcode j d hd).cx R F D fp ra i (T j) q f F')
    (hbl : ∃ pcB kk, (hcode j d hd).Bl ra pcB (Scc.Lower.Names.user g) kk ∧ q.ra = (pcB + 4).toBitVec)
    {j' : Nat} {fp' ra' : BitVec 64} {tp' : UInt64} {G0' : Ctl → Prop} {Ab' : FragS isaLSE2}
    (hc : CxOk j' (R.callee (-((hcode j d hd).cx.frame : Int)) (-D) 0) F' (f :: fs) fp' ra' tp' G0' Ab')
    (hfp : fp' = q.fp) (hra' : ra' = q.ra) (htp : tp' = tp)
    (hG0' : ∀ c, G0' c → FrameRunM p (q.cE, f :: fs) (c, f :: fs))
    (hj' : ∃ dg, P[j']? = some dg ∧ dg.retTy = .int) (hfty : f.ty = .int) :
    CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j'
      (R.callee (-((hcode j d hd).cx.frame : Int)) (-D) 0) F' (f :: fs) fp' ra' tp' G0' Ab' := by
  obtain ⟨hcj, st, hst⟩ := hcx
  obtain ⟨c0, pc, pc', kk, env, n, x, a, e, t, w, lits, cs, bufs, lw, hc0, -, hfr, -, -, -, -, hcl, ha, -, hlw, hq,
    ⟨l, k, r, hr, hcode', hblk, hW, hL, hC, hX⟩, hpin⟩ := hs
  obtain ⟨pcB, kB, hB, hqB⟩ := hbl
  let rec_ : StkFr := ⟨j, R, F, fp, ra, tp, G0, Ab, c0, q, D, pc, .let_ x (.call g [] a []) e, env, n, lits, cs,
    bufs⟩
  exact CxOkS.call (a := rec_) hst
    ⟨d, hd, hcj, hra, hc0, ⟨l, k, r, kk, hr, hfr, hcode', hblk, hW, hL, hC, hX⟩, hD0, hD8, hlo, rfl, hF', hCF,
      ⟨pcB, kB, g, hB, hqB⟩, ⟨x, g, a, e, t, w, lw, rfl, ha, hlw, hq⟩,
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
`g` a callee, `b`'s word `w` loaded by `lw`, the return address after the
call, the frame above's frame condition inside the caller's (`CalleeF2`)
and the caller pinned at the record's data (`CallerAt2`). -/
theorem StkFrOk.pin {k : StkKey} {a : StkFr} {f : TermRun.Frame}
    {fs : List TermRun.Frame} (h : StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk k a f fs) :
    ∃ (d : Decl) (hd : P[a.j]? = some d) (x g : String) (b : At) (e : Expr) (t : Ty) (w : Scc.IR.Operand)
      (lw : List Item), a.t = .let_ x (.call g [] b []) e ∧
      BodyPtW (hcode a.j d hd) a.ra a.pc a.t a.env a.n a.lits a.cs a.bufs ∧
      0 ≤ a.D ∧ a.R.lo ≤ -((hcode a.j d hd).cx.frame : Int) - a.D ∧
      k.R = a.R.callee (-((hcode a.j d hd).cx.frame : Int)) (-a.D) 0 ∧
      Spike.Lib.LowerCall.Callee (hcode a.j d hd).lcx g ∧ Scc.Lower.Inv.atomV a.env b = some (t, [w]) ∧
      (hcode a.j d hd).cx.getOp .X0 w = .ok lw ∧
      a.q.ra = (a.pc + Int64.ofNat (4 * (directives lw).length) + 4).toBitVec ∧
      (∀ m, k.F m → a.F m) ∧
      CallerAt2 p lbl lsize (hcode a.j d hd).cx a.R a.D a.fp a.ra a.q f k.F a.c0 a.t a.env a.lits a.cs a.bufs := by
  obtain ⟨d, hd, -, -, -, hb, h0, -, hlo, hk, -, hcal, -, ⟨x, g, b, e, t, w, lw, ht, ha, hw, hq⟩, hcl, hpin, -⟩ := h
  exact ⟨d, hd, x, g, b, e, t, w, lw, ht, hb, h0, hlo, hk, hcl x g b e ht, ha, hw, hq, fun m hm => (hcal m hm).1,
    hpin⟩

/-- **The frame above linked to a record** (`StkLink`). -/
theorem StkFrOk.link {k : StkKey} {a : StkFr} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (h : StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk k a f fs) : StkLink p P k a f fs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hl⟩ := h
  exact hl

end Stk

/-! ## The stack-depth bound -/

/-- **The stack-depth bound** at a state: the new frame's `sp` (`sp` less
the frame `fsz`) at least `lim` (`limOk_callee_ofPlaceOK`'s `hZ` at `lim =
stacksA + 4096`). -/
def StkRoomA (lim : Nat) (σ : AS) (fsz : Int) : Prop :=
  lim ≤ (σ.regs.SP.toBitVec - (Int64.ofInt fsz).toBitVec).toNat

/-- **The bound from room below `sp`**: a frame `0 ≤ fsz < 2^63` and
`lim + fsz ≤ sp`. -/
theorem stkRoomA_of_le {lim : Nat} {σ : AS} {fsz : Int} (h0 : 0 ≤ fsz) (h1 : fsz < 2 ^ 63)
    (h : lim + fsz.toNat ≤ σ.regs.SP.toBitVec.toNat) : StkRoomA lim σ fsz := by
  unfold StkRoomA
  have he : (Int64.ofInt fsz).toBitVec.toNat = fsz.toNat := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    have : fsz % (2 ^ 64 : Nat) = fsz := Int.emod_eq_of_lt h0 (by omega)
    rw [this]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, he]; omega), he]
  omega

section Place

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64ConsumerS (msOfS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ)

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.A64.PhRec.GOf (Ly h) (Spike.Lib.A64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) (G0 h)
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The first thread's pointer. -/
local notation "TP0" h:max => UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64)

/-- **A callee's prologue limit facts at any depth** (`limOk_callee_ofPlaceOK`
at `StkRoomA`): at the first thread, under a frame condition within `rtF`,
at a state with the stack-depth bound at the first stack's limit. -/
theorem limOk_callee_ofStk {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hfree : Spike.Lib.A64.Rt.RtFree (Ly h) (Ly h).Λ.static (fun _ => 0))
    {F : MachineData → Prop} (hF : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly h) m) (fs : List TermRun.Frame)
    {σ : AS} (htp : σ.regs.TPIDR_EL0 = TP0 h) {fsz : Int}
    (hZ : StkRoomA ((Ly h).stacksA.toNat + 4096) σ fsz) :
    Ret0.LimOk ((MSS h) fs) F (Ly h).exe (Ly h).endPc (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit))
      (σ.regs.SP.toBitVec - (Int64.ofInt fsz).toBitVec) :=
  limOk_callee_ofPlaceOK h hfree hF fs htp hZ

end Place

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.CxOkS.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CxOkS.call

/-- info: 'Spike.Lib.LowerA64.CxOkS.bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CxOkS.bot

/-- info: 'Spike.Lib.LowerA64.CxOkS.callSite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CxOkS.callSite

/-- info: 'Spike.Lib.LowerA64.StkFrOk.pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.StkFrOk.pin

/-- info: 'Spike.Lib.LowerA64.stkRoomA_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.stkRoomA_of_le

/-- info: 'Spike.Lib.LowerA64.limOk_callee_ofStk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.limOk_callee_ofStk
