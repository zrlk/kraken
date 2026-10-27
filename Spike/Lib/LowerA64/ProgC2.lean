/-
**Every function of an `Accepted2` program is one segment** (AArch64): the
code facts of each compiled block (`FnCode2`), the function's segment from
its label at every context (`FnSpecC2`) to its exits by placements with
the source facts for its callers (`ExitC2SL` at its return type), and the
induction over the call order (`fnSpecC2_allI`). The
`Accepted2` twin of `Spike/Lib/LowerA64/ProgC.lean`: the body by
`body2_segS_ofSL` (the calls, lane stores, buffers and prints as the
context's premises), the prologue by `prologue_seg_ofW` at any spill (its
edge into the body's entry node, `ProEdge2`, a premise).

- `FnCode2`: a compiled block's code facts (lowering context, frame,
  prologue with its spill's cells, body's closed form `lowerC2` and code,
  its walks' facts, the literal walk's `ret`s at the return type's layout);
- `ProEdge2`: the prologue's limit facts and its edge into the body's
  entry node at any spill;
- `BodyAt2`, `BodySpecC2`, `FnSpecC2`: the body's segment from its entry
  node at a context and at every context `CxOk`, and the function's from its
  label, to `ExitC2SL` at the return type;
- `fnSpecC2_of_body`: the function's segment from the body's (the
  prologue, `prologue_seg_ofW`);
- `bodySpecC2_of`: the body's segment from the context's construct
  premises (`CallC2`, `LaneC`, `NewBufC`, `PrintCallC`; the others by
  `addC2_of` … `ifC2_of`), `body2_segS_ofSL`;
- `CallIn2`, `fnSpecC2_allI`: every compiled block's `FnSpecC2` at contexts
  indexed by the block, its body's segment from the callees' `FnSpecC2` at
  smaller indices (the call order, `hord`, a premise);
- `CalleePre2`, `CalleePre2.seg`: a context's premises bundled, and the
  function's segment from them;
- `CalleePre2.segB`: at an `int` block, to `ExitC2B` (`ExitC2SL.toB_int`),
  the callee's segment a plain call's premise (`callC2_of`'s `hcal`) takes.
-/
import Spike.Lib.LowerA64.Body2SegX
import Spike.Lib.LowerA64.RetSL
import Spike.Lib.LowerA64.CallIface
import Spike.Lib.LowerA64.Body2SegOf
import Spike.Lib.LowerA64.FnC
import Spike.Lib.Src.CallOrder2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC2 Res2)

section ProgC2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
  {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **A compiled block's code facts** at the program `prog` laid out in
`exe` (ending at `endPc`), the code predicates `Cd ra` at each return
address `ra` with `RaOk ra`, the immediates `i` and the walk predicate
`T`: its lowering context `lcx` (calls plain, `hfrm`), call predicate
`Bl ra`, frame `cx`, label and prologue with its spill `ps` (each a cell
of the frame, `hps`), its body's closed form `r` from the environment `env`
(fresh from `0`) and its code at each `ra`, the lowering walk's facts, the
literal walk's from `lits` (every `ret` of it at the return type's
layout, `hretL`, every call at its callee's parameter layout, `hcallL`),
the pairs' counts and the lane stores' range; the parameter's word count
`na` with the environment, layouts and spill at it. -/
structure FnCode2 (exe : _root_.Executable) (prog : List Directive) (endPc : Int64)
    (RaOk : BitVec 64 → Prop) (Cd : BitVec 64 → Int64 → List Directive → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (d : Decl) where
  lcx : Scc.Lower.Ctx
  Bl : BitVec 64 → Int64 → Label → Nat → Prop
  cx : FnCtx
  fn : Label
  entry : Label
  kp : Nat
  env : Scc.Lower.Env
  r : Res2
  ps : List (XReg × Int64)
  lits : List (String × Scc.Lower.LitV)
  hf : FrameOk cx
  h1 : cx.frame ≤ 4095
  h16 : cx.frame % 16 = 0
  hp : Lays exe prog kp
  hend : endPc = endOf exe prog kp
  hfn : fn = Scc.Lower.Names.user d.name
  hpro : prologueIn prog fn (cx.local "stack_check") entry (Int64.ofInt cx.frame)
    (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) ps = true
  hps : ∀ q ∈ ps, offOk (-(Int64.ofInt cx.frame).toInt) 0 (-(Int64.ofInt cx.frame).toInt + q.2.toInt) = true
  hfrm : lcx.frames = none
  hr : lowerC2 lcx env 0 "entry" 0 d.body = some r
  hfr : Fresh env 0
  hCd : ∀ ra, RaOk ra → ∀ pc blk, Cd ra pc blk → CdOf exe endPc pc blk
  hcode : ∀ ra, RaOk ra → CodeC2 cx (Cd ra) (Bl ra) 0 ((_root_.Executable.labels exe).label entry) r.insts r.term
  hbl : ∀ ra, RaOk ra → BlocksCodeC2 cx (Cd ra) (Bl ra) (_root_.Executable.labels exe).label r.blocks
  hWk : ∀ q ∈ lowerEnvs2 lcx env 0 d.body, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
    LocBaseRegAt (ofEnv2 q.2.1) q.1
  hlit : ∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits d.body, LitPt q
  hretL : ∀ a lits', (.ret a, lits') ∈ Scc.Lower.litWalk2 lcx.prog lits d.body →
    (Scc.Lower.litAt lits' a).erase = Scc.Lower.shapeOf d.retTy
  hcallL : ∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits d.body, CallLk lcx.prog q
  hcnt : Scc.Lower.countsB lcx.prog [] [] lits d.body = true
  hxchg : xchgsB [] [] d.body = true
  /-- The parameter's word count: the body's environment (`env2`) and the literal walk's start
  (`params2`, `shapeOf`) are the parameter's, the prologue's spill its registers'. -/
  na : Nat
  henv : env = Spike.Lib.LowerShape.env2 d na
  hlits : lits = (Scc.Lower.params2 d).map (·, Scc.Lower.shapeOf d.argTy)
  hsp : Scc.Cert.Code1A64.spills cx (Spike.Lib.LowerShape.paramsR d na) = some ps

/-- **The body's entry node** of a compiled block (code facts `c`) at a
context: `bodyN2` at the entry label, the body, its environment and
literals, no known values or buffers, the thread pointer `tp`. -/
abbrev entryN2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) : ND :=
  (bodyN2 p lbl lsize i c.cx fp ra c0 ((_root_.Executable.labels exe).label c.entry) d.body (ofEnv2 c.env)
    c.lits [] []).withTp tp

/-- **The prologue's edge into the body** (`prologue_seg_ofW`'s `hedge`
at the body's entry node): at each entry state of `J`, the stack limit's
cell readable and unmapped in `F`, every limit value below the new `sp`,
and after the check, the frame's set-up and the spill `ps`, the body's
entry node's invariant. -/
def ProEdge2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (ms : MemSide isaLSE2) (F : MachineData → Prop) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl)
    (J : AS → Ctl → Prop) : Prop :=
  ∀ σ c', J σ c' →
    ms.rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
    ms.mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
    (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
    ∀ v : Val, ms.G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
      (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt c.cx.frame).toBitVec).toNat ∧
      ∀ σ' : AS, σ'.regs = frRegs (Int64.ofInt c.cx.frame)
          (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs (Int64.ofInt c.cx.frame) σ.regs }).regs →
        σ'.slot = stSlots (-(Int64.ofInt c.cx.frame).toInt) σ'.regs c.ps (frSlot σ) →
        (entryN2 p lbl lsize c fp ra tp c0).J σ' c'

/-- **A compiled block's body segment at a context** (code facts `c`):
from the body's entry node at the frames `fs` (any ghost `c0` in `G0`, the
thread pointer `tp`) in the region `R` meeting `body2_segS_ofSL`'s block
premises (for any fragment `W₀` inside `W` at `fs`) to its exits by
placements with `RetL` at its return type (`ExitC2SL`). -/
def BodyAt2 (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ms : List TermRun.Frame → MemSide isaLSE2) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2) : Prop :=
  ∀ (W₀ : Frag isaLSE2) (c0 : Ctl),
    FStable R F → R.OK → R.base.toNat % 16 = 0 → R.lo ≤ -(c.cx.frame : Int) → 0 ≤ R.hi →
    (∀ s c, W₀ s c → W s c fs) →
    (∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') →
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs) blk) →
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs k) blk) →
    (∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN2 i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs) →
    G0 c0 →
    SegWS W K p lbl ms ((At exe endPc R F (entryN2 p lbl lsize c fp ra tp c0)).at fs)
      (ExitC2SL p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab)

/-- **A compiled block's body segment** (code facts `c`): `BodyAt2` at
every context `CxOk` (every return address with `RaOk`). -/
def BodySpecC2 (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ms : List TermRun.Frame → MemSide isaLSE2) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop)
    (c : FnCode2 exe prog endPc RaOk Cd i T d) : Prop :=
  ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
    CxOk R F fs fp ra tp G0 Ab → RaOk ra → BodyAt2 W K p lbl lsize ms c R F fs fp ra tp G0 Ab

/-- **A compiled block's function segment** (code facts `c`): from its
label at any frames `fs` (`sp` at 0, the entry invariant `J`) in any
context `CxOk` meeting `body2_segS_ofSL`'s block premises and the
prologue's (`ProW`, `ProEdge2`) to its exits by placements with `RetL` at
its return type (`ExitC2SL`). -/
def FnSpecC2 (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ms : List TermRun.Frame → MemSide isaLSE2) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop)
    (c : FnCode2 exe prog endPc RaOk Cd i T d) : Prop :=
  ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isaLSE2) (W₀ : Frag isaLSE2) (J : AS → Ctl → Prop) (c0 : Ctl),
    CxOk R F fs fp ra tp G0 Ab → RaOk ra →
    FStable R F → R.OK → R.base.toNat % 16 = 0 → R.lo ≤ -(c.cx.frame : Int) → 0 ≤ R.hi →
    (∀ s c, W₀ s c → W s c fs) →
    (∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') →
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs) blk) →
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs k) blk) →
    (∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN2 i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs) →
    G0 c0 →
    ProW W₀ K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.cx) c.ps J →
    ProEdge2 p lbl lsize (ms fs) F c fp ra tp c0 J →
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC2SL p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab)

/-- **The prologue at a compiled block's label**: `prologue_seg_ofW` into
the body's entry node, at the frame `cx.frame` and the spill `ps`. -/
theorem proSeg2 {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) {R : Region} {F : MachineData → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(c.cx.frame : Int))
    (hhi : 0 ≤ R.hi) {W₀ : Frag isaLSE2} {ms0 : MemSide isaLSE2} {J : AS → Ctl → Prop}
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
    (hWpro : ProW W₀ K exe endPc R F ms0 ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.cx) c.ps J)
    (hedge : ProEdge2 p lbl lsize ms0 F c fp ra tp c0 J) :
    SegW W₀ K p lbl ms0 (At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F (entryN2 p lbl lsize c fp ra tp c0)) := by
  have hge := frame_ge16 c.hf
  have h1 := c.h1
  have hF64 : (Int64.ofInt c.cx.frame).toInt = c.cx.frame := toInt_ofInt_small (by omega) (by omega)
  have h16 := c.h16
  exact prologue_seg_ofW c.hp c.hend c.hpro (by rw [hF64]; omega) (by rw [hF64]; omega) hF hR hal
    (by rw [hF64]; exact hlo) hhi c.hps rfl (oF_le_oFr c.cx hF64) hWpro hedge

/-- **A function's segment from its body's**: the prologue (`proSeg2`)
then the body's segment at the same context. -/
theorem fnSpecC2_of_body {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (hb : BodySpecC2 W K p lbl lsize ms CxOk c) :
    FnSpecC2 W K p lbl lsize ms CxOk c := by
  intro R F fs fp ra tp G0 Ab W₀ J c0 hcx hra hF hR hal hlo hhi hW₀ hG0 hW hWp hab hg0 hWpro hedge
  exact (SegWS.liftS fs (proSeg2 c hF hR hal hlo hhi hWpro hedge) hW₀).seq
    (hb R F fs fp ra tp G0 Ab hcx hra W₀ c0 hF hR hal hlo hhi hW₀ hG0 hW hWp hab hg0)

omit [Kraken.Executable.ValidLayout exe] in
/-- **A body's segment from the context's construct premises**
(`body2_segS_ofSL`): at every context `CxOk` (every return address with
`RaOk`), the plain calls (`CallC2`), lane stores (`LaneC`), buffers
(`NewBufC`) and prints (`PrintCallC`) give `BodySpecC2`; the other
constructs by `addC2_of`, `subC2_of`, `pureMv2_of`, `splitMv2_of`,
`unpackMv2_of`, `ifC2_of`. -/
theorem bodySpecC2_of {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (c : FnCode2 exe prog endPc RaOk Cd i T d)
    (hcon : ∀ R F fs fp ra tp G0 Ab, CxOk R F fs fp ra tp G0 Ab → RaOk ra →
      CallC2 p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      LaneC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab ∧
      NewBufC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      PrintCallC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab) :
    BodySpecC2 W K p lbl lsize ms CxOk c := by
  intro R F fs fp ra tp G0 Ab hcx hra W₀ c0 hF hR hal hlo hhi hW₀ hG0 hW hWp hab hg0
  obtain ⟨hcall, hlane, hbuf, hprint⟩ := hcon R F fs fp ra tp G0 Ab hcx hra
  have hCd := c.hCd ra hra
  exact body2_segS_ofSL c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hG0 hW c.hfrm d.retTy hcall hlane hbuf hprint
    (addC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW hWp hab c.lcx tp)
    (subC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW hWp c.lcx tp)
    (pureMv2_of c.lcx tp) (splitMv2_of c.lcx tp) (unpackMv2_of c.lcx tp)
    (ifC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW c.lcx tp)
    d.body c.env 0 "entry" 0 c.r 0 _ c.lits [] [] c.hr c.hfr (c.hcode ra hra) (c.hbl ra hra) c.hWk
    (fun q hq => ⟨c.hlit q hq, c.hcallL q hq⟩) c.hretL c.hcnt c.hxchg c0 hg0

/-- **`g` is called at a term still to lower in `e`** (`TailOf`, e.g. a
point of the `Accepted2` lowering walk, `lowerEnvs2_tail`), a plain call:
`g` is not among the context's externs (`Callee`'s first part; a call of
the output extern is a print, `PrintCallC`). -/
def CallIn2 (lcx : Scc.Lower.Ctx) (e : Expr) (g : String) : Prop :=
  ∃ x is a ts e', TailOf (.let_ x (.call g is a ts) e') e ∧ lcx.externs.find? (·.1 == g) = none

/-- **Every compiled block is one segment, at contexts depending on its
index**: the `j`th block of `P` (e.g. `compiled2 p`) with its contexts
`CxOk j` and walk predicate `T j`, its body's segment (`hbody_of`, e.g.
`bodySpecC2_of`) from each callee's `FnSpecC2` at its own index `j' < j`,
the callees earlier (`hord`). By strong induction on the index. -/
theorem fnSpecC2_allI {P : Prog} {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d)
    (hord : ∀ (j : Nat) d (hd : P[j]? = some d) g dg,
      CallIn2 (hcode j d hd).lcx d.body g → p.find? (·.name == g) = some dg →
      ∃ j' : Nat, j' < j ∧ P[j']? = some dg)
    (hbody_of : ∀ (j : Nat) d (hd : P[j]? = some d),
      (∀ g dg, CallIn2 (hcode j d hd).lcx d.body g →
        p.find? (·.name == g) = some dg →
        ∃ j' : Nat, j' < j ∧ ∃ hd' : P[j']? = some dg, FnSpecC2 W K p lbl lsize ms (CxOk j') (hcode j' dg hd')) →
      BodySpecC2 W K p lbl lsize ms (CxOk j) (hcode j d hd)) :
    ∀ (j : Nat) d (hd : P[j]? = some d), FnSpecC2 W K p lbl lsize ms (CxOk j) (hcode j d hd) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro d hd
    refine fnSpecC2_of_body (hcode j d hd) (hbody_of j d hd fun g dg hc hf => ?_)
    obtain ⟨j', hlt, hd'⟩ := hord j d hd g dg hc hf
    exact ⟨j', hlt, hd', ih j' hlt dg hd'⟩

/-- **A context's premises at a compiled block** (code facts `c`), for
`FnSpecC2` at the frames `fs`, the ghost `c0` and the entry invariant `J`:
the context in `CxOk`, its region, the ghosts closed under the frame runs,
the blocks' and the prologue's states inside `W` at `fs`, the overflow
abort an `Ab`, the prologue's edge into the body. -/
structure CalleePre2 (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop)
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2) (J : AS → Ctl → Prop) (c0 : Ctl) :
    Prop where
  hcx : CxOk R F fs fp ra tp G0 Ab
  hra : RaOk ra
  hF : FStable R F
  hR : R.OK
  hal : R.base.toNat % 16 = 0
  hlo : R.lo ≤ -(c.cx.frame : Int)
  hhi : 0 ≤ R.hi
  hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c'
  hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk →
    (fs = [] → ∀ a, t ≠ .ret a) →
    BlkW (fun s c => W s c fs) K exe endPc R F (bodyN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs) blk
  hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
    (fs = [] → ∀ a, t ≠ .ret a) →
    BlkW (fun s c => W s c fs) K exe endPc R F (pendN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs k) blk
  hab : ∀ c0, G0 c0 → ∀ s c',
    At exe endPc R F (abortN2 i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' → Ab s c' fs
  hg0 : G0 c0
  hpro : ProW (fun s c => W s c fs) K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn)
    (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.cx) c.ps J
  hedge : ProEdge2 p lbl lsize (ms fs) F c fp ra tp c0 J

omit [Kraken.Executable.ValidLayout exe] in
/-- **A function's segment at a context** from its `FnSpecC2` and the
context's premises (`CalleePre2`). -/
theorem CalleePre2.seg {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    {c : FnCode2 exe prog endPc RaOk Cd i T d} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2} {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R F fs fp ra tp G0 Ab J c0) (hs : FnSpecC2 W K p lbl lsize ms CxOk c)
    (hfs : fs ≠ []) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC2SL p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab) :=
  hs R F fs fp ra tp G0 Ab (fun s c => W s c fs) J c0 h.hcx h.hra h.hF h.hR h.hal h.hlo h.hhi (fun _ _ h => h)
    h.hG0 (fun c0 hg pc t s l cs b blk hc hk => h.hW c0 hg pc t s l cs b blk hc hk fun e => absurd e hfs)
    (fun c0 hg pc t s l cs b k blk hc hk h1 => h.hWp c0 hg pc t s l cs b k blk hc hk h1 fun e => absurd e hfs)
    h.hab h.hg0 h.hpro h.hedge

omit [Kraken.Executable.ValidLayout exe] in
/-- **An `int` function's segment at a context to `ExitC2B`** (`CalleePre2.seg`
then `ExitC2SL.toB_int`): the exits at the frame's type `ty`, the block's
return type (`hty`) `int` (`hint`). -/
theorem CalleePre2.segB {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    {c : FnCode2 exe prog endPc RaOk Cd i T d} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2} {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R F fs fp ra tp G0 Ab J c0) (hs : FnSpecC2 W K p lbl lsize ms CxOk c)
    (hfs : fs ≠ []) {ty : Ty} (hty : d.retTy = ty) (hint : ty = .int) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC2B p lbl exe endPc R F fp ra tp c0 fs ty Ab) := by
  subst hint
  exact (h.seg hs hfs).mono_post fun _ _ _ h' => ExitC2SL.toB_int (hty ▸ h')

omit [Kraken.Executable.ValidLayout exe] in
/-- **A plain call's callee segment** (`callC2_of`'s `hcal` conclusion) from
the callee's `FnSpecC2` and its context's premises at the call (`CalleePre2`
in the callee's region `R'`, frame condition `F'`, frames `frm :: fs`, the
call's saved pair, entry control and the entry node `calleeN`): the callee
`dg` named `g` of return type `int` (`plain2`), the frame's type its. -/
theorem hcal_of {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {dg : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    {c : FnCode2 exe prog endPc RaOk Cd i T dg} {g : String} (hg : dg.name = g) (hint : dg.retTy = .int)
    {q : CallG} {frm : TermRun.Frame} (hty : frm.ty = dg.retTy) {R' : Region} {F' : MachineData → Prop}
    {fs : List TermRun.Frame} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R' F' (frm :: fs) q.fp q.ra tp G0 Ab
      (calleeN (_root_.Executable.labels exe).label g tp q).J q.cE)
    (hs : FnSpecC2 W K p lbl lsize ms CxOk c) :
    SegWS W K p lbl ms ((At exe endPc R' F' (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
      (ExitC2B p lbl exe endPc R' F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab) := by
  have hn : calleeN (_root_.Executable.labels exe).label g tp q =
      ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩,
        (calleeN (_root_.Executable.labels exe).label g tp q).J⟩ := by
    rw [c.hfn, hg]; rfl
  rw [hn]
  exact h.segB hs (List.cons_ne_nil _ _) hty.symm (hty.trans hint)

end ProgC2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.fnSpecC2_of_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnSpecC2_of_body

/-- info: 'Spike.Lib.LowerA64.bodySpecC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bodySpecC2_of

/-- info: 'Spike.Lib.LowerA64.fnSpecC2_allI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnSpecC2_allI

/-- info: 'Spike.Lib.LowerA64.CalleePre2.seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CalleePre2.seg

/-- info: 'Spike.Lib.LowerA64.CalleePre2.segB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CalleePre2.segB

/-- info: 'Spike.Lib.LowerA64.hcal_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hcal_of

end Spike.Lib.LowerA64
