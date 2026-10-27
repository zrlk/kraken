/-
**Every function of an `Accepted2` program is one segment** (x86-64): the
twin of `Spike/Lib/LowerA64/ProgC2.lean`, the `Accepted2` twin of
`Spike/Lib/LowerX64/ProgC.lean`. The code facts of each compiled block
(`FnCode2`), the prologue by `prologue_seg_ofW` at any spill (its edge into
the body's entry node, `ProEdge2`, a premise), and the body's segment from
its entry node at a context (`BodyAt2`) to its exits by placements
(`ExitC2SL`, with `RetL` at the return type), and the induction over the
call order (`fnSpecC2_allI`).

- `FnCode2`: a compiled block's code facts (lowering context, frame,
  prologue with its spill's cells, body's closed form `lowerC2` and code,
  its walks' facts);
- `entryN2`: the body's entry node at a context;
- `ProEdge2`: the prologue's limit facts and its edge into the body's
  entry node at any spill;
- `proSeg2`: the prologue from the function's label in the region `R` to
  the body's entry node in the rebased region `rbR R`;
- `BodyAt2`, `BodySpecC2`, `FnSpecC2`: the body's segment from its entry
  node at a context, in `rbR R`, and at every context `CxOk`, and the
  function's from its label, to `ExitC2SL`;
- `fnSpecC2_of_body`: the function's segment from the body's (the
  prologue, `proSeg2`);
- `bodySpecC2_of`: the body's segment from the context's construct
  premises (`CallC2`, `LaneC`, `NewBufC`, `PrintCallC`), `body2_segS_ofSL`;
- `CallIn2`, `fnSpecC2_allI`: a plain callee at a term still to lower in a
  compiled block's body (`TailOf`), and every compiled block's `FnSpecC2`
  by the call order;
- `CalleePre2`, `CalleePre2.seg`, `CalleePre2.segB`, `hcal_of`: a context's
  premises bundled, the function's segment from them (to `ExitC2B` at
  `int`), and a plain call's callee segment (`callC2_of`'s `hcal`).

Where x86-64 differs from AArch64: as in `ProgC.lean`, the prologue pushes
the frame pointer, so the body runs in the rebased region `rbR R` (`at_rbR`,
the slots shifted by `shSl`), `R.lo ≤ -8 - fr.size` and `8 ≤ R.hi`; the
prologue's cells carry sizes (`zl` … `zs`, the spill's in `ps`), and the
entry block's label counter is `kk`.
-/
import Spike.Lib.LowerX64.Body2SegOf
import Spike.Lib.LowerX64.FnC
import Spike.Lib.LowerX64.RetSL
import Spike.Lib.LowerX64.CallNodes
import Spike.Lib.Src.CallOrder2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (prologueIn prologue_seg_ofW XProW xStSlots xS1 xFrRegs)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC2 Res2)

section ProgC2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **A compiled block's code facts** at the cells `cells` laid out in
`exe` (ending at `endPc`), the code predicates `Cd ra` at each return
address `ra` with `RaOk ra`, the immediates `i` and the walk predicate
`T`: its lowering context `lcx` (calls plain, `hfrm`), call predicate
`Bl ra`, frame `fr`, label and prologue (its cells' sizes `zl` … `zs`) with
its spill `ps` (each a cell of the frame, `hps`), its body's closed form `r`
from the environment `env` (fresh from `0`) and its code at each `ra` (the
entry block's label counter `kk`), the lowering walk's facts, the literal
walk's from `lits` (every `ret` of it at the return type's layout,
`hretL`, every call at its callee's parameter layout, `hcallL`), the pairs'
counts and the lane stores' range; the parameter's word count
`na` with the environment, layouts and spill at it. -/
structure FnCode2 (exe : _root_.Executable) (cells : List (Directive × Nat)) (endPc : Int64)
    (RaOk : BitVec 64 → Prop) (Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (d : Decl) where
  lcx : Scc.Lower.Ctx
  Bl : BitVec 64 → Int64 → Nat → Label → Nat → Prop
  fr : Scc.Emit.X64.Frame
  fn : Label
  entry : Label
  zl : Nat
  zf : Nat
  z1 : Nat
  z2 : Nat
  zs : Nat
  kp : Nat
  env : Scc.Lower.Env
  r : Res2
  kk : Nat
  ps : List (Reg64 × Int64 × Nat)
  lits : List (String × Scc.Lower.LitV)
  hf : FrameOk fr
  h1 : fr.size ≤ 2 ^ 31
  h16 : fr.size % 16 = 0
  hp : Lays exe cells kp
  hend : endPc = endOf exe cells kp
  hfn : fn = Scc.Lower.Names.user d.name
  hpro : prologueIn cells fn (Scc.Emit.X64.labelOf fr.fn "chk") entry (Int64.ofInt fr.size)
    (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs ps = true
  hps : ∀ q ∈ ps, offOk (-8 - (Int64.ofInt fr.size).toInt) 0 (-8 + q.2.1.toInt) = true
  hfrm : lcx.frames = none
  hr : lowerC2 lcx env 0 "entry" 0 d.body = some r
  hfr : Fresh env 0
  hCd : ∀ ra, RaOk ra → ∀ pc blk, Cd ra pc blk → CdOf exe endPc pc blk
  hcode : ∀ ra, RaOk ra → CodeC2 fr (Cd ra) (Bl ra) kk ((_root_.Executable.labels exe).label entry) r.insts r.term
  hbl : ∀ ra, RaOk ra → BlocksCodeC2 fr (Cd ra) (Bl ra) (_root_.Executable.labels exe).label r.blocks
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
  hsp : ∃ zs, Scc.Cert.Code1X64.spills fr (Spike.Lib.LowerShape.paramsR d na) zs = some ps

/-- **The body's entry node** of a compiled block (code facts `c`) at a
context: `bodyN2` at the entry label, the body, its environment and
literals, no known values or buffers, the thread pointer `tp`. -/
abbrev entryN2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) : ND :=
  (bodyN2 p lbl lsize i c.fr fp ra c0 ((_root_.Executable.labels exe).label c.entry) d.body (ofEnv2 c.env)
    c.lits [] []).withTp tp

/-- **The prologue's edge into the body** (`prologue_seg_ofW`'s `hedge`
at the body's entry node): at each entry state of `J`, the stack limit's
cell (off the `%fs` base) readable and unmapped in `F`, every limit value
below the new `%rsp`, and after the check, the frame's set-up and the spill
`ps`, the body's entry node's invariant at the slots shifted to the frame
pointer (`shSl`). -/
def ProEdge2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (ms : MemSide isa) (F : MachineData → Prop) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl)
    (J : AS → Ctl → Prop) : Prop :=
  ∀ σ c', J σ c' →
    ms.rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
    ms.mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
    (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
      = none) ∧
    ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
      (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt c.fr.size).toBitVec).toNat ∧
      ∀ σ' : AS, σ'.regs = xFrRegs (Int64.ofInt c.fr.size) (v.setWidth 64) σ.regs →
        σ'.slot = xStSlots σ'.regs c.ps (xS1 σ).slot →
        (entryN2 p lbl lsize c fp ra tp c0).J { σ' with slot := shSl σ'.slot } c'

/-- **The prologue at a compiled block's label**: `prologue_seg_ofW` into
the body's entry node, at the frame `fr.size` and the spill `ps`, the
entry node in the rebased region `rbR R` (`at_rbR`). -/
theorem proSeg2 {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) {R : Region} {F : MachineData → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 0 ≤ R.hi)
    {W₀ : Frag isa} {ms0 : MemSide isa} {J : AS → Ctl → Prop}
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
    (hWpro : XProW W₀ K exe endPc R F ms0 ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps J)
    (hedge : ProEdge2 p lbl lsize ms0 F c fp ra tp c0 J) :
    SegW W₀ K p lbl ms0 (At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩)
      (At exe endPc (rbR R) F (entryN2 p lbl lsize c fp ra tp c0)) := by
  have h1 := c.h1
  have hZ : (Int64.ofInt c.fr.size).toInt = c.fr.size := toInt_ofInt_small (by omega) (by omega)
  exact (prologue_seg_ofW (nb := ⟨(_root_.Executable.labels exe).label c.entry,
      Spike.Lib.X64.Flow.oF (Int64.ofInt c.fr.size), fun σ c' =>
        (entryN2 p lbl lsize c fp ra tp c0).J { σ with slot := shSl σ.slot } c'⟩)
    c.hp c.hend c.hpro (by rw [hZ]; omega) hF hR (by rw [hZ]; exact hlo) hhi c.hps rfl
    (by simp [SO.le, lk]) hWpro hedge).mono_post fun _ _ h =>
      at_rbR (J' := (entryN2 p lbl lsize c fp ra tp c0).J)
        (by show -8 - _ = _; rw [hZ]) (by simp [SO.get, lk]) (fun _ _ h => h) h

/-- **A compiled block's body segment at a context** (code facts `c`):
from the body's entry node at the frames `fs` (any ghost `c0` in `G0`, the
thread pointer `tp`) in the rebased region `rbR R` meeting
`body2_segS_ofS`'s block premises (for any fragment `W₀` inside `W` at
`fs`) to its exits by placements with `RetL` at its return type
(`ExitC2SL`). -/
def BodyAt2 (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ms : List TermRun.Frame → MemSide isa) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa) : Prop :=
  ∀ (W₀ : Frag isa) (c0 : Ctl),
    FStable R F → R.OK → R.lo ≤ -8 - (c.fr.size : Int) → 8 ≤ R.hi →
    (∀ s c, W₀ s c → W s c fs) →
    (∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') →
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk →
      BlkW W₀ K exe endPc (rbR R) F (bodyN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs) blk) →
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc (rbR R) F (pendN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs k) blk) →
    (∀ c0, G0 c0 → ∀ s c',
      At exe endPc (rbR R) F (abortN2 i T p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs) →
    G0 c0 →
    SegWS W K p lbl ms ((At exe endPc (rbR R) F (entryN2 p lbl lsize c fp ra tp c0)).at fs)
      (ExitC2SL p lbl exe endPc (rbR R) F fp ra tp c0 fs d.retTy Ab)

/-- **A compiled block's body segment** (code facts `c`): `BodyAt2` at
every context `CxOk` (every return address with `RaOk`). -/
def BodySpecC2 (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ms : List TermRun.Frame → MemSide isa) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop)
    (c : FnCode2 exe cells endPc RaOk Cd i T d) : Prop :=
  ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isa),
    CxOk R F fs fp ra tp G0 Ab → RaOk ra → BodyAt2 W K p lbl lsize ms c R F fs fp ra tp G0 Ab

/-- **A compiled block's function segment** (code facts `c`): from its
label at any frames `fs` (`%rsp` at 0, the entry invariant `J`) in any
context `CxOk` meeting `body2_segS_ofSL`'s block premises in the rebased
region `rbR R` and the prologue's (`XProW`, `ProEdge2`) to its exits by
placements with `RetL` at its return type (`ExitC2SL`) in `rbR R`. -/
def FnSpecC2 (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ms : List TermRun.Frame → MemSide isa) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop)
    (c : FnCode2 exe cells endPc RaOk Cd i T d) : Prop :=
  ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isa) (W₀ : Frag isa) (J : AS → Ctl → Prop) (c0 : Ctl),
    CxOk R F fs fp ra tp G0 Ab → RaOk ra →
    FStable R F → R.OK → R.lo ≤ -8 - (c.fr.size : Int) → 8 ≤ R.hi →
    (∀ s c, W₀ s c → W s c fs) →
    (∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') →
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk →
      BlkW W₀ K exe endPc (rbR R) F (bodyN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs) blk) →
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc (rbR R) F (pendN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs k) blk) →
    (∀ c0, G0 c0 → ∀ s c',
      At exe endPc (rbR R) F (abortN2 i T p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs) →
    G0 c0 →
    XProW W₀ K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps J →
    ProEdge2 p lbl lsize (ms fs) F c fp ra tp c0 J →
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC2SL p lbl exe endPc (rbR R) F fp ra tp c0 fs d.retTy Ab)

/-- **A function's segment from its body's**: the prologue (`proSeg2`)
then the body's segment at the same context. -/
theorem fnSpecC2_of_body {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (hb : BodySpecC2 W K p lbl lsize ms CxOk c) :
    FnSpecC2 W K p lbl lsize ms CxOk c := by
  intro R F fs fp ra tp G0 Ab W₀ J c0 hcx hra hF hR hlo hhi hW₀ hG0 hW hWp hab hg0 hWpro hedge
  exact (SegWS.liftS fs (proSeg2 c hF hR hlo (by omega) hWpro hedge) hW₀).seq
    (hb R F fs fp ra tp G0 Ab hcx hra W₀ c0 hF hR hlo hhi hW₀ hG0 hW hWp hab hg0)

omit [Kraken.Executable.ValidLayout exe] in
/-- **The rebased region's facts** for `body2_segS_ofSL`: from `R`'s
(`R.lo ≤ -8 - size`, `8 ≤ R.hi`), `rbR R` is valid, `F` stable on it, and
it holds the frame (`-size`) and the return address (`16`). -/
theorem rbR_facts {R : Region} {F : MachineData → Prop} {size : Nat} (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - (size : Int)) (hhi : 8 ≤ R.hi) :
    FStable (rbR R) F ∧ (rbR R).OK ∧ (rbR R).lo ≤ -(size : Int) ∧ 16 ≤ (rbR R).hi :=
  ⟨rbR_fstable hR (by omega) (by omega) hF, rbR_ok hR (by omega) (by omega),
    by simp only [rbR, Region.callee]; omega, by simp only [rbR, Region.callee]; omega⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **A body's segment from the context's construct premises**
(`body2_segS_ofSL` in the rebased region): at every context `CxOk` (every
return address with `RaOk`), the plain calls (`CallC2`), lane stores
(`LaneC`), buffers (`NewBufC`) and prints (`PrintCallC`) in `rbR R` give
`BodySpecC2`; the other constructs by `addC2_of`, `subC2_of`,
`pureMv2_of`, `splitMv2_of`, `unpackMv2_of`, `ifC2_of`. -/
theorem bodySpecC2_of {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (c : FnCode2 exe cells endPc RaOk Cd i T d)
    (hcon : ∀ R F fs fp ra tp G0 Ab, CxOk R F fs fp ra tp G0 Ab → RaOk ra →
      CallC2 p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      LaneC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab ∧
      NewBufC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      PrintCallC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab) :
    BodySpecC2 W K p lbl lsize ms CxOk c := by
  intro R F fs fp ra tp G0 Ab hcx hra W₀ c0 hF hR hlo hhi hW₀ hG0 hW hWp hab hg0
  obtain ⟨hcall, hlane, hbuf, hprint⟩ := hcon R F fs fp ra tp G0 Ab hcx hra
  obtain ⟨hF', hR', hlo', hhi'⟩ := rbR_facts hF hR hlo hhi
  have hCd := c.hCd ra hra
  exact body2_segS_ofSL c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀ hG0 hW c.hfrm d.retTy hcall hlane hbuf hprint
    (addC2_of c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀ hW hWp hab c.lcx tp)
    (subC2_of c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀ hW hWp c.lcx tp)
    (pureMv2_of c.lcx tp) (splitMv2_of c.lcx tp) (unpackMv2_of c.lcx tp)
    (ifC2_of c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀ hW c.lcx tp)
    d.body c.env 0 "entry" 0 c.r c.kk _ c.lits [] [] c.hr c.hfr (c.hcode ra hra) (c.hbl ra hra) c.hWk
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
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d)
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
the blocks' states (in the rebased region `rbR R`) and the prologue's inside
`W` at `fs`, the overflow abort an `Ab`, the prologue's edge into the
body. -/
structure CalleePre2 (W : FragS isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (ms : List TermRun.Frame → MemSide isa) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop)
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa) (J : AS → Ctl → Prop) (c0 : Ctl) :
    Prop where
  hcx : CxOk R F fs fp ra tp G0 Ab
  hra : RaOk ra
  hF : FStable R F
  hR : R.OK
  hlo : R.lo ≤ -8 - (c.fr.size : Int)
  hhi : 8 ≤ R.hi
  hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c'
  hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk →
    (fs = [] → ∀ a, t ≠ .ret a) →
    BlkW (fun s c => W s c fs) K exe endPc (rbR R) F (bodyN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs) blk
  hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
    (fs = [] → ∀ a, t ≠ .ret a) →
    BlkW (fun s c => W s c fs) K exe endPc (rbR R) F (pendN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs k)
      blk
  hab : ∀ c0, G0 c0 → ∀ s c',
    At exe endPc (rbR R) F (abortN2 i T p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
      Ab s c' fs
  hg0 : G0 c0
  hpro : XProW (fun s c => W s c fs) K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn)
    (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps J
  hedge : ProEdge2 p lbl lsize (ms fs) F c fp ra tp c0 J

omit [Kraken.Executable.ValidLayout exe] in
/-- **A function's segment at a context** from its `FnSpecC2` and the
context's premises (`CalleePre2`). -/
theorem CalleePre2.seg {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    {c : FnCode2 exe cells endPc RaOk Cd i T d} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa} {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R F fs fp ra tp G0 Ab J c0) (hs : FnSpecC2 W K p lbl lsize ms CxOk c)
    (hfs : fs ≠ []) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC2SL p lbl exe endPc (rbR R) F fp ra tp c0 fs d.retTy Ab) :=
  hs R F fs fp ra tp G0 Ab (fun s c => W s c fs) J c0 h.hcx h.hra h.hF h.hR h.hlo h.hhi (fun _ _ h => h)
    h.hG0 (fun c0 hg pc t s l cs b blk hc hk => h.hW c0 hg pc t s l cs b blk hc hk fun e => absurd e hfs)
    (fun c0 hg pc t s l cs b k blk hc hk h1 => h.hWp c0 hg pc t s l cs b k blk hc hk h1 fun e => absurd e hfs)
    h.hab h.hg0 h.hpro h.hedge

omit [Kraken.Executable.ValidLayout exe] in
/-- **An `int` function's segment at a context to `ExitC2B`**
(`CalleePre2.seg` then `ExitC2SL.toB_int`): the exits at the frame's type
`ty`, the block's return type (`hty`) `int` (`hint`). -/
theorem CalleePre2.segB {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    {c : FnCode2 exe cells endPc RaOk Cd i T d} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa} {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R F fs fp ra tp G0 Ab J c0) (hs : FnSpecC2 W K p lbl lsize ms CxOk c)
    (hfs : fs ≠ []) {ty : Ty} (hty : d.retTy = ty) (hint : ty = .int) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC2B p lbl exe endPc (rbR R) F fp ra tp c0 fs ty Ab) := by
  subst hint
  exact (h.seg hs hfs).mono_post fun _ _ _ h' => ExitC2SL.toB_int (hty ▸ h')

omit [Kraken.Executable.ValidLayout exe] in
/-- **A plain call's callee segment** (`callC2_of`'s `hcal` conclusion) from
the callee's `FnSpecC2` and its context's premises at the call (`CalleePre2`
in the callee's region `R'`, e.g. `calleeR R fr.size D`, frame condition
`F'`, frames `frm :: fs`, the call's saved pair, entry control and the entry
node `calleeN`): the callee `dg` named `g` of return type `int`
(`plain2`), the frame's type its; the exits in `rbR R'`. -/
theorem hcal_of {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {dg : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    {c : FnCode2 exe cells endPc RaOk Cd i T dg} {g : String} (hg : dg.name = g) (hint : dg.retTy = .int)
    {q : CallG} {frm : TermRun.Frame} (hty : frm.ty = dg.retTy) {R' : Region} {F' : MachineData → Prop}
    {fs : List TermRun.Frame} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R' F' (frm :: fs) q.fp q.ra tp G0 Ab
      (calleeN (_root_.Executable.labels exe).label g tp q).J q.cE)
    (hs : FnSpecC2 W K p lbl lsize ms CxOk c) :
    SegWS W K p lbl ms ((At exe endPc R' F' (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
      (ExitC2B p lbl exe endPc (rbR R') F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab) := by
  have hn : calleeN (_root_.Executable.labels exe).label g tp q =
      ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩,
        (calleeN (_root_.Executable.labels exe).label g tp q).J⟩ := by
    rw [c.hfn, hg]; rfl
  rw [hn]
  exact h.segB hs (List.cons_ne_nil _ _) hty.symm (hty.trans hint)

end ProgC2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.proSeg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms proSeg2

/-- info: 'Spike.Lib.LowerX64.fnSpecC2_of_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnSpecC2_of_body

/-- info: 'Spike.Lib.LowerX64.bodySpecC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bodySpecC2_of

/-- info: 'Spike.Lib.LowerX64.fnSpecC2_allI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnSpecC2_allI

/-- info: 'Spike.Lib.LowerX64.hcal_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hcal_of

end Spike.Lib.LowerX64
