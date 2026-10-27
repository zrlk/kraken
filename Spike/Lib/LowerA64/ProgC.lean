/-
**Every function of an `Accepted1` program is one segment** (AArch64, H7a
calls): the code facts of each code block (`FnCode`), the function's
segment at every context (`FnSpecC`), and the induction over the call
order (`fnSpecC_allI`). The twin of `Spike/Lib/LowerX64/ProgC.lean`, with
the call premise abstract: a code block's body segment at every context
(`BodySpecC`) is what its calls must give, from the plain calls
(`bodySpecC_of_call`, `bodyC_segS` with `CallC`) or from any other
lowering of the calls.

- `InWalkC`, `InWalkD`, `fresh_env1`: a term at a point of some code
  block's (of a given code block's) walk with calls; a code block's entry
  environment fresh from `0`.
- `FnCode`: a code block's code facts (lowering context, frame, prologue
  with its spill, body's lowering and code, walk's immediates and returns),
  without the lowering context's depth limit.
- `BodyAt`, `BodySpecC`, `FnSpecC`: the body's segment from its entry node
  at a context and at every context `CxOk`, and the function's from its
  label, to the exits `ExitC`.
- `fnSpecC_of_body`: the function's segment from the body's (the
  prologue, `fnC_segB`).
- `bodySpecC_of_call`: the body's segment from the plain calls, lowered
  without the depth counter (`bodyC_segS`).
- `fnSpecC_allI`: every code block's `FnSpecC` at contexts indexed by the
  code block, its body's segment from the callees' `FnSpecC` at smaller
  indices (`specs_of_callOrderLt`).
-/
import Spike.Lib.LowerA64.FnC
import Spike.Lib.LowerCallOrder
import Spike.Lib.SlotOrderC1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lowerC Res1 params1R env1)
open Spike.Lib.LowerCallOrder (CallIn)

/-- **A term at a point of some code block's walk with calls** (from its
entry environment, at the depth limit `frames`). -/
def InWalkC (p : Prog) (frames : Option Nat) (e : Expr) : Prop :=
  ∃ d ∈ p, ∃ q ∈ lowerEnvsC frames (env1 d) 0 d.body, q.1 = e

/-- **A term at a point of the code block `d`'s walk with calls** (from its
entry environment, at the depth limit `frames`). -/
def InWalkD (frames : Option Nat) (d : Decl) (e : Expr) : Prop :=
  ∃ q ∈ lowerEnvsC frames (env1 d) 0 d.body, q.1 = e

/-- A point of a code block's walk is a point of some code block's walk. -/
theorem InWalkD.inWalkC {p : Prog} {frames : Option Nat} {d : Decl} (hd : d ∈ p) {e : Expr}
    (h : InWalkD frames d e) : InWalkC p frames e :=
  let ⟨q, hq, he⟩ := h; ⟨d, hd, q, hq, he⟩

/-- **A code block's entry environment is fresh from `0`**: its parameter
register `x.0` is no `fresh` name (`param_ne_regName`). -/
theorem fresh_env1 (d : Decl) : Fresh (env1 d) 0 := by
  intro v hv o ho r hr y k _
  simp only [env1, List.mem_singleton] at hv
  subst hv
  simp only [params1R] at ho
  split at ho
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho
    subst ho
    cases hr
    exact Spike.Lib.SlotOrder.param_ne_regName d.arg y k
  · cases ho

section ProgC

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
  {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **A code block's code facts** at the program `prog` laid out in `exe`
(ending at `endPc`), the code predicates `Cd ra` at each return address
`ra` with `RaOk ra`, the immediates `i` and the walk predicate `T`: its
lowering context `lcx`, block predicate `Bl ra`, frame `cx`, label and
prologue with its parameter spill, its body's lowering from the
environment `env` and counter `n`, the code of its blocks, its walk's
immediates and returns. Unlike the x86-64 one, no depth limit of `lcx`
(the call premise's business). -/
structure FnCode (exe : _root_.Executable) (prog : List Directive) (endPc : Int64)
    (RaOk : BitVec 64 → Prop) (Cd : BitVec 64 → Int64 → List Directive → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (d : Decl) where
  lcx : Scc.Lower.Ctx
  Bl : BitVec 64 → Int64 → Label → Nat → Prop
  cx : FnCtx
  fn : Label
  entry : Label
  kp : Nat
  env : Scc.Lower.Env
  n : Nat
  l : Scc.IR.Label
  k : Nat
  r : Res1
  kk : Nat
  ps : List (XReg × Int64)
  prs : List Scc.IR.Reg
  hf : FrameOk cx
  h1 : cx.frame ≤ 4095
  h16 : cx.frame % 16 = 0
  hp : Lays exe prog kp
  hend : endPc = endOf exe prog kp
  hfn : fn = Scc.Lower.Names.user d.name
  hpro : prologueIn prog fn (cx.local "stack_check") entry (Int64.ofInt cx.frame)
    (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) ps = true
  hsp : ParamSpill cx ps prs
  hr : lowerC lcx env n l k d.body = some r
  hfr : Fresh env n
  hCd : ∀ ra, RaOk ra → ∀ pc blk, Cd ra pc blk → CdOf exe endPc pc blk
  hcode : ∀ ra, RaOk ra → CodeC cx (Cd ra) (Bl ra) kk ((_root_.Executable.labels exe).label entry) r.insts r.term
  hbl : ∀ ra, RaOk ra → BlocksCodeC cx (Cd ra) (Bl ra) (_root_.Executable.labels exe).label r.blocks
  hImm : ∀ q ∈ lowerEnvsC lcx.frames env n d.body, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1
  hOne : ∀ q ∈ lowerEnvsC lcx.frames env n d.body, RetOne q

/-- **Code facts at a weaker walk predicate** (`T` only in `hImm`). -/
def FnCode.monoT {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T T' : Expr → Prop} {d : Decl}
    (c : FnCode exe prog endPc RaOk Cd i T d) (hT : ∀ e, T e → T' e) : FnCode exe prog endPc RaOk Cd i T' d :=
  { c with hImm := fun q hq => ⟨(c.hImm q hq).1, hT _ (c.hImm q hq).2⟩ }

/-- **A code block's body segment at a context** (code facts `c`, the
code predicate `Cd'` at the context's return address): from the body's
entry node at the frames `fs` (any ghost `c0` in `G0`, the thread pointer
`tp`) in the region `R` meeting `bodyC_segS`'s block premises (for any
fragment `W₀` inside `W` at `fs`) to its exits `ExitC`. -/
def BodyAt (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode exe prog endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2) : Prop :=
  ∀ (W₀ : Frag isaLSE2) (c0 : Ctl),
    FStable R F → R.OK → R.base.toNat % 16 = 0 → R.lo ≤ -(c.cx.frame : Int) → 0 ≤ R.hi →
    (∀ s c, W₀ s c → W s c fs) →
    (∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c') →
    (∀ c0, G0 c0 → ∀ pc t s blk, SubCd (Cd ra) pc blk → Kind1 c.cx blk →
      BlkW W₀ K exe endPc R F (bodyN p lbl c.cx fp ra c0 pc t s) blk) →
    (∀ c0, G0 c0 → ∀ pc t s k blk, SubCd (Cd ra) pc blk → Kind1 c.cx blk →
      BlkW W₀ K exe endPc R F (pendN p lbl c.cx fp ra c0 pc t s k) blk) →
    (∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs) →
    G0 c0 →
    SegWS W K p lbl ms
      ((At exe endPc R F ((bodyN p lbl c.cx fp ra c0 ((_root_.Executable.labels exe).label c.entry) d.body
        (ofEnv c.env)).withTp tp)).at fs)
      (ExitC p lbl exe endPc R F fp ra tp c0 fs Ab)

/-- **A code block's body segment** (code facts `c`): `BodyAt` at every
context `CxOk` (every return address with `RaOk`). What the code block's
calls give (`bodySpecC_of_call`). -/
def BodySpecC (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop)
    (c : FnCode exe prog endPc RaOk Cd i T d) : Prop :=
  ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
    CxOk R F fs fp ra tp G0 Ab → RaOk ra → BodyAt W K p lbl ms c R F fs fp ra tp G0 Ab

/-- **A function's segment** (code facts `c`): from its label at any
frames `fs` (`sp` at 0, the entry invariant `J` pinning the thread pointer
to `tp`) in any context `CxOk` meeting `bodyC_segS`'s and the prologue's
premises to its exits `ExitC`. -/
def FnSpecC (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop)
    (c : FnCode exe prog endPc RaOk Cd i T d) : Prop :=
  ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isaLSE2) (W₀ : Frag isaLSE2) (J : AS → Ctl → Prop) (c0 : Ctl),
    CxOk R F fs fp ra tp G0 Ab → RaOk ra →
    FStable R F → R.OK → R.base.toNat % 16 = 0 → R.lo ≤ -(c.cx.frame : Int) → 0 ≤ R.hi →
    (∀ s c, W₀ s c → W s c fs) →
    (∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c') →
    (∀ c0, G0 c0 → ∀ pc t s blk, SubCd (Cd ra) pc blk → Kind1 c.cx blk →
      BlkW W₀ K exe endPc R F (bodyN p lbl c.cx fp ra c0 pc t s) blk) →
    (∀ c0, G0 c0 → ∀ pc t s k blk, SubCd (Cd ra) pc blk → Kind1 c.cx blk →
      BlkW W₀ K exe endPc R F (pendN p lbl c.cx fp ra c0 pc t s k) blk) →
    (∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs) →
    G0 c0 →
    ProW W₀ K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.cx) c.ps J →
    (∀ σ c', J σ c' → σ.regs.TPIDR_EL0 = tp) →
    (∀ σ c', J σ c' →
      ((ms fs).rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
        (ms fs).mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
        ∀ v : Val, (ms fs).G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt c.cx.frame).toBitVec).toNat) ∧
      σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧
      (∀ sl, (∀ pr ∈ c.prs, ∀ k, rsOf c.cx pr = some k → sl k = σ.regs.X0.toBitVec) →
        NJ p lbl (rsOf c.cx) d.body (ofEnv c.env) sl c') ∧
      LocalRun p c0 c') →
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC p lbl exe endPc R F fp ra tp c0 fs Ab)

/-- **A function's segment from its body's** (`fnC_segB`): the prologue
then the body's segment at the same context. -/
theorem fnSpecC_of_body {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (c : FnCode exe prog endPc RaOk Cd i T d) (hb : BodySpecC W K p lbl ms CxOk c) :
    FnSpecC W K p lbl ms CxOk c := by
  intro R F fs fp ra tp G0 Ab W₀ J c0 hcx hra hF hR hal hlo hhi hW₀ hG0 hWb hWs hab hg0 hWpro htp hedge
  exact fnC_segB c.hf c.h1 c.h16 c.hp c.hend c.hpro c.hsp hF hR hal hlo hhi hW₀
    (hb R F fs fp ra tp G0 Ab hcx hra W₀ c0 hF hR hal hlo hhi hW₀ hG0 hWb hWs hab hg0) hWpro htp hedge

omit [Kraken.Executable.ValidLayout exe] in
/-- **A body's segment from its plain calls** (`bodyC_segS`): lowered
without the depth counter (`hfrm`), the plain calls at every context `CxOk`
(every return address with `RaOk`) give `BodySpecC`. -/
theorem bodySpecC_of_call {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (c : FnCode exe prog endPc RaOk Cd i T d) (hfrm : c.lcx.frames = none)
    (hcl : ∀ R F fs fp ra tp G0 Ab, CxOk R F fs fp ra tp G0 Ab → RaOk ra →
      CallC p lbl c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab) :
    BodySpecC W K p lbl ms CxOk c := by
  intro R F fs fp ra tp G0 Ab hcx hra W₀ c0 hF hR hal hlo hhi hW₀ hG0 hWb hWs hab hg0
  exact bodyC_segS c.hf c.h1 c.h16 hF hR hal hlo hhi (c.hCd ra hra) hW₀ hG0 hWb hWs hab hfrm
    (hcl R F fs fp ra tp G0 Ab hcx hra) _ _ _ _ _ _ _ _ c.hr c.hfr (c.hcode ra hra) (c.hbl ra hra) c.hImm c.hOne
    c0 hg0

/-- **Every function of an `Accepted1` program is one segment, at contexts
depending on the code block's index**: the `j`th code block's contexts
`CxOk j` and walk predicate `T j`, its body's segment (`hbody_of`, e.g.
from its plain calls, `bodySpecC_of_call`) from each callee's
`FnSpecC` at its own index `j' < j` (`specs_of_callOrderLt`). -/
theorem fnSpecC_allI (hp : Scc.Lower.Accepted1 p = true) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (hcode : ∀ (j : Nat) d, p[j]? = some d → FnCode exe prog endPc RaOk Cd i (T j) d)
    (hbody_of : ∀ (j : Nat) d (hd : p[j]? = some d),
      (∀ g dg, CallIn (hcode j d hd).lcx.frames (hcode j d hd).env (hcode j d hd).n d.body g →
        p.find? (·.name == g) = some dg →
        ∃ j' : Nat, j' < j ∧ ∃ hd' : p[j']? = some dg, FnSpecC W K p lbl ms (CxOk j') (hcode j' dg hd')) →
      BodySpecC W K p lbl ms (CxOk j) (hcode j d hd)) :
    ∀ (j : Nat) d (hd : p[j]? = some d), FnSpecC W K p lbl ms (CxOk j) (hcode j d hd) := by
  classical
  have H := Spike.Lib.LowerCallOrder.specs_of_callOrderLt hp
    (fun j d => if hd : p[j]? = some d then (hcode j d hd).lcx.frames else none)
    (fun j d => if hd : p[j]? = some d then (hcode j d hd).env else [])
    (fun j d => if hd : p[j]? = some d then (hcode j d hd).n else 0)
    (Spec := fun j d => ∃ hd : p[j]? = some d, FnSpecC W K p lbl ms (CxOk j) (hcode j d hd))
    fun j d hd ih => ⟨hd, fnSpecC_of_body (hcode j d hd) (hbody_of j d hd fun g dg hc hf => by
      obtain ⟨j', hlt, -, hd', hs⟩ := ih g dg (by simpa [hd] using hc) hf
      exact ⟨j', hlt, hd', hs⟩)⟩
  intro j d hd
  exact (H j d hd).2

end ProgC

end Spike.Lib.LowerA64
