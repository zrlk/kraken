/-
**Every function's segment from the calls' and the callees' premises**
(AArch64, H7a calls): `fnSpecC_allI` (`Spike/Lib/LowerA64/ProgC.lean`)
with each code block's body segment from its call premise (`CallPre`),
its callees' segments (`CalleeSegs`) the callees' `FnSpecC`, at the
callee's index (smaller, the call order) found from the call's term in the
caller's walk. The twin of `Spike/Lib/LowerX64/ProgCB.lean`, with the call
premise abstract: `CallPre` is what a lowering of the calls must give (a
plain call's, `callPreC_of` in `Spike/Lib/LowerA64/CallC.lean`).

- `CalleeSegs`: the callees' segments at a call site (`CallC`'s callee
  premise, the call's term in `T`): from the callee's entry `calleeN` at the pushed
  frame, in the callee's region below the frame with room `D`, to its exits;
- `CallPre`: at a context, the callees' segments give the body's segment
  (`BodyAt`);
- `CalleePre`: `FnSpecC`'s premises at a context (the callee's after a
  call, or `main`'s), with the entry invariant `J` and ghost `c0`;
  `CalleePre.seg`: the function's segment from its `FnSpecC`;
- `at_sp0`: `sp` at a node of offset `0` is the region's base;
- `fnSpecC_all_ofPre`: every code block's `FnSpecC`, from `CallPre` at
  every context of `CxOk j` and, at each call from it, `CalleePre` at the
  callee's context after the call (the callee's region, `calleeN` with `sp`
  at the region's base, the frame pushed).
-/
import Spike.Lib.LowerA64.ProgC
import Spike.Lib.LowerA64.CallIface

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.LowerCallOrder (CallIn)

/-- **The callees' segments at a call site** of the frame `cx` (block
predicate `Bl`) at the frames `fs`, the callee room `D`: for every callee
`g` called from a ghost in `G0` at a term in `T`, every callee ghost `q`
(`ArgV`, the return address after a `bl g`) and frame condition `F'`
(`CalleeF`, stable in the callee's region), the callee's segment at the
pushed frame `fr :: fs` from its entry `calleeN` to its exits `ExitC` in
its region `R.callee (-frame) (-D) 0` (`CallC`'s callee premise, the
call's term in `T`). -/
def CalleeSegs (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2) (K : State → State → Prop)
    (ms : List TermRun.Frame → MemSide isaLSE2) (cx : FnCtx) (Bl : Int64 → Label → Nat → Prop)
    (fp ra : BitVec 64) (tp : UInt64) (fs : List TermRun.Frame) (G0 : Ctl → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (D : Int) (Ab : FragS isaLSE2) : Prop :=
  ∀ (g : String) (q : CallG) (fr : TermRun.Frame) (F' : MachineData → Prop),
    FStable (R.callee (-(cx.frame : Int)) (-D) 0) F' → CalleeF p lbl cx R F D fp ra i T q fr F' →
    (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE fr) → ArgV lbl q →
    (∃ pcB k, Bl pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
    SegWS W K p lbl ms ((At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F'
        (calleeN (_root_.Executable.labels exe).label g tp q)).at (fr :: fs))
      (ExitC p lbl exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' q.fp q.ra tp q.cE (fr :: fs) Ab)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
  {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **A code block's call premise at a context**, at the callee room `D`:
the callees' segments (`CalleeSegs` at the code block's frame and block
predicate at `ra`) give the body's segment there (`BodyAt`). Supplied by
the lowering of the calls (the plain call's `callPreC_of` at the context,
from `bodyC_segS`). -/
def CallPre (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode exe prog endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2) (D : Int) : Prop :=
  CalleeSegs p lbl exe endPc R F W K ms c.cx (c.Bl ra) fp ra tp fs G0 i T D Ab →
    BodyAt W K p lbl ms c R F fs fp ra tp G0 Ab

/-- **`FnSpecC`'s premises at a context** (code facts `c`): the context
`CxOk`, the return address `RaOk`, the region holding the frame, the ghosts
closed under the frame runs at `fs`, the body's blocks and the prologue
inside `W` at `fs`, the aborts, the ghost `c0`, the entry invariant `J`'s
limit facts and ghosts. -/
structure CalleePre (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isaLSE2) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop)
    (c : FnCode exe prog endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2) (J : AS → Ctl → Prop) (c0 : Ctl) :
    Prop where
  hcx : CxOk R F fs fp ra tp G0 Ab
  hra : RaOk ra
  hF : FStable R F
  hR : R.OK
  hal : R.base.toNat % 16 = 0
  hlo : R.lo ≤ -(c.cx.frame : Int)
  hhi : 0 ≤ R.hi
  hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c'
  hWb : ∀ c0, G0 c0 → ∀ pc t s blk, SubCd (Cd ra) pc blk → Kind1 c.cx blk →
    BlkW (fun s c => W s c fs) K exe endPc R F (bodyN p lbl c.cx fp ra c0 pc t s) blk
  hWs : ∀ c0, G0 c0 → ∀ pc t s k blk, SubCd (Cd ra) pc blk → Kind1 c.cx blk →
    BlkW (fun s c => W s c fs) K exe endPc R F (pendN p lbl c.cx fp ra c0 pc t s k) blk
  hab : ∀ c0, G0 c0 → ∀ s c',
    At exe endPc R F (abortN i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' → Ab s c' fs
  hg0 : G0 c0
  hpro : ProW (fun s c => W s c fs) K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn)
    (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.cx) c.ps J
  hedge : ∀ σ c', J σ c' →
    ((ms fs).rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
      (ms fs).mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
      ∀ v : Val, (ms fs).G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt c.cx.frame).toBitVec).toNat) ∧
    σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧
    (∀ sl, (∀ pr ∈ c.prs, ∀ k, rsOf c.cx pr = some k → sl k = σ.regs.X0.toBitVec) →
      NJ p lbl (rsOf c.cx) d.body (ofEnv c.env) sl c') ∧
    LocalRun p c0 c'

omit [Kraken.Executable.ValidLayout exe] in
/-- **A function's segment at a context** from its `FnSpecC` and the
context's premises (`CalleePre`), the entry pinning the thread pointer to
`tp` (`htp`). -/
theorem CalleePre.seg {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    {c : FnCode exe prog endPc RaOk Cd i T d} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2} {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre W K p lbl ms CxOk c R F fs fp ra tp G0 Ab J c0) (hs : FnSpecC W K p lbl ms CxOk c)
    (htp : ∀ σ c', J σ c' → σ.regs.TPIDR_EL0 = tp) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC p lbl exe endPc R F fp ra tp c0 fs Ab) :=
  hs R F fs fp ra tp G0 Ab (fun s c => W s c fs) J c0 h.hcx h.hra h.hF h.hR h.hal h.hlo h.hhi (fun _ _ h => h)
    h.hG0 h.hWb h.hWs h.hab h.hg0 h.hpro htp h.hedge

omit [Kraken.Executable.ValidLayout exe] in
/-- **`sp` at a node of offset `0` is the region's base**: the node's
invariant may claim it. -/
theorem at_sp0 {R : Region} {F : MachineData → Prop} {pc : Int64} {J : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F ⟨pc, ⟨0, []⟩, J⟩ s c) :
    At exe endPc R F ⟨pc, ⟨0, []⟩, fun σ c => J σ c ∧ σ.regs.SP.toBitVec = R.base⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  refine ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, ?_⟩
  have := hA.so .SP 0 rfl
  simpa [Region.addr, Reg64s.getRegOrSp64] using this

/-- The callee's entry pins the thread pointer. -/
theorem calleeN_tp {lab : Label → Int64} {g : String} {tp : UInt64} {q : CallG} (σ : AS) (c : Ctl)
    (h : (calleeN lab g tp q).J σ c) : σ.regs.TPIDR_EL0 = tp :=
  h.2.2.2.2

/-- **Every function of an `Accepted1` program is one segment, from the
premises at the contexts**: `fnSpecC_allI` with each code block's body
segment from its call premise (`CallPre`, at every context of `CxOk j`, at
some callee room `D`), the callees' segments from their `FnSpecC` at the
callee's context after the call (`CalleePre` in the callee's region,
`calleeN`'s entry with `sp` at the region's base, the frame pushed, some
ghosts `G0'`). The callee is the code block the call's term names (in the
caller's walk, `hTin`, so at a smaller index; the premise is given that
block's lookup `p.find?`). -/
theorem fnSpecC_all_ofPre (hp : Scc.Lower.Accepted1 p = true) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (hcode : ∀ (j : Nat) d, p[j]? = some d → FnCode exe prog endPc RaOk Cd i (T j) d)
    (hTin : ∀ j d (hd : p[j]? = some d) e, T j e →
      ∃ q ∈ lowerEnvsC (hcode j d hd).lcx.frames (hcode j d hd).env (hcode j d hd).n d.body, q.1 = e)
    (hpre : ∀ j d (hd : p[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      ∃ D, CallPre W K p lbl ms (hcode j d hd) R F fs fp ra tp G0 Ab D ∧
        ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop) (j' : Nat) (dg : Decl)
          (hd' : p[j']? = some dg), j' < j → dg.name = g → p.find? (·.name == g) = some dg →
          FStable (R.callee (-((hcode j d hd).cx.frame : Int)) (-D) 0) F' →
          CalleeF p lbl (hcode j d hd).cx R F D fp ra i (T j) q frm F' →
          (∃ c x a e, G0 c ∧ T j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
            CallTo p c q.cE frm) → ArgV lbl q →
          (∃ pcB k, (hcode j d hd).Bl ra pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
          ∃ G0', CalleePre W K p lbl ms (CxOk j') (hcode j' dg hd')
            (R.callee (-((hcode j d hd).cx.frame : Int)) (-D) 0) F' (frm :: fs) q.fp q.ra tp G0' Ab
            (fun σ c => (calleeN (_root_.Executable.labels exe).label g tp q).J σ c ∧
              σ.regs.SP.toBitVec = (R.callee (-((hcode j d hd).cx.frame : Int)) (-D) 0).base) q.cE) :
    ∀ (j : Nat) d (hd : p[j]? = some d), FnSpecC W K p lbl ms (CxOk j) (hcode j d hd) := by
  refine fnSpecC_allI hp hcode fun j d hd ih R F fs fp ra tp G0 Ab hcx hra => ?_
  obtain ⟨D, hcp, hc⟩ := hpre j d hd R F fs fp ra tp G0 Ab hcx hra
  refine hcp ?_
  intro g q frm F' hFS hCF hc3 harg hbl
  obtain ⟨c, x, a, e, hg, hT, hct, hcall⟩ := hc3
  obtain ⟨x', f, a', e', dg, t, ws, ht, hfd, -, -, -⟩ := id hcall
  rw [hct] at ht
  cases ht
  obtain ⟨qw, hqw, hq1⟩ := hTin j d hd _ hT
  obtain ⟨j', hlt, hd', hs⟩ := ih g dg ⟨qw, hqw, x, [], a, [], e, hq1⟩ hfd
  have hname : dg.name = g := by simpa using List.find?_some hfd
  obtain ⟨G0', hcp'⟩ := hc g q frm F' j' dg hd' hlt hname hfd hFS hCF ⟨c, x, a, e, hg, hT, hct, hcall⟩ harg hbl
  have hfn : (hcode j' dg hd').fn = Scc.Lower.Names.user g := by rw [(hcode j' dg hd').hfn, hname]
  have H := hcp'.seg hs fun σ c h => calleeN_tp σ c h.1
  rw [hfn] at H
  exact H.mono_pre fun s c fs ⟨hA, hfs⟩ => ⟨at_sp0 hA, hfs⟩

end Spike.Lib.LowerA64
