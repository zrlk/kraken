/-
**Every function of a lowered `Accepted1` program with calls is one segment**
(x86-64, H7a calls): the induction over the program's declarations
(`specs_of_callOrder`), each function's segment `fnC_segS` with its calls
(`CallC`, the lowering's calls plain) from its callees' segments (the call
step a premise).

- `FnCode`: a code block's code facts (its frame, prologue, lowering, code
  at the code predicates `Cd ra`/`Bl ra` of each return address `ra` with
  `RaOk ra`, its walk's immediates and returns).
- `FnSpecC`: the function's segment from its label at any frames `fs`, in
  any context `CxOk` (the region, frame data, frames, ghost and abort
  exits a call site provides) meeting `fnC_segS`'s premises, to its exits
  `ExitC`.
- `fnSpecC_of`: `FnSpecC` from the calls at every such context.
- `fnSpecC_all`: every code block's `FnSpecC`, from code facts for each
  (`hcode`) and the call step (`hbr_of`: the calls at a context from
  the callees' `FnSpecC`).
-/
import Spike.Lib.LowerX64.FnC
import Spike.Lib.LowerCallOrder
import Spike.Lib.Rt.X64SegsS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.LowerNode
open Spike.Lib.LowerCall (Callee)
open Scc.Lower.Inv (lowerC Res1)
open Spike.Lib.LowerCallOrder (CallIn specs_of_callOrder)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **A code block's code facts** at the cells `cells` laid out in `exe`
(ending at `endPc`), the lowering context `lcx`, the code predicates `Cd ra`,
at each return address `ra` with `RaOk ra`, the immediates `i` and the walk
predicate `T`: its lowering context, block predicate `Bl ra`, frame, label and prologue, its body's lowering
from the environment `env` and counter `n`, the code of its blocks, its
walk's immediates and returns. -/
structure FnCode (exe : _root_.Executable) (cells : List (Directive × Nat)) (endPc : Int64)
    (RaOk : BitVec 64 → Prop)
    (Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (d : Decl) where
  lcx : Scc.Lower.Ctx
  Bl : BitVec 64 → Int64 → Nat → Label → Nat → Prop
  fr : Scc.Emit.X64.Frame
  fn : String
  entry : String
  zl : Nat
  zf : Nat
  z1 : Nat
  z2 : Nat
  zs : Nat
  kp : Nat
  env : Scc.Lower.Env
  n : Nat
  l : Scc.IR.Label
  k : Nat
  r : Res1
  kk : Nat
  ps : List (Reg64 × Int64 × Nat)
  prs : List Scc.IR.Reg
  hf : FrameOk fr
  h1 : fr.size ≤ 2 ^ 31
  hp : Lays exe cells kp
  hend : endPc = endOf exe cells kp
  hfn : fn = Scc.Lower.Names.user d.name
  hpro : Spike.Lib.X64.Flow.prologueIn cells fn (Scc.Emit.X64.labelOf fr.fn "chk") entry (Int64.ofInt fr.size)
    (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs ps = true
  hps : (ps = [] ∧ prs = []) ∨ ∃ pr o zp, ps = [(.rdi, o, zp)] ∧ prs = [pr] ∧
    (∀ k, rsOf fr pr = some k → k = o.toInt) ∧ o.toInt ≤ -8 ∧ offOk (-8 - (fr.size : Int)) 0 (-8 + o.toInt) = true
  hr : lowerC lcx env n l k d.body = some r
  hfr : Fresh env n
  hCd : ∀ ra, RaOk ra → ∀ pc blk, Cd ra pc blk → CdOf exe endPc pc blk
  hcode : ∀ ra, RaOk ra → CodeC fr (Cd ra) (Bl ra) kk ((_root_.Executable.labels exe).label entry) r.insts r.term
  hbl : ∀ ra, RaOk ra → BlocksCodeC fr (Cd ra) (Bl ra) (_root_.Executable.labels exe).label r.blocks
  hImm : ∀ q ∈ lowerEnvsC lcx.frames env n d.body, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1
  hOne : ∀ q ∈ lowerEnvsC lcx.frames env n d.body, RetOne q

/-- **Code facts at a weaker walk predicate** (`T` only in `hImm`). -/
def FnCode.monoT {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T T' : Expr → Prop} {d : Decl}
    (c : FnCode exe cells endPc RaOk Cd i T d) (hT : ∀ e, T e → T' e) : FnCode exe cells endPc RaOk Cd i T' d :=
  { c with hImm := fun q hq => ⟨(c.hImm q hq).1, hT _ (c.hImm q hq).2⟩ }

/-- **The prologue's spills of an `Accepted1` code block** (`spills` at
its parameter registers `params1R d`): none, or `%rdi`'s at its parameter's
cell, an offset inside the frame (`FnCode.hps`). -/
theorem hps_of_spills {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {d : Decl}
    {zps : List Nat} {ps : List (Reg64 × Int64 × Nat)}
    (h : Scc.Cert.Code1X64.spills fr (Scc.Lower.Inv.params1R d) zps = some ps) :
    (ps = [] ∧ Scc.Lower.Inv.params1R d = []) ∨ ∃ pr o zp, ps = [(.rdi, o, zp)] ∧
      Scc.Lower.Inv.params1R d = [pr] ∧ (∀ k, rsOf fr pr = some k → k = o.toInt) ∧ o.toInt ≤ -8 ∧
      offOk (-8 - (fr.size : Int)) 0 (-8 + o.toInt) = true := by
  unfold Scc.Lower.Inv.params1R at h ⊢
  generalize s!"{d.arg}.{0}" = pr at h ⊢
  split
  · next hi =>
    simp only [hi, ite_true] at h
    refine .inr ?_
    unfold Scc.Cert.Code1X64.spills at h
    split at h
    · next hl =>
      simp only [Bool.and_eq_true, beq_iff_eq, List.length_cons, List.length_nil] at hl
      match zps, hl with
      | [zp], _ =>
        cases hr : rsOf fr pr with
        | none => simp [Scc.Emit.X64.argRegs, hr] at h
        | some o =>
          simp [Scc.Emit.X64.argRegs, hr] at h
          subst h
          obtain ⟨hb8, hm, hsz⟩ := rsOf_bounds hf hr
          have ho : (Int64.ofInt o).toInt = o := toInt_ofInt_small (by omega) (by omega)
          refine ⟨_, Int64.ofInt o, zp, rfl, rfl, fun k hk => ?_, by omega, ?_⟩
          · rw [ho]; rw [hr] at hk; exact (Option.some.inj hk).symm
          · rw [ho]; simp only [offOk, decide_eq_true_eq]; omega
    · cases h
  · next hi =>
    simp only [Bool.not_eq_true] at hi
    simp only [hi, Bool.false_eq_true, ite_false] at h
    refine .inl ⟨?_, rfl⟩
    unfold Scc.Cert.Code1X64.spills at h
    split at h
    · simpa using h.symm
    · cases h

/-- **A function's segment** (code facts `c`): from its label at any
frames `fs` (`%rsp` at 0, the entry invariant `J` pinning the `%fs` base to
`tp`) in any context `CxOk` meeting `fnC_segS`'s premises to its exits
`ExitC` in the rebased region. -/
def FnSpecC (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop)
    (c : FnCode exe cells endPc RaOk Cd i T d) : Prop :=
  ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isa) (W₀ : Frag isa) (J : AS → Ctl → Prop) (c0 : Ctl),
    CxOk R F fs fp ra tp G0 Ab → RaOk ra →
    FStable R F → R.OK → R.lo ≤ -8 - (c.fr.size : Int) → 8 ≤ R.hi →
    (∀ s c, W₀ s c → W s c fs) →
    (∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c') →
    (∀ c0, G0 c0 → ∀ pc t s blk, SubCd (Cd ra) pc blk → Kind1 c.fr blk →
      BlkW W₀ K exe endPc (rbR R) F (bodyN p lbl c.fr fp ra c0 pc t s) blk) →
    (∀ c0, G0 c0 → ∀ pc t s k blk, SubCd (Cd ra) pc blk → Kind1 c.fr blk →
      BlkW W₀ K exe endPc (rbR R) F (pendN p lbl c.fr fp ra c0 pc t s k) blk) →
    (∀ c0, G0 c0 → ∀ s c',
      At exe endPc (rbR R) F (abortN i T p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs) →
    G0 c0 →
    XProW W₀ K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps J →
    (∀ σ c', J σ c' → σ.regs.fsBase = tp) →
    (∀ σ c', J σ c' →
      ((ms fs).rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        (ms fs).mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, (ms fs).G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt c.fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧
      (∀ sl, (∀ pr ∈ c.prs, ∀ k, rsOf c.fr pr = some k → sl k = σ.regs.rdi.toBitVec) →
        NJ p lbl (rsOf c.fr) d.body (ofEnv c.env) sl c') ∧
      LocalRun p c0 c') →
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC p lbl exe endPc (rbR R) F fp ra tp c0 fs Ab)

/-- **A function's segment from its calls** (`fnC_segS`): the code block
lowered with plain calls (`hnone`) and its calls (`CallC`) at every context
`CxOk` (every return address with `RaOk`, in the rebased region) give
`FnSpecC`. -/
theorem fnSpecC_of {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (c : FnCode exe cells endPc RaOk Cd i T d) (hnone : c.lcx.frames = none)
    (hbr : ∀ R F fs fp ra tp G0 Ab, CxOk R F fs fp ra tp G0 Ab → RaOk ra →
      CallC p lbl c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab) :
    FnSpecC W K p lbl ms CxOk c := by
  intro R F fs fp ra tp G0 Ab W₀ J c0 hcx hra hF hR hlo hhi hW₀ hG0 hWb hWs hab hg0 hWpro htp hedge
  have hpro := c.hpro
  rcases c.hps with ⟨hps, hprs⟩ | ⟨pr, o, zp, hps, hprs, hpr, ho, hoff⟩
  · rw [hps] at hpro hWpro
    exact fnC_segS c.hf c.h1 c.hp c.hend hpro hF hR hlo hhi (c.hCd ra hra) hW₀ hG0 hWb hWs hab hnone
      (hbr R F fs fp ra tp G0 Ab hcx hra) c.hr c.hfr (c.hcode ra hra) (c.hbl ra hra) c.hImm c.hOne hg0 hWpro htp
      fun σ c' h => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hedge σ c' h
        exact ⟨h1, h2, h3, fun sl => h4 sl (by simp [hprs]), h5⟩
  · rw [hps] at hpro hWpro
    exact fnC_segSP c.hf c.h1 c.hp c.hend hpro hpr ho hoff hF hR hlo hhi (c.hCd ra hra) hW₀ hG0 hWb hWs hab
      hnone (hbr R F fs fp ra tp G0 Ab hcx hra) c.hr c.hfr (c.hcode ra hra) (c.hbl ra hra) c.hImm c.hOne hg0
      hWpro htp fun σ c' h => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hedge σ c' h
        exact ⟨h1, h2, h3, fun sl hsl => h4 sl (by simpa [hprs] using hsl), h5⟩

/-- **Every function of an `Accepted1` program is one segment**: from code
facts for every code block (`hcode`), each lowered with plain calls
(`hnone`), and the call step (`hbr_of`: the `j`th code block's calls at
every context from the `FnSpecC` of each
callee called in its walk, found by `find?`), every code block's
`FnSpecC`. By `specs_of_callOrder`: every callee's segment from its own
`fnC_segS`. -/
theorem fnSpecC_all (hp : Scc.Lower.Accepted1 p = true) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hcode : ∀ (j : Nat) d, p[j]? = some d → FnCode exe cells endPc RaOk Cd i T d)
    (hnone : ∀ (j : Nat) d (hd : p[j]? = some d), (hcode j d hd).lcx.frames = none)
    (hbr_of : ∀ (j : Nat) d (hd : p[j]? = some d),
      (∀ g dg, CallIn (hcode j d hd).lcx.frames (hcode j d hd).env (hcode j d hd).n d.body g → p.find? (·.name == g) = some dg →
        ∃ j' : Nat, ∃ hd' : p[j']? = some dg, FnSpecC W K p lbl ms CxOk (hcode j' dg hd')) →
      ∀ R F fs fp ra tp G0 Ab, CxOk R F fs fp ra tp G0 Ab → RaOk ra →
        CallC p lbl (hcode j d hd).lcx (hcode j d hd).fr (Cd ra)
          ((hcode j d hd).Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab) :
    ∀ (j : Nat) d (hd : p[j]? = some d), FnSpecC W K p lbl ms CxOk (hcode j d hd) := by
  classical
  have H := specs_of_callOrder hp
    (fun j d => if hd : p[j]? = some d then (hcode j d hd).lcx.frames else none)
    (fun j d => if hd : p[j]? = some d then (hcode j d hd).env else [])
    (fun j d => if hd : p[j]? = some d then (hcode j d hd).n else 0)
    (Spec := fun j d => ∃ hd : p[j]? = some d, FnSpecC W K p lbl ms CxOk (hcode j d hd))
    fun j d hd ih => ⟨hd, fnSpecC_of (hcode j d hd) (hnone j d hd) (hbr_of j d hd fun g dg hc hf => by
      obtain ⟨j', -, hd', hs⟩ := ih g dg (by simpa [hd] using hc) hf
      exact ⟨j', hd', hs⟩)⟩
  intro j d hd
  exact (H j d hd).2

/-- **`fnSpecC_all` at contexts depending on the code block's index**: the
`j`th code block's contexts `CxOk j` (e.g. carrying the call depth's bound
`fs.length + j < p.length`) and walk predicate `T j` (e.g. its own walk, so
that a call's term is a call of its walk), its calls from each callee's `FnSpecC` at
its own index `j' < j` (`specs_of_callOrderLt`). -/
theorem fnSpecC_allI (hp : Scc.Lower.Accepted1 p = true) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hcode : ∀ (j : Nat) d, p[j]? = some d → FnCode exe cells endPc RaOk Cd i (T j) d)
    (hnone : ∀ (j : Nat) d (hd : p[j]? = some d), (hcode j d hd).lcx.frames = none)
    (hbr_of : ∀ (j : Nat) d (hd : p[j]? = some d),
      (∀ g dg, CallIn (hcode j d hd).lcx.frames (hcode j d hd).env (hcode j d hd).n d.body g →
        p.find? (·.name == g) = some dg →
        ∃ j' : Nat, j' < j ∧ ∃ hd' : p[j']? = some dg, FnSpecC W K p lbl ms (CxOk j') (hcode j' dg hd')) →
      ∀ R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
        CallC p lbl (hcode j d hd).lcx (hcode j d hd).fr (Cd ra)
          ((hcode j d hd).Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i (T j) Ab) :
    ∀ (j : Nat) d (hd : p[j]? = some d), FnSpecC W K p lbl ms (CxOk j) (hcode j d hd) := by
  classical
  have H := Spike.Lib.LowerCallOrder.specs_of_callOrderLt hp
    (fun j d => if hd : p[j]? = some d then (hcode j d hd).lcx.frames else none)
    (fun j d => if hd : p[j]? = some d then (hcode j d hd).env else [])
    (fun j d => if hd : p[j]? = some d then (hcode j d hd).n else 0)
    (Spec := fun j d => ∃ hd : p[j]? = some d, FnSpecC W K p lbl ms (CxOk j) (hcode j d hd))
    fun j d hd ih => ⟨hd, fnSpecC_of (hcode j d hd) (hnone j d hd) (hbr_of j d hd fun g dg hc hf => by
      obtain ⟨j', hlt, -, hd', hs⟩ := ih g dg (by simpa [hd] using hc) hf
      exact ⟨j', hlt, hd', hs⟩)⟩
  intro j d hd
  exact (H j d hd).2

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_main`'s user function at depth from its exits**
(`UserCallWS`): at every frame condition and ghost of the interface, a
segment at the empty frames from the entry `uN0` to the exits `ExitC` of a
function (`hseg`, e.g. `main`'s `FnSpecC` at `[]`), its aborts `Ab` never
ending (`hAb`: the abort path's segment at depth) and its return node
past `ret` (after the source's frame run from the ghost) the
interface's return `uNx` (`hret`). -/
theorem userCallWS_of_exitC {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.X64.Flow.Ret0.CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : Spike.Lib.X64.Flow.Ret0.WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      ∃ (Ab : FragS isa) (fp ra' : BitVec 64) (c0' : Ctl),
        SegWS W K p lbl ms
          ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g)).at [])
          (ExitC p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' fp ra' tp c0' [] Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False) ∧
        ∀ c1 s c, FrameRun p (c0', []) (c1, []) →
          At exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' ((retN p lbl fp ra' c1).withTp tp) s c →
          At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' (Spike.Lib.X64.Rt.uNx Post g) s c) :
    Spike.Lib.X64.Rt.UserCallWS W K p lbl ms exe endPc R F fn Z D ZU Post ra c0 tp := by
  intro F' hR0 hF' hFF g hra hc htp
  obtain ⟨Ab, fp, ra', c0', h1, hAb, hret⟩ := hseg F' hR0 hF' hFF g hra hc htp
  refine (SegWS.seq_left (Q := Ab) (E := (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
      (Spike.Lib.X64.Rt.uNx Post g)).at []) (h1.mono_post fun s c fs h => ?_) hAb).mono_post fun s c fs h => ?_
  · rcases h with ⟨rfl, c1, hr, hA⟩ | h
    · exact .inr ⟨hret c1 s c hr hA, rfl⟩
    · exact .inl h
  · exact h.elim False.elim id

end Spike.Lib.LowerX64
