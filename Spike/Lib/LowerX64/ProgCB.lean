/-
**Every function's segment from the calls' and the callees' premises**
(x86-64, H7a calls): `fnSpecC_allI` (`Spike/Lib/LowerX64/ProgC.lean`) with
each code block's calls from `callC_of`
(`Spike/Lib/LowerX64/CallC.lean`), its callee's segment (`hcal`)
the callee's `FnSpecC`, at the callee's index (smaller, the call order) found
from the call's term in the caller's walk.

What is left are the premises at the contexts:

- `CallPre`: `callC_of`'s premises at a code block's context, but the
  callee's segment, at a callee room `D` (the region `rbR R`, the call's
  blocks inside `W` at `fs`);
- `CalleePre`: `FnSpecC`'s premises at a context (the callee's after a
  call, or `main`'s), with the entry invariant `J` and ghost `c0`;
  `CalleePre.seg`: the function's segment from its `FnSpecC`;
- `at_rsp0`: `%rsp` at a node of offset `0` is the region's base;
- `fnSpecC_all_ofPre`: every code block's `FnSpecC`, from `CallPre` at every
  context of `CxOk j` and, at each call from it, `CalleePre` at the callee's
  context after the call (`calleeR`, `calleeN` with `%rsp` at the region's
  base, the frame pushed).
-/
import Spike.Lib.LowerX64.CallC
import Spike.Lib.LowerX64.ProgC

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW CallTo)
open Scc.Emit.X64 (i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.LowerCallOrder (CallIn)
open Spike.Lib.X64Consumer (noRetBlk)

/-- **`callC_of`'s premises at a code block's context but the callee's
segment** (`hcal`), at the callee room `D`: the region and its room, the
call blocks' code, the ghosts closed under the frame runs at `fs`, the
call's covered `ret`-free blocks and its `callq` inside `W` at `fs`, the
callee's entry inside `W` at a function of the program, the calls'
arguments (see `callC_of`). -/
structure CallPre (p : Prog) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (W : FragS isa) (K : State → State → Prop) (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (fp ra : BitVec 64) (fs : List TermRun.Frame) (G0 : Ctl → Prop) (T : Expr → Prop)
    (D : Int) : Prop where
  hF : FStable R F
  hR : R.OK
  hD0 : 0 ≤ D
  hD8 : D % 8 = 0
  hlo : R.lo ≤ -(fr.size : Int) - 8 - D
  hhi : 16 ≤ R.hi
  hBl : ∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)]
  hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c'
  hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
    noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
    BlkW (fun s c => W s c fs) K exe endPc R F n blk
  hWBl : ∀ (n : ND) zc g k, Bl n.pc zc g k → n.o = oB fr → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
    BlkW (fun s c => W s c fs) K exe endPc R F n [(i64 (.call (rel g)), zc)]
  hWC : ∀ (n : ND) g dg, p.find? (·.name == g) = some dg →
    n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
    n.o = { oB fr with sp := (oB fr).sp - 8 } → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
    ∀ s c, At exe endPc R F n s c → W s c fs
  hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = []

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **`FnSpecC`'s premises at a context** (code facts `c`): the context in
`CxOk`, the return address with `RaOk`, the region and its room, the ghosts
`G0` closed under the frame runs at `fs` with the ghost `c0`, the body's
construct blocks inside `W` at `fs`, the aborts in `Ab`, the prologue
inside `W` at `fs` (`XProW`) at the entry invariant `J`, and the entry's
facts (the limit word, `%rbp`, the return address, the entry's source). -/
structure CalleePre (W : FragS isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isa) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop)
    (c : FnCode exe cells endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa) (J : AS → Ctl → Prop) (c0 : Ctl) :
    Prop where
  hcx : CxOk R F fs fp ra tp G0 Ab
  hra : RaOk ra
  hF : FStable R F
  hR : R.OK
  hlo : R.lo ≤ -8 - (c.fr.size : Int)
  hhi : 8 ≤ R.hi
  hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c'
  hWb : ∀ c0, G0 c0 → ∀ pc t s blk, SubCd (Cd ra) pc blk → Kind1 c.fr blk →
    BlkW (fun s c => W s c fs) K exe endPc (rbR R) F (bodyN p lbl c.fr fp ra c0 pc t s) blk
  hWs : ∀ c0, G0 c0 → ∀ pc t s k blk, SubCd (Cd ra) pc blk → Kind1 c.fr blk →
    BlkW (fun s c => W s c fs) K exe endPc (rbR R) F (pendN p lbl c.fr fp ra c0 pc t s k) blk
  hab : ∀ c0, G0 c0 → ∀ s c',
    At exe endPc (rbR R) F (abortN i T p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
      Ab s c' fs
  hg0 : G0 c0
  hpro : XProW (fun s c => W s c fs) K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn)
    (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps J
  hedge : ∀ σ c', J σ c' →
    ((ms fs).rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
      (ms fs).mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
        = none) ∧
      ∀ v : Val, (ms fs).G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt c.fr.size).toBitVec).toNat) ∧
    σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧
    (∀ sl, (∀ pr ∈ c.prs, ∀ k, rsOf c.fr pr = some k → sl k = σ.regs.rdi.toBitVec) →
      NJ p lbl (rsOf c.fr) d.body (ofEnv c.env) sl c') ∧
    LocalRun p c0 c'

omit [Kraken.Executable.ValidLayout exe] in
/-- **A function's segment at a context** from its `FnSpecC` and the
context's premises (`CalleePre`), the entry pinning the `%fs` base to `tp`
(`htp`). -/
theorem CalleePre.seg {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    {c : FnCode exe cells endPc RaOk Cd i T d} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa} {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre W K p lbl ms CxOk c R F fs fp ra tp G0 Ab J c0) (hs : FnSpecC W K p lbl ms CxOk c)
    (htp : ∀ σ c', J σ c' → σ.regs.fsBase = tp) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC p lbl exe endPc (rbR R) F fp ra tp c0 fs Ab) :=
  hs R F fs fp ra tp G0 Ab (fun s c => W s c fs) J c0 h.hcx h.hra h.hF h.hR h.hlo h.hhi (fun _ _ h => h) h.hG0
    h.hWb h.hWs h.hab h.hg0 h.hpro htp h.hedge

omit [Kraken.Executable.ValidLayout exe] in
/-- **`%rsp` at a node of offset `0` is the region's base**: the node's
invariant may claim it. -/
theorem at_rsp0 {R : Region} {F : MachineData → Prop} {pc : Int64} {J : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F ⟨pc, ⟨0, []⟩, J⟩ s c) :
    At exe endPc R F ⟨pc, ⟨0, []⟩, fun σ c => J σ c ∧ σ.regs.rsp.toBitVec = R.base⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  refine ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, ?_⟩
  have := hA.so .rsp 0 (by simp [SO.get])
  simpa [Region.addr, Reg64s.get64] using this

/-- **Every function of an `Accepted1` program is one segment, from the
premises at the contexts**: `fnSpecC_allI` with each code block's calls
(the code blocks lowered with plain calls, `hnone`) from `callC_of` at
`CallPre` (at every context of `CxOk j`, in the rebased
region, at some callee room `D`), the callee's segment from its `FnSpecC`
at the callee's context after the call (`CalleePre` at `calleeR`'s region,
`calleeN`'s entry with `%rsp` at the region's base, the frame pushed, some
ghosts `G0'`). The callee is the
code block the call's term names (in the caller's walk, `hTin`, so at a
smaller index; the premise is given that block's lookup `p.find?`). -/
theorem fnSpecC_all_ofPre (hp : Scc.Lower.Accepted1 p = true) {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hcode : ∀ (j : Nat) d, p[j]? = some d → FnCode exe cells endPc RaOk Cd i (T j) d)
    (hprog : ∀ j d (hd : p[j]? = some d), (hcode j d hd).lcx.prog = p)
    (hnone : ∀ j d (hd : p[j]? = some d), (hcode j d hd).lcx.frames = none)
    (hTin : ∀ j d (hd : p[j]? = some d) e, T j e →
      ∃ q ∈ lowerEnvsC (hcode j d hd).lcx.frames (hcode j d hd).env (hcode j d hd).n d.body, q.1 = e)
    (hpre : ∀ j d (hd : p[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      ∃ D, CallPre p exe endPc (rbR R) F W K (hcode j d hd).fr (Cd ra)
          ((hcode j d hd).Bl ra) fp ra fs G0 (T j) D ∧
        ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop) (j' : Nat) (dg : Decl)
          (hd' : p[j']? = some dg), j' < j → dg.name = g → p.find? (·.name == g) = some dg →
          FStable (calleeR (rbR R) (hcode j d hd).fr.size D) F' →
          CalleeF p lbl (hcode j d hd).fr (rbR R) F D fp ra i (T j) q frm F' →
          (∃ c x a e, G0 c ∧ T j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
            CallTo p c q.cE frm) → ArgV lbl q →
          (∃ pcB zc k, (hcode j d hd).Bl ra pcB zc (Scc.Lower.Names.user g) k ∧
            q.ra = (pcB + Int64.ofNat zc).toBitVec) →
          ∃ G0', CalleePre W K p lbl ms (CxOk j') (hcode j' dg hd') (calleeR (rbR R) (hcode j d hd).fr.size D) F'
            (frm :: fs) q.fp q.ra tp G0' Ab (fun σ c => (calleeN (_root_.Executable.labels exe).label g tp q).J σ c ∧
              σ.regs.rsp.toBitVec = (calleeR (rbR R) (hcode j d hd).fr.size D).base) q.cE) :
    ∀ (j : Nat) d (hd : p[j]? = some d), FnSpecC W K p lbl ms (CxOk j) (hcode j d hd) := by
  refine fnSpecC_allI hp hcode hnone fun j d hd ih R F fs fp ra tp G0 Ab hcx hra => ?_
  obtain ⟨D, hb, hc⟩ := hpre j d hd R F fs fp ra tp G0 Ab hcx hra
  refine callC_of (hcode j d hd).hf (hcode j d hd).h1 (hprog j d hd) hb.hF hb.hR hb.hD0 hb.hD8 hb.hlo hb.hhi
    ((hcode j d hd).hCd ra hra) hb.hBl (W₀ := fun s c => W s c fs) (fun _ _ h => h) hb.hG0 hb.hWB hb.hWBl hb.hWC
    hb.hTc ?_
  intro g q frm F' hFS hCF hc3 harg hbl
  obtain ⟨c, x, a, e, hg, hT, hct, hcall⟩ := hc3
  obtain ⟨x', f, a', e', dg, t, ws, ht, hfd, -, -, -⟩ := id hcall
  rw [hct] at ht
  cases ht
  obtain ⟨qw, hqw, hq1⟩ := hTin j d hd _ hT
  obtain ⟨j', hlt, hd', hs⟩ := ih g dg ⟨qw, hqw, x, [], a, [], e, hq1⟩ hfd
  have hname : dg.name = g := by simpa using List.find?_some hfd
  obtain ⟨G0', hcp⟩ := hc g q frm F' j' dg hd' hlt hname hfd hFS hCF ⟨c, x, a, e, hg, hT, hct, hcall⟩ harg hbl
  have hfn : (hcode j' dg hd').fn = Scc.Lower.Names.user g := by rw [(hcode j' dg hd').hfn, hname]
  have H := hcp.seg hs fun σ c h => calleeN_tp σ c h.1
  rw [hfn] at H
  exact H.mono_pre fun s c fs ⟨hA, hfs⟩ => ⟨at_rsp0 hA, hfs⟩

end Spike.Lib.LowerX64
