/-
**A context's premises for `main`'s call after the setup block, less the
fields the placement check and the setup call give** (AArch64; the twin of
`Spike/Lib/LowerX64/MainCallOf.lean`): `CalleePre2R`, the record the
held-return route (`mainCallWSF_ofHeld`, `Spike/Lib/LowerA64/MainHeldA.lean`)
and its value variant (`Spike/Lib/LowerA64/HeldPostA.lean`) take per
context, with the return address's phase (`raOk_main`, at `setupMC sw`'s
`sp1`), the prologue inside `W2` (`hpro_main_ofPlaceOK` at the entry `uNM`)
and the prologue's edge into `main`'s body (`proEdge2_ofUNM`) left to them.

- `CalleePre2R`: `CalleePre2` without `hra`, `hpro` and `hedge`, with the
  region facts `hpro_main_ofPlaceOK` reads;
- `CalleePre2R.toPre`: `CalleePre2` from it and the three fields.

`main`'s call is not routed through `FnSpecC2` at the empty frames (its
body's paths end in held returns, so the blocks' `BlkW` at a `ret` under no
frames is excluded by `CalleePre2`'s guard).
-/
import Spike.Lib.LowerA64.HproOf
import Spike.Lib.LowerA64.SetupCallC2
import Spike.Lib.LowerA64.HPlSOfSPostC
import Spike.Lib.LowerA64.RaMain2
import Spike.Lib.LowerA64.ProEdge2UNM

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (K0)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.A64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs)
open Spike.Lib.A64.Flow.Ret0 (StackOff limA WcG CallerCells)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 IsNum)

/-- **A context's premises without the return address, the prologue and
its edge** (`CalleePre2` less `hra`, `hpro`, `hedge`), with the region facts
the prologue from the placement check reads (`hpro_main_ofPlaceOK`'s `hl`,
`hh`, `hFO` at the stack `rS`). -/
structure CalleePre2R (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) {exe : _root_.Executable} {prog : List Directive}
    {endPc : Int64} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop)
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (rS : Range) (R : Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2)
    (c0 : Ctl) : Prop where
  hcx : CxOk R F fs fp ra tp G0 Ab
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
    At exe endPc R F (abortN2 i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
      Ab s c' fs
  hg0 : G0 c0
  hl : R.lo % 8 = 0
  hh : R.hi % 8 = 0
  hFO : ∀ m, F m → StackOff rS R m

/-- **`CalleePre2` from its rest** and the three fields left out. -/
theorem CalleePre2R.toPre {W : FragS isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} {exe : _root_.Executable} {prog : List Directive}
    {endPc : Int64} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    {c : FnCode2 exe prog endPc RaOk Cd i T d} {rS : Range} {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre2R W K p lbl lsize ms CxOk c rS R F fs fp ra tp G0 Ab c0) (hra : RaOk ra)
    (hpro : ProW (fun s c => W s c fs) K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn)
      (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.cx) c.ps J)
    (hedge : ProEdge2 p lbl lsize (ms fs) F c fp ra tp c0 J) :
    CalleePre2 W K p lbl lsize ms CxOk c R F fs fp ra tp G0 Ab J c0 :=
  ⟨h.hcx, hra, h.hF, h.hR, h.hal, h.hlo, h.hhi, h.hG0, h.hW, h.hWp, h.hab, h.hg0, hpro, hedge⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.CalleePre2R.toPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CalleePre2R.toPre

end Spike.Lib.LowerA64
