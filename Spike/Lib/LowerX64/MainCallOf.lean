/-
**A context's premises for `main`'s call after the setup block, less the
fields the placement check gives** (x86-64): `CalleePre2R`, the record the
held-return route (`mainCallWSF_ofHeld`, `Spike/Lib/LowerX64/MainHeldX.lean`)
and its value variant (`Spike/Lib/LowerX64/HeldPostX.lean`) take per context,
with the return address's phase (`raOk_main`, at `setupMC sw`'s `sp1`) and
the prologue inside `W2` (`hpro_main_ofPlaceOK` at the entry `uNM`) left
to them.

- `CalleePre2R`: `CalleePre2` without `hra` and `hpro`, with the region
  facts `hpro_main_ofPlaceOK` reads;
- `CalleePre2R.toPre`: `CalleePre2` from it and the two fields.

`main`'s call is not routed through `FnSpecC2` at the empty frames (its
body's paths end in held returns, so the blocks' `BlkW` at a `ret` under no
frames is excluded by `CalleePre2`'s guard).
-/
import Spike.Lib.LowerX64.HproOf
import Spike.Lib.LowerX64.SetupCallC2
import Spike.Lib.LowerX64.HPlSOfSPostC
import Spike.Lib.LowerX64.RaMain2
import Spike.Lib.LowerX64.ProEdge2UNM

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW CallTo)
open Spike.Lib.X64Consumer (K0)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA WcG CallerCells)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2)

/-- **A context's premises without the return address and the prologue**
(`CalleePre2` less `hra`, `hpro`), with the region facts the prologue from
the placement check reads (`hpro_main_ofPlaceOK`'s `hR8`, `hl`, `hh`,
`hFO` at the stack `rS`). -/
structure CalleePre2R (W : FragS isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (ms : List TermRun.Frame → MemSide isa) {exe : _root_.Executable} {cells : List (Directive × Nat)}
    {endPc : Int64} {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop)
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (rS : Range) (R : Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa)
    (J : AS → Ctl → Prop) (c0 : Ctl) : Prop where
  hcx : CxOk R F fs fp ra tp G0 Ab
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
  hedge : ProEdge2 p lbl lsize (ms fs) F c fp ra tp c0 J
  hR8 : R.base.toNat % 8 = 0
  hl : R.lo % 8 = 0
  hh : R.hi % 8 = 0
  hFO : ∀ m, F m → StackOff rS R m

/-- **`CalleePre2` from its rest** and the two fields left out. -/
theorem CalleePre2R.toPre {W : FragS isa} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isa} {exe : _root_.Executable} {cells : List (Directive × Nat)}
    {endPc : Int64} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    {c : FnCode2 exe cells endPc RaOk Cd i T d} {rS : Range} {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre2R W K p lbl lsize ms CxOk c rS R F fs fp ra tp G0 Ab J c0) (hra : RaOk ra)
    (hpro : XProW (fun s c => W s c fs) K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label c.fn)
      (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps J) :
    CalleePre2 W K p lbl lsize ms CxOk c R F fs fp ra tp G0 Ab J c0 :=
  ⟨h.hcx, hra, h.hF, h.hR, h.hlo, h.hhi, h.hG0, h.hW, h.hWp, h.hab, h.hg0, hpro, h.hedge⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.CalleePre2R.toPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CalleePre2R.toPre

end Spike.Lib.LowerX64
