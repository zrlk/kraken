/-
**A base context for lane stores and buffers inside `W2`** (x86-64; the
twin of `Spike/Lib/LowerA64/CxLB.lean`): the facts a context of a compiled
block gives `laneC_w2E` (`Spike/Lib/LowerX64/LaneCW2.lean`) and
`newBufC_of` (`Spike/Lib/LowerX64/NewBufC2.lean`), stated as they consume
them, so that a call-free block's `FnSpecC2` (`fnSpecC2_ofLaneBuf`,
`Spike/Lib/LowerX64/FnSpecLaneBuf2.lean`) follows at every context implying
them in the rebased region `rbR R`. Generic in the program, the block's
code, the region, the placement and the `W2` instance (its read side `rd`
and the layout's immediates `Λ.imms` included); the allocations'
`AllocW2At` (`hAW`) is `allocW2_w2Full`'s
(`Spike/Lib/LowerX64/AllocW2Full.lean`) conclusion.

- `CxLB`: the context's facts; the region bound `hlo` at the allocator's
  form `-size - 8 + -160 - 32` (`allocW2_w2Full`'s);
- `CxLB.hloF`, `CxLB.hloA`: the bounds `laneC_w2E` and `newBufC_of` take;
- `fnSpecC2_ofCxLB`: `FnSpecC2` of a call-free block at code `CdCLE` and
  immediates `Λ.imms`, at the `W2` instance, from `CxLB` at its contexts'
  rebased regions.
-/
import Spike.Lib.LowerX64.FnSpecLaneBuf2
import Spike.Lib.LowerX64.LaneCW2
import Spike.Lib.LowerX64.AllocW2Full

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun FrameRunM MemSide)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (FStable At AS)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Flow.NewBuf (nbX allocAbortDepth)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad LblRoom IsNum LblRange)
open Scc.Emit.X64 (i64 rel)

/-- **A context's facts for lane stores and buffers inside `W2`** at the
region `R` (the block's, `rbR` of the context's), frame condition `F`,
frames `fs`, saved pair `fp`/`ra`, thread pointer `tp`, ghosts `G0` and
aborts `Ab'`: for the block's lowering context `lcx`, frame `fr`, code
`Cd`, calls `Bl`, immediates `i`, walk predicate `T` and literal lookups
`Lk`, inside the `W2` instance at `Λ`, `rd`, … and the placement `lbl`,
`lsize`, the memory side `ms`. The region's facts (`hlo` at the
allocator's depth), the frame's registers' slots in the region (`hrs`),
the frames placed (`hfp`), reads numbers (`hrd`), the labels' room and
range (`hroom`, `hrg`), no runtime word loaded (`hwn`), the placed labels'
words heap words (`hHW`), the ghosts free of `ZBad` (`hG0F`) and closed
under frame runs (`hG0`), the memory side's kernel (`hK`), each
allocation's `AllocW2` (`hAW`, `AllocW2At`, `allocW2_w2Full`'s) and its
heap abort, from a call node `NbJcOf`, in `Ab'` (`hAb`). -/
structure CxLB (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : Own) (rS : Range) (Tk : State → Prop) (ar : Arena) (Jv : InvS) (Dt : State → Prop)
    (lab : Label → Int64) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (ms : List TermRun.Frame → MemSide isa) (lbl : Lbl) (lsize : Lsize) (lcx : Scc.Lower.Ctx)
    (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop)
    (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab' : FragS isa) : Prop where
  hR : R.OK
  hR8 : R.base.toNat % 8 = 0
  hl : R.lo % 8 = 0
  hh : R.hi % 8 = 0
  hlo : R.lo ≤ -(fr.size : Int) - 8 + -160 - 32
  hhi : 16 ≤ R.hi
  hFS : FStable R F
  hFO : ∀ m, F m → StackOff rS R m
  hrs : ∀ r k, rsOf fr r = some k → R.Off k
  hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B
  hrd : ∀ w', (ms fs).rd w' → IsNum w'
  hroom : LblRoom lbl
  hrg : LblRange Λ lbl lsize
  hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone Λ m.dmem
  hHW : ∀ l b k (A : BitVec 64), lbl l = some b → k < lsize l → A.toNat = b + 8 * k →
    HeapW Λ own ar lbl lsize F A
  hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs
  hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c'
  hK : (ms fs).K = some Scc.Sem.X64.abi
  hAW : AllocW2At p lbl lsize lcx fr Cd Bl
    (fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F (ms fs) fp ra tp
    G0 i T Lk
  hAb : ∀ (Jc : AS → Ctl → Prop) (pcR : Int64) s c, NbJcOf i lbl fr Jc → (∀ σ c', Jc σ c' → T c'.term) →
    At exe endPc R F (nbX (ms fs) (_root_.Executable.labels exe).label lbl R fr.size pcR Jc .abort) s c →
      Ab' s c fs

namespace CxLB

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {Jv : InvS} {Dt : State → Prop}
  {lab : Label → Int64} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {ms : List TermRun.Frame → MemSide isa} {lbl : Lbl} {lsize : Lsize} {lcx : Scc.Lower.Ctx}
  {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
  {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
  {G0 : Ctl → Prop} {Ab' : FragS isa}

/-- The frame's bound (`laneC_w2E`'s `hlo`). -/
theorem hloF (H : CxLB Λ μ p rd G own rS Tk ar Jv Dt lab K exe endPc ms lbl lsize lcx fr Cd Bl i T Lk R F fs fp ra
    tp G0 Ab') : R.lo ≤ -(fr.size : Int) := by
  have := H.hlo; omega

/-- The heap abort's bound (`newBufC_of`'s `hlo`). -/
theorem hloA (H : CxLB Λ μ p rd G own rS Tk ar Jv Dt lab K exe endPc ms lbl lsize lcx fr Cd Bl i T Lk R F fs fp ra
    tp G0 Ab') : R.lo ≤ -allocAbortDepth (fr.size : Int) := by
  have := H.hlo
  simp only [allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]; omega

end CxLB

section Fn

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {Jv : InvS} {Dt : State → Prop}
  {lbl : Lbl} {lsize : Lsize} {ms : List TermRun.Frame → MemSide isa}

/-- **A call-free block's segment inside `W2` from `CxLB`**
(`fnSpecC2_ofLaneBuf`): a compiled block at the code `CdCLE` and the
immediates `Λ.imms` of the `W2` instance's layout, its walk predicate `T`
only at points of its body (`hT`), none a call (`hnc`), its allocations'
element types `elem2` (`hTn`), its calls in the code (`hBl`); at every
context `CxOk` (with `RaOk`) the facts `CxLB` in the rebased region `rbR R`
(`hcx`). The lane stores by `laneC_w2E`, the buffers by `newBufC_of`. -/
theorem fnSpecC2_ofCxLB (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hp : ProgNoS ZBad p)
    {RaOk : BitVec 64 → Prop} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (c : FnCode2 exe cells endPc RaOk (fun ra => CdCLE cells okPc ph lab (Int64.ofBitVec ra)) Λ.imms T d)
    (hT : ∀ t, T t → Spike.Lib.LowerNode.TailOf t d.body)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hBl : ∀ ra, RaOk ra → ∀ pc zc g k, c.Bl ra pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    (hcx : ∀ R F fs fp ra tp G0 Ab, CxOk R F fs fp ra tp G0 Ab → RaOk ra →
      CxLB Λ μ p rd G own rS Tk ar Jv Dt lab K exe endPc ms lbl lsize c.lcx c.fr
        (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) Λ.imms T (RetLk d.retTy) (rbR R) F fs fp ra tp G0
        Ab) :
    FnSpecC2 (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K p lbl lsize ms CxOk c := by
  refine fnSpecC2_ofLaneBuf c hT hnc fun R F fs fp ra tp G0 Ab' hc hra => ?_
  have H := hcx R F fs fp ra tp G0 Ab' hc hra
  refine ⟨laneC_w2E hI hpr hab c.hf c.h1 H.hR H.hR8 H.hloF H.hhi H.hl H.hh hsub hfit H.hFO H.hFS hp H.hrs
    H.hfp (lcx := c.lcx) (tp := tp) (fun _ _ h => h) H.hrd H.hroom H.hrg H.hwn H.hHW H.hG0F, ?_⟩
  exact newBufC_of c.hf c.h1 c.hp c.hend hA H.hFS H.hR H.hloA H.hhi (c.hCd ra hra) (hBl ra hra)
    (W₀ := fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) (fun _ _ h => h) H.hK
    H.hG0 hTn c.lcx H.hAW H.hAb

end Fn

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.CxLB.hloA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CxLB.hloA

/-- info: 'Spike.Lib.LowerX64.fnSpecC2_ofCxLB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnSpecC2_ofCxLB

end Spike.Lib.LowerX64
