/-
**`hello1`'s setup call `hS` at the setup call's known frame condition,
the pieces named** (AArch64): `hS_assembledBAC`
(`Spike/Lib/LowerA64/HSAssembledBA.lean`) with every input the library
gives filled in, for the `hS` the assembled start segment under
`h0InA_setup_assembledCB` needs (`SetupCallWSB` at `SetupGF`), at every
choice of the bounds (`Bounds2A`).

Closed here: the setup block's compiled index and return type
(`rodata_of_setupOf`, `rodata_compiled2`), its label, the start's call of
it (`callTo_setupTerm`, `CallTo.unique`), the limit word's facts (`hms`,
`hmr`, `hun`), the stack's range, `ProgNoS`; and in the callee's
precondition: the context's stack records at the bottom frame (`CxOkS.bot`
from `SetupBot`, `setupBot_ofGF`), the region's facts (`hF`, `hR`, `hal`,
`hlo`, `hhi`, `hl`, `hh`, `hFO` by `stackOff_callee`), the ghosts (the
controls a frame run reaches from the callee's entry), the aborts (the abort
node's states), the callee's `FrOk2` (`FrOk2.step` at the call).

Open (`SetupOpenA`, at the setup block's compiled index `j` and a base
context `CxOk0`, the bottom keys the setup frame's `SetupBot`): the setup
function's segment `FnSpecC2` at `CxOkS … CxOk0 (SetupBot …) j`, the base context,
the setup function's construct blocks' branch and call targets off the write
abort (`hTg`) and the aborts' segment at the setup frame. The body's blocks
inside `W2` (`CalleePre2R`'s `hW`, `hWp`) are `cxBlk2_ofFn` at the callee
region, the suspended start frame placed by `framesPlaced_setup`, the ghosts' `FrOk2` by
`FrOk2.runM`, the return address `scc_rt_main`'s marshalling block at `sp0`
(`posOff_of_blockAt`, one instruction past `e0`: `label_labelGap`).
The code facts are the placement check's at the theorem's immediates
(`fnCode2OfPMe`, the ones the world `W2At … (imms2Me Λ p)` reads); their
parameter count, frame (`Bounds2A`'s frame row) and overflow stub
(`posOff_proL_of_fnOk1`) come from `fnCode2OfPMe_spec2`.

- `CxBlk2`, `AbOf2`: a context's blocks inside `W` (`CalleePre2R`'s `hW`,
  `hWp`) and its abort node's states;
- `cxBlk2_ofFn`: `CxBlk2` at `W2` from `cxBlk2_ofW2`
  (`Spike/Lib/LowerA64/CxBlk2Of.lean`);
- `SetupOpenA`, `OpenSA`: the open premises, at one choice and at every
  choice of the bounds;
- `HSBA`: the `hS` the skeleton needs at every choice of the bounds;
- `hS_ofOpenA`, `hSBA_ofOpenSA`: `hS` from the open premises;
- `hello1_huA`, `hello1_hSA`: at `hello1o`.
-/
import Spike.Lib.LowerA64.HSAssembledBA
import Spike.Lib.LowerA64.FnCode2Me
import Spike.Lib.A64NewBuf
import Spike.Lib.LowerA64.NewBufC2
import Spike.Lib.LowerA64.CxBlk2Of
import Spike.Lib.LowerA64.Start2C0A
import Spike.Lib.LowerA64.StkOfA
import Spike.Test.A64Hello1ClosedAt2B
import Spike.Lib.LowerA64.FramesPlacedSetup

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (SetupCode setupMC SetupCallWSB SetupGF SetupArgs swFSL rS0 rtF arOf)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2)
open Spike.Lib.A64.Flow.Ret0 (LimOk WcG CallerCells limA)
open Spike.Lib.AllocReach (Reach IN)

section Ctx

variable {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}

/-- **A context's body blocks inside `W` at the frames `fs`**
(`CalleePre2R`'s `hW`, `hWp`): every body and pending node's block at a
ghost in `G0`. -/
def CxBlk2 (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (c : FnCode2 exe prog endPc RaOk Cd i T d) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (G0 : Ctl → Prop) : Prop :=
  (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk →
    (fs = [] → ∀ a, t ≠ .ret a) →
    BlkW (fun s c => W s c fs) K exe endPc R F (bodyN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs) blk) ∧
  (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
    (fs = [] → ∀ a, t ≠ .ret a) →
    BlkW (fun s c => W s c fs) K exe endPc R F (pendN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs k) blk)

/-- **A context's abort node's states** at the frames `fs`, at a ghost in
`G0` (`CalleePre2R`'s `hab` by construction). -/
def AbOf2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (c : FnCode2 exe prog endPc RaOk Cd i T d)
    (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (G0 : Ctl → Prop) :
    FragS isaLSE2 := fun s c' fs' =>
  fs' = fs ∧ ∃ c0, G0 c0 ∧
    Spike.Lib.A64.Flow.At exe endPc R F (abortN2 i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c'

/-- **A context's buffer allocations' heap abort exits** at the frames
`fs`: the states at the allocator's heap abort exit (`nbX … .abort`, the
jump to `scc_rt_abort`) from the context's region `R` at its frame, at any
call node invariant placing its controls (`NbJcOf`) and landing pc
(`CxLB.hAb`'s premise). -/
def AbAl2 (ms : List TermRun.Frame → MemSide isaLSE2) (lbl : WeakMem.AllocLabel → Option Nat)
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) :
    FragS isaLSE2 := fun s c' fs' =>
  fs' = fs ∧ ∃ (Jc : AS → Ctl → Prop) (pcR : Int64), NbJcOf i lbl c.cx Jc ∧
    Spike.Lib.A64.Flow.At exe endPc R F
      (Spike.Lib.A64.Flow.NewBuf.nbX (ms fs) (_root_.Executable.labels exe).label lbl R c.cx.frame pcR Jc .abort) s c'

/-- **A context's aborts**: its abort node's states (`AbOf2`) and its buffer
allocations' heap abort exits (`AbAl2`). -/
def AbU2 (p : Prog) (ms : List TermRun.Frame → MemSide isaLSE2) (lbl : WeakMem.AllocLabel → Option Nat)
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (G0 : Ctl → Prop) : FragS isaLSE2 := fun s c' fs' =>
  AbOf2 p lbl c R F fs fp ra G0 s c' fs' ∨ AbAl2 ms lbl c R F fs s c' fs'

/-- **`CxBlk2` at `W2`** (`cxBlk2_ofW2` at `c`'s frame): the code facts'
blocks at `ra` inside `CdCLE` (`hCd`), at the write abort `Ab lab` and the
immediates `Λ.imms`. -/
theorem cxBlk2_ofFn [Kraken.Executable.ValidLayout exe] {lab : Label → Int64} {μ : Marks} {own : Own}
    {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    {Λ : Scc.Sem.Layout} {rS : Range} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    (hI : Spike.Lib.A64.Rt.InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hp : ProgNoS ZBad p) {RaOk' : BitVec 64 → Prop} {Cd' : BitVec 64 → Int64 → List Directive → Prop}
    {T' : Expr → Prop} {d' : Decl} (c : FnCode2 exe prog endPc RaOk' Cd' Λ.imms T' d')
    {R : Region} {F : MachineData → Prop} (hFS : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {fp ra : BitVec 64}
    (hCd : ∀ pc blk, Cd' ra pc blk → CdCLE prog okPc ph lab (Int64.ofBitVec ra) pc blk)
    (hraP : PosOff prog lab (Int64.ofBitVec ra))
    (hTg : ∀ pc blk, SubCd (Cd' ra) pc blk → Kind2 c.cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff prog lab (lab L)) :
    CxBlk2 (fun s c fs => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs) K p
      lbl lsize c R F fs fp ra G0 :=
  cxBlk2_ofW2 hI hpr habt hp c.hf c.h1 c.h16 hFS hR hal hlo hhi hl hh hsub hfit hFO hfp hG0F hCd hraP hTg

end Ctx

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSA`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB's address. -/
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (X0)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s code facts'). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The setup call's segment's premises at the callee's frame condition
`F'`, ghost `g` and frame `fr` (`hS_assembledBAC`'s `hpre`'s), all of them. -/
local notation "PRE" F':max g:max fr:max => (RC).OK ∧ (RC).base.toNat % 16 = 0 ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (swR v (-L) 0) (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.A64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option hygiene false in
/-- The ghosts at the setup frame: the controls a frame run reaches from
the callee's entry `g.c0` at the frames `[fr]`. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
/-- The stack records' bottom keys at the setup frame: the setup frame's
(`SetupBot`), the only bottom the setup function's segment sees. -/
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
    (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs

/-- **The setup frame's open premises** at the bounds `L`, `D1`, `fS`, the
invariant `J`, the top `v`, the setup block's compiled index `j` and a base
context `CxOk0`, the stack records' bottom keys the setup frame's (`SB`,
`SetupBot`, which `SetupGF` gives: `setupBot_ofGF`). Each names its
producer. -/
structure SetupOpenA (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (CxOk0 : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop) : Prop where
  /-- The setup function's segment at the contexts with their stack records (from the program-wide
  `fnSpecC2_allI` at `CxOkS … CxOk0 (SB …)`, its construct premises: plain calls, lane stores, buffers
  through the allocator's `W2` instance, prints). -/
  hs : FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J)
    (CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ) CxOk0 (SB J v D1 fS) j)
    (fnCode2OfPMe hp h Λ j d hd)
  /-- The base context at the setup frame (the program-wide base context's producer), at the setup
  frame's bottom key (`setupBot_ofGF`). -/
  hcx : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
    CxOk0 j (RC) F' [fr] g.fp g.ra TP0 (GR g fr)
      (AbU2 p (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr] g.fp g.ra (GR g fr))
  /-- Every label a construct block of the setup function at the setup call's return address branches or
  calls to is off the write abort (`cxBlk2_ofFn`'s `hTg`; decided at a concrete output). -/
  hTg : ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab
      (Int64.ofBitVec ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec)) pc blk →
    Kind2 (fnCode2OfPMe hp h Λ j d hd).cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff OP (Ly).lab ((Ly).lab L)
  /-- The aborts' segment at the setup frame (the abort node's states never end inside `W2`). -/
  hab : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbOf2 p (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr] g.fp g.ra (GR g fr)) (fun _ _ _ => False)
  /-- The buffer allocations' heap aborts' segment at the setup frame (`AbortSeg2.heapAbSeg2`: the jump to
  `scc_rt_abort` never ends inside `W2`). -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr]) (fun _ _ _ => False)

/-- **The setup call's `hS` from the open premises** (`hS_assembledBAC`) at
one choice of the bounds: the setup block `rodata` at its compiled index
(`rodata_of_setupOf`, `rodata_compiled2`), the open premises there
(`SetupOpenA`), the rest from the library (see the module docstring). -/
theorem hS_ofOpenA {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) (hu : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit)
    {L D1 : Int} {fS nS : Nat} (hfS : fS ≤ nS) (hnS : (nS : Int) + 48 ≤ D1) (hL0 : 0 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0) (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L)
    (hrow : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS)
    (J : InvS) (v : BitVec 64)
    (H : ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenA h Dt hp J v L D1 fS hd CxOk0) :
    SetupCallWSB (W2S J) (KT) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt fS) (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v) (setupMC (setupWords2 p)) D1
        (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0)) := by
  obtain ⟨dr, hf, hrt⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hty
  obtain ⟨j, hd, hn⟩ := Spike.Lib.LowerNode.rodata_compiled2 hf
  obtain ⟨CxOk0, HO⟩ := H j dr hd hn
  obtain ⟨w, fi, hLw, hna, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j dr hd
  have hframe : (fnCode2OfPMe hp h Λ j dr hd).cx.frame = fS := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user dr.name = _; rw [hn])
  have hna0 : (fnCode2OfPMe hp h Λ j dr hd).na = 0 := by
    have h1 := hLw.1
    rw [hu dr hf] at h1
    exact hna.trans (Option.some.inj (h1.symm.trans rfl))
  have hL : PosOff (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (Ly).lab
      ((Ly).lab (proL (fnCode2OfPMe hp h Λ j dr hd).cx)) := by
    have hok := Scc.Cert.Code1A64.fnOk1_of_fnCode1Ok (fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)) hmem rfl
    have hab : proL (fnCode2OfPMe hp h Λ j dr hd).cx ∉ abLabs := by
      unfold proL; exact local_not_abLabs (fnCode2OfPMe_spec hp h Λ j dr hd).2.2.1 _
    rw [hcx] at hab ⊢
    exact posOff_proL_of_fnOk1 hok hab _
  have hc0 : C0 = Spike.Lib.Ctl.mk Scc.Sem.SrcSem.setupTerm [("me", .ptr .pub .void,
      [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))]), ("u", .unit, [])] none := by
    simp only [th02, hty]
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  refine hS_assembledBAC h hty J v hrt (fnCode2OfPMe hp h Λ j dr hd) (fnCode2OfPMe_spec hp h Λ j dr hd).2.2
    (raOk_setup _ _) HO.hs (hu dr hf) hna0
    (by rw [(fnCode2OfPMe hp h Λ j dr hd).hfn, hn]; rfl) (by rw [hframe]) ?_ ?_ hL ?_
    (fun _ hm => hm.1.2) (Spike.Lib.A64.Rt.rS0_sub _)
    (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hpN ?_
  · intro cE fr hct
    have hcall := callTo_setupTerm (p := p) (c0 := C0) (by rw [hc0]) (by rw [hc0]; rfl) hf
    exact (CallTo.unique hct hcall).1
  · intro _ _ _ hl
    revert hl
    dsimp only [MSAt]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hl => ⟨hl.rt, hl.mp, hl.unmapped, hl.room⟩
  · rw [(Ly).lab_pin, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  · intro F' hR0 hal hF' hFF g fr hra htp hct hSB hbase
    have hP : PRE F' g fr := ⟨hR0, hal, hF', hFF, hra, htp, hct, hbase⟩
    have hlo0 : (RC).lo ≤ -((fnCode2OfPMe hp h Λ j dr hd).cx.frame : Int) := by
      show -D1 ≤ _; rw [hframe]; omega
    have hFO0 : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m := by
      intro m hm
      obtain ⟨⟨⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
      subst hv
      have hok : (swR (TOP) (-L) 0).OK := by
        rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
      have h8 : (swR (TOP) (-L) 0).base.toNat % 8 = 0 := by
        show (TOP).toNat % 8 = 0
        rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
      exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl)
        (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
    -- the setup call's return point (`scc_rt_main`'s marshalling block at `sp0`, one instruction past
    -- `e0`) is off the write abort
    have hraP : PosOff OP (Ly).lab ((Ly).lab (setupMC (setupWords2 p)).e0 + 4) := by
      have hin := Spike.Lib.A64.Rt.mainSIn_of_okS (rtCodeOkS_setupWords2A h hp hs')
      simp only [Spike.Lib.A64.Rt.mainSIn, Bool.and_eq_true] at hin
      have h0 := posOff_of_blockAt (lab := (Ly).lab) hin.1.1.2 (by simp only [setupMC]; decide) (i := 0)
        (by simp [Spike.Lib.A64.Rt.marshal]; omega)
      have hg : (Ly).lab (setupMC (setupWords2 p)).sp0 = (Ly).lab (setupMC (setupWords2 p)).e0 + 4 :=
        Scc.Cert.Rt.A64.label_labelGap (Ly).lays hin.1.1.1.2
      rw [Nat.add_zero, ofNat4_zero, hg] at h0
      exact h0
    -- the body's blocks inside `W2` (`cxBlk2_ofFn`)
    have hblk : CxBlk2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j dr hd) (RC) F' [fr]
        g.fp g.ra (GR g fr) :=
      cxBlk2_ofFn (Λ := (Ly).Λ) (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly)))
        (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hpN (fnCode2OfPMe hp h Λ j dr hd) hF' hR0 hal hlo0
        (show (0 : Int) ≤ 0 from Int.le_refl _) (by show (-D1) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
        (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hFO0
        (fun s _ => framesPlaced_setup h hp hty hct s) (G0 := GR g fr)
        (fun _ hc => FrOk2.runM hpN hc (FrOk2.step hpN (hct.step []) (hf0_start2A hty _)))
        (fp := g.fp) (ra := g.ra) (fun _ _ h => h) (by rw [hra, Int64.ofBitVec_toBitVec]; exact hraP)
        (by rw [hra]; exact HO.hTg)
    refine ⟨GR g fr,
      AbU2 p (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j dr hd) (RC) F' [fr] g.fp g.ra (GR g fr),
      ⟨?_, hF', hR0, hal, hlo0, ?_, fun _ _ h1 h2 => h1.trans h2, hblk.1, hblk.2,
        fun c0 hc0' _ _ hA => .inl ⟨rfl, c0, hc0', hA⟩, .refl _, ?_, ?_, hFO0⟩, ?_,
      SegWS.or_pre (HO.hab F' g fr hP) (HO.habA F' g fr hP)⟩
    · have hB := hSB j (GR g fr)
      rw [htp] at hB
      exact CxOkS.bot (HO.hcx F' g fr hP hB) hB
    · show (0 : Int) ≤ 0; exact Int.le_refl _
    · show (-D1) % 8 = 0; omega
    · show (0 : Int) % 8 = 0; rfl
    · exact FrOk2.step hpN (hct.step []) (hf0_start2A hty _)

/-- **The open premises at every choice of the bounds** (`SetupOpenA` at
`Bounds2A`'s `L`, `D1`, `fS`, every invariant holding at the starts, every
top and the setup block's compiled index). -/
def OpenSA (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenA h Dt hp J v L D1 fS hd CxOk0

/-- **The setup call's `hS` at every choice of the bounds** at the setup
call's known frame condition (`h0InA_setup_assembledCB`'s `hS` at
`Bounds2A`'s `L`, `D1`, `ZU1 = Int64.ofInt fS`, as `OpenBA`'s). -/
def HSBA (ty : Ty) (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (KT) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt (fS : Int))
      (SRetR (fun _ => none) ty) ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v) (setupMC (setupWords2 p)) D1
        (Int64.ofInt (fS : Int)) ⟨TOP, TP0, C0⟩ (X0))

/-- **`HSBA` from the open premises** (`hS_ofOpenA` at each choice of the
bounds). -/
theorem hSBA_ofOpenSA (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hu : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenSA h hp E El Dt) : HSBA h ty E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v
  obtain ⟨-, hfS, hnS, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, hL1, -, -, -, -, -⟩ := id hB
  exact hS_ofOpenA h hp hty hu hfS hnS hL0 hLm hL8 hD18 hL1 hrow J v
    fun j d hd hn => H L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- **`hello1o`'s setup block takes `Unit`.** -/
theorem hello1_huA : ∀ dr, (P1A).find? (·.name == "rodata") = some dr → dr.argTy = .unit := by
  have hm : ((P1A).find? (·.name == "rodata")).map (·.argTy) = some .unit := by decide
  intro dr hf
  rw [hf] at hm
  exact Option.some.inj hm

/-- **`hello1`'s setup call `hS` on AArch64, the open premises named**: at
every admissible output and entry, `HSBA` (the `hS` of the assembled start
segment at the setup call's known frame condition) from `OpenSA`. -/
theorem hello1_hSA
    (h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenSA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    HSBA h' hello1_htyA.choose E El Dt :=
  hSBA_ofOpenSA h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec hello1_huA H

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hS_ofOpenA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hS_ofOpenA

/-- info: 'Spike.Lib.LowerA64.hSBA_ofOpenSA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hSBA_ofOpenSA

/-- info: 'Spike.Lib.LowerA64.hello1_huA' does not depend on any axioms -/
#guard_msgs in #print axioms hello1_huA

/-- info: 'Spike.Lib.LowerA64.hello1_hSA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_hSA

/-- info: 'Spike.Lib.LowerA64.cxBlk2_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cxBlk2_ofFn

end Spike.Lib.LowerA64
