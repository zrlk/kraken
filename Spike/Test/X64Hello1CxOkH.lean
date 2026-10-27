/-
**The setup frame's contexts and bottoms free of the frame invariant**
(x86-64; the twin of `Spike/Test/A64Hello1CxOkH.lean`): the contexts
`CxOkH` and the bottom keys `BotH` the landings `ElX`
(`Spike/Lib/LowerX64/H1InLand.lean`) carry, fixed before the frame
invariant `J` (the landings' family is chosen before `J`, which the starts at
those landings constrain).

- `CxOkH`: a context of the setup frame: the block `rodata` at some bounds
  (as `setupCxLB_ofPre` takes them), the setup call's premises `PRE` at the
  start's frame condition with `WordsNone` (`Spike/Test/X64Hello1ClosedBVBF.lean`'s
  switch region frame condition), the private memory loading no heap or
  static word, the setup frame's bottom key at the context, the region the
  setup callee's, the frames `[fr]`, the saved pair and thread pointer the
  call's, the ghosts the frame runs from the callee's entry, the aborts
  `AbU2` at some family;
- `BotH`: the setup frame's bottom keys `SetupBot` at some family, top and
  bounds, with the bounds' `Bounds2`, at the block `rodata`.
-/
import Spike.Test.X64Hello1ClosedBVBF
import Spike.Test.X64Hello1HS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Rt (setupMC rS0 swFSL)
open Spike.Lib.LowerNode (setupWords2 compiled2)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`HSBVF`'s). -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

/-- **A context at the setup frame, free of the frame invariant**: the
`j`th compiled block `rodata` (`d`, `hd`) at bounds `L`, `D1`, `fS + 8 ≤ nS`
as `setupCxLB_ofPre` takes them, the setup call's premises `PRE F g fr`
(`SetupCallWSB`'s, at `FS`, with the callee region's base 8-aligned), the
private memory loading no heap or static word (`hwn`), the setup frame's
bottom key `SetupBot` at the context (at the family `J`), the context the
setup frame's (region `RC`, frames `[fr]`, saved pair and thread
pointer `g`'s and the first TCB, ghosts `GR g fr`), its aborts `AbU2` at
some family `J`. -/
def CxOkH (hp : Scc.Lower.Accepted2 p = true) (j : Nat) (R : Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa) : Prop :=
  ∃ (d : Decl) (hd : (compiled2 p)[j]? = some d) (L D1 : Int) (fS nS : Nat) (v : BitVec 64) (g : WcG)
    (fr : TermRun.Frame) (J : InvS),
    d.name = "rodata" ∧ fS + 8 ≤ nS ∧ (nS : Int) + 48 + 208 ≤ D1 ∧ 8 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧
    D1 % 8 = 0 ∧ 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L ∧
    (∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS) ∧
    -- `PRE F g fr`
    ((RC).OK ∧ (RC).base.toNat % 8 = 0 ∧ FStable (RC) F ∧
      (∀ m, F m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
      g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
      Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp) ∧
    (∀ m, F m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem) ∧
    -- the setup frame's bottom key at the context (`SetupOpen`'s `SB J v D1 fS`)
    SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
      ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec ⟨j, RC, F, g.fp, g.ra, TP0, GR g fr⟩ [fr] ∧
    R = RC ∧ fs = [fr] ∧ fp = g.fp ∧ ra = g.ra ∧ tp = TP0 ∧ G0 = GR g fr ∧
    Ab = AbU2 p (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F [fr] g.fp g.ra (GR g fr)

set_option linter.unusedVariables false in
/-- **The setup frame's bottom keys at some family and bounds**
(`SetupOpen`'s `SB J v D1 fS`, at a switch region's depth `L`), with the
bounds `Bounds2` it is taken at (sharing `L`, `D1`, `fS`; the bottom's
segments ask the setup frame's and `main`'s bounds at the same `L`), the
key's block `rodata` (`CxOkH`'s: its return type is the setup result's, so
`main`'s call exists at the key's post). -/
def BotH (k : StkKey) (fs : List TermRun.Frame) : Prop :=
  (∃ (J : InvS) (L D1 : Int) (fS : Nat) (v : BitVec 64) (D2 : Int) (lS lM : String) (nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM ∧
    SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
      ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec k fs) ∧
  ∃ d, (compiled2 p)[k.j]? = some d ∧ d.name = "rodata"

end Assembled

end Spike.Lib.LowerX64
