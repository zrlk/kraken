/-
**`h0In_setup_assembledCB`'s `hS` from the placement check** (x86-64; the
twin of `Spike/Lib/LowerA64/HSAssembledBA.lean`): `hS_assembled`
(`Spike/Lib/LowerX64/HSAssembled.lean`) through `setupCallWSB_ofPlaceOK`
(`Spike/Lib/LowerX64/SetupCallB2.lean`), the setup call at `SetupCallWSB`
with the callee's frame condition `SetupGF`, the callee's precondition asked
with the bottom key `SetupBot` (`Spike/Lib/LowerX64/SetupBot.lean`) known.
Unlike A64's, x86-64's `hpre` has no alignment premise.

- `hS_assembledB`: the setup call's `SetupCallWSB` at the assembled instance.
- `hS_assembledBC`: the same at any code facts `c` with `ProOK` (e.g. `fnCode2OfPMe`).
-/
import Spike.Lib.LowerX64.HSAssembled
import Spike.Lib.LowerX64.SetupBot
import Spike.Lib.LowerX64.SetupCallB2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open A9NoSpawn Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (LimOk WcG CallerCells limA)
open Scc.Sem (ValRep)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2)
open Spike.Lib.X64.Rt (SetupCode SetupCallWSB SetupGF MainCallWSF MainSW SetupArgs swFSL mainSIn oU rS0 entryR
  rtF setupMC
  rtCodeOkS mainS0R mainSRR CFactsC arOf marshal)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt
  (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
  (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

/-- **`hS_assembledB` at any code facts**: the setup function's code facts `c` at any
immediates `im` (e.g. `fnCode2OfPMe`, at the theorem's), call and code predicates, with its
prologue's facts (`hc`) and the return address past the setup call in `RaOk` (`hraS`)
(`setupCallWSB_ofPlaceOKC`). -/
theorem hS_assembledBC {Dt : State → Prop}
    {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {L : Int} {D1 : Int} {ZU1 : Int64} (J : InvS) (v : BitVec 64)
    {dS : Decl} (hrt : dS.retTy = ty)
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {im : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    (c : FnCode2 (LY0).exe (LY0).prog (LY0).endPc RaOk Cd im T dS)
    (hc : ProOK (LY0) dS c) (hraS : RaOk ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec)
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hs : FnSpecC2 (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none) (fun _ => 0) (MSS J)
      CxOk c)
    (hu : dS.argTy = .unit) (hna : c.na = 0)
    (hfn : (setupMC (setupWords2 p)).setup = c.fn)
    (hZU : ZU1 = Int64.ofInt c.fr.size)
    (hcE : ∀ cE fr, Spike.Lib.X64.Flow.CallTo p C0 cE fr → cE = Spike.Lib.Ctl.mk dS.body [(dS.arg, dS.argTy, [])] none)
    (hms : ∀ (fr : TermRun.Frame) a Z', Spike.Lib.X64.Flow.Ret0.LimOk ((MSS J) []) (FS v) a Z' →
      Spike.Lib.X64.Flow.Ret0.LimOk ((MSS J) [fr]) (FS v) a Z')
    (hL : Spike.Lib.LowerX64.PosOff (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog (Ly).lab
      ((Ly).lab (proL c.fr)))
    (hv : ValRep (fun _ => none) (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)).val
      (Λ.pinned.lo + 8))
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false ⟨limA TP0, 8⟩ = true)
    (hun : ∀ m, (FS v) m → Mem.loadInt m.dmem (limA TP0) 8 = none)
    (hsub : (rS0 (Ly)).Sub (Ly).Λ.stackPool) (hfit : (rS0 (Ly)).lo + (rS0 (Ly)).size ≤ 2 ^ 64)
    (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop,
      ((RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).OK →
      FStable ((RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8) F' →
      (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) →
      ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec → g.tp = TP0 →
      Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr →
      (∀ (j : Nat) (G0 : Ctl → Prop), SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1
        ZU1 ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec
        ⟨j, (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8, F', g.fp, g.ra, g.tp, G0⟩ [fr]) →
      ((RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa),
        (ProEdge2 p (fun _ => none) (fun _ => 0) ((MSS J) [fr]) F' c g.fp g.ra TP0 g.c0
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (Ly).exe).label ((MSS J) []) (FS v)
              (setupMC (setupWords2 p)).setup ZU1 g).J →
          CalleePre2R (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none) (fun _ => 0) (MSS J)
            CxOk c (rS0 (Ly))
            ((RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8) F' [fr] g.fp g.ra TP0 G0 Ab
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (Ly).exe).label ((MSS J) []) (FS v)
              (setupMC (setupWords2 p)).setup ZU1 g).J g.c0) ∧
        FrOk2 g.c0 [fr] ∧ SegWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none) (MSS J) Ab
          (fun _ _ _ => False)) :
    SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0
      (SetupGF p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 ZU1 ⟨TOP - 8#64, TP0, C0⟩
        (TP0).toBitVec) := by
  have hc0 : C0 = Spike.Lib.Ctl.mk Scc.Sem.SrcSem.setupTerm [("me", .ptr .pub .void,
      [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)]), ("u", .unit, [])] none := by
    simp only [th02, hty]
  rw [← hrt]
  exact setupCallWSB_ofPlaceOKC h (Λw := (Ly).Λ) c hc hraS hs hu hna hfn hZU hc0 hcE hms hL
    (Spike.Lib.LowerNode.imms2Me_setupK hty) hv hmr hun hsub hfit hpN
    fun F' hR0 hF' hFF g fr hra htp hct hGF hbase =>
      hpre F' hR0 hF' hFF g fr hra htp hct (fun j G0 => setupBot_ofGF hGF hbase j G0) hbase


/-- **`h0In_setup_assembledCB`'s `hS` at one invariant and top, from the
placement check** (`hS_assembled` through `setupCallWSB_ofPlaceOK`): the
setup call at `SetupCallWSB` with the callee's frame condition `SetupGF`;
the callee's precondition `hpre` is asked at a frame condition `F'`, ghost
`g` and frame `fr` whose bottom key is known: `SetupBot` at the setup
call's callee region, `F'` and `g`'s parameters, at every block `j` and
ghost predicate `G0` (`setupBot_ofGF`), the premise `CxOkS.bot` takes. -/
theorem hS_assembledB {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true)
    {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {L : Int} {D1 : Int} {ZU1 : Int64} (J : InvS) (v : BitVec 64)
    {jS : Nat} {dS : Decl} (hdS : (Spike.Lib.LowerNode.compiled2 p)[jS]? = some dS) (hrt : dS.retTy = ty)
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hs : FnSpecC2 (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none) (fun _ => 0) (MSS J)
      CxOk (fnCode2OfP hp h jS dS hdS))
    (hu : dS.argTy = .unit) (hna : (fnCode2OfP hp h jS dS hdS).na = 0)
    (hfn : (setupMC (setupWords2 p)).setup = (fnCode2OfP hp h jS dS hdS).fn)
    (hZU : ZU1 = Int64.ofInt (fnCode2OfP hp h jS dS hdS).fr.size)
    (hcE : ∀ cE fr, Spike.Lib.X64.Flow.CallTo p C0 cE fr → cE = Spike.Lib.Ctl.mk dS.body [(dS.arg, dS.argTy, [])] none)
    (hms : ∀ (fr : TermRun.Frame) a Z', Spike.Lib.X64.Flow.Ret0.LimOk ((MSS J) []) (FS v) a Z' →
      Spike.Lib.X64.Flow.Ret0.LimOk ((MSS J) [fr]) (FS v) a Z')
    (hL : Spike.Lib.LowerX64.PosOff (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog (Ly).lab
      ((Ly).lab (proL (fnCode2OfP hp h jS dS hdS).fr)))
    (hv : ValRep (fun _ => none) (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)).val
      (Λ.pinned.lo + 8))
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false ⟨limA TP0, 8⟩ = true)
    (hun : ∀ m, (FS v) m → Mem.loadInt m.dmem (limA TP0) 8 = none)
    (hsub : (rS0 (Ly)).Sub (Ly).Λ.stackPool) (hfit : (rS0 (Ly)).lo + (rS0 (Ly)).size ≤ 2 ^ 64)
    (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop,
      ((RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).OK →
      FStable ((RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8) F' →
      (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) →
      ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec → g.tp = TP0 →
      Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr →
      (∀ (j : Nat) (G0 : Ctl → Prop), SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1
        ZU1 ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec
        ⟨j, (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8, F', g.fp, g.ra, g.tp, G0⟩ [fr]) →
      ((RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa),
        (ProEdge2 p (fun _ => none) (fun _ => 0) ((MSS J) [fr]) F' (fnCode2OfP hp h jS dS hdS) g.fp g.ra TP0 g.c0
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (Ly).exe).label ((MSS J) []) (FS v)
              (setupMC (setupWords2 p)).setup ZU1 g).J →
          CalleePre2R (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none) (fun _ => 0) (MSS J)
            CxOk (fnCode2OfP hp h jS dS hdS) (rS0 (Ly))
            ((RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8) F' [fr] g.fp g.ra TP0 G0 Ab
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (Ly).exe).label ((MSS J) []) (FS v)
              (setupMC (setupWords2 p)).setup ZU1 g).J g.c0) ∧
        FrOk2 g.c0 [fr] ∧ SegWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none) (MSS J) Ab
          (fun _ _ _ => False)) :
    SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0
      (SetupGF p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 ZU1 ⟨TOP - 8#64, TP0, C0⟩
        (TP0).toBitVec) :=
  hS_assembledBC h hty J v hrt (fnCode2OfP hp h jS dS hdS) (fnCode2OfP_spec hp h jS dS hdS).2.2
    (raOk_setup _ _) hs hu hna hfn hZU hcE hms hL hv hmr hun hsub hfit hpN hpre

end Assembled

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerX64.hS_assembledB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms hS_assembledB

/--
info: 'Spike.Lib.LowerX64.hS_assembledBC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms hS_assembledBC

end Spike.Lib.LowerX64
