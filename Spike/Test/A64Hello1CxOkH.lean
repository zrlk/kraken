/-
**`hello1`'s landing contexts, free of the frame invariant** (AArch64):
the contexts `CxOkH` and bottom keys `BotH` the landings `ElA`
(`Spike/Lib/LowerA64/H1InLandA.lean`) are taken at, for `hello1`'s
`H1InA`. The landings are fixed before the invariant `J` (`OpenSA`,
`HSBA` quantify `J` after `El`), so neither may mention `J`: `CxOkH` is
the setup call's premises `PRE` at the setup frame (which do not read `J`),
the private memory's `WordsNone`, the setup block's bounds and frame row,
its aborts `AbU2` at some family; `BotH` is the setup frame's bottom key
`SetupBot` at some family and bounds (an instance of `Bounds2A`), at the
block `rodata`.

- `CxOkH`: a context at the setup frame of the block `rodata`;
- `BotH`: the setup frame's bottom keys at some family and `Bounds2A` bounds,
  at the block `rodata`;
- `ElH`: the landings `ElA` at `CxOkH`, `BotH`.
-/
import Spike.Test.A64Hello1CxLBOf
import Spike.Lib.LowerA64.H1InLandA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 swFSL)
open Spike.Lib.LowerNode (setupWords2 compiled2 imms2Me)
open Spike.Lib.A64.Flow.Ret0 (WcG CallerCells limA)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

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
/-- The switch region's frame condition at the private memory's `WordsNone`
(`SetupOpenFA`'s, the setup call's caller frame condition). -/
local notation "FW" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0

set_option hygiene false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

/-- **A context at the setup frame, free of the frame invariant**: the
`j`th compiled block `rodata` (`d`, `hd`) at bounds `L`, `D1`, `fS ≤ nS`
as `setupCxLB_ofPre` takes them (`Bounds2A`'s), the setup call's premises
`PRE F g fr` (`hS_ofOpenA`'s), the private memory loading no runtime word
(`hwn`), the setup frame's bottom key `SetupBot` at `J` (`hSB`), the
context the setup frame's (region `RC`, frames `[fr]`, saved
pair and thread pointer `g`'s and the first TCB, ghosts `GR g fr`), its
aborts `AbU2` at some family `J`. -/
def CxOkH (hp : Scc.Lower.Accepted2 p = true) (j : Nat) (R : Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2) : Prop :=
  ∃ (d : Decl) (hd : (compiled2 p)[j]? = some d) (L D1 : Int) (fS nS : Nat) (v : BitVec 64) (g : WcG)
    (fr : TermRun.Frame) (J : InvS),
    d.name = "rodata" ∧ fS ≤ nS ∧ (nS : Int) + 48 + 208 ≤ D1 ∧ 0 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧ D1 % 8 = 0 ∧
    (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L ∧
    (∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS) ∧
    -- `PRE F g fr`
    ((RC).OK ∧ (RC).base.toNat % 16 = 0 ∧ FStable (RC) F ∧
      (∀ m, F m → (FS v) m ∧ CallerCells (swR v (-L) 0) (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0 m) ∧
      g.ra = ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec ∧ g.tp = TP0 ∧
      Spike.Lib.A64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp) ∧
    (∀ m, F m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem) ∧
    SetupBot p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FW v)
      (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0)
      ⟨j, RC, F, g.fp, g.ra, TP0, GR g fr⟩ [fr] ∧
    R = RC ∧ fs = [fr] ∧ fp = g.fp ∧ ra = g.ra ∧ tp = TP0 ∧ G0 = GR g fr ∧
    Ab = AbU2 p (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F [fr] g.fp g.ra (GR g fr)

/-- **The setup frame's bottom keys at some family and bounds**
(`SetupOpenA`'s `SB J v D1 fS`, at a switch region's depth `L`), the bounds
an instance of `Bounds2A` (the setup call's and `main`'s, at the same `L`:
the bottom frames' exits need both), the key's block `rodata` (`CxOkH`'s:
its return type is the setup result's, so `main`'s call exists at the key's
post). -/
def BotH (k : StkKey) (fs : List TermRun.Frame) : Prop :=
  (∃ (J : InvS) (L D1 : Int) (fS : Nat) (v : BitVec 64) (D2 : Int) (lS lM : String) (nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM ∧
    SetupBot p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FW v)
      (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs) ∧
  ∃ d, (compiled2 p)[k.j]? = some d ∧ d.name = "rodata"

/-- **`hello1`'s landings**: `ElA` at the code `fnCode2OfPMe`, the
contexts `CxOkH` and the bottom keys `BotH`. -/
def ElH (hp : Scc.Lower.Accepted2 p = true) : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2 :=
  ElA h (fnCode2OfPMe hp h Λ) (CxOkH h hp) (BotH h)

end Assembled

end Spike.Lib.LowerA64
