/-
**The setup frame's bottom keys' exits** (x86-64): `H1OpenXW.hbot`'s
per-key shape `ExitStk` (`Spike/Lib/LowerX64/ResumeStk2.lean`) at a setup
bottom key (`SetupBot`, `Spike/Test/X64Hello1CxOkH.lean`'s `BotH` shape) at
any family `J0` of the key and any segment world `W`, memory side `ms` and
labels `lbl` (a landing's extended placement): `setupBot_exitStkMT`
(`Spike/Lib/LowerX64/SetupBotM.lean`) at the post `SPostC` of the key's
block's return type, the frame pop `hPS_framed`, the region facts from
`Bounds2`.

- `exitStk_ofSetupBotB`: the exits from the key's exits inside `W` (`hW`),
  `scc_rt_main`'s segment from `mainS0` at that post (`h0`) and the aborts'
  (`hAb`);
- `exitStk_ofBotH`: the same at a `BotH` key, `h0` at each of its witnesses.
-/
import Spike.Test.X64Hello1CxOkH
import Spike.Lib.LowerX64.SetupBotM
import Spike.Lib.LowerX64.SetupCall2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable At)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Rt (setupMC rS0 swFSL mainS0)
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

/-- **The exits at a setup bottom key** (`H1OpenXW.hbot`'s per-key shape):
at a key `k` the setup frame's (`SetupBot` at the key's memory side
`MSS J0 []`, any `J0`), at the bounds `Bounds2` it was taken at, the exits
`ExitStk` reach `Q` inside `W`, given the key's exits at its block's return
type inside `W` (`hW`), `scc_rt_main`'s segment from `mainS0` at the post
`SPostC` of that type (`h0`) and the aborts' segment (`hAb`). The block's
return type is the one `P` gives at `k.j` (no block, no exits). -/
theorem exitStk_ofSetupBotB {W : FragS isa} {K : State → State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isa} {Q : FragS isa} {P : Prog} {Ab₀ : FragS isa}
    {J0 : InvS} {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat} {v : BitVec 64}
    {k : StkKey} {fs : List TermRun.Frame}
    (hZ8 : (setupMC (setupWords2 p)).Z.toInt % 8 = 0) (hZ : 8 ≤ (setupMC (setupWords2 p)).Z.toInt)
    (hBd : Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM)
    (hB : SetupBot p (Ly).lab ((MSS J0) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
      ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec k fs)
    (hW : ∀ c0 ty, k.G0 c0 → (∃ d, P[k.j]? = some d ∧ d.retTy = ty) → ∀ s c,
      ExitC2SL p lbl (Ly).exe (Ly).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs →
        W s c fs)
    (hAb : SegWS W K p lbl ms Ab₀ Q)
    (h0 : ∀ d, P[k.j]? = some d → SegWS W K p lbl ms
      ((At (Ly).exe (Ly).endPc (RS v) (FS v) (mainS0 (Ly).lab (setupMC (setupWords2 p))
        (SPostC p lbl d.retTy C0) ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec)).at []) Q) :
    SegWS W K p lbl ms (ExitStk p P lbl (Ly).exe (Ly).endPc k fs Ab₀) Q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hD10, -, -, -, -, hL1, -⟩ := hBd
  cases hj : P[k.j]? with
  | none =>
    exact hAb.mono_pre fun _ _ _ ⟨_, _, _, ⟨_, hd, _⟩, _⟩ => by rw [hj] at hd; cases hd
  | some d =>
    refine setupBot_exitStkMT (PostS := SPostC p lbl d.retTy C0) hD10 hZ8 hZ
      (by simp only [Region.callee]; omega) (by simp only [Region.callee]; omega) hB ?_ hW hAb (h0 d hj)
    rintro ty ⟨d', hd', rfl⟩ cE fr c rs hct hR
    rw [hj] at hd'
    cases hd'
    exact hPS_framed cE fr c rs hct hR

/-- **`exitStk_ofSetupBotB` at a `BotH` key** (`H1OpenXW.hbot`'s per-key
shape at `Bot := BotH h`): `h0` at each of `BotH`'s witnesses. -/
theorem exitStk_ofBotH {W : FragS isa} {K : State → State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isa} {Q : FragS isa} {P : Prog} {Ab₀ : FragS isa}
    {k : StkKey} {fs : List TermRun.Frame}
    (hZ8 : (setupMC (setupWords2 p)).Z.toInt % 8 = 0) (hZ : 8 ≤ (setupMC (setupWords2 p)).Z.toInt)
    (hB : BotH h k fs)
    (hW : ∀ c0 ty, k.G0 c0 → (∃ d, P[k.j]? = some d ∧ d.retTy = ty) → ∀ s c,
      ExitC2SL p lbl (Ly).exe (Ly).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs →
        W s c fs)
    (hAb : SegWS W K p lbl ms Ab₀ Q)
    (h0 : ∀ (J0 : InvS) (L D1 : Int) (fS : Nat) (v : BitVec 64) (D2 : Int) (lS lM : String) (nS fM nM : Nat),
      Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
      SetupBot p (Ly).lab ((MSS J0) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
        ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec k fs →
      ∀ d, P[k.j]? = some d → SegWS W K p lbl ms
        ((At (Ly).exe (Ly).endPc (RS v) (FS v) (mainS0 (Ly).lab (setupMC (setupWords2 p))
          (SPostC p lbl d.retTy C0) ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec)).at []) Q) :
    SegWS W K p lbl ms (ExitStk p P lbl (Ly).exe (Ly).endPc k fs Ab₀) Q := by
  obtain ⟨⟨J0, L, D1, fS, v, D2, lS, lM, nS, fM, nM, hBd, hSB⟩, -⟩ := hB
  exact exitStk_ofSetupBotB h hZ8 hZ hBd hSB hW hAb (h0 J0 L D1 fS v D2 lS lM nS fM nM hBd hSB)

end Assembled

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.exitStk_ofSetupBotB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.exitStk_ofSetupBotB

/-- info: 'Spike.Lib.LowerX64.exitStk_ofBotH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.exitStk_ofBotH
