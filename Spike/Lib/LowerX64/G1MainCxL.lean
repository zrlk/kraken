/-
**`main`'s frame is a base context at a reachable placement** (x86-64;
the twin of `Spike/Lib/LowerA64/G1MainCxL.lean`): `CxCore2L`
(`Spike/Lib/LowerX64/G1FnSpecL.lean`) at `main`'s compiled block, at the
frames `[]` and a placement `L`, `ls` reachable from the start's, from
`main`'s context facts there `MainCx2L`
(`Spike/Lib/LowerX64/G1MainStmtL.lean`) and an entry control free of
`ZBad`; as `cxCore2_main` (`Spike/Lib/LowerX64/G1MainCx.lean`), the
allocation facts vacuous (`main_noNewBuf`).

- `cxCore2_mainL`: `CxCore2L` at `main`'s frame, ghosts the frame runs
  from the entry control;
- `cxG2ML_main`: the base context `CxG2ML` at `main`'s frame, at the aborts
  `AbG2L`.
-/
import Spike.Lib.LowerX64.G1MainCx
import Spike.Lib.LowerX64.G1MainStmtL
import Spike.Lib.LowerX64.G1FnSpecL

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)
open Spike.Lib.AllocReach (Reach)

section G1MainCxL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **`main`'s frame is a base context at a reachable placement**
(`CxCore2L` at the frames `[]`): at `main`'s compiled block `j` (`hd`,
`hn`), a placement `L`, `ls` reachable from the start's (`hre`), the
context facts `MainCx2L` there at the region `R`, frame condition `F`,
return address `ra` and thread pointer `tp`, and an entry control `cP`
free of `ZBad` (`hE`): `CxCore2L` with the saved pair `fp`/`ra`, the ghosts
the frame runs from `cP` (as `cxCore2_main`). -/
theorem cxCore2_mainL (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} {J : InvS}
    {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat} {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main")
    (hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls) {R : Region} {F : MachineData → Prop}
    {fp ra : BitVec 64} {tp : UInt64} (hc : MainCx2L h L ls R F ra tp) {cP : Ctl} (hE : FrOk2 cP []) :
    CxCore2L h hp Dt J L ls j R F [] fp ra tp (fun c => FrameRunM p (cP, []) (c, [])) := by
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hnb := main_noNewBuf hp hd hn
  have hroom : ∀ d', (compiled2 p)[j]? = some d' →
      NeedRoomX (OUT).place.need (Scc.Lower.Names.user d'.name) 256 (R.lo - 8) := by
    intro d' hd'
    rw [hd] at hd'
    cases hd'
    rw [hn]
    exact hc.room
  refine
    { hre := hre
      hR := hc.hR
      hR8 := hc.hR8
      hal := hc.hal
      hl := hc.hl
      hh := hc.hh
      hhi := hc.hhi
      hFS := hc.hFS
      hFO := hc.hFO
      hrs := ?_
      hfp := fun _ _ => ⟨fun _ => False, FramesPlacedInI.nil _⟩
      hes := fun _ _ _ hf => nomatch hf
      hfs := fun hn' => absurd hn' hnb
      hrd := ?_
      hwn := hc.hwn
      hG0F := fun _ hr => Spike.Lib.LowerNode.FrOk2.runM hpN hr hE
      hG0 := fun _ _ h1 h2 => h1.trans h2
      hK := msOfAX_K_abi
      hAW := fun _ _ hn' => absurd hn' hnb
      room := hroom
      lim := ?_
      htp := hc.htp
      hun := hc.hun }
  · intro d' hd' r k hk
    have hlo := room2Own h hp j d' hd' 256 (R.lo - 8) (hroom d' hd')
    have hhi := hc.hhi
    exact regionOff_of_rsOf (FC j d' hd').hf (by omega) (by omega) hk
  · intro w
    dsimp only [MSAtL]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hw => hw
  · intro m hm d' hd'
    rw [hd] at hd'
    cases hd'
    rw [hn]
    exact hc.lim m hm J

/-- **`main`'s frame is a base context at the aborts `AbG2L`** (`CxG2ML`
at the frames `[]`): `cxCore2_mainL` at the rebased region `rbR R`. -/
theorem cxG2ML_main (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} {J : InvS}
    {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat} {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main")
    (hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls) {R : Region} {F : MachineData → Prop}
    {fp ra : BitVec 64} {tp : UInt64} (hc : MainCx2L h L ls (rbR R) F ra tp) {cP : Ctl} (hE : FrOk2 cP []) :
    CxG2ML h hp Dt J L ls j R F [] fp ra tp (fun c => FrameRunM p (cP, []) (c, []))
      (AbG2L h hp Dt J L ls) :=
  ⟨cxCore2_mainL h hp hd hn hre hc hE, fun _ _ _ h' => h'⟩

end G1MainCxL

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.cxCore2_mainL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxCore2_mainL

/-- info: 'Spike.Lib.LowerX64.cxG2ML_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxG2ML_main
