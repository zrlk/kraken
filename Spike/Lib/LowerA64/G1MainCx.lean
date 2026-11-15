/-
**`main`'s frame is a base context at no suspended frames** (AArch64):
`CxCore2` (`Spike/Lib/LowerA64/G1FnSpec.lean`) at `main`'s compiled block,
at the frames `[]`, from `main`'s context facts `MainCx2`
(`Spike/Lib/LowerA64/G1MainStmt.lean`) and an entry control free of `ZBad`.

`CxCore2` asks a suspended frame only at a block allocating a buffer
(`HasNewBuf2`); `main` allocates none (`main2`'s body check has no
allocations), so its allocation facts hold vacuously.

- `main_noNewBuf`: `main` allocates no buffer on its walk
  (`Spike/Lib/Src/MainNoBuf2.lean`);
- `cxCore2_main`: `CxCore2` at `main`'s frame, ghosts the frame runs from the
  entry control;
- `cxCore2_mainL`: `CxCore2L` (`Spike/Lib/LowerA64/G1FnSpecL.lean`) at
  `main`'s frame at a reachable placement, from `MainCx2L`
  (`Spike/Lib/LowerA64/G1MainStmtL.lean`).
-/
import Spike.Lib.LowerA64.G1MainStmtL
import Spike.Lib.LowerA64.G1Room2
import Spike.Lib.LowerA64.HeldRes
import Spike.Lib.Src.MainNoBuf2
import Spike.Lib.Src.RunOk2

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.A64.Rt (rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)
open Spike.Lib.AllocReach (Reach)

/-- **`main` allocates no buffer on its walk** (`main_noNewBufT`). -/
theorem main_noNewBuf {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") : ¬ HasNewBuf2 p j :=
  fun ⟨x, cn, τ, e, ht⟩ => Spike.Lib.LowerNode.main_noNewBufT hp hd hn x cn τ e ht

section G1MainCx

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **`main`'s frame is a base context** (`CxCore2` at the frames `[]`):
at `main`'s compiled block `j` (`hd`, `hn`), the context facts `MainCx2`
at the region `R`, frame condition `F`, return address `ra` and thread
pointer `tp`, and an entry control `cP` free of `ZBad` (`hE`): `CxCore2`
with the saved pair `fp`/`ra`, the ghosts the frame runs from `cP`. The
frame cells lie in `R` by `main`'s room covering its frame (`room2Own`),
the allocation facts are vacuous (`main_noNewBuf`). -/
theorem cxCore2_main (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} {J : InvS} {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") {R : Region} {F : MachineData → Prop}
    {fp ra : BitVec 64} {tp : UInt64} (hc : MainCx2 h R F ra tp) {cP : Ctl} (hE : FrOk2 cP []) :
    CxCore2 h hp Dt J j R F [] fp ra tp (fun c => FrameRunM p (cP, []) (c, [])) := by
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hnb := main_noNewBuf hp hd hn
  have hroom : ∀ d', (compiled2 p)[j]? = some d' →
      NeedRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user d'.name) 256 R.lo := by
    intro d' hd'
    rw [hd] at hd'
    cases hd'
    rw [hn]
    exact hc.room
  refine
    { hR := hc.hR
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
    have hlo := room2Own h hp j d' hd' 256 R.lo (hroom d' hd')
    exact regionOff_of_rsOf (FC j d' hd').hf (by omega) hc.hhi hk
  · intro w
    dsimp only [MSAt]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hw => hw
  · intro m hm d' hd'
    rw [hd] at hd'
    cases hd'
    rw [hn]
    exact hc.lim m hm J

/-- **`main`'s frame is a base context at a reachable placement**
(`cxCore2_main`'s at `L`, `ls`, `CxCore2L`): from `MainCx2L` at `L`, `ls`
reachable from the start's (`hre`). No frame is suspended, so the frames
are placed at any `L`. -/
theorem cxCore2_mainL (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} {J : InvS}
    {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat}
    (hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") {R : Region} {F : MachineData → Prop}
    {fp ra : BitVec 64} {tp : UInt64} (hc : MainCx2L h L ls R F ra tp) {cP : Ctl} (hE : FrOk2 cP []) :
    CxCore2L h hp Dt J L ls j R F [] fp ra tp (fun c => FrameRunM p (cP, []) (c, [])) := by
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hnb := main_noNewBuf hp hd hn
  have hroom : ∀ d', (compiled2 p)[j]? = some d' →
      NeedRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user d'.name) 256 R.lo := by
    intro d' hd'
    rw [hd] at hd'
    cases hd'
    rw [hn]
    exact hc.room
  refine
    { hre := hre
      hR := hc.hR
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
    have hlo := room2Own h hp j d' hd' 256 R.lo (hroom d' hd')
    exact regionOff_of_rsOf (FC j d' hd').hf (by omega) hc.hhi hk
  · intro w
    dsimp only [MSAtL]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hw => hw
  · intro m hm d' hd'
    rw [hd] at hd'
    cases hd'
    rw [hn]
    exact hc.lim m hm J

end G1MainCx

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.main_noNewBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.main_noNewBuf

/-- info: 'Spike.Lib.LowerA64.cxCore2_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxCore2_main

/-- info: 'Spike.Lib.LowerA64.cxCore2_mainL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxCore2_mainL
