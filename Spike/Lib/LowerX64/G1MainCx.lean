/-
**`main`'s frame is a base context at no suspended frames** (x86-64; the
twin of `Spike/Lib/LowerA64/G1MainCx.lean`): `CxCore2`
(`Spike/Lib/LowerX64/G1FnSpec.lean`) at `main`'s compiled block, at the
frames `[]`, from `main`'s context facts `MainCx2`
(`Spike/Lib/LowerX64/G1MainStmt.lean`) and an entry control free of `ZBad`.

`CxCore2` asks a suspended frame only at a block allocating a buffer
(`HasNewBuf2`); `main` allocates none (`main_noNewBufT`,
`Spike/Lib/Src/MainNoBuf2.lean`), so its allocation facts hold vacuously.

- `main_noNewBuf`: `main` allocates no buffer on its walk;
- `cxCore2_main`: `CxCore2` at `main`'s frame, ghosts the frame runs from the
  entry control;
- `cxG2M_main`: the base context `CxG2M` at `main`'s frame, at the aborts
  `AbG2`.
-/
import Spike.Lib.LowerX64.G1MainStmt
import Spike.Lib.LowerX64.G1Room2
import Spike.Lib.LowerX64.HeldRes
import Spike.Lib.Src.MainNoBuf2

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

/-- **`main` allocates no buffer on its walk** (`main_noNewBufT`). -/
theorem main_noNewBuf {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") : ¬ HasNewBuf2 p j :=
  fun ⟨x, cn, τ, e, ht⟩ => Spike.Lib.LowerNode.main_noNewBufT hp hd hn x cn τ e ht

section G1MainCx

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
      NeedRoomX (OUT).place.need (Scc.Lower.Names.user d'.name) 256 (R.lo - 8) := by
    intro d' hd'
    rw [hd] at hd'
    cases hd'
    rw [hn]
    exact hc.room
  refine
    { hR := hc.hR
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
    dsimp only [MSAt]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hw => hw
  · intro m hm d' hd'
    rw [hd] at hd'
    cases hd'
    rw [hn]
    exact hc.lim m hm J

/-- **`main`'s frame is a base context at the aborts `AbG2`** (`CxG2M` at
the frames `[]`): `cxCore2_main` at the rebased region `rbR R`. -/
theorem cxG2M_main (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} {J : InvS} {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") {R : Region} {F : MachineData → Prop}
    {fp ra : BitVec 64} {tp : UInt64} (hc : MainCx2 h (rbR R) F ra tp) {cP : Ctl} (hE : FrOk2 cP []) :
    CxG2M h hp Dt J j R F [] fp ra tp (fun c => FrameRunM p (cP, []) (c, [])) (AbG2 h hp Dt J) :=
  ⟨cxCore2_main h hp hd hn hc hE, fun _ _ _ h' => h'⟩

end G1MainCx

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.main_noNewBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.main_noNewBuf

/-- info: 'Spike.Lib.LowerX64.cxCore2_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxCore2_main

/-- info: 'Spike.Lib.LowerX64.cxG2M_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxG2M_main
