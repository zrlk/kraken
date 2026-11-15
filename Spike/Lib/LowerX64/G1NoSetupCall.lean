/-
**`main`'s call at the bare start** (x86-64; the twin of
`Spike/Lib/LowerA64/G1NoSetupCall.lean`): for an `Accepted2` program
without a setup block, `scc_rt_main` (`bareMC`) calls `main` directly, in
`scc_rt_main`'s callee region of the switch region (`RS v`), at the callee
region `RC` below `bareMC`'s frame.

- `posOff_bareRa`: the return address `bareMC.sp0` is off the write abort;
- `limS_bare`: `main`'s limit room at its entry `%rsp`
  (`(rbR RC).base + 8`), the switch region's top the first stack's;
- `mainCx2_bare`: `MainCx2` (`Spike/Lib/LowerX64/G1MainStmt.lean`) at
  `main`'s callee frame at the bare start (the twin of `mainCx2_setup`).
-/
import Spike.Lib.LowerX64.G1NoSetupDefs
import Spike.Lib.LowerX64.G1SetupCx
import Spike.Lib.LowerX64.MainRetPos

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (bareMC rS0 RuntimeLayout swFSL)
open Spike.Lib.X64 (FStable)
open Spike.Lib.LowerNode (compiled2 imms2Me)

/-- **The return address of `main`'s call at the bare start is off the
write abort**: `bareMC.sp0` heads the `exit_group` tail
(`posOff_mainRetU`). -/
theorem posOff_bareRa {cells : List (Directive × Nat)} (lab : Label → Int64)
    (hin : Spike.Lib.X64.Rt.mainUIn cells bareMC = true) :
    PosOff cells lab (Int64.ofBitVec (lab bareMC.sp0).toBitVec) := by
  rw [Int64.ofBitVec_toBitVec]
  exact posOff_mainRetU hin

section Assembled

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
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- `scc_rt_main`'s callee region of the switch region at depth `L`, below
the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top
`v`, the caller's cells outside `RS v`. -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- `main`'s callee region at the bare start. -/
local notation "RC" => (RS v).callee (-8 - bareMC.Z.toInt - 8 - 0) (-D) 8

/-- **`main`'s limit room at its entry `%rsp` at the bare start**
(`MainCx2.lim` at `(rbR RC).base + 8`), the switch region's top the first
stack's (`v = TOP`): `main` is a stack-checked callee of `scc_rt_main`
whose need `n` fits `Z + 16 + n ≤ 12288` (`mainRowBare` at `CfgNeedOk`),
so above the limit `stacksA + 4096` or the limit word's initial `0`
(`room_of_le`) the need fits below the callee's entry `TOP - 24 - Z`. -/
theorem limS_bare (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none)
    (hcfg : CfgNeedOk pcfg = true) {L D : Int} (hL0 : 8 ≤ L) (hLm : L ≤ 16384) (hD8 : 8 ≤ D)
    (hL2 : 8 + 8 + bareMC.Z.toInt + 8 + D ≤ L) (J : InvS) {v : BitVec 64} (hv : v = TOP) :
    LimRoomX (OUT).place.need (Scc.Lower.Names.user "main")
      (((MSS J) []).G ⟨limA (TP0), 8⟩) ((rbR (RC)).base.toNat + 8) := by
  have hZ := bareZ_toIntX
  obtain ⟨jm, dm, hdm, hnm⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
  obtain ⟨f, hf, hck, hfn⟩ := userFn2 h hp hdm
  rw [hnm] at hfn
  obtain ⟨l, n, hr, -, hn'⟩ := mainRowBare h hp hs hcfg hf hck hfn
  rw [hfn] at hr
  refine ⟨l, _, n, hr, fun w hw => ?_⟩
  -- the callee's entry: `TOP - 8 - 16 - Z`
  have hok : (swR v (-L) 0).OK := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have hR1 : (RS v).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS v).base.toNat : Int) = v.toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hRC : (RC).OK :=
    Region.callee_ok hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
      (by show _ ≤ (8 : Int); omega)
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - bareMC.Z.toInt - 8 - 0)
    (lo' := -D) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hb2 := rbR_base hRC (by show -D ≤ -8; omega) (by show (0 : Int) ≤ 8; decide)
  have htop : v.toNat = (Ly).stacksA.toNat + 16384 := by
    rw [hv, show stacksA (Ly).lab = (Ly).stacksA from (Ly).lab_stacks, Spike.Lib.X64.Rt.top0_toNat]
  have hw' := Spike.Lib.X64.PhRec.room_of_le h (imms2Me Λ p)
    (b := (rbR (RC)).base.toNat + 8 + 8 - n) (by omega) w (by
      revert hw
      rw [Spike.Lib.X64.Rt.pinA_lab0]
      dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun h' => h')
  omega

/-- **`main`'s context facts at its callee frame at the bare start**
(`MainCx2` at the rebased region `rbR RC`, `v = TOP`): from the callee
frame's premises (the callee region `OK`, the frame condition stable and
inside `FS TOP` with the caller's cells, the return address `bareMC.sp0`,
the first TCB), the region's facts as `mainCx2_setup`'s, the return point
off the write abort (`posOff_bareRa`), the room from `Bounds0X`'s
`nM + 48 + 208 ≤ D` and the limit room by `limS_bare`. -/
theorem mainCx2_bare (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none)
    (hcfg : CfgNeedOk pcfg = true) {L D : Int} {lM : String} {fM nM : Nat}
    (hB : Bounds0X cfg p sizes labelOffs (Ly) L D lM fM nM) {F' : MachineData → Prop} {g : WcG}
    {v : BitVec 64} (hv : v = TOP) (hok' : (RC).OK) (hst : FStable (RC) F')
    (hFF : ∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - bareMC.Z.toInt - 8 - 0) (-D) 8 m)
    (hra : g.ra = ((Ly).lab bareMC.sp0).toBitVec) (htp : g.tp = TP0) :
    MainCx2 h (rbR (RC)) F' g.ra g.tp := by
  obtain ⟨hrM, -, hnM2, hnM3, -, -, hL0, hLm, hL8, hD0, hD8, hL2, -⟩ := id hB
  have hZ := bareZ_toIntX
  -- the regions: the switch region, its callee `RS TOP`, `main`'s `RC`
  have hok : (swR v (-L) 0).OK := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : v.toNat % 8 = 0 := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have htop16 : v.toNat % 16 = 0 := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_h16 (Ly)
  have hR1 : (RS v).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS v).base.toNat : Int) = v.toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hb8 : (RS v).base.toNat % 8 = 0 := by omega
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - bareMC.Z.toInt - 8 - 0)
    (lo' := -D) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hlo1 : (RC).lo ≤ -8 := by show -D ≤ -8; omega
  have hhi1 : (0 : Int) ≤ (RC).hi := by show (0 : Int) ≤ 8; decide
  have hb := rbR_base hok' hlo1 hhi1
  refine
    { hR := rbR_ok hok' hlo1 hhi1
      hR8 := by omega
      hal := by omega
      hl := by show (-D + 8) % 8 = 0; omega
      hh := by show ((8 : Int) + 8) % 8 = 0; decide
      hhi := by show (16 : Int) ≤ 8 + 8; decide
      hFS := rbR_fstable hok' hlo1 hhi1 hst
      hFO := fun m hm => stackOff_rbR hok' hlo1 hhi1
        (Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
          (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
          (by show _ < (8 : Int); omega) (by omega)
          (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
            (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
            (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2.2 (hFF m hm).1.2)
          (hFF m hm).2)
      hwn := fun m hm => (hFF m hm).1.1.1
      hraP := by rw [hra]; exact posOff_bareRa _ (mainUIn_bare2 h hp hs)
      hraK := by
        -- the labels read the executable, which the immediates do not change
        have e : (Ly).lab =
            (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab := rfl
        rw [hra, Int64.ofBitVec_toBitVec, e]
        rfl
      htp := htp
      hun := fun m hm => by rw [htp]; exact (hFF m hm).1.1.2.1.2
      room := ⟨lM, fM + 8, nM, hrM, by show -D + 8 - 8 ≤ _; omega⟩
      lim := fun m hm J => ?_ }
  rw [htp]
  exact limS_bare h hp hs hcfg hL0 hLm (by omega) hL2 J hv

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.posOff_bareRa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms posOff_bareRa

/-- info: 'Spike.Lib.LowerX64.limS_bare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms limS_bare

/-- info: 'Spike.Lib.LowerX64.mainCx2_bare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainCx2_bare

end Spike.Lib.LowerX64
