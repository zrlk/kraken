/-
**`main`'s context facts after the setup block** (x86-64; the twin of the
AArch64 `limS_main` and `mainCx2_setup` in
`Spike/Lib/LowerA64/G1MainCall.lean`): `MainCx2`
(`Spike/Lib/LowerX64/G1MainStmt.lean`) at the rebased region of `main`'s
callee region `RC` below the first stack's top (the switch region `RS TOP`
and `scc_rt_main`'s frame `Z`), from the premises the construct premise
`hpre` of `mainCallWSF_ofPlaceOKHMVCR` (`Spike/Lib/LowerX64/HeldPostXV.lean`)
hands its callee frame and the bounds `Bounds2`, for any `Accepted2` program
with a setup block.

- `limS_main`: `main`'s limit room at the callee's entry `%rsp`
  (`calleeRow`, as `limS_setup`);
- `mainCx2_setup`: `MainCx2` at `main`'s callee frame: the region's facts as
  `cxCore2_setup`'s (at the room `D2`), `WordsNone` and the limit word's
  freedom from the frame condition, the return point `sp1` off the write
  abort (`posOff_mainRetS`) at the phase anchor's phase (`raOk_main`), the room from `Bounds2`'s
  `nM + 48 + 208 ≤ D2` and the limit room by `limS_main`.
-/
import Spike.Lib.LowerX64.G1MainStmt
import Spike.Lib.LowerX64.G1SetupCx
import Spike.Lib.LowerX64.MainRetPos
import Spike.Lib.LowerX64.RaMain2

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Rt (swFSL rS0 setupMC)
open Spike.Lib.LowerNode (setupWords2 compiled2 imms2Me)

section MainCx

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
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 p)

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`HUBVF`'s). -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- `main`'s callee region below the first stack's top, at the room `D2`. -/
local notation "RCM" => (RS (TOP)).callee (-8 - (SC).Z.toInt - 8 - 0) (-D2) 8

/-- **`main`'s limit room at the callee's entry `%rsp`** (`MainCx2.lim`,
`(rbR RCM).base + 8`): `main` is a stack-checked callee of `scc_rt_main`
whose need `n` fits `Z + 16 + n ≤ 12288` (`calleeRow` at `CfgNeedOk`), so
above the limit `stacksA + 4096` or the limit word's initial `0`
(`room_of_le`) the need fits below the callee's entry `TOP - 24 - Z`
(`limS_setup`'s argument at `main`). -/
theorem limS_main (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true)
    (hcfg : CfgNeedOk pcfg = true) {L D2 : Int} (hL0 : 8 ≤ L) (hLm : L ≤ 16384) (hD8 : 8 ≤ D2)
    (hL2 : 8 + 8 + (SC).Z.toInt + 8 + D2 ≤ L) (J : InvS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") :
    LimRoomX (OUT).place.need (Scc.Lower.Names.user d.name)
      (((MSS J) []).G ⟨limA (TP0), 8⟩) ((rbR (RCM)).base.toNat + 8) := by
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs) (rtCodeOkS_setupWords2 h hp hs)).1
  have hZ := setupMC_Z _ hsw
  obtain ⟨f, hf, hck, hfn⟩ := userFn2 h hp hd
  have hcall := (user_mem_callees2 (setupWords2 p) (Spike.Lib.LowerNode.setupMask2 p)).2
  rw [← hn, ← hfn] at hcall
  obtain ⟨l, n, hr, -, hn'⟩ := calleeRow h hp hs hcfg hf hck hcall
  rw [hfn] at hr
  refine ⟨l, _, n, hr, fun w hw => ?_⟩
  -- the callee's entry: `TOP - 8 - 16 - Z`
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have hR1 : (RS (TOP)).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS (TOP)).base.toNat : Int) = (TOP).toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hRC : (RCM).OK :=
    Region.callee_ok hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
      (by show _ ≤ (8 : Int); omega)
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (SC).Z.toInt - 8 - 0)
    (lo' := -D2) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hb2 := rbR_base hRC (by show -D2 ≤ -8; omega) (by show (0 : Int) ≤ 8; decide)
  have htop : (TOP).toNat = (Ly).stacksA.toNat + 16384 := by
    rw [show stacksA (Ly).lab = (Ly).stacksA from (Ly).lab_stacks, Spike.Lib.X64.Rt.top0_toNat]
  have hw' := Spike.Lib.X64.PhRec.room_of_le h (imms2Me Λ p)
    (b := (rbR (RCM)).base.toNat + 8 + 8 - n) (by omega) w (by
      revert hw
      rw [Spike.Lib.X64.Rt.pinA_lab0]
      dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun h' => h')
  omega

/-- **`main`'s context facts at its callee frame after the setup block**
(`MainCx2` at the rebased region `rbR RCM`): from `hpre`'s premises (the
callee region `OK`, the frame condition stable and inside `FS TOP` with the
caller's cells, the return address `sp1`, the first TCB), the region's
facts as `cxCore2_setup`'s, the return point off the write abort
(`posOff_mainRetS`), the room from `Bounds2`'s `nM + 48 + 208 ≤ D2` and the
limit room by `limS_main`. -/
theorem mainCx2_setup (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true) {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM) {F' : MachineData → Prop} {g : WcG}
    (hok' : (RCM).OK) (hst : FStable (RCM) F')
    (hFF : ∀ m, F' m → (FS (TOP)) m ∧ CallerCells (RS (TOP)) (-8 - (SC).Z.toInt - 8 - 0) (-D2) 8 m)
    (hra : g.ra = ((Ly).lab (SC).sp1).toBitVec) (htp : g.tp = TP0) :
    MainCx2 h (rbR (RCM)) F' g.ra g.tp := by
  obtain ⟨-, -, -, -, -, hrM, -, -, hnM2, -, -, -, hL0, hLm, hL8, -, -, hD20, hD28, -, -, hL2, -⟩ := id hB
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hc := rtCodeOkS_setupWords2 h hp hs
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs) hc).1
  have hZ := setupMC_Z _ hsw
  obtain ⟨j, d, hd, hn⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
  -- the regions: the switch region, its callee `RS TOP`, `main`'s `RCM`
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : (TOP).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have htop16 : (TOP).toNat % 16 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_h16 (Ly)
  have hR1 : (RS (TOP)).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS (TOP)).base.toNat : Int) = (TOP).toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hb8 : (RS (TOP)).base.toNat % 8 = 0 := by omega
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (SC).Z.toInt - 8 - 0)
    (lo' := -D2) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hlo1 : (RCM).lo ≤ -8 := by show -D2 ≤ -8; omega
  have hhi1 : (0 : Int) ≤ (RCM).hi := by show (0 : Int) ≤ 8; decide
  have hb := rbR_base hok' hlo1 hhi1
  refine
    { hR := rbR_ok hok' hlo1 hhi1
      hR8 := by omega
      hal := by omega
      hl := by show (-D2 + 8) % 8 = 0; omega
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
      hraP := by rw [hra]; exact posOff_mainRetS (Spike.Lib.X64.Rt.mainSIn_of_okS hc)
      hraK := by rw [hra]; exact RaMain.raOk_main h (Scc.Lower.imms2Of p) hc
      htp := htp
      hun := fun m hm => by rw [htp]; exact (hFF m hm).1.1.2.1.2
      room := ⟨lM, fM + 8, nM, hrM, by show -D2 + 8 - 8 ≤ _; omega⟩
      lim := fun m hm J => ?_ }
  have := limS_main h hp hs hcfg hL0 hLm (by omega) hL2 J hd hn
  rw [hn] at this
  rw [htp]
  exact this

end MainCx

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.limS_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.limS_main

/-- info: 'Spike.Lib.LowerX64.mainCx2_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCx2_setup
