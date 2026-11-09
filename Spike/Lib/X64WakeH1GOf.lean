/-
**`H1G` from its open fields** (x86-64, the twin of
`Spike/Lib/A64WakeH1GOf.lean`): `h1G_of` builds `WakeH1Root.H1G` from the
loader's facts, `BoxPure` and the fields that have not landed, discharging
the landed ones:

- `wcWf`: `WakeWcW1I.wcMainW_wfB`, its `hst` from `OwnMid.wcMidW_wcGX`
  (`hstG_of`), its `hoffT` from `CalWf.hoffT_W` and `htid` from `tid`'s
  frame part.
- `hstR`: `hstG_of`'s reserve field, then `CalWf.reserveW_noK`.
- `hplR`: `PlacedCal.reserveW_placed`.
- `hstT`: `hstG_of`'s second-TCB field (`OwnTcb2.tcb2W_ownGX` inside
  `wcSp3W_wcGX`), then `CalWf.tcbWG_noK`.
- `hplT`: `PlacedCal.tcbWG_placed`.

`hstG_of`'s premises are discharged from A13's data part:
`ownGXW`'s separations (`tcbSep_W`, `tcbM_ne_ntA_W`, `tcb2_notG_W`), the
counter's (`sepN_W`, `hmN_W`), the counters' (`wsep_W`), the second TCB's
(`LdFacts.hhdr_W`, `hmP_W`, `hmH_W`, `htid1_W`, `htid3_W`) and the tid
word off `tcbM` (`tid_ne_tcbM`); every frame's band on the pool from
`BoxPure` (`band_of_box`).

**Unlike AArch64**: the `SFactsSt2` facts are built once for all of
`wc_main` (`wcMidW_wcGX`, at the move of the pool range) and projected to
`hstR`/`hstT`, rather than per producer (A64's `hstT_of` with
`tcb2W_ownGK`); `hstR` is a field (A64's `reserveW_wf` builds it); the band
is `BandOnP R (-256) 8`, one premise for every frame, from `BoxPure`'s
`R.base + 64 = stacksA + 16384` and A8's `stacks_sub` (A64's
`bands_of_box`: `BandSp3`, `BandTi`); `ti`/`wcl` are `HMidPA`'s (the callee
under the take; `wcl` without `StackM`); the assembly is a parameter `asm`.
No absolute address appears in this file.
-/
import Spike.Lib.X64WakeH1Root
import Spike.Lib.X64WakeOwnBoxM
import Spike.Lib.X64WakeOwnSW
import Spike.Lib.X64WakeOwnT2W
import Spike.Lib.X64WakeLdFacts
import Spike.Lib.X64WakePlacedCal

namespace Spike.Lib.X64.WakeH1GOf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (WcMidW t2 kOf rAR)
open Spike.Lib.X64.WakePh.WcSp4 (wcNI)
open Spike.Lib.X64.WakePh.WcClone (wcNS)
open Spike.Lib.X64.WakePh.Tcb2Call (oC tcb2Q)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StOk StackM)
open Spike.Lib.X64.Rt (TcbOkGA hdrA)
open Spike.Lib.X64.Rt.Reserve (ResOkA ntA)
open Spike.Lib.X64.KeepTP (NoSetFsAt tpXa)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.X64.WakeOPremW (W1W)
open Spike.Lib.X64.WakeBoxW (SpawnSrc W1X)
open Spike.Lib.X64.WakeHMid (BoxPure QB)
open Spike.Lib.X64ConsumerA (TakeCK SFactsSt2)
open Spike.Lib.X64.WakeH1Root (H1G)
open Spike.Lib.X64.WakePh (BandOnP)
open SccCode (wakeCells)
open Scc.Cert.Rt.X64 (endOf)

/-- **Every frame of `wc_main` on the stack pool** from `BoxPure`: `R`'s
`[-256, 8]` lies in the first stack (`R.base + 64` its top, A8's
`stacks_sub`). -/
theorem band_of_box {L : Spike.Lib.X64.Rt.RuntimeLayout} {F0 : MachineData → Prop} {n : Nat} {R : Region}
    {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure L F0 n R F J0 t) :
    BandOnP L R (-256) 8 := by
  obtain ⟨⟨hR, -, -, hRlo, hhi⟩, -, -, ⟨-, -, hbase, -⟩, -⟩ := hB
  intro k h1 h2
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  simp only at hs1 hs2
  have e := Region.addr_toNat_of hR (k := k) (by omega) (by omega)
  omega

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W asm hp i E cT ls0 l b n []

set_option hygiene false in
/-- The end of text. -/
local notation "eR" => WakeH1Inv.endR hp i

set_option hygiene false in
/-- The callee's outside move: the take of the second stack or a `clone` refusal. -/
local notation "KA" => TakeCK (X64WakeOSide.aW hp i E) (X64WakeOSide.r1W hp i) (WakeOD.ClW hp i)

/-- `H1G.ti`'s type. -/
abbrev TiG (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) (t : UInt64) : Prop :=
  ∀ (c0 : Ctl), (∃ l' A', QB l b l' A' c0) → ∀ (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)
    (R' : Region) (F' : MachineData → Prop), cA.toNat = b → m.toNat = tcb0 (Ly).Λ →
    R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi → FStable R' F' → KStable KA F' →
    (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
    (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
    ∀ g : Ret0.AllocTcb.G,
      (∃ σC c, (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
        (tiN (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-72) σC) c) →
      (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧ (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
        (tiN (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-72) σC) c ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      SegW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c [] ∧ NoSetFsAt s) KA X64WakeT1.wakeSrc
        (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) (tpXa ms1 t)
        (fun s c => At (Ly).exe eR R' F' (tiN (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) .e) s c ∧
          Spike.Lib.X64Consumer.Pz (X64WakeOSide.r1W hp i) s.st.1)
        (fun s c => ∃ x, At (Ly).exe eR R' F' (tiX (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) x) s c ∧
          StackM (X64WakeOSide.r1W hp i) s.st.1)

/-- `H1G.wcl`'s type. -/
abbrev WclG (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) : Prop :=
  ∀ s c cA m fr,
    At (Ly).exe eR R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c →
    cA.toNat = b → m.toNat = tcb0 (Ly).Λ →
    SpawnSrc l c → W1W asm hp i E Dt Ctx ls0 l b n s c []

/-- **`wc_main`'s nodes inside `SFactsSt2` at `ownGXW`** at one ghost of
`Box`: `OwnMid.wcMidW_wcGX` at the move of the pool range, its band from
`band_of_box`, its separations and the second TCB's facts from A13's data
part, the unmapped words under `F` given (`hunN`, `hunP`, `hunH`, `htid`). -/
theorem hstG_of (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 128#64) 8 = none)
    (htid : ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none) :
    WcMidW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab)) s)
      (Spike.Lib.X64.PhRec.K (Ly) (Ly).Λ.stackPool) (Ly).exe (Ly).endPc R F F (tpXa ms1 t) J0 (QB l b) := by
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab : ∀ l x, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => PlaceWX.hlab_ofPlaceWX hp i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hp)
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hp i hA13
  have hb := band_of_box hB
  obtain ⟨⟨hR, -, -, hRlo, hhi⟩, -⟩ := hB
  exact Spike.Lib.X64.WakePh.OwnMid.wcMidW_wcGX (L := Ly) (Λ := (Ly).Λ) hpg hlo hΛ hlab
    (PlaceWX.site_ofPlaceWX hp i) (Spike.Lib.X64.WakePh.tcbSep_W hp i)
    (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp i hA13) (Spike.Lib.X64.WakePh.tcb2_notG_W hp i hA13)
    hb hR (by omega) hhi (Ly).Λ.stackPool (Spike.Lib.X64.WakePh.CalWf.sepN_W hp i hA13)
    (Spike.Lib.X64.WakePh.CalWf.hmN_W hp i hA13 true) hunN ⟨hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a⟩
    (Spike.Lib.X64.WakePh.LdFacts.hhdr_W hp i hA13) (Spike.Lib.X64.WakePh.LdFacts.hmP_W hp i)
    (Spike.Lib.X64.WakePh.LdFacts.hmH_W hp i hA13) hunP hunH
    ⟨Spike.Lib.X64.WakePh.LdFacts.htid1_W hp i hA13, htid, Spike.Lib.X64.WakePh.LdFacts.htid3_W hp i hA13⟩
    (Spike.Lib.X64.WakePh.tid_ne_tcbM (Ly))

/-- **`H1G` from its open fields** `hunN`, `hunP`, `hunH`, `resA`,
`hdrA`, `tcbA`, `tid`, `ti`, `wcl` (each of `H1G`'s type), given the
loader's facts, `BoxPure` and `l`'s freshness. -/
theorem h1G_of (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.X64.Rt.CtrZ o)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t) (hl : L0T (Ly).Λ l = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 128#64) 8 = none)
    (resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA ms1 F (Ly).exe eR (rAR R) F ⟨g.1, 0#64, g.2⟩)
    (hdrA' : ∀ c0 g, StOk ms1 F (hdrA (Ly).lab (tcb2Q g c0)) ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe eR (R.callee (-72) (-184) 8) F (tcb2Q g c0))
    (tid : (ms1).rt (t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨t2 (Ly).lab + 56#64, 8⟩ true ∧
      (ms1).G ⟨t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none)
    (ti : TiG asm hp i E cT Dt Ctx ls0 l b n R F t) (wcl : WclG asm hp i E Dt Ctx ls0 l b n R F) :
    H1G asm hp i E cT Dt Ctx ls0 l b n R F J0 t := by
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hE : (Ly).endPc = eR := by
    show endOf _ (Ly).prog _ = _; rw [WakeSrcCtl.prog_W hp i hpa hwp]
  have hst := hstG_of asm hp i E cT ls0 hpa hwp hlo0 hA13 (l := l) (b := b) hB hunN hunP hunH tid.2.2.2
  have hW := WakeWcW1I.wcMainW_wfB hp i asm E Dt Ctx ls0 l b n hpg hlo hpa hB hl tid.2.2.2
    (Spike.Lib.X64.WakePh.CalWf.hoffT_W hp i hpin2 hcz) hst
  rw [hE] at hW
  obtain ⟨⟨hR, -, -, hRlo, hhi⟩, -, -, ⟨-, hJ0, -, -⟩, -⟩ := hB
  have hne := Spike.Lib.X64.WakePh.PlacedLy.ne_of_fresh hl
  exact ⟨hW, hunN,
    fun g hg nd => Spike.Lib.X64.WakePh.CalWf.reserveW_noK (hst.res.res g hg) (fun _ _ h => h) nd,
    fun g _ nd => Spike.Lib.X64.WakePh.PlacedCal.reserveW_placed hR (by omega) hhi hne hJ0 nd,
    hunP, hunH,
    fun c0 cA m fr hM g hg nd =>
      Spike.Lib.X64.WakePh.CalWf.tcbWG_noK ((hst.sp3 c0 cA m fr hM).tcb g hg) (fun _ _ h => h) nd,
    fun _ _ _ _ hM _ _ nd => Spike.Lib.X64.WakePh.PlacedCal.tcbWG_placed hR (by omega) hhi hne hJ0 hM nd,
    resA, hdrA', tcbA, tid, ti, wcl⟩

end Spike.Lib.X64.WakeH1GOf

/-- info: 'Spike.Lib.X64.WakeH1GOf.band_of_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1GOf.band_of_box

/-- info: 'Spike.Lib.X64.WakeH1GOf.hstG_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1GOf.hstG_of

/-- info: 'Spike.Lib.X64.WakeH1GOf.h1G_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1GOf.h1G_of
