import Spike.Lib.A64WakeWcW1I
import Spike.Lib.A64WakeLdFacts
import Spike.Lib.A64WakePlacedCal

/-
**`H1G` from its open fields** (AArch64): `h1G_of` builds `WakeH1Root.H1G`
from the loader's facts, `BoxPure` and the fields that have not landed,
discharging the landed ones:

- `wcWf`: `WakeWcW1I.wcMainW_wf`, its bands from `bands_of_box`, its
  loader facts from `LdFacts` (`hhdr_W`, `hmP_W`, `hmH_W`, `htid1_W`,
  `htid3_W`) and `htidW`'s frame part from `tid`'s.
- `hplR`: `PlacedCal.reserveW_placed`.
- `hstT`: `hstT_of`, i.e. `Tcb2CallW.tcb2W_ownGK` at the empty stack range
  (as `WcMidWG.wcSp3W_wcG`), then `CalWf.tcbWG_noK`, `WakeWc.tcbWG_mono` and
  `WakeWc.tcbWG_c0`.
- `hplT`: `PlacedCal.tcbWG_placed`.

No absolute address appears in this file.
-/

namespace Spike.Lib.WakeH1GOf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (WcMainW rAR)
open Spike.Lib.A64.WakePh.WcSp4 (wcNS wcNI)
open Spike.Lib.A64.WakePh.Tcb2Call (oW tcb2Q)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX)
open Spike.Lib.A64.Rt (TcbOkGA hdrA TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResOkA ReserveW ntA)
open Spike.Lib.A64.KeepTP (tpXa)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.WakeOPremW (W1W)
open Spike.Lib.WakeBoxW (SpawnSrc)
open Spike.Lib.WakeHMid (BoxPure SB WB)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.WakeH1Root (H1G)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2)
  (ls0 : Spike.Lib.A64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W hp i E cT ls0 l b n []

/-- `H1G.ti`'s type. -/
abbrev TiG (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop)
    (t : UInt64) : Prop :=
  ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region) (F' : MachineData → Prop),
  R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
  0 ≤ R'.hi → FStable R' F' → KStable (fun _ _ => False) F' → (∀ m, F' m → F m) →
  R' = R.callee (-80) (-256) 0 →
  (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -80) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
  ∀ g : Ret0.ThreadInit.G,
    (∃ σC c, (wcNI (Ly).lab c0 (WakeWc.t2 (Ly).lab) cA m fr).J σC c ∧
      (tiN (Ly).lab (WakeWc.tiQ (WakeWc.t2 (Ly).lab) c0 g) .e).J (enter (-80) σC) c) →
    (∀ m', F' m' → ∃ mC σC c, Abs R oW mC σC ∧ (wcNI (Ly).lab c0 (WakeWc.t2 (Ly).lab) cA m fr).J σC c ∧
      (tiN (Ly).lab (WakeWc.tiQ (WakeWc.t2 (Ly).lab) c0 g) .e).J (enter (-80) σC) c ∧
      ∀ k, R.Off k → ¬ R'.Off (k - -80) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
    SegW (NoMsrW (WB hp i E Dt Ctx ls0 l b n) (fun _ _ => False)) (fun _ _ => False) WakeT1.wakeSrc
      (A64ConsumerA.upd (L0T (Ly).Λ) l b) (tpXa ms1 t)
      (At (Ly).exe (WakeSpawnR.endR hp i) R' F' (tiN (Ly).lab (WakeWc.tiQ (WakeWc.t2 (Ly).lab) c0 g) .e))
      (fun s c => ∃ x, At (Ly).exe (WakeSpawnR.endR hp i) R' F'
        (tiX (Ly).lab (WakeWc.tiQ (WakeWc.t2 (Ly).lab) c0 g) x) s c ∧ True)

/-- `H1G.wcl`'s type. -/
abbrev WclG (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) : Prop :=
  ∀ s c cA m fr,
  At (Ly).exe (WakeSpawnR.endR hp i) R F (wcNS (Ly).lab c (WakeWc.t2 (Ly).lab) (WakeWc.kOf (Ly).lab) cA m fr) s c →
  SpawnSrc l c → W1W hp i E Dt Ctx ls0 l b n s c [] ∧ Ret0.StackM (WakeOSide.r1W hp i) s.st.1

/-- **`H1G.hstT` from `BoxPure`** and the unmapped words `hunP`, `hunH`:
`Tcb2CallW.tcb2W_ownGK` at the empty stack range, then `CalWf.tcbWG_noK`,
`WakeWc.tcbWG_mono` and `WcMidWG.tcbWG_c0`. -/
theorem hstT_of (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none) :
    ∀ c0, (∃ l' A', SB l b l' A' c0) →
    ∀ g : Ret0.AllocTcb.G, g.ra = ((Ly).lab ".L21_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s _ => A64ConsumerA.SFactsSt2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly))
        (Spike.Lib.A64.WakePh.ownG (Ly) (ntA (Ly).lab)) s) (fun _ _ => False)
      (Ly).exe (Ly).endPc (R.callee (-80) (-192) 0) F (tcb2Q g c0) nd := by
  intro c0 _ g hra nd
  have hbd := WakeWcW1I.bands_of_box hB
  obtain ⟨⟨hR, hal, -, hRlo, hhi, -, -⟩, -⟩ := hB
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hs := Spike.Lib.A64.WakePh.StartPlaceLy.wsep_W hp i hA13
  obtain ⟨hRc, halc⟩ := Spike.Lib.A64.Flow.Ret0.Inst.callee_facts hR hal (kc := -80) (lo' := -192)
    (by omega) (by decide) (by omega) (by decide)
  have eH : hdrA (Ly).lab (tcb2Q g Spike.Lib.A64Consumer.c0) = (Ly).pinA + 96#64 := by
    rw [Spike.Lib.A64.WakePh.Tcb2Call.tcb2Q_hdrA, (Ly).lab_pin]
  have h := Spike.Lib.A64.WakePh.Tcb2CallW.tcb2W_ownGK (L := Ly) hpg hlo (ntA (Ly).lab) ⟨0, 0⟩
    (Spike.Lib.PlaceW.site_ofPlaceW hp i) (Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp))
    (fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hp i l x (by rw [hlo, hpg]; exact h))
    ⟨hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a⟩ (Spike.Lib.A64.WakePh.LdFacts.hhdr_W hp i hA13) (lbl := fun _ => none)
    (c0 := Spike.Lib.A64Consumer.c0) Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hRc halc (Int.le_refl _)
    (Int.le_refl _) hbd.1 g hra (F := F) (Spike.Lib.A64.WakePh.LdFacts.hmP_W hp i) (by rw [eH]; exact Spike.Lib.A64.WakePh.LdFacts.hmH_W hp i hA13)
    hunP (fun m h => by rw [eH]; exact hunH m h) (rS := ⟨(Ly).Λ.stackPool.lo, 0⟩)
    (by simp only [Scc.Sem.Range.Sub]; omega) (fun _ m' _ _ => Spike.Lib.A64.WakePh.WcMidWG.stackM_nil _ m')
  exact Spike.Lib.A64.WakePh.WcMidWG.tcbWG_c0 (fun _ _ _ h => h)
    (WakeWc.tcbWG_mono (Spike.Lib.A64.WakePh.CalWf.tcbWG_noK h (fun _ _ h => h) nd)
      fun m h => ⟨h, Spike.Lib.A64.WakePh.WcMidWG.stackM_nil _ m⟩)

/-- **`H1G` from its open fields** `hunN`, `hunP`, `hunH`, `resA`,
`hdrA`, `tcbA`, `tid`, `ti`, `wcl` (each of `H1G`'s type), given the
loader's facts, `BoxPure` and `l`'s freshness. -/
theorem h1G_of (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.A64.Rt.CtrZ o)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t) (hl : L0T (Ly).Λ l = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none)
    (resA : ∀ g : Reserve.G × Ctl, ResOkA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (rAR R) F ⟨g.1, 0#64, g.2⟩)
    (hdrA' : ∀ c0 g, Ret0.StOk ms1 F (Ly).exe (WakeSpawnR.endR hp i) (hdrA (Ly).lab (tcb2Q g c0))
      ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (R.callee (-80) (-192) 0) F (tcb2Q g c0))
    (tid : (ms1).rt (WakeWc.t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨WakeWc.t2 (Ly).lab + 56#64, 8⟩ true ∧
      (ms1).G ⟨WakeWc.t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (WakeWc.t2 (Ly).lab + 56#64) 8 = none)
    (ti : TiG hp i E cT Dt Ctx ls0 l b n R F J0 t) (wcl : WclG hp i E Dt Ctx ls0 l b n R F) :
    H1G hp i E cT Dt Ctx ls0 l b n R F J0 t := by
  have hbd := WakeWcW1I.bands_of_box hB
  have hW := WakeWcW1I.wcMainW_wf hp i E cT Dt Ctx ls0 hpa hwp hlo0 hA13 hpin2 hcz (b := b) hB hl hunN hbd.1
    (Spike.Lib.A64.WakePh.LdFacts.hhdr_W hp i hA13) (Spike.Lib.A64.WakePh.LdFacts.hmP_W hp i) (Spike.Lib.A64.WakePh.LdFacts.hmH_W hp i hA13) hunP hunH hbd.2
    ⟨Spike.Lib.A64.WakePh.LdFacts.htid1_W hp i hA13, tid.2.2.2, Spike.Lib.A64.WakePh.LdFacts.htid3_W hp i hA13⟩
  have hst := hstT_of hp i hpa hwp hlo0 hA13 (l := l) (b := b) hB hunP hunH
  obtain ⟨⟨hR, hal, -, hRlo, hhi, -, -⟩, -, -, ⟨-, hJ0, -⟩, -⟩ := hB
  refine ⟨hW, hunN, fun g _ nd => ?_, hunP, hunH, hst,
    fun _ _ _ _ hM _ _ nd => Spike.Lib.A64.WakePh.PlacedCal.tcbWG_placed hR (by omega) hhi
      (Spike.Lib.A64.WakePh.PlacedLy.ne_of_fresh hl) hJ0 hM nd, resA, hdrA', tcbA, tid, ti, wcl⟩
  exact Spike.Lib.A64.WakePh.PlacedCal.reserveW_placed hR (by omega) hhi
    (Spike.Lib.A64.WakePh.PlacedLy.ne_of_fresh hl) hJ0 nd

end Spike.Lib.WakeH1GOf

/-- info: 'Spike.Lib.WakeH1GOf.h1G_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeH1GOf.h1G_of

/-- info: 'Spike.Lib.WakeH1GOf.hstT_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeH1GOf.hstT_of
