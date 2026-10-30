/-
**`hB_box`'s `hmid` with `scc_rt_thread_init`'s take** (AArch64, `hatA`):
`hmid_box` at `WakeTi2Hat.hti_W`'s callee, inside `W1X ∧ NoMsrAt` under the
take of the second stack or a `clone` refusal (`TakeCK aW r1W ClW`), the late
frame condition `F ∧ StackM r1W` (the child's stack private at the clone).
`wake_wc_mid_hatK` from the landing: `WB`'s nodes (`WcMidW.antiF₂`, `NoMsrW`)
are in `W1X` (`x1W_off`), unmoved by `TakeCK`; `TakeCK` keeps `F`, `R`'s
cells and the thread pointer (`takeCK_fK`, `takeCK_kR`, `takeCK_tp`).

- `HMidPA`: `HMidP` with `ti` at `hti_W`'s conclusion, `wcl` only `W1W`;
- `k1W_iff`: `K1W` is `TakeCK aW r1W ClW` at `W1X`'s states (`X1W`'s take clause);
- `hmid_boxA`: `hmid` at `l`, `b`, `n`. No absolute address appears here.
-/
import Spike.Lib.A64WakeHMid
import Spike.Lib.A64WakeWcHatK
import Spike.Lib.A64WakeWcK1
import Spike.Lib.A64WakeStartPlaceLy

namespace Spike.Lib.WakeHatA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (WcMainW WcMidW bX t2 kOf tiQ rAR wcMidW_w1)
open Spike.Lib.A64.WakePh.WcSp4 (wcNS wcNI)
open Spike.Lib.A64.WakePh.Tcb2Call (oW tcb2Q)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX StackM TakeK)
open Spike.Lib.A64.Rt (TcbOkGA hdrA)
open Spike.Lib.A64.Rt.Reserve (ResOkA)
open Spike.Lib.A64.KeepTP (NoMsrAt TP tpXa)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeLoadT (L0T tcb0)
open Spike.Lib.WakeOPremW (W1W)
open Spike.Lib.WakeBoxW (SpawnSrc W1X CloneP)
open Spike.Lib.WakeHMid (BoxPure QB SB WB at_bX_ms)
open Spike.Lib.A64ConsumerA (TakeCK)
open Spike.Lib.A64.Rt.PreChild (r1Of)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize)
  (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W hp i E cT ls0 l b n []

set_option hygiene false in
/-- The callee's outside move: the take of the second stack or a `clone` refusal. -/
local notation "KA" => TakeCK (WakeOSide.aW hp i E) (WakeOSide.r1W hp i) (WakeOD.ClW hp i)

/-- **`hmid`'s named premises at one ghost with the callee's take**: `HMidP`'s
`wcWf`, `res`, `tcb`, `resA`, `hdrA`, `tcbA`, `tid`; the callee at
`hti_W`'s conclusion (`ti`); `W1W` at the clone's `svc` (`wcl`). -/
structure HMidPA (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64) : Prop where
  /-- `wc_main`'s nodes inside `W1W` (`A64WakeWcWf`). -/
  wcWf : WcMainW (fun s c => W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe
    (WakeSpawnR.endR hp i) R F F (tpXa ms1 t) J0 (SB l b) (QB l b)
  /-- The reserve's nodes inside `W1W` (`HMidP.res`). -/
  res : ∀ g : Reserve.G × Ctl, g.1.ra = ((Ly).lab ".L21_wc_main.sp3").toBitVec →
    ∀ nd, Spike.Lib.A64.Rt.Reserve.ReserveW (fun s c => W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False)
      (Ly).exe (WakeSpawnR.endR hp i) (rAR R)
      (fun m => F m ∧ Ret0.CallerCells R (-80) (-48) 0 m ∧ WakeWc.ResCtx (Ly).lab R
        (WakeWc.rN (tpXa ms1 t) (Ly).lab J0 (SB l b) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- The second TCB's nodes inside `W1W` (`HMidP.tcb`). -/
  tcb : ∀ c0 cA m fr, WakeWc.MidG (SB l b) c0 cA ∧ WakeWc.FrG J0 fr ∧ WakeWc.FrMG J0 fr m →
    ∀ g : Ret0.AllocTcb.G, g.ra = ((Ly).lab ".L21_wc_main.sp4").toBitVec →
    ∀ nd, Spike.Lib.A64.Rt.TcbWG (fun s c => W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe
      (WakeSpawnR.endR hp i) (R.callee (-80) (-192) 0) (fun mm => F mm ∧ Ret0.CallerCells R (-80) (-192) 0 mm ∧
        WakeWc.TcbCtx (Ly).lab R (WakeWc.wcNC' (Ly).lab c0 cA m fr).J c0 g mm) (tcb2Q g c0) nd
  /-- `wake_wc_mid_hatK`'s `hres`. -/
  resA : ∀ g : Reserve.G × Ctl, ResOkA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (rAR R) F ⟨g.1, 0#64, g.2⟩
  /-- `wake_wc_mid_hatK`'s `hhdr`. -/
  hdrA : ∀ c0 g, Ret0.StOk ms1 F (Ly).exe (WakeSpawnR.endR hp i) (hdrA (Ly).lab (tcb2Q g c0))
    ((tcb2Q g c0).h ||| 1#64 <<< 36)
  /-- `wake_wc_mid_hatK`'s `htcb`. -/
  tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (R.callee (-80) (-192) 0) F (tcb2Q g c0)
  /-- `wake_wc_mid_hatK`'s `htid`. -/
  tid : (ms1).rt (t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨t2 (Ly).lab + 56#64, 8⟩ true ∧
    (ms1).G ⟨t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none
  /-- The callee (`WakeTi2Hat.hti_W`'s conclusion). -/
  ti : ∀ (c0 : Ctl), (∃ l' A', SB l b l' A' c0) → ∀ (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region)
    (F' : MachineData → Prop), cA.toNat = b → m.toNat = tcb0 (Ly).Λ →
    R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 → 0 ≤ R'.hi → FStable R' F' → KStable KA F' →
    (∀ m, F' m → F m) → R' = R.callee (-80) (-256) 0 →
    (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -80) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
    ∀ g : Ret0.ThreadInit.G,
      (∃ σC c, (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
        (tiN (Ly).lab (tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-80) σC) c) →
      (∀ m', F' m' → ∃ mC σC c, Abs R oW mC σC ∧ (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
        (tiN (Ly).lab (tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-80) σC) c ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -80) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      SegW (fun s c => W1X hp i E Dt Ctx ls0 l b n s c [] ∧ NoMsrAt s) KA WakeT1.wakeSrc
        (A64ConsumerA.upd (L0T (Ly).Λ) l b) (tpXa ms1 t)
        (fun s c => At (Ly).exe (WakeSpawnR.endR hp i) R' F' (tiN (Ly).lab (tiQ (t2 (Ly).lab) c0 g) .e) s c ∧
          Spike.Lib.A64Consumer.Pz (WakeOSide.r1W hp i) s.st.1)
        (fun s c => ∃ x, At (Ly).exe (WakeSpawnR.endR hp i) R' F' (tiX (Ly).lab (tiQ (t2 (Ly).lab) c0 g) x) s c ∧
          StackM (WakeOSide.r1W hp i) s.st.1)
  /-- `W1W` at the clone's `svc`. -/
  wcl : ∀ s c cA m fr,
    At (Ly).exe (WakeSpawnR.endR hp i) R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c →
    cA.toNat = b → m.toNat = tcb0 (Ly).Λ →
    SpawnSrc l c → W1W hp i E Dt Ctx ls0 l b n s c []

/-- **`K1W` is the callee's move at `W1X`'s states**: at the take's pc the
site's range is the second stack (`X1W`'s take clause). -/
theorem k1W_iff {s : State} {c : Ctl} (h : W1X hp i E Dt Ctx ls0 l b n s c []) (s' : State) :
    WakeH1Inv.K1W hp i E s s' ↔ KA s s' := by
  obtain ⟨-, -, hX⟩ := h
  by_cases ha : s.st.2 = WakeOSide.aW hp i E
  · have hr := (hX (by show s.st.2.toBitVec.toNat = _; rw [ha])).1
    show TakeK _ (Kernel.siteRange abi s) s s' ∨ _ ↔ TakeK _ _ s s' ∨ _
    rw [hr]
  · exact ⟨fun h => h.imp (fun h => (ha h.1).elim) id, fun h => h.imp (fun h => (ha h.1).elim) id⟩

/-- **`hB_box`'s `hmid` at `l`, `b`, `n` with the callee's take**:
`hmid_box`'s premises, `HMidPA` for `HMidP`, A13's data part (`hA13`: the
second stack in the pool, `StartPlaceLy.hsub1_W`). -/
theorem hmid_boxA {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop} (hprog : (Ly).prog = wakeProg)
    (haW : WakeOSide.aW hp i E = (Ly).lab Ret0.StackTake.siteL)
    (hokb : ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms0 (Ly).lab → q.OKB ms1 (Ly).lab)
    (hg : ms0.heap = (WakeOD.arW hp i).heap ∧ ms0.cells = (WakeOD.arW hp i).cells ∧
      ms0.off = (WakeOD.arW hp i).off ∧ ms0.units = (WakeOD.arW hp i).units)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hP : ∀ R F J0 t, BoxPure (Ly) F0 n R F J0 t → HMidPA hp i E cT Dt Ctx ls0 l b n R F J0 t) :
    SegWS (W1X hp i E Dt Ctx ls0 l b n) (WakeH1Inv.K1W hp i E) WakeT1.wakeSrc (A64ConsumerA.upd (L0T (Ly).Λ) l b)
      (WakeH1Inv.ms1W hp i E cT ls0 l b n) (fun s c fs => WakeWc.Box (Ly) ms0 F0 l b n s c ∧ fs = [])
      (CloneP hp i E Dt Ctx ls0 l b n) := by
  have eW : SccCode.wakeProg = wakeProg := by decide +kernel
  have hL : Scc.Cert.Rt.A64.Lays (Ly).exe wakeProg (Ly).pfx := hprog ▸ (Ly).lays
  have hL' : Scc.Cert.Rt.A64.Lays (Ly).exe SccCode.wakeProg (Ly).pfx := eW ▸ hL
  have hE : (Ly).endPc = WakeSpawnR.endR hp i := by
    show Scc.Cert.Rt.A64.endOf _ (Ly).prog _ = _; rw [hprog]
  have hfit1 : (WakeOSide.r1W hp i).lo + (WakeOSide.r1W hp i).size ≤ 2 ^ 64 := by
    have := (Ly).pool_fit; obtain ⟨-, h⟩ := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13; omega
  refine (SegWS.exists_pre (P := fun (g : Region × (MachineData → Prop) × (AS → Ctl → Prop) × UInt64) s c fs =>
    BoxPure (Ly) F0 n g.1 g.2.1 g.2.2.1 g.2.2.2 ∧ (At (Ly).exe (Ly).endPc g.1 g.2.1
      (bX ms0 (Ly).lab g.2.2.1 l b) s c ∧ TP g.2.2.2 s) ∧ QB l b l b c ∧ A64.KeepUn.U (r1Of (Ly).lab) s ∧ fs = [])
      fun g => ?_).mono_pre ?_
  · obtain ⟨R, F, J0, t⟩ := g
    by_cases hC : BoxPure (Ly) F0 n R F J0 t
    case neg => exact ⟨fun _ _ _ => False, fun _ _ _ h => hC h.1, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    have hp' := hP R F J0 t hC
    obtain ⟨⟨hR, hal, hF, hlo, hhi, hfit, hup⟩, -, -, ⟨⟨J, σC, rfl⟩, hx0, hst⟩, ht, hn, hcl, hcg, hhi48, -⟩ := hC
    have hfence : WcMidW (WB hp i E Dt Ctx ls0 l b n) (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F
        (fun m => F m ∧ StackM (WakeOSide.r1W hp i) m) (tpXa ms1 t) (WakeM.wJ0 (WakeM.wNC (Ly).lab J).J σC)
        (SB l b) (QB l b) :=
      WcMidW.antiF₂ (fun _ h => h.1) (WcMidW.mapWK (fun _ _ ⟨⟨hc, ha⟩, hw⟩ hk =>
        ⟨⟨hw, WakeWc.pcOf_ne hc, WakeWc.pcOf_ne ha⟩, hk⟩)
        (WcMidW.and (WakeWc.wcMidW_offC hL) (wcMidW_w1 hp i E Dt Ctx ls0 l b n hp'.wcWf hp'.res hp'.tcb)))
    have hW : WcMidW (fun s c => W1X hp i E Dt Ctx ls0 l b n s c [] ∧ NoMsrAt s) KA (Ly).exe
        (WakeSpawnR.endR hp i) R F (fun m => F m ∧ StackM (WakeOSide.r1W hp i) m) (tpXa ms1 t)
        (WakeM.wJ0 (WakeM.wNC (Ly).lab J).J σC) (SB l b) (QB l b) :=
      WcMidW.mapWK (fun s c ⟨⟨hw, hc, ha⟩, hnm, _⟩ _ =>
        ⟨⟨⟨hw, WakeH1Inv.x1W_off hc (by rw [haW]; exact ha)⟩, hnm⟩,
          fun s' (hk : KA s s') => hk.elim (fun h => ha (by rw [← haW]; unfold pcOf; rw [h.1]))
            fun h => hc h.1.1⟩) (WcMidW.noMsr hL' (by rw [eW]) hfence)
    have hseg := WakeWc.wake_wc_mid_hatK (p := WakeT1.wakeSrc) (lbl := A64ConsumerA.upd (L0T (Ly).Λ) l b)
      (ms := ms1) (t := t) (W := fun s c => W1X hp i E Dt Ctx ls0 l b n s c []) (K := KA)
      (M := StackM (WakeOSide.r1W hp i)) rfl hL' (by rw [eW]) hF hR hal hlo hhi
      (fun m m' h hd => ⟨hF m m' h.1 hd, WakeWc.stackM_r1 hhi48 hst hfit1 m m' h.2 hd⟩)
      (fun _ h1 h2 => ⟨h1, h2⟩) hfit (fun m h => hup m h.1) hW
      (fun q l' A ⟨e1, e2, ht, hh, ho, hme⟩ => (WakeBoxW.src_spawn (WakeOD.arW_pub hp i) ht hh ho hme).imp
        fun _ h => ⟨h.1, e1, e2, h.2⟩) hp'.resA hp'.hdrA hp'.tcbA hp'.tid
      (WakeWc.takeCK_fK hcl hcg) (fun s s' hk _ k hk' _ => WakeWc.takeCK_kR hR hhi48 hst hfit1 s s' hk k hk')
      WakeWc.takeCK_tp (fun _ _ _ ⟨ho1, ho2⟩ _ hk => hk.elim (fun h => (ho2 (h.1.trans haW)).elim)
        fun h => (WakeWc.pcOf_ne ho1 h.1.1).elim) fun c0 cA m fr hM => by
        obtain ⟨⟨l', A', hS, hcA⟩, -, ⟨σe, c', hJ, -, hm⟩⟩ := hM
        exact fun R' F' h1 h2 h3 h4 h5 h6 h7 h8 h9 g h10 h11 => (hp'.ti c0 ⟨l', A', hS⟩ cA m fr R' F'
          (hcA.trans hS.2.1) (by rw [hm]; exact hx0 σe c' hJ) h1 h2 h3 h4 h5 h6 h7 h8 h9 g h10 h11)
    have hseg := hseg.mono_K (K' := WakeH1Inv.K1W hp i E) fun s c h s' => k1W_iff hp i E Dt Ctx ls0 l b n h s'
    refine ((SegWS.liftS [] hseg fun s c h => h).mono_pre ?_).mono_post ?_
    · rintro s c fs ⟨-, ⟨hA, htp⟩, hq, hu, rfl⟩
      exact ⟨⟨⟨l, b, at_bX_ms hokb ⟨hg.1.symm, hg.2.1.symm, hg.2.2.1.symm, hg.2.2.2.symm⟩ (hE ▸ hA), hq⟩, hu, htp⟩,
        rfl⟩
    · rintro s c fs ⟨⟨cA, m, fr, ⟨l', A, ⟨rfl, rfl, hsrc⟩, hcA⟩, hG, ⟨σe, c', hJ, -, rfl⟩, hA, hok, hat, hsp, htp⟩, rfl⟩
      have htb : t.toBitVec = (Ly).pinA + 0#64 + 8#64 := by
        apply BitVec.eq_of_toNat_eq
        have h1 := t.toBitVec.isLt; have h2 := (Ly).pinA.isLt; have ht' : t.toBitVec.toNat = _ := ht
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hAF : At (Ly).exe (WakeSpawnR.endR hp i) R F
          (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA _ fr) s c :=
        let ⟨he, hn', hd, hpc, σ, hAb, hD, hJ'⟩ := hA; ⟨he, hn', hd, hpc, σ, hAb, hD.1, hJ'⟩
      have hSM : StackM (WakeOSide.r1W hp i) s.st.1 := let ⟨_, _, _, _, _, _, hD, _⟩ := hA; hD.2
      exact ⟨rfl, hsrc, hn, hp'.wcl s c cA _ fr hAF hcA (hx0 σe c' hJ) hsrc, R, _, J, σC, cA, _, fr, t, hR, hal,
        hlo, hhi, hst, hG, htb, htp, hA, hok, hat, hsp, hcA, hx0 σe c' hJ, hSM⟩
  · rintro s c fs ⟨⟨R, F, J0, t, h1, h2, h3, h4, ⟨hA, htp, ht⟩, hn, hsrc, ⟨-, hu⟩, h5⟩, rfl⟩
    exact ⟨(R, F, J0, t), ⟨h1, h2, h3, h4, ht, hn, h5⟩, ⟨hA, htp⟩, ⟨rfl, rfl, hsrc⟩, hu, rfl⟩

end Inst

end Spike.Lib.WakeHatA

/-- info: 'Spike.Lib.WakeHatA.k1W_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeHatA.k1W_iff

/-- info: 'Spike.Lib.WakeHatA.hmid_boxA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeHatA.hmid_boxA
