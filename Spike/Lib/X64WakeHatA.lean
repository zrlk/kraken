/-
**`hB_box`'s `hmid` with `scc_rt_thread_init`'s take** (x86-64, the twin of
`Spike/Lib/A64WakeHatA.lean`): `hmid_box` with the callee inside
`W1X ∧ NoSetFsAt` under the take of the second stack or a `clone` refusal
(`TakeCK aW r1W ClW`), the late frame condition `F ∧ StackM r1W` (the
child's stack private at the clone). `wake_wc_mid_hatK` from the landing:
`WB`'s nodes (`WcMidW.antiF₂`, `NoSetFsW`) are in `W1X` (`x1W_off`), unmoved
by `TakeCK`; `TakeCK` keeps `F`, `R`'s cells and the thread pointer
(`takeCK_fK`, `takeCK_kR`, `takeCK_tp`).

- `HMidPA`: `HMidP` with `ti` inside `W1X ∧ NoSetFsAt` under the take, its
  entry at `Pz r1W` and its exit at `StackM r1W`; `wcl` only `W1W`;
- `k1W_iff`: `K1W` is `TakeCK aW r1W ClW` at `W1X`'s states (`X1W`'s take
  clause);
- `hmid_boxA`: `hmid` at `l`, `b`, `n`.

**Unlike AArch64** (as in `X64WakeHMid`): the exit of `wake_wc_mid_hatK` is
at the box's published control `boxPubCtl`, so the pair step to `SpawnSrc l`
is taken after the segment (`pub_spawn`, `SegWS.post_run`) and the clone's
and main's nodes are moved to the new control (`at_wcNS_ctl`, `at_JS_ctl`);
there is no `SB` (`ti`'s source fact is `QB`'s); the fence is inside
`NoSetFsW`/`NoSetFsAt`, not `NoMsrW`/`NoMsrAt`; the assembly is a parameter
`asm`; the regions are x86-64's (`ti` at `R.callee (-72) (-248) 8`, no
alignment premise on `R'`, `Abs R oC`); `R` ends `64` below the second stack
(`takeCK_kR`, `stackM_r1` at `d = 64`; A64 `48`); `ti`'s thread-init ghost
is `Ret0.AllocTcb.G` (x86-64's `tiQ`). No absolute address appears here.
-/
import Spike.Lib.X64WakeHMid
import Spike.Lib.X64WakeWcHatK
import Spike.Lib.X64WakeStartPlaceLy

namespace Spike.Lib.X64.WakeHatA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (WcMainW WcMidW bX t2 kOf rAR wcMidW_w1 MidG FrG FrMG)
open Spike.Lib.X64.WakePh.WcSp4 (wcNI)
open Spike.Lib.X64.WakePh.WcClone (oW wcNS)
open Spike.Lib.X64.WakePh.Tcb2Call (oC tcb2Q)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StOk CallerCells StackM TakeK)
open Spike.Lib.X64.Rt (TcbOkGA hdrA TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResOkA ReserveW)
open Spike.Lib.X64.KeepTP (NoSetFsAt TP tpXa)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.X64.WakeOPremW (W1W)
open Spike.Lib.X64.WakeBoxW (SpawnSrc W1X CloneP)
open Spike.Lib.X64.WakeHMid (BoxPure QB WB at_bX_ms pub_spawn at_wcNS_ctl at_JS_ctl)
open Spike.Lib.X64ConsumerA (TakeCK)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open SccCode (wakeCells)
open Scc.Cert.Rt.X64 (Lays endOf)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)
  (l : WeakMem.AllocLabel) (b n : Nat)

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

/-- **`hmid`'s named premises at one ghost with the callee's take**:
`HMidP`'s `wcWf`, `res`, `tcb`, `resA`, `hdrA`, `tcbA`, `tid`; the callee
inside `W1X ∧ NoSetFsAt` under the take (`ti`); `W1W` at the clone's
`syscall` (`wcl`). -/
structure HMidPA (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64) : Prop where
  /-- `wc_main`'s nodes inside `W1W`. -/
  wcWf : WcMainW (fun s c => W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe eR R F F
    (tpXa ms1 t) J0 (QB l b)
  /-- The reserve's nodes inside `W1W` (`HMidP.res`). -/
  res : ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = ((Ly).lab ".Lwc_main.x1").toBitVec →
    ∀ nd, ReserveW (fun s c => W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe eR (rAR R)
      (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ WakeWc.ResCtx (Ly).lab R
        (WakeWc.rN (tpXa ms1 t) (Ly).lab R J0 (QB l b) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- The second TCB's nodes inside `W1W` (`HMidP.tcb`). -/
  tcb : ∀ c0 cA m fr, MidG (QB l b) c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    ∀ g : Ret0.AllocTcb.G, g.ra = ((Ly).lab ".Lwc_main.x2").toBitVec →
    ∀ nd, TcbWG (fun s c => W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe eR
      (R.callee (-72) (-184) 8) (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧
        WakeWc.TcbCtx (Ly).lab R (WakeWc.wcNCR (Ly).lab c0 cA m fr).J c0 g mm) (tcb2Q g c0) nd
  /-- `wake_wc_mid_hatK`'s `hres`. -/
  resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA ms1 F (Ly).exe eR (rAR R) F ⟨g.1, 0#64, g.2⟩
  /-- `wake_wc_mid_hatK`'s `hhdr`. -/
  hdrA : ∀ c0 g, StOk ms1 F (hdrA (Ly).lab (tcb2Q g c0)) ((tcb2Q g c0).h ||| 1#64 <<< 36)
  /-- `wake_wc_mid_hatK`'s `htcb`. -/
  tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe eR (R.callee (-72) (-184) 8) F (tcb2Q g c0)
  /-- `wake_wc_mid_hatK`'s `htid`. -/
  tid : (ms1).rt (t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨t2 (Ly).lab + 56#64, 8⟩ true ∧
    (ms1).G ⟨t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none
  /-- The callee inside `W1X ∧ NoSetFsAt` under the take, from `Pz r1W` to
  `StackM r1W`, at the box's source facts, its cell `b` and main's word. -/
  ti : ∀ (c0 : Ctl), (∃ l' A', QB l b l' A' c0) → ∀ (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)
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
  /-- `W1W` at the clone's `syscall`. -/
  wcl : ∀ s c cA m fr,
    At (Ly).exe eR R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c →
    cA.toNat = b → m.toNat = tcb0 (Ly).Λ →
    SpawnSrc l c → W1W asm hp i E Dt Ctx ls0 l b n s c []

/-- **`K1W` is the callee's move at `W1X`'s states**: at the take's pc the
site's range is the second stack (`X1W`'s take clause). -/
theorem k1W_iff {s : State} {c : Ctl} (h : W1X asm hp i E Dt Ctx ls0 l b n s c []) (s' : State) :
    WakeH1Inv.K1W hp i E s s' ↔ KA s s' := by
  obtain ⟨-, -, hX⟩ := h
  by_cases ha : s.st.2 = X64WakeOSide.aW hp i E
  · have hr := (hX (by show s.st.2.toBitVec.toNat = _; rw [ha])).1
    show TakeK _ (Kernel.siteRange abi s) s s' ∨ _ ↔ TakeK _ _ s s' ∨ _
    rw [hr]
  · exact ⟨fun h => h.imp (fun h => (ha h.1).elim) id, fun h => h.imp (fun h => (ha h.1).elim) id⟩

/-- **`hB_box`'s `hmid` at `l`, `b`, `n` with the callee's take**:
`hmid_box`'s premises, `HMidPA` for `HMidP`, A13's data part (`hA13`: the
second stack in the pool, `StartPlaceLy.hsub1_W`). -/
theorem hmid_boxA {ms0 : MemSide isa} {F0 : MachineData → Prop} (hprog : (Ly).prog = wakeCells)
    (haW : X64WakeOSide.aW hp i E = (Ly).lab Ret0.StackTake.siteL)
    (hokb : ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB ms0 (Ly).lab → q.OKB ms1 (Ly).lab)
    (hg : ms0.heap = (WakeOD.arW hp i).heap ∧ ms0.cells = (WakeOD.arW hp i).cells ∧
      ms0.off = (WakeOD.arW hp i).off ∧ ms0.units = (WakeOD.arW hp i).units)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hP : ∀ R F J0 t, BoxPure (Ly) F0 n R F J0 t → HMidPA asm hp i E cT Dt Ctx ls0 l b n R F J0 t) :
    SegWS (W1X asm hp i E Dt Ctx ls0 l b n) (WakeH1Inv.K1W hp i E) X64WakeT1.wakeSrc
      (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
      (WakeH1Inv.ms1W asm hp i E cT ls0 l b n) (fun s c fs => WakeWc.Box (Ly) ms0 F0 l b n s c ∧ fs = [])
      (CloneP asm hp i E Dt Ctx ls0 l b n) := by
  have hL : Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hE : (Ly).endPc = eR := by
    show endOf _ (Ly).prog _ = _; rw [hprog]
  have hfit1 : (X64WakeOSide.r1W hp i).lo + (X64WakeOSide.r1W hp i).size ≤ 2 ^ 64 := by
    have := (Ly).pool_fit; have h := Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hp i hA13
    simp only [Scc.Sem.Range.Sub] at h; omega
  refine (SegWS.exists_pre (P := fun (g : Region × (MachineData → Prop) × (AS → Ctl → Prop) × UInt64) s c fs =>
    BoxPure (Ly) F0 n g.1 g.2.1 g.2.2.1 g.2.2.2 ∧ (At (Ly).exe (Ly).endPc g.1 g.2.1
      (bX ms0 (Ly).lab g.2.2.1 l b) s c ∧ TP g.2.2.2 s) ∧ QB l b l b c ∧
      Spike.Lib.X64.KeepUn.U (r1Of (Ly).lab) s ∧ fs = []) fun g => ?_).mono_pre ?_
  · obtain ⟨R, F, J0, t⟩ := g
    by_cases hC : BoxPure (Ly) F0 n R F J0 t
    case neg => exact ⟨fun _ _ _ => False, fun _ _ _ h => hC h.1, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    have hp' := hP R F J0 t hC
    obtain ⟨⟨hR, -, hF, hlo, hhi⟩, -, -, ⟨⟨J, σC, rfl⟩, hdi, hst, hsp0⟩, ht, hn, hcl, hcg, hhi64, -⟩ := hC
    have hfence : WcMidW (WB asm hp i E Dt Ctx ls0 l b n) (fun _ _ => False) (Ly).exe eR R F
        (fun m => F m ∧ StackM (X64WakeOSide.r1W hp i) m) (tpXa ms1 t) (WakeM.wJ0 (WakeM.wNC (Ly).lab J).J σC)
        (QB l b) :=
      WakeWc.WcMidW.antiF₂ (fun _ h => h.1) (WcMidW.mapWK (fun _ _ ⟨⟨hc, ha⟩, hw⟩ hk =>
        ⟨⟨hw, WakeWc.pcOf_ne hc, WakeWc.pcOf_ne ha⟩, hk⟩)
        (WcMidW.and (WakeWc.wcMidW_offC hL) (wcMidW_w1 asm hp i E Dt Ctx ls0 l b n hp'.wcWf hp'.res hp'.tcb)))
    have hW : WcMidW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c [] ∧ NoSetFsAt s) KA (Ly).exe eR R F
        (fun m => F m ∧ StackM (X64WakeOSide.r1W hp i) m) (tpXa ms1 t)
        (WakeM.wJ0 (WakeM.wNC (Ly).lab J).J σC) (QB l b) :=
      WcMidW.mapWK (fun s c ⟨⟨hw, hc, ha⟩, hnm, _⟩ _ =>
        ⟨⟨⟨hw, WakeH1Inv.x1W_off hc (by rw [haW]; exact ha)⟩, hnm⟩,
          fun s' (hk : KA s s') => hk.elim (fun h => ha (by rw [← haW]; unfold pcOf; rw [h.1]))
            fun h => hc h.1.1⟩) (WakeWc.WcMidW.noSetFs hL rfl hfence)
    have hseg := WakeWc.wake_wc_mid_hatK (p := X64WakeT1.wakeSrc)
      (lbl := Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) (ms := ms1) (t := t)
      (W := fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (K := KA)
      (M := StackM (X64WakeOSide.r1W hp i)) rfl hL rfl hF hR hlo hhi
      (fun m m' h hd => ⟨hF m m' h.1 hd, WakeWc.stackM_r1 hhi64 hst hfit1 m m' h.2 hd⟩)
      (fun _ h1 h2 => ⟨h1, h2⟩) hW
      (by rintro l' A c ⟨rfl, -, ht, hh, ho, -⟩; exact ⟨ht, hh, _, ho⟩) (WakeOD.arW_pub hp i)
      hp'.resA hp'.hdrA hp'.tcbA hp'.tid
      (WakeWc.takeCK_fK hcl hcg) (fun s s' hk _ k hk' _ => WakeWc.takeCK_kR hR hhi64 hst hfit1 s s' hk k hk')
      WakeWc.takeCK_tp (fun _ _ _ ⟨ho1, ho2⟩ _ hk => hk.elim (fun h => (ho2 (h.1.trans haW)).elim)
        fun h => (WakeWc.pcOf_ne ho1 h.1.1).elim) fun c0 cA m fr hM => by
        obtain ⟨⟨l', A', hS, hcA⟩, -, ⟨σe, c', hJ, -, hm⟩⟩ := hM
        exact fun R' F' h1 h2 h3 h4 h5 h6 h7 h8 g h9 h10 => hp'.ti c0 ⟨l', A', hS⟩ cA m fr R' F'
          (hcA.trans hS.2.1) (by rw [hm]; exact hdi σe c' hJ) h1 h2 h3 h4 h5 h6 h7 h8 g h9 h10
    have hseg := hseg.mono_K (K' := WakeH1Inv.K1W hp i E) fun s c h s' => k1W_iff asm hp i E Dt Ctx ls0 l b n h s'
    refine SegWS.post_run (((SegWS.liftS [] hseg fun s c h => h).mono_pre ?_).mono_post ?_)
    · rintro s c fs ⟨-, ⟨hA, htp⟩, hq, hu, rfl⟩
      rw [hE] at hA
      exact ⟨⟨⟨l, b, at_bX_ms hokb ⟨hg.1.symm, hg.2.1.symm, hg.2.2.1.symm, hg.2.2.2.symm⟩ hA, hq⟩, hu, htp⟩, rfl⟩
    · rintro s c fs ⟨⟨c0, ty, l', cA, m, fr, rfl, ⟨⟨rfl, hcA, -, -, ho, hme⟩, -, -, ho'⟩, hG, hGm, hA, hok, hat, hsp,
        htp⟩, rfl⟩
      have hty := congrArg Prod.fst (Option.some.inj (ho.symm.trans ho'))
      cases hty
      obtain ⟨c', hr, hsrc⟩ := pub_spawn (p := X64WakeT1.wakeSrc) (l := l') hme
      have hA' := at_wcNS_ctl (c' := c') hA
      have hAF : At (Ly).exe eR R F (wcNS (Ly).lab c' (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c' :=
        let ⟨he, hn', hd, hpc, σ, hAb, hD, hJ'⟩ := hA'; ⟨he, hn', hd, hpc, σ, hAb, hD.1, hJ'⟩
      have hSM : StackM (X64WakeOSide.r1W hp i) s.st.1 := let ⟨_, _, _, _, _, _, hD, _⟩ := hA'; hD.2
      have htb : t.toBitVec = (Ly).pinA + 0#64 + 8#64 := by
        apply BitVec.eq_of_toNat_eq
        have h1 := t.toBitVec.isLt; have h2 := (Ly).pinA.isLt; have ht' : t.toBitVec.toNat = _ := ht
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      obtain ⟨σe, ce, hJ, -, rfl⟩ := hGm
      have hm := hdi σe ce hJ
      have hσ := hsp0 σe ce hJ
      obtain ⟨rfl, -⟩ := hJ
      exact ⟨c', [], hr, rfl, hsrc, hn, hp'.wcl s c' cA _ fr hAF hcA hm hsrc, R, _, J, σC, cA, _, fr, t, hR, hlo,
        hhi, hst, hG, htb, htp, hA', hok, at_JS_ctl hat, hsp, hcA, hm, hSM, hσ⟩
  · rintro s c fs ⟨⟨R, F, J0, t, h1, h2, h3, h4, ⟨hA, htp, ht⟩, hn, hsrc, ⟨-, hu⟩, h5⟩, rfl⟩
    exact ⟨(R, F, J0, t), ⟨h1, h2, h3, h4, ht, hn, h5⟩, ⟨hA, htp⟩, ⟨rfl, rfl, hsrc⟩, hu, rfl⟩

end Inst

end Spike.Lib.X64.WakeHatA

/-- info: 'Spike.Lib.X64.WakeHatA.k1W_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHatA.k1W_iff

/-- info: 'Spike.Lib.X64.WakeHatA.hmid_boxA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHatA.hmid_boxA
