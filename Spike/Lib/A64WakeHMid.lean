/-
**`hB_box`'s `hmid`** (AArch64; `A64WakeBoxW.hB_box`): wake's box, past its
store, runs inside `h1`'s fence `W1X` under `h1`'s outside move `K1W` to
main's `clone` (`CloneP`), at the fresh label `l` of `n` bytes at `b`.

`wake_wc_mid_hatW` from the box's landing `bX`, its source facts `QB` (the
box's), the source at the clone `SB` (`SpawnSrc l` at `l`, `b`: `src_spawn`
with the arena's publication `WakeOD.arW_pub`), its fence off the clone's
and the take site's pcs (`wcMidW_offC`) and `W1W`'s (`wcMidW_w1`), at no
outside move; `K1W` moves no state of the fence (`takeCKS_none`,
`SegW.mono_K`); lifted at no frames (`SegWS.liftS`, `X1W` off both pcs by
`x1W_off`).

- `BoxPure`: `Box`'s facts of its ghosts alone (`R`, `F`, `J0`, `t`, `n`).
- `at_bX_ms`: the landing across memory sides admitting the same box calls.
- `HMidP`: the named premises at one ghost: `wcWf`, `res`, `tcb`
  (`wcMidW_w1`'s), `resA`, `hdrA`, `tcbA`, `tid`, `ti`
  (`wake_wc_mid_hatW`'s at no outside move), and `wcl` (`W1W` at the clone's
  `svc`).
- `hmid_box`: `hmid` at `l`, `b`, `n`.

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeBoxW
import Spike.Lib.A64WakeWcW1
import Spike.Lib.A64WakeWcHat
import Spike.Lib.A64WakeWcNoMsr
import Spike.Lib.WakeAWSite

namespace Spike.Lib.WakeHMid

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (WcMainW WcMidW bX t2 kOf rAR wcMidW_w1 boxTerm MidG FrG FrMG)
open Spike.Lib.A64.WakePh.WcSp4 (wcNS wcNI)
open Spike.Lib.A64.WakePh.Tcb2Call (oW tcb2Q)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX)
open Spike.Lib.A64.Rt (TcbOkGA hdrA)
open Spike.Lib.A64.Rt.Reserve (ResOkA)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeLoadT (L0T tcb0)
open Spike.Lib.WakeOPremW (W1W)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.WakeBoxW (SpawnSrc W1X CloneP)
open Spike.Lib.HeapLand (AllocLand)

/-- **The landing across memory sides** admitting the same box calls, with
the same arena geometry (`heap`, `cells`, `off`, `units`). -/
theorem at_bX_ms {ms ms' : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (hq : ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms (_root_.Executable.labels exe).label →
      q.OKB ms' (_root_.Executable.labels exe).label)
    (hg : ms'.heap = ms.heap ∧ ms'.cells = ms.cells ∧ ms'.off = ms.off ∧ ms'.units = ms.units)
    (h : At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c) :
    At exe endPc R F (bX ms' (_root_.Executable.labels exe).label J0 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := hg
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, hq _ q.2⟩, h1, h2, h3, by rw [g1, g2, g3, g4]; exact h4⟩

/-- **`Box`'s facts of its ghosts alone**: the region `R`, the frame
condition `F`, the entry node `J0`, the thread pointer `t`, one object. -/
def BoxPure (L : Spike.Lib.A64.Rt.RuntimeLayout) (F0 : MachineData → Prop) (n : Nat) (R : Region)
    (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64) : Prop :=
  (R.OK ∧ R.base.toNat % 16 = 0 ∧ FStable R F ∧ R.lo ≤ -336 ∧ 0 ≤ R.hi ∧
      (R.base.toNat : Int) + 16 ≤ 2 ^ 64 ∧
      ∀ m, F m → ∀ k : Int, k % 8 = 0 → 0 ≤ k → k < 16 → (Mem.loadInt m.dmem (R.addr k) 8).isSome) ∧
    (∀ k, -128 ≤ k → k ≤ -80 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
      (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size) ∧
    (∀ m, F m → F0 m) ∧
    ((∃ (J : AS → Ctl → Prop) (σC : AS), J0 = WakeM.wJ0 (WakeM.wNC (_root_.Executable.labels L.exe).label J).J σC) ∧
      (∀ σe c, J0 σe c → σe.regs.X0.toNat = tcb0 L.Λ) ∧ R.base.toNat + 48 = L.stacksA.toNat + 16384) ∧
    t.toNat = L.pinA.toNat + 8 ∧ n = 1 ∧
    ((∀ m pm, F m → F (Ret0.takeMem pm (Spike.Lib.A64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) m)) ∧
      (∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m') ∧ R.hi ≤ 48 ∧
      (∀ m, F m → Ret0.StackOff (Spike.Lib.A64.Rt.Ti2.r0Of (_root_.Executable.labels L.exe).label) R m) ∧
      R.lo % 8 = 0 ∧ R.hi % 8 = 0)

/-- **The box's source facts** at `l` (`b`): `boxTerm`, no hold, `o` at `l`'s
owned locative, `me` at main's. -/
def QB (l : WeakMem.AllocLabel) (b : Nat) (l' : WeakMem.AllocLabel) (A : Nat) (c : Ctl) : Prop :=
  l' = l ∧ A = b ∧ c.term = boxTerm ∧ c.hold = none ∧
    TermRun.evalAt c.env (.var "o") = some (.ptr .own .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
    TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])

/-- **The source at the clone** at `l` (`b`): `SpawnSrc l`. -/
def SB (l : WeakMem.AllocLabel) (b : Nat) (l' : WeakMem.AllocLabel) (A : Nat) (c : Ctl) : Prop :=
  l' = l ∧ A = b ∧ SpawnSrc l c

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

/-- **The fence `wake_wc_mid_hatW` runs in**: `W1W` at no frames, off the
clone's pc and the take site's. -/
def WB : Frag isaLSE2 := fun s c => W1W hp i E Dt Ctx ls0 l b n s c [] ∧
  pcOf s ≠ WakeWc.clonePc (Ly) ∧ pcOf s ≠ ((Ly).lab Ret0.StackTake.siteL).toBitVec.toNat

/-- **`hmid`'s named premises at one ghost** (`R`, `F`, `J0`, `t`). -/
structure HMidP (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64) : Prop where
  /-- `wc_main`'s nodes inside `W1W` (`A64WakeWcWf`). -/
  wcWf : WcMainW (fun s c => W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe
    (WakeSpawnR.endR hp i) R F F (tpXa ms1 t) J0 (SB l b) (QB l b)
  /-- The reserve's nodes inside `W1W` (`reserveW_wf`). -/
  res : ∀ g : Reserve.G × Ctl, g.1.ra = ((Ly).lab ".L21_wc_main.sp3").toBitVec →
    ∀ nd, Spike.Lib.A64.Rt.Reserve.ReserveW (fun s c => W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False)
      (Ly).exe (WakeSpawnR.endR hp i) (rAR R)
      (fun m => F m ∧ Ret0.CallerCells R (-80) (-48) 0 m ∧ WakeWc.ResCtx (Ly).lab R
        (WakeWc.rN (tpXa ms1 t) (Ly).lab J0 (SB l b) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- The second TCB's nodes inside `W1W` (`tcbWG_wf`). -/
  tcb : ∀ c0 cA m fr, MidG (SB l b) c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    ∀ g : Ret0.AllocTcb.G, g.ra = ((Ly).lab ".L21_wc_main.sp4").toBitVec →
    ∀ nd, Spike.Lib.A64.Rt.TcbWG (fun s c => W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe
      (WakeSpawnR.endR hp i) (R.callee (-80) (-192) 0) (fun mm => F mm ∧ Ret0.CallerCells R (-80) (-192) 0 mm ∧
        WakeWc.TcbCtx (Ly).lab R (WakeWc.wcNC' (Ly).lab c0 cA m fr).J c0 g mm) (tcb2Q g c0) nd
  /-- `wake_wc_mid_hatW`'s `hres`. -/
  resA : ∀ g : Reserve.G × Ctl, ResOkA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (rAR R) F ⟨g.1, 0#64, g.2⟩
  /-- `wake_wc_mid_hatW`'s `hhdr`. -/
  hdrA : ∀ c0 g, Ret0.StOk ms1 F (Ly).exe (WakeSpawnR.endR hp i) (hdrA (Ly).lab (tcb2Q g c0))
    ((tcb2Q g c0).h ||| 1#64 <<< 36)
  /-- `wake_wc_mid_hatW`'s `htcb`. -/
  tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (R.callee (-80) (-192) 0) F (tcb2Q g c0)
  /-- `wake_wc_mid_hatW`'s `htid`. -/
  tid : (ms1).rt (t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨t2 (Ly).lab + 56#64, 8⟩ true ∧
    (ms1).G ⟨t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none
  /-- `wake_wc_mid_hatW`'s `hti`, inside `WB`, at no outside move, no
  post beyond the frame. -/
  ti : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region) (F' : MachineData → Prop),
    R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
    0 ≤ R'.hi → FStable R' F' → KStable (fun _ _ => False) F' → (∀ m, F' m → F m) →
    R' = R.callee (-80) (-256) 0 →
    (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -80) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
    ∀ g : Ret0.ThreadInit.G,
      (∃ σC c, (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
        (tiN (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-80) σC) c) →
      (∀ m', F' m' → ∃ mC σC c, Abs R oW mC σC ∧ (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
        (tiN (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-80) σC) c ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -80) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      SegW (NoMsrW (WB hp i E Dt Ctx ls0 l b n) (fun _ _ => False)) (fun _ _ => False) WakeT1.wakeSrc
        (A64ConsumerA.upd (L0T (Ly).Λ) l b) (tpXa ms1 t)
        (At (Ly).exe (WakeSpawnR.endR hp i) R' F' (tiN (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) .e))
        (fun s c => ∃ x, At (Ly).exe (WakeSpawnR.endR hp i) R' F' (tiX (Ly).lab (WakeWc.tiQ (t2 (Ly).lab) c0 g) x) s c ∧
          True)
  /-- `W1W` at the clone's `svc`, and the child's stack in private
  memory there (interim: `scc_rt_thread_init`'s take, until `hatA`). -/
  wcl : ∀ s c cA m fr,
    At (Ly).exe (WakeSpawnR.endR hp i) R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c →
    SpawnSrc l c → W1W hp i E Dt Ctx ls0 l b n s c [] ∧ Ret0.StackM (WakeOSide.r1W hp i) s.st.1

/-- **`hB_box`'s `hmid` at `l`, `b`, `n`**: from the box past its store to
main's clone inside `W1X` under `K1W`, given the layout's program wake's
(`hprog`), the take site at `scc_rt_take_site` (`haW`: `aW_site`), the box
call's premises from `ms0` at `h1`'s side (`hokb`: `okb_ms1`), `ms0`'s
arena geometry the arena's (`hg`, for the landing's allocator fact), and
`HMidP` at every ghost of `Box`'s. -/
theorem hmid_box {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop} (hprog : (Ly).prog = wakeProg)
    (haW : WakeOSide.aW hp i E = (Ly).lab Ret0.StackTake.siteL)
    (hokb : ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms0 (Ly).lab → q.OKB ms1 (Ly).lab)
    (hg : ms0.heap = (WakeOD.arW hp i).heap ∧ ms0.cells = (WakeOD.arW hp i).cells ∧
      ms0.off = (WakeOD.arW hp i).off ∧ ms0.units = (WakeOD.arW hp i).units)
    (hP : ∀ R F J0 t, BoxPure (Ly) F0 n R F J0 t → HMidP hp i E cT Dt Ctx ls0 l b n R F J0 t) :
    SegWS (W1X hp i E Dt Ctx ls0 l b n) (WakeH1Inv.K1W hp i E) WakeT1.wakeSrc (A64ConsumerA.upd (L0T (Ly).Λ) l b)
      (WakeH1Inv.ms1W hp i E cT ls0 l b n) (fun s c fs => WakeWc.Box (Ly) ms0 F0 l b n s c ∧ fs = [])
      (CloneP hp i E Dt Ctx ls0 l b n) := by
  have eW : SccCode.wakeProg = wakeProg := by decide +kernel
  have hL : Scc.Cert.Rt.A64.Lays (Ly).exe wakeProg (Ly).pfx := hprog ▸ (Ly).lays
  have hL' : Scc.Cert.Rt.A64.Lays (Ly).exe SccCode.wakeProg (Ly).pfx := eW ▸ hL
  have hE : (Ly).endPc = WakeSpawnR.endR hp i := by
    show Scc.Cert.Rt.A64.endOf _ (Ly).prog _ = _; rw [hprog]
  refine (SegWS.exists_pre (P := fun (g : Region × (MachineData → Prop) × (AS → Ctl → Prop) × UInt64) s c fs =>
    BoxPure (Ly) F0 n g.1 g.2.1 g.2.2.1 g.2.2.2 ∧ (At (Ly).exe (Ly).endPc g.1 g.2.1
      (bX ms0 (Ly).lab g.2.2.1 l b) s c ∧ TP g.2.2.2 s) ∧ QB l b l b c ∧ fs = []) fun g => ?_).mono_pre ?_
  · obtain ⟨R, F, J0, t⟩ := g
    by_cases hC : BoxPure (Ly) F0 n R F J0 t
    case neg => exact ⟨fun _ _ _ => False, fun _ _ _ h => hC h.1, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    have hp' := hP R F J0 t hC
    obtain ⟨⟨hR, hal, hF, hlo, hhi, hfit, hup⟩, -, -, ⟨⟨J, σC, rfl⟩, hx0, hst⟩, ht, hn, -, -, -⟩ := hC
    have hfence : WcMidW (WB hp i E Dt Ctx ls0 l b n) (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F F
        (tpXa ms1 t) (WakeM.wJ0 (WakeM.wNC (Ly).lab J).J σC) (SB l b) (QB l b) :=
      WcMidW.mapWK (fun _ _ ⟨⟨hc, ha⟩, hw⟩ hk => ⟨⟨hw, WakeWc.pcOf_ne hc, WakeWc.pcOf_ne ha⟩, hk⟩)
        (WcMidW.and (WakeWc.wcMidW_offC hL) (wcMidW_w1 hp i E Dt Ctx ls0 l b n hp'.wcWf hp'.res hp'.tcb))
    have hseg := WakeWc.wake_wc_mid_hatW (p := WakeT1.wakeSrc) (lbl := A64ConsumerA.upd (L0T (Ly).Λ) l b)
      (ms := ms1) (t := t) rfl (M := fun _ => True) (F₂ := F) hL' (by rw [eW]) hF hR hal hlo hhi hF
      (fun _ h _ => h) hfit hup (WcMidW.noMsr hL' (by rw [eW]) hfence)
      (fun q l' A ⟨e1, e2, ht, hh, ho, hme⟩ => (WakeBoxW.src_spawn (WakeOD.arW_pub hp i) ht hh ho hme).imp
        fun _ h => ⟨h.1, e1, e2, h.2⟩) hp'.resA hp'.hdrA hp'.tcbA hp'.tid (KStable.none F)
        (fun _ _ h => h.elim) hp'.ti
    have hseg := hseg.mono_K (K' := WakeH1Inv.K1W hp i E) fun s _ ⟨_, hc, ha⟩ s' =>
      ⟨fun h => (WakeWc.takeCKS_none (Cl := WakeOD.ClW hp i) (fun _ h => h.1)
        (fun e => ha (by rw [← haW]; unfold pcOf; rw [e])) hc s' h).elim, False.elim⟩
    refine ((SegWS.liftS [] hseg fun s c ⟨hw, hc, ha⟩ => ⟨hw, WakeH1Inv.x1W_off hc (by rw [haW]; exact ha)⟩).mono_pre
      ?_).mono_post ?_
    · rintro s c fs ⟨-, ⟨hA, htp⟩, hq, rfl⟩
      exact ⟨⟨⟨l, b, at_bX_ms hokb ⟨hg.1.symm, hg.2.1.symm, hg.2.2.1.symm, hg.2.2.2.symm⟩ (hE ▸ hA), hq⟩, htp⟩, rfl⟩
    · rintro s c fs ⟨⟨cA, m, fr, ⟨l', A, ⟨rfl, rfl, hsrc⟩, hcA⟩, hG, ⟨σe, c', hJ, -, rfl⟩, hA, hok, hat, hsp, htp⟩, rfl⟩
      have htb : t.toBitVec = (Ly).pinA + 0#64 + 8#64 := by
        apply BitVec.eq_of_toNat_eq
        have h1 := t.toBitVec.isLt; have h2 := (Ly).pinA.isLt; have ht' : t.toBitVec.toNat = _ := ht
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact ⟨rfl, hsrc, hn, (hp'.wcl s c cA _ fr hA hsrc).1, R, F, J, σC, cA, _, fr, t, hR, hal, hlo, hhi, hst, hG,
        htb, htp, hA, hok, hat, hsp, hcA, hx0 σe c' hJ, (hp'.wcl s c cA _ fr hA hsrc).2⟩
  · rintro s c fs ⟨⟨R, F, J0, t, h1, h2, h3, h4, ⟨hA, htp, ht⟩, hn, hsrc, -, h5⟩, rfl⟩
    exact ⟨(R, F, J0, t), ⟨h1, h2, h3, h4, ht, hn, h5⟩, ⟨hA, htp⟩, ⟨rfl, rfl, hsrc⟩, rfl⟩

end Inst

end Spike.Lib.WakeHMid

/-- info: 'Spike.Lib.WakeHMid.at_bX_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeHMid.at_bX_ms

/-- info: 'Spike.Lib.WakeHMid.hmid_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeHMid.hmid_box
