/-
**`h1` assembled** (AArch64): `A64WakeWcInv.H1Stmt` at `inv1W` from wake's
box (`WakeBoxW.h1Stmt_box`), its `hmid` from `WakeHMid.hmid_box`, `hmid`'s
reserve and second-TCB premises from `CalWf.reserveW_wf`/`CalWf.tcbWG_wf`,
and its `hseg` from `WakeRefSeg.seg_refB`.

The layout premises are discharged here from the loader's facts:
- `hprog`: `WakeSrcCtl.prog_W`.
- `hna`: `WakeSrcCtl.hna_W`.
- `hsub1`: `StartPlaceLy.hsub1_W`.
- `haW`: `WakeOSide.aW_site`.
- `hmN`, `hoffN`, `hoffP`, `hoffH`: `CalWf.hmN_W`, `hoffN_W`, `hoffP_W`,
  `hoffH_W`.
- `hsep`: `StartPlaceLy.wsep_W`.
- `hSctl`: `WakeSrcCtl.spawnSrc_ctl`.

The pieces that have not landed are named premises, each with exactly the
type its consumer takes:
- `H1G`: the premises at one ghost of `Box` (`R`, `F`, `J0`, `t`), under
  `BoxPure`.
- `wake_h1`: the remaining global premises (`hokb`, `hobl`), and the
  loader facts `hpa`, `hwp`, `hlo0`, `hA13`, `hpin2`, `hcz`.
-/
import Spike.Lib.A64WakeHMid
import Spike.Lib.A64WakeWfCalW1
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.A64WakeRefSeg
import Spike.Lib.A64WakeSrcCtl
import Spike.Lib.A64WakeWfCalOff

namespace Spike.Lib.WakeH1Root

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
open Spike.Lib.WakeHMid (BoxPure HMidP SB QB WB)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64ConsumerS (PlacedSE)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W hp i E cT ls0 l b n []

/-- **`h1`'s premises at one ghost of `Box`**, for the label `l` of `n`
bytes at `b`, at the region `R`, frame condition `F`, entry node `J0` and
thread pointer `t`. These are `HMidP`'s fields, except that `res` and `tcb`
are replaced by the premises `reserveW_wf`/`tcbWG_wf` take. -/
structure H1G (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop)
    (t : UInt64) : Prop where
  /-- `wc_main`'s nodes inside `W1W` (`HMidP.wcWf`). See `A64WakeWcWf`. -/
  wcWf : WcMainW (fun s c => W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe
    (WakeSpawnR.endR hp i) R F F (tpXa ms1 t) J0 (SB l b) (QB l b)
  /-- `scc_rt_nthreads` is unmapped under `F` (`reserveW_wf`'s `hunN`). -/
  hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none
  /-- The reserve's frames are placed (`reserveW_wf`'s `hpl`). -/
  hplR : ∀ g : Spike.Lib.A64.Flow.Reserve.G × Ctl, g.1.ra = ((Ly).lab ".L21_wc_main.sp3").toBitVec →
    ∀ nd, ReserveW (fun s c => PlacedSE (Ly).Λ (A64ConsumerA.upd (L0T (Ly).Λ) l b) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (rAR R)
      (fun m => F m ∧ Ret0.CallerCells R (-80) (-48) 0 m ∧
        WakeWc.ResCtx (Ly).lab R (WakeWc.rN (tpXa ms1 t) (Ly).lab J0 (SB l b) .call).J g m)
      ⟨g.1, 0#64, g.2⟩ nd
  /-- `scc_rt_pinned_next` is unmapped under `F` (`tcbWG_wf`'s `hunP`). -/
  hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none
  /-- `scc_rt_pinned + 96` is unmapped under `F` (`tcbWG_wf`'s `hunH`). -/
  hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none
  /-- The second TCB's per-node `SFactsSt2` at no move (`tcbWG_wf`'s `hst`). See `Tcb2CallW.tcb2W_ownGK`. -/
  hstT : ∀ c0, (∃ l' A', SB l b l' A' c0) →
    ∀ g : Ret0.AllocTcb.G, g.ra = ((Ly).lab ".L21_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s _ => A64ConsumerA.SFactsSt2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly))
        (Spike.Lib.A64.WakePh.ownG (Ly) (ntA (Ly).lab)) s) (fun _ _ => False)
      (Ly).exe (Ly).endPc (R.callee (-80) (-192) 0) F (tcb2Q g c0) nd
  /-- The second TCB's frames are placed (`tcbWG_wf_pt`'s `hpl`), at `HMidP.tcb`'s ghosts and frame
  condition (`PlacedCal.tcbWG_placed`'s form). -/
  hplT : ∀ c0 cA m fr, WakeWc.MidG (SB l b) c0 cA ∧ WakeWc.FrG J0 fr ∧ WakeWc.FrMG J0 fr m →
    ∀ g : Ret0.AllocTcb.G, g.ra = ((Ly).lab ".L21_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s c => PlacedSE (Ly).Λ (A64ConsumerA.upd (L0T (Ly).Λ) l b) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (R.callee (-80) (-192) 0) (fun mm => F mm ∧ Ret0.CallerCells R (-80) (-192) 0 mm ∧
        WakeWc.TcbCtx (Ly).lab R (WakeWc.wcNC' (Ly).lab c0 cA m fr).J c0 g mm) (tcb2Q g c0) nd
  /-- `wake_wc_mid_hatW`'s `hres` (`HMidP.resA`). -/
  resA : ∀ g : Reserve.G × Ctl, ResOkA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (rAR R) F ⟨g.1, 0#64, g.2⟩
  /-- `wake_wc_mid_hatW`'s `hhdr` (`HMidP.hdrA`). -/
  hdrA : ∀ c0 g, Ret0.StOk ms1 F (Ly).exe (WakeSpawnR.endR hp i) (hdrA (Ly).lab (tcb2Q g c0))
    ((tcb2Q g c0).h ||| 1#64 <<< 36)
  /-- `wake_wc_mid_hatW`'s `htcb` (`HMidP.tcbA`). -/
  tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (R.callee (-80) (-192) 0) F (tcb2Q g c0)
  /-- `wake_wc_mid_hatW`'s `htid` (`HMidP.tid`). -/
  tid : (ms1).rt (WakeWc.t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨WakeWc.t2 (Ly).lab + 56#64, 8⟩ true ∧
    (ms1).G ⟨WakeWc.t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (WakeWc.t2 (Ly).lab + 56#64) 8 = none
  /-- `wake_wc_mid_hatW`'s `hti` (`HMidP.ti`). See `TakeCK`, `r1W`, `mono_K`. -/
  ti : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region) (F' : MachineData → Prop),
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
  /-- `W1W` at the clone's `svc` and the child's stack in private memory there (`HMidP.wcl`);
  the `StackM` part comes from `hatA`. -/
  wcl : ∀ s c cA m fr,
    At (Ly).exe (WakeSpawnR.endR hp i) R F (wcNS (Ly).lab c (WakeWc.t2 (Ly).lab) (WakeWc.kOf (Ly).lab) cA m fr) s c →
    SpawnSrc l c → W1W hp i E Dt Ctx ls0 l b n s c [] ∧ Ret0.StackM (WakeOSide.r1W hp i) s.st.1

/-- **`HMidP` from `H1G`**: `res` comes from `reserveW_wf` and `tcb` from
`tcbWG_wf`, with the counters' separation from `wsep_W` and the source's
control from `spawnSrc_ctl`. -/
theorem hMidP_of (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨ntA (Ly).lab, 8⟩ = true)
    (hoffN : ¬ ((WakeOD.arW hp i).heap ≤ (ntA (Ly).lab).toNat ∧
        (ntA (Ly).lab).toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨ntA (Ly).lab, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc)
    (hoffP : ¬ ((WakeOD.arW hp i).heap ≤ (Ly).pnA.toNat ∧
        (Ly).pnA.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨(Ly).pnA, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc)
    (hoffH : ¬ ((WakeOD.arW hp i).heap ≤ ((Ly).pinA + 96#64).toNat ∧
        ((Ly).pinA + 96#64).toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨(Ly).pinA + 96#64, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t)
    (hG : H1G hp i E cT Dt Ctx ls0 l b n R F J0 t) : HMidP hp i E cT Dt Ctx ls0 l b n R F J0 t := by
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hE : (Ly).endPc = WakeSpawnR.endR hp i := by
    show Scc.Cert.Rt.A64.endOf _ (Ly).prog _ = _; rw [WakeSrcCtl.prog_W hp i hpa hwp]
  have hs := Spike.Lib.A64.WakePh.StartPlaceLy.wsep_W hp i hA13
  have hSctl : ∀ l' A c, SB l b l' A c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf WakeT1.wakeSrc c [] :=
    fun _ _ _ h => WakeSrcCtl.spawnSrc_ctl h.2.2
  obtain ⟨⟨hR, hal, -, hRlo, hhi, -, -⟩, -⟩ := hB
  refine ⟨hG.wcWf, ?_, ?_, hG.resA, hG.hdrA, hG.tcbA, hG.tid, hG.ti, hG.wcl⟩
  · rw [← hE]
    exact Spike.Lib.A64.WakePh.CalWf.reserveW_wf hp i E Dt Ctx ls0 l b n hpg hlo hpa hR hal (by omega) hhi hSctl
      ⟨hs.pn_a.symm, hs.lock_a.symm, hs.freeN_a.symm, hs.next_a.symm⟩ hmN hG.hunN hoffN hG.hplR
  · rw [← hE]
    intro c0 cA m fr hM g hra
    have hS : ∃ l' A', SB l b l' A' c0 := hM.1.imp fun _ => .imp fun _ h => h.1
    exact Spike.Lib.A64.WakePh.CalWf.tcbWG_wf_pt hp i E Dt Ctx ls0 l b n hpg hlo hpa hR hal (by omega) hhi hSctl
      (fun m h => hG.hunP m h.1) hoffP (fun m h => hG.hunH m h.1) hoffH c0 hS g hra
      (fun nd => WakeWc.tcbWG_mono (hG.hstT c0 hS g hra nd) fun _ h => h.1) (hG.hplT c0 cA m fr hM g hra)

/-- **`h1`** (`H1Stmt` at `inv1W`) from wake's box, at `h0`'s memory side
`ms0` and frame condition `F0`, given the loader's facts and the named
premises listed below.

Loader facts, owned by the integration/assembly layer:
- `hpa`, `hwp`: the certificate parses to the output's program and to
  wake's.
- `hlo0`: the code base.
- `hA13`: A13's data part.
- `hpin2`: the pinned region reaches `pinA + 168` (`StartPlaceLy.hpin2_W`).
- `hcz`: the counter's zeroed item (`CtrZ`).
From these, `hmN`, `hoffN`, `hoffP`, `hoffH` come from `CalWf.hmN_W`,
`hoffN_W`, `hoffP_W`, `hoffH_W`.

Named premises:
- `hokb`: the box call's premises carry from `ms0` to `ms1W`, on the
  `h0` side; this is `WakeBoxW.okb_ms1` with `WakeOD.hok_W` when
  `ms0` is `h0`'s `msOfA`.
- `hg`: `ms0`'s arena geometry (`heap`, `cells`, `off`, `units`) the
  arena's (`rfl` at `h0`'s `msOfA`), for the landing's allocator fact.
- `hG`: `H1G` at each ghost of `Box` (see its fields).
- `hobl`: the refusal path's obligations (`RefObl`). See `refObl_of`. -/
theorem wake_h1 {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop}
    (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.A64.Rt.CtrZ o)
    (hokb : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms0 (Ly).lab → q.OKB (WakeH1Inv.ms1W hp i E cT ls0 l b n []) (Ly).lab)
    (hg : ms0.heap = (WakeOD.arW hp i).heap ∧ ms0.cells = (WakeOD.arW hp i).cells ∧
      ms0.off = (WakeOD.arW hp i).off ∧ ms0.units = (WakeOD.arW hp i).units)
    (hG : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ R F J0 t, BoxPure (Ly) F0 n R F J0 t → H1G hp i E cT Dt Ctx ls0 l b n R F J0 t)
    (hobl : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      WakeRefSeg.RefObl hp i E cT Dt Ctx ls0 l b n) :
    WakeWc.H1Stmt (W1W hp i E Dt Ctx ls0) (WakeH1Inv.K1W hp i E) (WakeOD.arW hp i) (L0T (Ly).Λ)
      (WakeH1Inv.ms1W hp i E cT ls0) (Ly) (WakeSpawnR.endR hp i) (WakeWc.Box (Ly) ms0 F0)
      (WakeH1Inv.inv1W hp i E cT Dt Ctx ls0) := by
  have hprog := WakeSrcCtl.prog_W hp i hpa hwp
  have hwpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have haW := WakeOSide.aW_site hp i hpa hwp hwpL (Spike.Lib.PlaceW.site_ofPlaceW hp i) E
  have hL : Scc.Cert.Rt.A64.Lays (Ly).exe wakeProg (Ly).pfx := hprog ▸ (Ly).lays
  exact WakeBoxW.h1Stmt_box hp i E cT Dt Ctx ls0 hprog (WakeSrcCtl.hna_W hp i hpa hwp E)
    (Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13)
    (fun l b n hl hb => WakeHMid.hmid_box hp i E cT Dt Ctx ls0 l b n hprog haW (hokb l b n hl hb) hg
      fun R F J0 t hB => hMidP_of hp i E cT Dt Ctx ls0 hpa hwp hlo0 hA13
        (Spike.Lib.A64.WakePh.CalWf.hmN_W hp i hA13 true)
        (Spike.Lib.A64.WakePh.CalWf.hoffN_W hp i hA13) (Spike.Lib.A64.WakePh.CalWf.hoffP_W hp i)
        (Spike.Lib.A64.WakePh.CalWf.hoffH_W hp i hpin2 hcz) hB
        (hG l b n hl hb R F J0 t hB))
    (fun l b n hl hb => WakeRefSeg.seg_refB hp i E cT Dt Ctx ls0 hL (hobl l b n hl hb))

end Spike.Lib.WakeH1Root

/-- info: 'Spike.Lib.WakeH1Root.hMidP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeH1Root.hMidP_of

/-- info: 'Spike.Lib.WakeH1Root.wake_h1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeH1Root.wake_h1
