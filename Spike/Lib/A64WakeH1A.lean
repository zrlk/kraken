/-
**`h1` assembled with the callee's take** (AArch64): `WakeH1Root.wake_h1`'s
statement with `hmid` from `WakeHatA.hmid_boxA` in place of
`WakeHMid.hmid_box`: the callee at `WakeTi2Hat.hti_W`'s conclusion, `wcl`
only `W1W` (the child's stack comes from `hatA`'s late frame condition).

- `TiA`, `WclA`: `HMidPA.ti`'s and `HMidPA.wcl`'s types.
- `H1GA`: the open premises at one ghost of `Box`, under `BoxPure`.
- `hMidPA_of`: `HMidPA` from `H1GA`: `wcl` by `WakeWcl.wcl_W1`, `wcWf` by `WakeWcW1I.wcMainW_wf`
  (as `WakeH1GOf.h1G_of`), `res`/`tcb` by `CalWf.reserveW_wf`/`tcbWG_wf_pt`
  (as `WakeH1Root.hMidP_of`), their placement by `PlacedCal`, `hstT` by
  `WakeH1GOf.hstT_of`.
- `wake_h1A`: `H1Stmt` at `inv1W` (`WakeBoxW.h1Stmt_box`), as `wake_h1`.

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeH1Root
import Spike.Lib.A64WakeH1GOf
import Spike.Lib.A64WakeHatA
import Spike.Lib.A64WakeWcl

namespace Spike.Lib.WakeH1A

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (rAR t2 kOf tiQ)
open Spike.Lib.A64.WakePh.WcSp4 (wcNS wcNI)
open Spike.Lib.A64.WakePh.Tcb2Call (oW tcb2Q)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX StackM)
open Spike.Lib.A64.Rt (TcbOkGA hdrA)
open Spike.Lib.A64.Rt.Reserve (ResOkA ntA)
open Spike.Lib.A64.KeepTP (NoMsrAt tpXa)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeLoadT (L0T tcb0)
open Spike.Lib.WakeOPremW (W1W)
open Spike.Lib.WakeBoxW (SpawnSrc W1X)
open Spike.Lib.WakeHMid (BoxPure SB)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64ConsumerA (TakeCK)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W hp i E cT ls0 l b n []

set_option hygiene false in
/-- The callee's outside move: the take of the second stack or a `clone` refusal. -/
local notation "KA" => TakeCK (WakeOSide.aW hp i E) (WakeOSide.r1W hp i) (WakeOD.ClW hp i)

/-- `HMidPA.ti`'s type (`WakeTi2Hat.hti_W`'s conclusion). -/
abbrev TiA (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) (t : UInt64) : Prop :=
  ∀ (c0 : Ctl), (∃ l' A', SB l b l' A' c0) → ∀ (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region)
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

/-- `HMidPA.wcl`'s type. -/
abbrev WclA (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) : Prop :=
  ∀ s c cA m fr, At (Ly).exe (WakeSpawnR.endR hp i) R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c →
    cA.toNat = b → m.toNat = tcb0 (Ly).Λ → SpawnSrc l c → W1W hp i E Dt Ctx ls0 l b n s c []

/-- **`h1`'s open premises at one ghost of `Box`** with the callee's take:
`H1G`'s open fields, `ti` at `HMidPA`'s type (`wcl` is `WakeWcl.wcl_W1`, in `hMidPA_of`). -/
structure H1GA (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) (t : UInt64) : Prop where
  /-- `scc_rt_nthreads` unmapped under `F` (`H1G.hunN`). -/
  hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none
  /-- `scc_rt_pinned_next` unmapped under `F` (`H1G.hunP`). -/
  hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none
  /-- `scc_rt_pinned + 96` unmapped under `F` (`H1G.hunH`). -/
  hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none
  /-- `H1G.resA`. -/
  resA : ∀ g : Reserve.G × Ctl, ResOkA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (rAR R) F ⟨g.1, 0#64, g.2⟩
  /-- `H1G.hdrA`. -/
  hdrA : ∀ c0 g, Ret0.StOk ms1 F (Ly).exe (WakeSpawnR.endR hp i) (hdrA (Ly).lab (tcb2Q g c0))
    ((tcb2Q g c0).h ||| 1#64 <<< 36)
  /-- `H1G.tcbA`. -/
  tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (R.callee (-80) (-192) 0) F (tcb2Q g c0)
  /-- `H1G.tid`. -/
  tid : (ms1).rt (t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨t2 (Ly).lab + 56#64, 8⟩ true ∧
    (ms1).G ⟨t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none
  /-- The callee (`HMidPA.ti`, see `WakeTi2Hat.hti_W`). -/
  ti : TiA hp i E cT Dt Ctx ls0 l b n R F t

/-- **`HMidPA` from `H1GA`**, given the loader's facts, `BoxPure` and `l`'s freshness. -/
theorem hMidPA_of (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.A64.Rt.CtrZ o)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t) (hl : L0T (Ly).Λ l = none)
    (hG : H1GA hp i E cT Dt Ctx ls0 l b n R F t) : WakeHatA.HMidPA hp i E cT Dt Ctx ls0 l b n R F J0 t := by
  have hbd := WakeWcW1I.bands_of_box hB
  have hW := WakeWcW1I.wcMainW_wf hp i E cT Dt Ctx ls0 hpa hwp hlo0 hA13 hpin2 hcz (b := b) hB hl hG.hunN hbd.1
    (Spike.Lib.A64.WakePh.LdFacts.hhdr_W hp i hA13) (Spike.Lib.A64.WakePh.LdFacts.hmP_W hp i)
    (Spike.Lib.A64.WakePh.LdFacts.hmH_W hp i hA13) hG.hunP hG.hunH hbd.2
    ⟨Spike.Lib.A64.WakePh.LdFacts.htid1_W hp i hA13, hG.tid.2.2.2, Spike.Lib.A64.WakePh.LdFacts.htid3_W hp i hA13⟩
  have hst := WakeH1GOf.hstT_of hp i hpa hwp hlo0 hA13 (l := l) (b := b) hB hG.hunP hG.hunH
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hE : (Ly).endPc = WakeSpawnR.endR hp i := by
    show Scc.Cert.Rt.A64.endOf _ (Ly).prog _ = _; rw [WakeSrcCtl.prog_W hp i hpa hwp]
  have hs := Spike.Lib.A64.WakePh.StartPlaceLy.wsep_W hp i hA13
  have hSctl : ∀ l' A c, SB l b l' A c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf WakeT1.wakeSrc c [] :=
    fun _ _ _ h => WakeSrcCtl.spawnSrc_ctl h.2.2
  have hne := Spike.Lib.A64.WakePh.PlacedLy.ne_of_fresh hl
  obtain ⟨⟨hR, hal, -, hRlo, hhi, -, -⟩, -, -, ⟨-, hJ0, -⟩, -⟩ := hB
  refine ⟨hW, ?_, ?_, hG.resA, hG.hdrA, hG.tcbA, hG.tid, hG.ti,
    WakeWcl.wcl_W1 hp i E Dt Ctx ls0 (WakeWcW1I.ld_of hp i hpa hwp hlo0) hl⟩
  · rw [← hE]
    exact Spike.Lib.A64.WakePh.CalWf.reserveW_wf hp i E Dt Ctx ls0 l b n hpg hlo hpa hR hal (by omega) hhi hSctl
      ⟨hs.pn_a.symm, hs.lock_a.symm, hs.freeN_a.symm, hs.next_a.symm⟩
      (Spike.Lib.A64.WakePh.CalWf.hmN_W hp i hA13 true) hG.hunN (Spike.Lib.A64.WakePh.CalWf.hoffN_W hp i hA13)
      fun _ _ nd => Spike.Lib.A64.WakePh.PlacedCal.reserveW_placed hR (by omega) hhi hne hJ0 nd
  · rw [← hE]
    intro c0 cA m fr hM g hra
    have hS : ∃ l' A', SB l b l' A' c0 := hM.1.imp fun _ => .imp fun _ h => h.1
    exact Spike.Lib.A64.WakePh.CalWf.tcbWG_wf_pt hp i E Dt Ctx ls0 l b n hpg hlo hpa hR hal (by omega) hhi hSctl
      (fun m h => hG.hunP m h.1) (Spike.Lib.A64.WakePh.CalWf.hoffP_W hp i) (fun m h => hG.hunH m h.1)
      (Spike.Lib.A64.WakePh.CalWf.hoffH_W hp i hpin2 hcz) c0 hS g hra
      (fun nd => WakeWc.tcbWG_mono (hst c0 hS g hra nd) fun _ h => h.1)
      (fun nd => Spike.Lib.A64.WakePh.PlacedCal.tcbWG_placed hR (by omega) hhi hne hJ0 hM nd)

/-- **`h1`** (`H1Stmt` at `inv1W`) from wake's box with the callee's take:
`wake_h1`'s premises, `hG` at `H1GA`. -/
theorem wake_h1A {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop}
    (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.A64.Rt.CtrZ o)
    (hokb : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms0 (Ly).lab → q.OKB (WakeH1Inv.ms1W hp i E cT ls0 l b n []) (Ly).lab)
    (hg : ms0.heap = (WakeOD.arW hp i).heap ∧ ms0.cells = (WakeOD.arW hp i).cells ∧
      ms0.off = (WakeOD.arW hp i).off ∧ ms0.units = (WakeOD.arW hp i).units)
    (hG : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ R F J0 t, BoxPure (Ly) F0 n R F J0 t → H1GA hp i E cT Dt Ctx ls0 l b n R F t)
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
    (fun l b n hl hb => WakeHatA.hmid_boxA hp i E cT Dt Ctx ls0 l b n hprog haW (hokb l b n hl hb) hg hA13
      fun R F J0 t hB => hMidPA_of hp i E cT Dt Ctx ls0 hpa hwp hlo0 hA13 hpin2 hcz hB hl
        (hG l b n hl hb R F J0 t hB))
    (fun l b n hl hb => WakeRefSeg.seg_refB hp i E cT Dt Ctx ls0 hL (hobl l b n hl hb))

end Spike.Lib.WakeH1A

/-- info: 'Spike.Lib.WakeH1A.hMidPA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeH1A.hMidPA_of

/-- info: 'Spike.Lib.WakeH1A.wake_h1A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeH1A.wake_h1A
