/-
**`h1` assembled** (x86-64, the twin of `Spike/Lib/A64WakeH1Root.lean`):
`X64WakeWcInv.H1Stmt` at `inv1W` from wake's box (`WakeBoxW.h1Stmt_box`),
its `hmid` from `WakeHatA.hmid_boxA`, `hmid`'s reserve and second-TCB
premises from `CalWf.reserveW_wf`/`CalWf.tcbWG_wf`, and its `hseg` from
`WakeRefSeg.seg_refB`.

The layout premises are discharged here from the loader's facts:
- `hprog`: `WakeSrcCtl.prog_W`.
- `hna`: `WakeSrcCtl.hna_W`.
- `hsub1`: `StartPlaceLy.hsub1_W`.
- `haW`: `X64WakeOSide.aW_site`.
- `hoffN`, `hoffP`, `hoffH`: `CalWf.hoffN_W`, `hoffP_W`, `hoffH_W`.
- `hSctl`: `WakeWcW1I.boxT_runWf` at `QB`'s term.

The pieces that have not landed are named premises, each with exactly the
type its consumer takes:
- `H1G`: the premises at one ghost of `Box` (`R`, `F`, `J0`, `t`), under
  `BoxPure`.
- `wake_h1`: the remaining global premises (`hokb`, `hg`, `hobl`), and the
  loader facts `hpa`, `hwp`, `hlo0`, `hA13`, `hpin2`, `hcz`.

**Unlike AArch64**: `hmid` is `hmid_boxA` (the callee under the take, so
`H1G` carries `HMidPA`'s fields, not `HMidP`'s); there is no `SB` (the
source's facts are `QB`'s, whose term is the box's, so `hSctl` is
`boxT_runWf`, not `spawnSrc_ctl`); x86-64's `reserveW_wf` takes the
reserve's `SFactsSt2` at `ownGXW` as a premise, so `H1G` has a field `hstR`
(A64 builds it inside `reserveW_wf`) and `reserveW_wf` takes neither the
counters' separation (`wsep_W`) nor `hmN`; `hstT` is quantified at
`tcbWG_wf`'s source facts and frame ghosts (`MidG`, `FrG`, `FrMG`) in the
frame condition with `TcbCtx … wcNCR`, so `tcbWG_wf` is used, not
`tcbWG_wf_pt`; the assembly is a parameter `asm` (`cellsOf asm`); the
regions are x86-64's (`R.callee (-72) (-184) 8`, caller cells at
`-72 … -40` and `-72 … -184` above `8`); the ghost of the reserve is
`Ret0.AllocTcb.G × Ctl` and the return labels are `.Lwc_main.x19`/`.x20`.
-/
import Spike.Lib.X64WakeHatA
import Spike.Lib.X64WakeWfCalW1
import Spike.Lib.X64WakeWfCalOff
import Spike.Lib.X64WakeWcW1I
import Spike.Lib.X64WakeRefSeg
import Spike.Lib.X64WakeSrcCtl
import Spike.Lib.X64WakeStartPlaceLy

namespace Spike.Lib.X64.WakeH1Root

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (WcMainW t2 kOf rAR MidG FrG FrMG)
open Spike.Lib.X64.WakePh.WcSp4 (wcNI)
open Spike.Lib.X64.WakePh.WcClone (wcNS)
open Spike.Lib.X64.WakePh.Tcb2Call (oC tcb2Q)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StOk CallerCells StackM)
open Spike.Lib.X64.Rt (TcbOkGA hdrA TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResOkA ReserveW ntA)
open Spike.Lib.X64.KeepTP (NoSetFsAt tpXa)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.X64.WakeOPremW (W1W)
open Spike.Lib.X64.WakeBoxW (SpawnSrc W1X)
open Spike.Lib.X64.WakeHMid (BoxPure QB)
open Spike.Lib.X64.WakeHatA (HMidPA)
open Spike.Lib.X64ConsumerA (TakeCK SFactsSt2)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.HeapLand (AllocLand)
open SccCode (wakeCells)
open Scc.Cert.Rt.X64 (Lays endOf)

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

set_option hygiene false in
/-- The nodes' `SFactsSt2` at `ownGXW`. -/
local notation "SG" => fun (s : State) (_ : Ctl) =>
  SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab)) s

set_option hygiene false in
/-- The nodes' placement at `upd L0T l b`. -/
local notation "PG" => fun (s : State) (c : Ctl) =>
  PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) s c []

/-- **`h1`'s premises at one ghost of `Box`**, for the label `l` of `n`
bytes at `b`, at the region `R`, frame condition `F`, entry node `J0` and
thread pointer `t`. These are `HMidPA`'s fields, except that `res` and
`tcb` are replaced by the premises `reserveW_wf`/`tcbWG_wf` take. -/
structure H1G (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop)
    (t : UInt64) : Prop where
  /-- `wc_main`'s nodes inside `W1W` (`HMidPA.wcWf`). -/
  wcWf : WcMainW (fun s c => W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) (Ly).exe eR R F F
    (tpXa ms1 t) J0 (QB l b)
  /-- `scc_rt_nthreads` is unmapped under `F` (`reserveW_wf`'s `hunN`). -/
  hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none
  /-- The reserve's per-node `SFactsSt2` at `ownGXW` (`reserveW_wf`'s `hst`). -/
  hstR : ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = ((Ly).lab ".Lwc_main.x19").toBitVec →
    ∀ nd, ReserveW SG (fun _ _ => False) (Ly).exe (Ly).endPc (rAR R)
      (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ WakeWc.ResCtx (Ly).lab R
        (WakeWc.rN (tpXa ms1 t) (Ly).lab R J0 (QB l b) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- The reserve's frames are placed (`reserveW_wf`'s `hpl`). -/
  hplR : ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = ((Ly).lab ".Lwc_main.x19").toBitVec →
    ∀ nd, ReserveW PG (fun _ _ => False) (Ly).exe (Ly).endPc (rAR R)
      (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ WakeWc.ResCtx (Ly).lab R
        (WakeWc.rN (tpXa ms1 t) (Ly).lab R J0 (QB l b) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- `scc_rt_pinned_next` is unmapped under `F` (`tcbWG_wf`'s `hunP`). -/
  hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none
  /-- `scc_rt_pinned + 96` is unmapped under `F` (`tcbWG_wf`'s `hunH`). -/
  hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none
  /-- The second TCB's per-node `SFactsSt2` at `ownGXW` (`tcbWG_wf`'s `hst`). -/
  hstT : ∀ c0 cA m fr, MidG (QB l b) c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    ∀ g : Ret0.AllocTcb.G, g.ra = ((Ly).lab ".Lwc_main.x20").toBitVec →
    ∀ nd, TcbWG SG (fun _ _ => False) (Ly).exe (Ly).endPc (R.callee (-72) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧
        WakeWc.TcbCtx (Ly).lab R (WakeWc.wcNCR (Ly).lab c0 cA m fr).J c0 g mm) (tcb2Q g c0) nd
  /-- The second TCB's frames are placed (`tcbWG_wf`'s `hpl`). -/
  hplT : ∀ c0 cA m fr, MidG (QB l b) c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    ∀ g : Ret0.AllocTcb.G, g.ra = ((Ly).lab ".Lwc_main.x20").toBitVec →
    ∀ nd, TcbWG PG (fun _ _ => False) (Ly).exe (Ly).endPc (R.callee (-72) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧
        WakeWc.TcbCtx (Ly).lab R (WakeWc.wcNCR (Ly).lab c0 cA m fr).J c0 g mm) (tcb2Q g c0) nd
  /-- `wake_wc_mid_hatK`'s `hres` (`HMidPA.resA`). -/
  resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA ms1 F (Ly).exe eR (rAR R) F ⟨g.1, 0#64, g.2⟩
  /-- `wake_wc_mid_hatK`'s `hhdr` (`HMidPA.hdrA`). -/
  hdrA : ∀ c0 g, StOk ms1 F (hdrA (Ly).lab (tcb2Q g c0)) ((tcb2Q g c0).h ||| 1#64 <<< 36)
  /-- `wake_wc_mid_hatK`'s `htcb` (`HMidPA.tcbA`). -/
  tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe eR (R.callee (-72) (-184) 8) F (tcb2Q g c0)
  /-- `wake_wc_mid_hatK`'s `htid` (`HMidPA.tid`). -/
  tid : (ms1).rt (t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨t2 (Ly).lab + 56#64, 8⟩ true ∧
    (ms1).G ⟨t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none
  /-- The callee inside `W1X ∧ NoSetFsAt` under the take (`HMidPA.ti`). -/
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
  /-- `W1W` at the clone's `syscall` (`HMidPA.wcl`). -/
  wcl : ∀ s c cA m fr,
    At (Ly).exe eR R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c →
    cA.toNat = b → m.toNat = tcb0 (Ly).Λ →
    SpawnSrc l c → W1W asm hp i E Dt Ctx ls0 l b n s c []

/-- **`HMidPA` from `H1G`**: `res` comes from `reserveW_wf` and `tcb` from
`tcbWG_wf`, with the source's control from `boxT_runWf` at `QB`'s term. -/
theorem hMidP_of (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
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
    (hG : H1G asm hp i E cT Dt Ctx ls0 l b n R F J0 t) : HMidPA asm hp i E cT Dt Ctx ls0 l b n R F J0 t := by
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hE : (Ly).endPc = eR := by
    show endOf _ (Ly).prog _ = _; rw [WakeSrcCtl.prog_W hp i hpa hwp]
  have hSctl : ∀ l' A c, QB l b l' A c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf X64WakeT1.wakeSrc c [] :=
    fun _ _ _ h => WakeWcW1I.boxT_runWf (.inl h.2.2.1)
  obtain ⟨⟨hR, -, -, hRlo, hhi⟩, -⟩ := hB
  refine ⟨hG.wcWf, ?_, ?_, hG.resA, hG.hdrA, hG.tcbA, hG.tid, hG.ti, hG.wcl⟩
  · rw [← hE]
    exact Spike.Lib.X64.WakePh.CalWf.reserveW_wf hp i asm E Dt Ctx ls0 l b n hpg hlo hpa hR (by omega) (by omega)
      hSctl hG.hunN hoffN hG.hstR hG.hplR
  · rw [← hE]
    exact Spike.Lib.X64.WakePh.CalWf.tcbWG_wf hp i asm E Dt Ctx ls0 l b n hpg hlo hpa hR (by omega) (by omega)
      hSctl hG.hunP hoffP hG.hunH hoffH hG.hstT hG.hplT

/-- **`h1`** (`H1Stmt` at `inv1W`) from wake's box, at `h0`'s memory side
`ms0` and frame condition `F0`, given the loader's facts and the named
premises listed below.

Loader facts, owned by the integration/assembly layer:
- `hpa`, `hwp`: the assembly's cells are the output's program and wake's.
- `hlo0`: the code base.
- `hA13`: A13's data part.
- `hpin2`: the pinned region reaches `pinA + 168` (`StartPlaceLy.hpin2_W`).
- `hcz`: the counter's zeroed item (`CtrZ`).
From these, `hoffN`, `hoffP`, `hoffH` come from `CalWf.hoffN_W`,
`hoffP_W`, `hoffH_W`.

Named premises:
- `hokb`: the box call's premises carry from `ms0` to `ms1W`.
- `hg`: `ms0`'s arena geometry (`heap`, `cells`, `off`, `units`) the
  arena's, for the landing's allocator fact.
- `hG`: `H1G` at each ghost of `Box` (see its fields).
- `hobl`: the refusal path's obligations (`RefObl`). -/
theorem wake_h1 {ms0 : MemSide isa} {F0 : MachineData → Prop}
    (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.X64.Rt.CtrZ o)
    (hokb : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB ms0 (Ly).lab → q.OKB (WakeH1Inv.ms1W asm hp i E cT ls0 l b n []) (Ly).lab)
    (hg : ms0.heap = (WakeOD.arW hp i).heap ∧ ms0.cells = (WakeOD.arW hp i).cells ∧
      ms0.off = (WakeOD.arW hp i).off ∧ ms0.units = (WakeOD.arW hp i).units)
    (hG : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ R F J0 t, BoxPure (Ly) F0 n R F J0 t → H1G asm hp i E cT Dt Ctx ls0 l b n R F J0 t)
    (hobl : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      WakeRefSeg.RefObl asm hp i E cT Dt Ctx ls0 l b n) :
    WakeWc.H1Stmt (W1W asm hp i E Dt Ctx ls0) (WakeH1Inv.K1W hp i E) (WakeOD.arW hp i) (L0T (Ly).Λ)
      (WakeH1Inv.ms1W asm hp i E cT ls0) (Ly) eR (WakeWc.Box (Ly) ms0 F0)
      (WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0) := by
  have hprog := WakeSrcCtl.prog_W hp i hpa hwp
  have hL : Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  exact WakeBoxW.h1Stmt_box asm hp i E cT Dt Ctx ls0 hprog (WakeSrcCtl.hna_W hp i hpa hwp E)
    (Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hp i hA13)
    (fun l b n hl hb => WakeHatA.hmid_boxA asm hp i E cT Dt Ctx ls0 l b n hprog
      (X64WakeOSide.aW_site hp i hpa E) (hokb l b n hl hb) hg hA13
      fun R F J0 t hB => hMidP_of asm hp i E cT Dt Ctx ls0 hpa hwp hlo0
        (Spike.Lib.X64.WakePh.CalWf.hoffN_W hp i hA13) (Spike.Lib.X64.WakePh.CalWf.hoffP_W hp i)
        (Spike.Lib.X64.WakePh.CalWf.hoffH_W hp i hpin2 hcz) hB (hG l b n hl hb R F J0 t hB))
    (fun l b n hl hb => WakeRefSeg.seg_refB asm hp i E cT Dt Ctx ls0 hL (hobl l b n hl hb))

end Spike.Lib.X64.WakeH1Root

/-- info: 'Spike.Lib.X64.WakeH1Root.hMidP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Root.hMidP_of

/-- info: 'Spike.Lib.X64.WakeH1Root.wake_h1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Root.wake_h1
