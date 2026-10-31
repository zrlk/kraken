/-
**`h1` assembled with the callee's take** (x86-64, the twin of
`Spike/Lib/A64WakeH1A.lean`): `WakeH1Root.wake_h1` with `H1G` built from
the open premises by `WakeH1GOf.h1G_of`, its `wcl` by `WakeWcl.wcl_W1`.

- `H1GA`: the open premises at one ghost of `Box`, under `BoxPure`.
- `h1G_ofA`: `H1G` from `H1GA` (`h1G_of`, `wcl_W1` at the band of
  `band_of_box`).
- `hMidPA_of`: `HMidPA` from `H1GA` (`WakeH1Root.hMidP_of` at `h1G_ofA`).
- `wake_h1A`: `H1Stmt` at `inv1W`, as `wake_h1`.

**Unlike AArch64**: x86-64's `WakeH1Root` is already at `hmid_boxA`
(`HMidPA`), so `hMidPA_of` and `wake_h1A` go through `hMidP_of` and
`wake_h1` (A64 repeats their proofs); the callee's type is
`WakeH1GOf.TiG` (A64's `TiA`) and `wcl`'s `WakeH1GOf.WclG` (A64's `WclA`);
the assembly is a parameter `asm`; the regions are x86-64's. No absolute
address appears in this file.
-/
import Spike.Lib.X64WakeWcl

namespace Spike.Lib.X64.WakeH1A

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (rAR t2)
open Spike.Lib.X64.WakePh.Tcb2Call (tcb2Q)
open Spike.Lib.X64.Flow.Ret0 (StOk)
open Spike.Lib.X64.Rt (TcbOkGA hdrA)
open Spike.Lib.X64.Rt.Reserve (ResOkA ntA)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64.WakeOPremW (W1W)
open Spike.Lib.X64.WakeHMid (BoxPure)
open Spike.Lib.X64.WakeH1Root (H1G)
open Spike.Lib.X64.WakeH1GOf (TiG)
open Spike.Lib.HeapLand (AllocLand)
open SccCode (wakeCells)

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

/-- **`h1`'s open premises at one ghost of `Box`** with the callee's take:
`H1G`'s open fields (`wcl` is `WakeWcl.wcl_W1`, in `h1G_ofA`). -/
structure H1GA (l : WeakMem.AllocLabel) (b n : Nat) (R : Region) (F : MachineData → Prop) (t : UInt64) : Prop where
  /-- `scc_rt_nthreads` unmapped under `F` (`H1G.hunN`). -/
  hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none
  /-- `scc_rt_pinned_next` unmapped under `F` (`H1G.hunP`). -/
  hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none
  /-- `scc_rt_pinned + 96` unmapped under `F` (`H1G.hunH`). -/
  hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none
  /-- `H1G.resA`. -/
  resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA ms1 F (Ly).exe eR (rAR R) F ⟨g.1, 0#64, g.2⟩
  /-- `H1G.hdrA`. -/
  hdrA : ∀ c0 g, StOk ms1 F (hdrA (Ly).lab (tcb2Q g c0)) ((tcb2Q g c0).h ||| 1#64 <<< 36)
  /-- `H1G.tcbA`. -/
  tcbA : ∀ c0 g, TcbOkGA ms1 F (Ly).exe eR (R.callee (-72) (-184) 8) F (tcb2Q g c0)
  /-- `H1G.tid`. -/
  tid : (ms1).rt (t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨t2 (Ly).lab + 56#64, 8⟩ true ∧
    (ms1).G ⟨t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none
  /-- The callee (`HMidPA.ti`). -/
  ti : TiG asm hp i E cT Dt Ctx ls0 l b n R F t

/-- **`H1G` from `H1GA`**: `h1G_of` with `wcl` from `wcl_W1` at `wc_main`'s
band (`band_of_box`), given the loader's facts, `BoxPure` and `l`'s
freshness. -/
theorem h1G_ofA (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.X64.Rt.CtrZ o)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t) (hl : L0T (Ly).Λ l = none)
    (hG : H1GA asm hp i E cT Dt Ctx ls0 l b n R F t) : H1G asm hp i E cT Dt Ctx ls0 l b n R F J0 t :=
  WakeH1GOf.h1G_of asm hp i E cT Dt Ctx ls0 hpa hwp hlo0 hA13 hpin2 hcz hB hl hG.hunN hG.hunP hG.hunH hG.resA
    hG.hdrA hG.tcbA hG.tid hG.ti
    (WakeWcl.wcl_W1 asm hp i E Dt Ctx ls0 hpa hwp hlo0 hA13 hl
      (Spike.Lib.X64.WakePh.OwnMid.bandOnP_mono (WakeH1GOf.band_of_box hB) (by decide) (Int.le_refl _)))

/-- **`HMidPA` from `H1GA`**, given the loader's facts, `BoxPure` and `l`'s
freshness (`hMidP_of` at `h1G_ofA`). -/
theorem hMidPA_of (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.X64.Rt.CtrZ o)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t) (hl : L0T (Ly).Λ l = none)
    (hG : H1GA asm hp i E cT Dt Ctx ls0 l b n R F t) :
    WakeHatA.HMidPA asm hp i E cT Dt Ctx ls0 l b n R F J0 t :=
  WakeH1Root.hMidP_of asm hp i E cT Dt Ctx ls0 hpa hwp hlo0
    (Spike.Lib.X64.WakePh.CalWf.hoffN_W hp i hA13) (Spike.Lib.X64.WakePh.CalWf.hoffP_W hp i)
    (Spike.Lib.X64.WakePh.CalWf.hoffH_W hp i hpin2 hcz) hB
    (h1G_ofA asm hp i E cT Dt Ctx ls0 hpa hwp hlo0 hA13 hpin2 hcz hB hl hG)

/-- **`h1`** (`H1Stmt` at `inv1W`) from wake's box with the callee's take:
`wake_h1`'s premises, `hG` at `H1GA` (`h1G_ofA`). -/
theorem wake_h1A {ms0 : MemSide isa} {F0 : MachineData → Prop}
    (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.X64.Rt.CtrZ o)
    (hokb : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB ms0 (Ly).lab → q.OKB (WakeH1Inv.ms1W asm hp i E cT ls0 l b n []) (Ly).lab)
    (hg : ms0.heap = (WakeOD.arW hp i).heap ∧ ms0.cells = (WakeOD.arW hp i).cells ∧
      ms0.off = (WakeOD.arW hp i).off ∧ ms0.units = (WakeOD.arW hp i).units)
    (hG : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ R F J0 t, BoxPure (Ly) F0 n R F J0 t → H1GA asm hp i E cT Dt Ctx ls0 l b n R F t)
    (hobl : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      WakeRefSeg.RefObl asm hp i E cT Dt Ctx ls0 l b n) :
    WakeWc.H1Stmt (W1W asm hp i E Dt Ctx ls0) (WakeH1Inv.K1W hp i E) (WakeOD.arW hp i) (L0T (Ly).Λ)
      (WakeH1Inv.ms1W asm hp i E cT ls0) (Ly) eR (WakeWc.Box (Ly) ms0 F0)
      (WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0) :=
  WakeH1Root.wake_h1 asm hp i E cT Dt Ctx ls0 hpa hwp hlo0 hA13 hpin2 hcz hokb hg
    (fun l b n hl hb R F J0 t hB =>
      h1G_ofA asm hp i E cT Dt Ctx ls0 hpa hwp hlo0 hA13 hpin2 hcz hB hl (hG l b n hl hb R F J0 t hB))
    hobl

end Spike.Lib.X64.WakeH1A

/-- info: 'Spike.Lib.X64.WakeH1A.h1G_ofA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1A.h1G_ofA

/-- info: 'Spike.Lib.X64.WakeH1A.hMidPA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1A.hMidPA_of

/-- info: 'Spike.Lib.X64.WakeH1A.wake_h1A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1A.wake_h1A
