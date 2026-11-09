/-
**`RootOpen.hctr0`/`hnew0` at the root's context** (wake, x86-64):
`Ctx := CtxR`, `WakeCtr.CtxT` at a reference memory side `ref` with the
start's counter adds `GcW` (`scc_rt_alloc` called from `wc_main` at its
frame, as `WcPreW.alloc` gives it) under main's thread pointer and the box's
store `StAt … GsW` (its landing `bX` at main's thread pointer, as
`StartH0.wake_start_wc_h0`'s `hxa` reads it). At the root, `ref` is `refW`
(`msOfA` at `ownGXW` with no allocation fragment, so `Ctx`-free).

- `GcW`, `GsW`, `CtxR`: the counter adds, the store's landings, the context
  (generic in the layout `L`, `wc_main`'s entry control `c0` and `ref`).
- `refW`: the root's reference side.
- `at_bX_xa`: `bX` reads no `xa`.
- `hlt_R`: the counter word below the arena (`.data` below the heap, A8).
- `HLand`, `hctr0_R`: the counter add's tail (its `c2` landing under main's
  thread pointer in `inv0`) and `RootOpen.hctr0` at `CtxR`
  (`WakeCtr.hctr0_ofT` with `stAt_noWr`).
- `hnew0_R`: `RootOpen.hnew0` at `CtxR` (`WakeCtr.hnew0_of`), the store's
  landing `hland1` a premise.

x86-64 twin of `Spike/Lib/A64WakeLand.lean` (namespace
`Spike.Lib.X64.WakePh.Land`). **Unlike AArch64**:
- `GcW`, `GsW`, `CtxR` are generic in `L`, `c0` and `ref` (A64 at
  `ofPlaceW hp i`, `c0W`, `refW hp i ls0 E`); `refW` takes the assembly
  `asm` (A64: `SccCertificate.asm`) and is at `ownGXW` (A64: `ownG`);
- the frame is `wR (RS wcLsw v) wcD` with `FS L (rS0 L) wcLsw 0 v` and
  `CallerCells … 8` (A64: `wR (swR v (-384) 0) 336`, `… 0`), the call
  returning to `.Lwc_main.x0` (A64: `.L21_wc_main.sp0`), the landing `bX`
  on the frame `(wR …).fp (-8)`, the thread pointer `tpOf (tcbS L)`;
- no `hcode_R`: the allocator's code is the layout's (`L.lays`, `L.valid`,
  `allocIn` from `hprog : L.prog = wakeCells`), as `WakeCtr.hctr0_of`
  takes it; `hlt_R` is stated at the arena's heap (`refW`'s by `rfl`);
- the root's invariants are parameters: `HLand`, `hctr0_R` and `hnew0_R`
  are generic in `inv0`, `inv1` (A64 at `WakeRoot.inv0R`/`inv1R`), and
  `hland1_R` (A64 from `Hxa.hxa_R`) is not twinned: `hnew0_R` takes the
  landing `hland1` as a premise.
-/
import Spike.Lib.X64WakeCtr
import Spike.Lib.X64WakeStartH0
import Spike.Lib.X64WakeOD
import Spike.Lib.X64WakeHG
import Spike.Lib.Rt.X64ArenaOfPlaceW

namespace Spike.Lib.X64.WakePh.Land

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (msOfA I2 WrAt CtrRow PendA ArenaW)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (bX wAR WcCtx)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Alloc (Call N)
open Spike.Lib.X64.WakeCtr (CtxW CtxT CtrOk StAt)
open Spike.Lib (FragS Frag Region MemSide FrameRun PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeT1 (wakeSrc)

/-! ## `bX` reads no `xa` -/

/-- **The box's landing at `ms` is at `ms'`**, `ms'` being `ms` but for `xa`. -/
theorem at_bX_xa {ms ms' : MemSide isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J0 : Spike.Lib.X64.AS → Ctl → Prop} {l : WeakMem.AllocLabel}
    {A : Nat} {s : State} {c : Ctl} (he : ms' = { ms with xa := ms'.xa })
    (h : At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c) :
    At exe endPc R F (bX ms' (_root_.Executable.labels exe).label J0 l A) s c := by
  rw [he]
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, h⟩

/-! ## The context -/

section Ctx

variable (L : RuntimeLayout) (c0 : Ctl)

/-- **The start's counter adds**: `scc_rt_alloc` called from `wc_main` at
its frame on a stack based at `v` (`WcPreW.alloc`'s region and frame
condition), returning to `.Lwc_main.x0`. -/
def GcW (ms0 : MemSide isa) (R : Region) (F : MachineData → Prop) (q : Call) : Prop :=
  ∃ v m0 σC, R = wAR (wR (RS wcLsw v) wcD) ∧
    F = (fun m => wF (RS wcLsw v) wcD (FS L (Spike.Lib.X64.Rt.rS0 L) wcLsw 0#64 v) m0 σC m ∧
      CallerCells (wR (RS wcLsw v) wcD) (-80) (-160) 8 m ∧
      WcCtx ms0 L.lab (wR (RS wcLsw v) wcD) (wJ0 (wNC L.lab (JS L 0#64 c0)).J σC) q m) ∧
    q.ra = (L.lab ".Lwc_main.x0").toBitVec

/-- **The box store's landings**: `bX` at `ref` in `wc_main`'s frame, with
main's thread pointer, for one cell. -/
def GsW (ref : MemSide isa) (Lnd : WeakMem.AllocLabel → Nat → Nat → Frag isa) : Prop :=
  ∃ v m0 σC, Lnd = fun l A n s c =>
    n = 1 ∧ At L.exe L.endPc ((wR (RS wcLsw v) wcD).fp (-8))
      (wF (RS wcLsw v) wcD (FS L (Spike.Lib.X64.Rt.rS0 L) wcLsw 0#64 v) m0 σC)
      (bX ref L.lab (wJ0 (wNC L.lab (JS L 0#64 c0)).J σC) l A) s c ∧ TP (tpOf (tcbS L)) s

/-- **The root's context**: `CtxT` at `ref` with `GcW` under main's thread
pointer and the store at `GsW`. -/
def CtxR (ref : MemSide isa) : FragS isa :=
  CtxT ref L.exe L.endPc (GcW L c0) (tpOf (tcbS L)) (StAt ref wakeSrc (L0T L.Λ) (GsW L c0 ref))

end Ctx

/-! ## At the root's layout -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (c0 : Ctl) (ls0 : Entry → Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The reference memory side at entry `E`**: `msOfA` at the root's
guarantee and owned words (`ownGXW`), with no allocation fragment
(`WakeCtr`'s reference shape; `Ctx`-free). -/
abbrev refW (E : Entry) : MemSide isa :=
  msOfA (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) (fun _ => True)
    (Spike.Lib.X64WakeOG.gW hp i (Spike.Lib.X64WakeHG.cTW hp i))
    (fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
    (Spike.Lib.X64.WakeOD.arW hp i) (fun _ _ _ _ _ => False) (L0T (Ly).Λ) (ls0T (ls0 E)) []

/-- **The counter word lies below the arena**: in `.data`, below the heap (A8). -/
theorem hlt_R (hc : Spike.Lib.X64.Rt.CtrZ o) :
    (Spike.Lib.X64.WakeOD.arW hp i).ctr + 8 ≤ (Spike.Lib.X64.WakeOD.arW hp i).heap := by
  have hpl := Spike.Lib.PlaceWX.link i hp
  obtain ⟨-, h2, -⟩ := Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW hpl hc
  have hh := Spike.Lib.PlaceWX.heapOk_of_placeWX hpl
  simp only [Scc.Cert.PlaceOK.X64.heapOk, Bool.and_eq_true] at hh
  have hb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ (Ly).Λ.heap.lo :=
    Scc.Cert.PlaceOK.dataBelow_of_dataBelowHeap hh.2
  have h2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := h2
  show Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.heap.lo
  omega

/-- **The counter add's tail** (`WakeCtr.hctr0_ofT`'s `hland`) at `CtxR`:
from a counter add of `GcW` at `c2` under main's thread pointer (kept from
`CtxR`), `inv0`. -/
def HLand (inv0 : FragS isa) (E : Entry) : Prop :=
  ∀ (ms0 : MemSide isa) R F q, ms0 = { refW asm hp i ls0 E with xa := ms0.xa } → GcW (Ly) c0 ms0 R F q →
    CtrOk ms0 (Ly).lab R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (N (Ly).lab ms0 q .c2) s c → TP (tpOf (tcbS (Ly))) s → inv0 s c []

variable {asm hp i c0 ls0} {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}

/-- **`RootOpen.hctr0` at `CtxR`** given the tail `HLand`. -/
theorem hctr0_R (hprog : (Ly).prog = SccCode.wakeCells) (hc : Spike.Lib.X64.Rt.CtrZ o) (E : Entry)
    (hland : HLand asm hp i c0 ls0 inv0 E) :
    ∀ s c fs, inv0 s c fs → CtxR (Ly) c0 (refW asm hp i ls0 E) s c fs →
      WrAt s (Spike.Lib.X64.WakeOD.arW hp i).ctrLoc → ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') →
      abi.atSys s = false →
      CtrRow (msOfA (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) (fun _ => True)
          (Spike.Lib.X64WakeOG.gW hp i (Spike.Lib.X64WakeHG.cTW hp i))
          (fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
          (Spike.Lib.X64.WakeOD.arW hp i)
          (I2 (Spike.Lib.X64.WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T (ls0 E)) inv0 inv1) (L0T (Ly).Λ) (ls0T (ls0 E)) fs')
        (fun s' c'' => PendA wakeSrc (I2 (Spike.Lib.X64.WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T (ls0 E)) inv0 inv1)
          (L0T (Ly).Λ) (ls0T (ls0 E)) s' c'' fs') s c' := by
  haveI := (Ly).valid
  have hin : Spike.Lib.X64.Alloc.allocIn (Ly).prog = true := by
    rw [hprog]; exact Spike.Lib.X64.Flow.WakeWc.wake_alloc
  exact Spike.Lib.X64.WakeCtr.hctr0_ofT (Ly).lays rfl hin
    (Spike.Lib.X64.WakeCtr.stAt_noWr (hlt_R hp i hc)
      (Spike.Lib.X64.WakeOD.hok_W hp i E (Spike.Lib.X64WakeHG.cTW hp i) (fun _ => False) (ls0 E)
        (fun _ _ _ => False) (fun _ _ _ => False) (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False)
        hc).ctr_lt) hland

/-- **`RootOpen.hnew0` at `CtxR`**: `WakeCtr.hnew0_of` (the counter add
writes the counter; the store's `NewStM` at `h0`'s side), its landing in
`h0`'s fragment `hland1` a premise (A64: `Land.hland1_R`, from
`Hxa.hxa_R`). -/
theorem hnew0_R (hprog : (Ly).prog = SccCode.wakeCells) (E : Entry)
    (hland1 : ∀ Lnd, GsW (Ly) c0 (refW asm hp i ls0 E) Lnd → ∀ l A s' c', L0T (Ly).Λ l = none →
      Lnd l A 1 s' c' →
      (msOfA (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) (fun _ => True)
          (Spike.Lib.X64WakeOG.gW hp i (Spike.Lib.X64WakeHG.cTW hp i))
          (fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
          (Spike.Lib.X64.WakeOD.arW hp i)
          (I2 (Spike.Lib.X64.WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T (ls0 E)) inv0 inv1) (L0T (Ly).Λ)
          (ls0T (ls0 E)) []).xa l A 1 s' c') :
    ∀ s c fs, inv0 s c fs → CtxR (Ly) c0 (refW asm hp i ls0 E) s c fs →
      ¬ WrAt s (Spike.Lib.X64.WakeOD.arW hp i).ctrLoc → ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') →
      abi.atSys s = false →
      ∀ L, WrAt s L → ¬ ArenaW (Spike.Lib.X64.WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T (ls0 E)) c' L →
        NewStM wakeSrc (L0T (Ly).Λ)
          (msOfA (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) (fun _ => True)
            (Spike.Lib.X64WakeOG.gW hp i (Spike.Lib.X64WakeHG.cTW hp i))
            (fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
            (Spike.Lib.X64.WakeOD.arW hp i)
            (I2 (Spike.Lib.X64.WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T (ls0 E)) inv0 inv1) (L0T (Ly).Λ)
            (ls0T (ls0 E)) fs') s c' := by
  haveI := (Ly).valid
  have hin : Spike.Lib.X64.Alloc.allocIn (Ly).prog = true := by
    rw [hprog]; exact Spike.Lib.X64.Flow.WakeWc.wake_alloc
  exact fun s c fs h0 hC => Spike.Lib.X64.WakeCtr.hnew0_of (Ly).lays rfl hin hland1 s c fs h0 hC.ctxW

end Spike.Lib.X64.WakePh.Land

/-- info: 'Spike.Lib.X64.WakePh.Land.at_bX_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.at_bX_xa

/-- info: 'Spike.Lib.X64.WakePh.Land.hlt_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.hlt_R

/-- info: 'Spike.Lib.X64.WakePh.Land.hctr0_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.hctr0_R

/-- info: 'Spike.Lib.X64.WakePh.Land.hnew0_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.hnew0_R
