/-
**`RootOpen.hctr0`/`hnew0` at the root's context** (wake.w, AArch64):
`Ctx := CtxR`, `WakeCtr.CtxT` at the reference memory side `refW` (`msBot`
with no allocation fragment, so `Ctx`-free) with the start's counter adds
`GcW` (`scc_rt_alloc` called from `wc_main` at its frame, as
`WcPreW.alloc` gives it) under main's thread pointer and the box's store `StAt … GsW` (its landing
`bX` at main's thread pointer, as `hst0_ofW`'s `hxa` reads it).

- `refW`, `GcW`, `GsW`, `CtxR`: the reference side and the context.
- `at_bX_xa`: `bX` reads no `xa`.
- `hcode_R`, `hlt_R`: the allocator's code; the counter word below the
  arena (`.data` below the heap, A8).
- `hnew0_R`: `RootOpen.hnew0` at `CtxR` (at `IW`): `WakeCtr.hnew0_of`, its
  landing by `Hxa.hxa_R` (given `H1R` at `msBot E []`, `hF0`, the open
  `hUn1`) moved to `I2 inv0R` (`msOfA_xa_mono`).
- `hctr0_R`: `RootOpen.hctr0` at `CtxR`: `WakeCtr.hctr0_ofT` with
  `stAt_noWr`, given the counter add's tail `hland` (its `n4` landing under
  main's thread pointer in `inv0R`; `A64WakeLand2`).
-/
import Spike.Lib.A64WakeHxa
import Spike.Lib.A64WakeNew
import Spike.Lib.A64WakeRoot
import Spike.Lib.A64WakeCtrTp

namespace Spike.Lib.A64.WakePh.Land

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize Pz)
open Spike.Lib.A64ConsumerA (msOfA I2 WrAt CtrRow PendA ArenaW)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Ret0 (pinA CallerCells)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (bX wAR WcCtx AGB)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call N)
open Spike.Lib.A64.WakeCtr (CtxW CtxT CtrOk StAt)
open Spike.Lib (FragS Frag Region MemSide FrameRun)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)
open Spike.Lib.A64.WakeWf (DtW)

/-! ## `bX` reads no `xa` -/

/-- **The box's landing at `ms` is at `ms'`**, `ms'` being `ms` but for `xa`. -/
theorem at_bX_xa {ms ms' : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel}
    {A : Nat} {s : State} {c : Spike.Lib.Ctl} (he : ms' = { ms with xa := ms'.xa })
    (h : At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c) :
    At exe endPc R F (bX ms' (_root_.Executable.labels exe).label J0 l A) s c := by
  rw [he]
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, h1, h2, h3⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TPW" => TP (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))

/-! ## The context -/

/-- **The reference memory side at entry `E`**: `msBot` with no allocation
fragment (`WakeCtr`'s reference shape; `Ctx`-free). -/
abbrev refW (E : Entry) : MemSide isaLSE2 :=
  msOfA (Ly).Λ ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks SccCertificate.asm (Ly).Λ) (fun _ => True)
    (WakeOG.gW hp i (WakeHG.cTW hp i))
    (fun s _ => Spike.Lib.A64.WakePh.ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (WakeOD.arW hp i)
    (fun _ _ _ _ _ => False) (L0T (Ly).Λ) (ls0T (ls0 E)) []

/-- **The start's counter adds**: `scc_rt_alloc` called from `wc_main` at
its frame on the first stack (`WcPreW.alloc`'s region and frame condition),
returning to `.sp0`. -/
def GcW (_E : Entry) (ms0 : MemSide isaLSE2) (R : Region) (F : MachineData → Prop) (q : Call) : Prop :=
  ∃ v m0 σC, R = wAR (wR (swR v (-384) 0) 336) ∧
    F = (fun m => wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC m ∧ CallerCells (wR (swR v (-384) 0) 336) (-80) (-160) 0 m ∧ WcCtx ms0 (Ly).lab (wR (swR v (-384) 0) 336) ((JW) σC) q m) ∧
    q.ra = ((Ly).lab ".L21_wc_main.sp0").toBitVec

/-- **The box store's landings**: `bX` at `refW E` in `wc_main`'s frame,
with main's thread pointer, for one cell. -/
def GsW (E : Entry) (Lnd : WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2) : Prop :=
  ∃ v m0 σC, Lnd = fun l A n s c =>
    n = 1 ∧ At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (bX (refW hp i ls0 E) (Ly).lab ((JW) σC) l A) s c ∧ TPW s

/-- **The root's context**: `CtxT` at `refW` with `GcW` under main's thread
pointer and the store at `GsW`. -/
def CtxR (E : Entry) : FragS isaLSE2 :=
  CtxT (refW hp i ls0 E) (Ly).exe (Ly).endPc (GcW hp i E) (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))
    (StAt (refW hp i ls0 E) wakeSrc (L0T (Ly).Λ) (GsW hp i ls0 E))

/-! ## Layout facts -/

/-- **The allocator's code** in wake's layout. -/
theorem hcode_R (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) :
    ∀ ms0 q, Spike.Lib.A64.Alloc.Code ms0 q (Ly).exe (Ly).endPc := by
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hL : Scc.Cert.Rt.A64.Lays (Ly).exe wakeProg (Ly).pfx := hprog ▸ (Ly).lays
  have hend : (Ly).endPc = Scc.Cert.Rt.A64.endOf (Ly).exe wakeProg (Ly).pfx := by rw [← hprog]
  exact fun _ _ => Spike.Lib.A64.Flow.alloc_code_of hL hend Spike.Lib.A64.Flow.WakeWc.wake_alloc

/-- **The counter word lies below the arena**: in `.data`, below the heap (A8). -/
theorem hlt_R (hc : Spike.Lib.A64.Rt.CtrZ o) (E : Entry) :
    (WakeOD.arW hp i).ctr + 8 ≤ (refW hp i ls0 E).heap := by
  have hpl := Spike.Lib.PlaceW.link i hp
  obtain ⟨-, h2, -⟩ := Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW hpl hc
  have hh := Spike.Lib.A64.Rt.ArenaW.PlaceW.heapOk_of_placeW hpl
  simp only [Scc.Cert.PlaceOK.A64.heapOk, Bool.and_eq_true] at hh
  have hb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ (Ly).Λ.heap.lo :=
    Scc.Cert.PlaceOK.dataBelow_of_dataBelowHeap hh.2
  have h2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := h2
  show Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.heap.lo
  omega

/-! ## The counter add's tail and the open fields -/

/-- **The counter add's tail** (`WakeCtr.hctr0_ofT`'s `hland`) at `CtxR`:
from a counter add of `GcW` at `n4` under main's thread pointer (kept from
`CtxR`), `inv0R`. -/
def HLand (E : Entry) : Prop :=
  ∀ (ms0 : MemSide isaLSE2) R F q, ms0 = { refW hp i ls0 E with xa := ms0.xa } → GcW hp i E ms0 R F q →
    CtrOk ms0 (Ly).lab R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (N (Ly).lab ms0 q .n4) s c → TPW s →
      Spike.Lib.WakeRoot.inv0R hp i ls0 (CtxR hp i ls0) frM E s c []

/-- **`RootOpen.hctr0` at `CtxR`** given the tail `HLand`. -/
theorem hctr0_R (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hc : Spike.Lib.A64.Rt.CtrZ o) (E : Entry)
    (hland : HLand hp i ls0 frM E) :
    ∀ s c fs, Spike.Lib.WakeRoot.inv0R hp i ls0 (CtxR hp i ls0) frM E s c fs → CtxR hp i ls0 E s c fs →
      WrAt s (WakeOD.arW hp i).ctrLoc → ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA (Ly).Λ ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks SccCertificate.asm (Ly).Λ)
          (fun _ => True) (WakeOG.gW hp i (WakeHG.cTW hp i))
          (fun s _ => Spike.Lib.A64.WakePh.ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (WakeOD.arW hp i)
          (I2 (WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T (ls0 E)) (Spike.Lib.WakeRoot.inv0R hp i ls0 (CtxR hp i ls0) frM E)
            (Spike.Lib.WakeRoot.inv1R hp i ls0 (CtxR hp i ls0) E)) (L0T (Ly).Λ) (ls0T (ls0 E)) fs')
        (fun s' c'' => PendA wakeSrc (I2 (WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T (ls0 E))
          (Spike.Lib.WakeRoot.inv0R hp i ls0 (CtxR hp i ls0) frM E) (Spike.Lib.WakeRoot.inv1R hp i ls0 (CtxR hp i ls0) E))
          (L0T (Ly).Λ) (ls0T (ls0 E)) s' c'' fs') s c' :=
  Spike.Lib.A64.WakeCtr.hctr0_ofT (hcode_R hp i hpa hwp)
    (Spike.Lib.A64.WakeCtr.stAt_noWr (hlt_R hp i ls0 hc E)
      (WakeOD.hok_W hp i E (WakeHG.cTW hp i) DtW (ls0 E) (fun _ _ _ => False) (fun _ _ _ => False)
        (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) hc).ctr_lt) hland

section AtIW

variable (hp : PlaceW pcfg Λ0 o)

set_option hygiene false in
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "LyW" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RSW" => Spike.Lib.A64.Rt.rS0 (LyW)

set_option hygiene false in
local notation "JWW" => fun σC => wJ0 (wNC (LyW).lab (JS (LyW) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TPWW" => TP (UInt64.ofBitVec (pinA (LyW).lab + 0#64 + 8#64))

/-- **The store's landing is in `I2 inv0R inv1R`** at `IW`: `Hxa.hxa_R` at
`msBot E []` (`bX` moved from `refW`, `at_bX_xa`), its `⊥` disjunct
widened to `inv0R`. `hUn1` (OPEN) is `hxa_R`'s at `refW`. -/
theorem hland1_R (E : Entry) (hA13 : Scc.Cert.Spawn.A64.a13data (LyW).Λ o.prog o.secs = true)
    {F0 : MachineData → Prop}
    (h1 : Spike.Lib.WakeRoot.H1R hp IW ls0 (CtxR hp IW ls0)
      (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxR hp IW ls0) E []) F0 E)
    (hF0 : ∀ v m0 σC m, wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC m → F0 m)
    (hUn1 : ∀ v m0 σC l A s c, L0T (LyW).Λ l = none →
      At (LyW).exe (LyW).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC)
        (bX (refW hp IW ls0 E) (LyW).lab ((JWW) σC) l A) s c → TPWW s →
      Spike.Lib.A64.KeepUn.U (Spike.Lib.A64.Rt.PreChild.r1Of (LyW).lab) s) :
    ∀ Lnd, GsW hp IW ls0 E Lnd → ∀ l A s' c', L0T (LyW).Λ l = none → Lnd l A 1 s' c' →
      (msOfA (LyW).Λ ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks SccCertificate.asm (LyW).Λ)
          (fun _ => True) (WakeOG.gW hp IW (WakeHG.cTW hp IW))
          (fun s _ => Spike.Lib.A64.WakePh.ownG (LyW) (Spike.Lib.A64.Rt.Reserve.ntA (LyW).lab) s) (WakeOD.arW hp IW)
          (I2 (WakeOD.arW hp IW) (L0T (LyW).Λ) (ls0T (ls0 E))
            (Spike.Lib.WakeRoot.inv0R hp IW ls0 (CtxR hp IW ls0) frM E)
            (Spike.Lib.WakeRoot.inv1R hp IW ls0 (CtxR hp IW ls0) E)) (L0T (LyW).Λ) (ls0T (ls0 E)) []).xa
        l A 1 s' c' := by
  rintro Lnd ⟨v, m0, σC, rfl⟩ l A s' c' hl ⟨-, hA, htp⟩
  have hA' := at_bX_xa (ms' := Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxR hp IW ls0) E []) rfl hA
  have hU : ∀ v m0 σC l A s c, L0T (LyW).Λ l = none →
      At (LyW).exe (LyW).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC)
        (bX (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxR hp IW ls0) E []) (LyW).lab ((JWW) σC) l A) s c → TPWW s →
      Spike.Lib.A64.KeepUn.U (Spike.Lib.A64.Rt.PreChild.r1Of (LyW).lab) s :=
    fun v m0 σC l A s c hl hA htp => hUn1 v m0 σC l A s c hl (at_bX_xa rfl hA) htp
  exact A64GfpS.msOfA_xa_mono (fun _ _ _ _ _ hI => hI.elim (fun hF => hF.2.2.elim) .inr) []
    (Hxa.hxa_R hp ls0 (CtxR hp IW ls0) E hA13 h1 hF0 hU v m0 σC l A s' c' hl hA' htp)

end AtIW

end Spike.Lib.A64.WakePh.Land

/-- info: 'Spike.Lib.A64.WakePh.Land.at_bX_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.at_bX_xa

/-- info: 'Spike.Lib.A64.WakePh.Land.hcode_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.hcode_R

/-- info: 'Spike.Lib.A64.WakePh.Land.hlt_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.hlt_R

/-- info: 'Spike.Lib.A64.WakePh.Land.hctr0_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.hctr0_R

/-- info: 'Spike.Lib.A64.WakePh.Land.hland1_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.hland1_R
