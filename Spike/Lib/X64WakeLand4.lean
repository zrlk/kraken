/-
**The counter add's tail at the root's context, the child's stack carried
unmapped** (wake.w, x86-64): at the start control `c0W`, a counter add of
`GcW` (a box call from `wc_main` on the first stack, returning to
`.Lwc_main.x0`) at the allocator's `c2`, under main's thread pointer, is
one segment inside `WSX` at the root's context `CtxR … c0W (refW …)` to
`wc_main`'s heap abort; and the box store's landing of `GsW`, with the
child's stack unmapped, is in the memory side's allocation fragment.

- `hland_seg`: `WakeWc.wake_wc_c2_segW` at any memory side `ms` equal to
  `refW` but for `xa`, with `hWp`/`hWs` by `WcWfR.hWp_R`/`hWs_R` moved to
  `ms` (`StartH0X.wcPreW_xa`/`wcSp0W_xa`), the first stack's top pinned by
  the frame condition (any other base: no memory satisfies `wF`), the
  region facts at the top (`mainEF_ok`, `WakeM.wR_ok`), `hmem`/`hcell` from
  `WordsNoneP` (`StartGlue.hmemB_of_wordsNone`/`hcellB_of_wordsNone`), the
  box by `Land.box_c0`. The landing `hxa` a premise.
- `hland_segU`: `hland_seg` at `StartH0X.msU` (`hxa` from `h1`'s `Box`
  clause `hB1` by `Hxa.box_landing` given `U r1Of`), moved to
  `unXa MS r1Of` (`StartH0X.SegW.mono_xa`) and back to `MS` by
  `KeepUn.SegW.keepUn` (the take of `rS0` keeps `r1Of` unmapped): `U r1Of`
  at its entry and its exit, no `hUn1`.
- `hland1_U`: `RootUL.HLand1U`'s body at `MS` (`hnew0_R`'s `hland1` with
  `U r1Of` at the landing): `Land.at_bX_xa`, `Hxa.box_landing`, `hB1`.

x86-64 twin of `Spike/Lib/A64WakeLand4.lean` (namespace
`Spike.Lib.X64.WakePh.Land`) and of `A64WakeLandU.hland_RU`'s segment part.

**Where x86-64 differs from AArch64**:
- the allocator's node past the counter's add is `c2` (A64 `n4`), the call
  returns to `.Lwc_main.x0` (A64 `.L21_wc_main.sp0`), the frame is
  `wR (RS wcLsw v) wcD` with `CallerCells … 8` (A64 `wR (swR v (-384) 0)
  336`, `… 0`), and the landing `bX` is on `(wR …).fp (-8)`;
- the level is `WSX` at `ownGXW` (A64 `WS`), and `hWp`/`hWs` are not
  premises: `WcWfR.hWp_R`/`hWs_R` at `refW` give them at any `ms` that is
  `refW` but for `xa` (A64 `hland_seg` takes them at `tpXa ms`);
- the memory side is generic in `I2`'s `inv0`/`inv1` and the landing's
  frame `F0`, `h1`'s `Box` clause taken as `hB1` (A64 at `msBot E []` with
  `WakeRoot.H1R`);
- `hland_segU` stops at the segment (`U r1Of` at both ends): x86-64's lift
  to `inv0G` (`Land5.inv0_of_habW`, A64 `Land5.inv0_of_habW`) is applied
  where `HLandU` is assembled, not here;
- `hland1_U` is new here (A64 `Land.hland1_R` from `Hxa.hxa_R` with the
  open `hUn1`); its `U r1Of` is `HLand1U`'s;
- `c0W`'s placement (`hpl0`) stays a premise (A64
  `WakeImmsC0.placedSE_c0WW`; no x86-64 producer).
-/
import Spike.Lib.X64WakeStartH0X
import Spike.Lib.X64WakeWcN4

namespace Spike.Lib.X64.WakePh.Land

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry Range)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (msOfA I2)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (AGB bX wX wAR WcCtx)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib (Arena FragS MemSide SegW PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64.WakeC0 (c0W)

/-- The arena's units of a type with accesses are positive, its offset one
header word (as `StartH0`'s private `units_off`). -/
private theorem units_off {Λ : Scc.Sem.Layout} {τ : Ty}
    (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us) :
    1 ≤ (Spike.Lib.X64.Rt.arOf Λ).units 1 τ ∧ (Spike.Lib.X64.Rt.arOf Λ).off 1 τ = 8 := by
  obtain ⟨us, hus⟩ := hacc
  refine ⟨?_, ?_⟩
  · simp only [Spike.Lib.X64.Rt.arOf, Arena.ofWords, hus]
    split <;> omega
  · simp only [Spike.Lib.X64.Rt.arOf, Arena.ofWords, hus, Nat.mul_zero]

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Scc.Sem.X64.Asm) (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ls0 : Entry → Lsize)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "KW" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "μE" => (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
local notation "GW" => Spike.Lib.X64WakeOG.gW hpw i (Spike.Lib.X64WakeHG.cTW hpw i)

set_option hygiene false in
local notation "OWN" => fun s (_ : List TermRun.Frame) => Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab) s

set_option hygiene false in
/-- The memory side: `refW`'s, with `I2`'s fragment. -/
local notation "MS" => msOfA (Ly).Λ (μE) (fun _ => True) (GW) (OWN) (AR)
  (I2 (AR) (L0T (Ly).Λ) (ls0T (ls0 E)) inv0 inv1) (L0T (Ly).Λ) (ls0T (ls0 E)) []

set_option hygiene false in
local notation "MU" => Spike.Lib.X64.WakePh.StartH0X.msU asm hpw i ls0 inv0 inv1 E

set_option hygiene false in
/-- The root's reference side. -/
local notation "REF" => refW asm hpw i ls0 E

set_option hygiene false in
/-- The start's level at `ownGXW` at the root's context at `c0W`. -/
local notation "WSR" => Spike.Lib.X64.WakePh.WSX (Ly) (ntA (Ly).lab) (AR) wakeSrc Dt (Spike.Lib.X64.WakeOD.ClW hpw i)
  (CtxR (Ly) c0W (REF)) (L0T (Ly).Λ) (ls0T (ls0 E)) frM (Spike.Lib.X64.WakeWf.X0W (Ly) ax)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
/-- **The counter add's tail at any memory side `ms` that is `refW` but for
`xa`** (`hms`): from the allocator's `c2` for a box call `q` of `wc_main`
returning to `.Lwc_main.x0` (`hq`, `hra`) under main's thread pointer,
`wake_wc_c2_segW` to the heap abort. `hWp`/`hWs` by `WcWfR.hWp_R`/`hWs_R`
moved to `ms`; the region, arena and memory facts computed; the landing
`hxa` a premise. -/
theorem hland_seg {E : Entry} {Dt : State → Prop} {frM : TermRun.Frame} {ax : Int64}
    (hpo : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    /- `c0W`'s placement (no x86-64 producer) -/
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W [])
    {ms : MemSide isa} (hms : ms = { REF with xa := ms.xa })
    (hxa : ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8)) (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC)
        (bX ms (Ly).lab ((JW) σC) l A) s c → TP (TV) s → ms.xa l A 1 s c) :
    ∀ v m0 σC (q : Call), q.OKB ms (Ly).lab → q.ra = ((Ly).lab ".Lwc_main.x0").toBitVec →
    SegW (WSR) (KW) wakeSrc (L0T (Ly).Λ) ms
      (fun s c => At (Ly).exe (Ly).endPc (wAR (wR (RS wcLsw v) wcD))
        (fun m => wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC m ∧
          CallerCells (wR (RS wcLsw v) wcD) (-80) (-160) 8 m ∧
          WcCtx ms (Ly).lab (wR (RS wcLsw v) wcD) ((JW) σC) q m)
        (Spike.Lib.X64.Alloc.N (Ly).lab ms q .c2) s c ∧ TP (TV) s)
      (fun s c => At (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD) (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC)
        (wX ms (Ly).lab (wR (RS wcLsw v) wcD) ((JW) σC) .abort) s c ∧ TP (TV) s) := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { REF with xa := X } := ⟨_, hms⟩
  intro v m0 σC q hq hra
  by_cases hv : v = TOP
  case neg =>
    exact ⟨fun _ _ => False, fun _ _ ⟨⟨_, _, _, _, _, _, hD, _⟩, _⟩ =>
      hv (Spike.Lib.X64.WakePh.WcWfR.v_top hD.1), fun _ _ h => h.elim, fun _ _ h => h.elim⟩
  subst hv
  -- the layout's facts
  haveI := (Ly).valid
  have hprog : (Ly).prog = wakeCells := hpo
  have hpS : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = Scc.Cert.Rt.X64.endOf (Ly).exe wakeCells (Ly).pfx := by
    show Scc.Cert.Rt.X64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  -- the region and its frame condition at the first stack's top (as `Land.hctx_R`)
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hpw
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hok : (Spike.Lib.X64.swR (TOP) (-wcLsw) 0).OK := by
    (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_hokD _ (by decide) (by decide)
  have hFwS := Spike.Lib.X64.Rt.wordsNoneP_swFSL_fstable
    (a := Spike.Lib.X64.Flow.Ret0.limA (tpOf (tcbS (Ly)))) (v := TOP) hwf hsub hok (by decide)
    (by decide)
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
        exact Spike.Lib.X64.Rt.rS0_subRD _ (by decide) (by decide))
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _)
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
        exact Spike.Lib.X64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
  have hR2 := Spike.Lib.X64.Rt.mainEF_ok (tcb := tcbS (Ly)) (by decide) (by decide) hok hFwS
  obtain ⟨hR, hF⟩ := Spike.Lib.X64.Flow.WakeM.wR_ok (D := wcD) (by decide) (by decide) hR2.1 hR2.2
    (by show (8 : Int) - wcLsw ≤ -48 - wcD; decide) (by show (0 : Int) ≤ 8; decide) m0 σC
  -- the arena
  have hL := Spike.Lib.PlaceWX.link i hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hL
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW hL
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW hL
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW hL hc
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hct : ({ REF with xa := X } : MemSide isa).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hu2 : (REF).units 1 .int = 2 := rfl
  have hf1 : (REF).off 1 .int = 8 := rfl
  have hoff : ∀ q : Call, q.OKB { REF with xa := X } (Ly).lab →
      ({ REF with xa := X } : MemSide isa).off q.n q.τ ≤ 16 * ({ REF with xa := X } : MemSide isa).units q.n q.τ :=
    fun q hq => by
      obtain ⟨hu, hf⟩ := units_off (Λ := (Ly).Λ) hq.toS.accs
      have hu' : 1 ≤ ({ REF with xa := X } : MemSide isa).units 1 q.τ := hu
      have hf' : ({ REF with xa := X } : MemSide isa).off 1 q.τ = 8 := hf
      rw [hq.one, hf']; omega
  -- the counter and the headers, the box's cell
  have hmem := Spike.Lib.X64.WakePh.StartGlue.hmemB_of_wordsNone
    (F := wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC) (ms := { REF with xa := X })
    (lab := (Ly).lab) (show (Ly).Λ.WF from hwf) (fun _ h => h.1.1.1.wn) (Nat.le_refl _)
    (by show (Ly).Λ.heap.lo + 16 * 4194304 ≤ _; omega)
    (.inr (by rw [hct]; unfold Spike.Lib.DmemPriv.WordIn Scc.Sem.Range.contains; omega)) hoff
  have hcell := Spike.Lib.X64.WakePh.StartGlue.hcellB_of_wordsNone
    (F := wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC) (P := fun q => q.c0 = c0W)
    (ms := { REF with xa := X }) (lab := (Ly).lab)
    (fun _ h => h.1.1.1.wn) (Nat.le_refl _)
    (by show (Ly).Λ.heap.lo + 16 * 4194304 ≤ _; omega)
    (by show (Ly).Λ.heap.lo + 16 * 4194304 ≤ _; omega)
    (fun q hq => by
      obtain ⟨_, hτ', -⟩ := box_c0 Spike.Lib.X64.WakeC0.c0W_box q hq
      rw [hτ']
      show (REF).off 1 .int + 16 ≤ 16 * (REF).units 1 .int
      rw [hf1, hu2]; omega)
    (fun q _ o h1 h2 => Spike.Lib.X64.WakePh.StartH0.mp_cellW hpw i
      (⟨q.1, { q.2 with toS := { q.2.toS with } }⟩ : AGB (REF) (Ly).lab) o h1 h2)
  -- `hWp`/`hWs` at `refW`, moved to `ms`
  have hWp := Spike.Lib.X64.WakePh.StartH0X.wcPreW_xa (X := (tpXa { REF with xa := X } (TV)).xa)
    (Spike.Lib.X64.WakePh.WcWfR.hWp_R asm hpw i c0W ls0 hpo hlo hc hA13 (Dt := Dt)
      (Cl := Spike.Lib.X64.WakeOD.ClW hpw i) (frM := frM) (fun _ h => h.2) hax Spike.Lib.X64.WakeC0.c0W_ctl hpl0
      E (TOP) m0 σC)
  have hWs := Spike.Lib.X64.WakePh.StartH0X.wcSp0W_xa (X := (tpXa { REF with xa := X } (TV)).xa)
    (Spike.Lib.X64.WakePh.WcWfR.hWs_R asm hpw i c0W ls0 hpo hlo hc hA13 Spike.Lib.X64.WakeC0.c0W_box
      (Dt := Dt) (Cl := Spike.Lib.X64.WakeOD.ClW hpw i) (frM := frM) (fun _ h => h.2) hax
      Spike.Lib.X64.WakeC0.c0W_ctl hpl0 E (TOP) m0 σC)
  exact Spike.Lib.X64.Flow.WakeWc.wake_wc_c2_segW (p := wakeSrc) (lbl := L0T (Ly).Λ) (ms := { REF with xa := X })
    rfl hpS hendS hF hR (by show -wcD ≤ -240; decide) (by show (8 : Int) ≤ 8; decide) hWp hWs hq hra (hmem q hq)
    (fun q ⟨_, h⟩ => by
      obtain ⟨w, hτ, hws, hw0⟩ := box_c0 Spike.Lib.X64.WakeC0.c0W_box q (Spike.Lib.X64.WakePh.WcPl.c0_wJ0 h)
      exact ⟨w, hws, by rw [hτ]; rfl, by rw [hw0]; exact ⟨by decide, rfl⟩⟩)
    (fun q ⟨_, h⟩ o h1 h2 => hcell q (Spike.Lib.X64.WakePh.WcPl.c0_wJ0 h) o h1 h2)
    (hxa _ m0 σC)

set_option maxHeartbeats 1600000 in
/-- **The counter add's tail at `MS`, the child's stack carried unmapped**:
`hland_seg` at `msU` (its `hxa` the `Box` landing given `U r1Of`, `hB1`),
moved to `unXa MS r1Of` (`SegW.mono_xa`) and back by `KeepUn.SegW.keepUn`
(the take of `rS0`, disjoint from `r1Of`, keeps it unmapped). -/
theorem hland_segU {E : Entry} {Dt : State → Prop} {frM : TermRun.Frame} {ax : Int64}
    {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {F0 : MachineData → Prop}
    (hpo : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    /- `c0W`'s placement (no x86-64 producer) -/
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W [])
    /- `h1`'s `Box ⊆ inv1` clause and `wc_main`'s frame inside `F0` -/
    (hB1 : ∀ l b n, L0T (Ly).Λ l = none → Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n →
      ∀ s c, Spike.Lib.X64.Flow.WakeWc.Box (Ly) (MS) F0 l b n s c → inv1 l b n s c [])
    (hF0 : ∀ v m0 σC m, wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC m → F0 m) :
    ∀ v m0 σC (q : Call), q.OKB (MS) (Ly).lab → q.ra = ((Ly).lab ".Lwc_main.x0").toBitVec →
    SegW (WSR) (KW) wakeSrc (L0T (Ly).Λ) (MS)
      (fun s c => (At (Ly).exe (Ly).endPc (wAR (wR (RS wcLsw v) wcD))
        (fun m => wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC m ∧
          CallerCells (wR (RS wcLsw v) wcD) (-80) (-160) 8 m ∧
          WcCtx (MS) (Ly).lab (wR (RS wcLsw v) wcD) ((JW) σC) q m)
        (Spike.Lib.X64.Alloc.N (Ly).lab (MS) q .c2) s c ∧ TP (TV) s) ∧ U R1 s)
      (fun s c => (∃ v m0 σC,
        At (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD) (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC)
          (wX (MS) (Ly).lab (wR (RS wcLsw v) wcD) ((JW) σC) .abort) s c ∧ TP (TV) s) ∧ U R1 s) := by
  intro v m0 σC q hq hra
  -- the ranges: `r1Of` in the pool, disjoint from `rS0`, both in the address space
  have hsub1 := Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hpw i hA13
  obtain ⟨-, -, -, -, hd0, hwS0, hw1⟩ := Spike.Lib.X64WakeOSide.ranges_W hpw i hsub1
  have hr0 : Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab = RS0 := Spike.Lib.X64.WakePh.RootP.r0Of_rS0
  have hd : (R1).Disjoint (RS0) := by
    have := hd0; simp only [Spike.Lib.X64WakeOSide.r1W, Spike.Lib.X64WakeOSide.r0W, hr0] at this; exact this
  have hwS : (RS0).lo + (RS0).size ≤ 2 ^ 64 := by
    have := hwS0; simp only [Spike.Lib.X64WakeOSide.r0W, hr0] at this; exact this
  -- `hxa` at `msU`: the landing is a `Box` given `U r1Of`
  have hxa : ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8)) (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC)
        (bX (MU) (Ly).lab ((JW) σC) l A) s c → TP (TV) s → (MU).xa l A 1 s c := by
    intro v m0 σC l A s c hl hA htp
    have hA' : At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8))
        (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC) (bX (MS) (Ly).lab ((JW) σC) l A) s c :=
      at_bX_xa rfl hA
    obtain ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩ := hA
    obtain ⟨hu, hf⟩ := units_off (Λ := (Ly).Λ) q.2.toS.accs
    have hu' : 1 ≤ (MU).units 1 q.1.τ := hu
    have hf' : (MU).off 1 q.1.τ = 8 := hf
    have hcl : (MU).cells = 4194304 := rfl
    have hAL : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells A 1 := by
      show (MU).heap + 8 ≤ A ∧ A + 8 * 1 ≤ (MU).heap + 16 * (MU).cells ∧ 1 + 1 ≤ (MU).cells
      rw [hf'] at hAo; omega
    exact ⟨hAL, fun hU => .inr ⟨l, A, 1, hl, hAL, rfl, rfl, hB1 l A 1 hl hAL s c
      (Spike.Lib.X64.WakePh.Hxa.box_landing hpw i hA13 hF0 hA' htp hU)⟩⟩
  -- the segment at `msU`, then at `unXa MS r1Of`, then `keepUn`
  have hS := hland_seg asm hpw i ls0 (E := E) (Dt := Dt) (frM := frM) (ax := ax) hpo hlo hc hA13 hax hpl0
    (ms := MU) rfl hxa v m0 σC q { hq with toS := { hq.toS with } } hra
  have hS1 := Spike.Lib.X64.WakePh.StartH0X.SegW.mono_xa (ms' := unXa (MS) (R1)) hS rfl
    fun _ _ _ _ _ h hU => ⟨h.1, h.2 hU⟩
  have hS2 := Spike.Lib.X64.KeepUn.SegW.keepUn rfl hS1 fun _ _ _ s' hk hs => by
    obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.X64.KeepUn.take_un pm hd hw1 hwS hs
  refine (hS2.mono_pre fun s c h => h).mono_post fun s c hQ => ?_
  obtain ⟨⟨⟨he, hn, hdc, hpc, σ, hAb, hD, h0, h30, q', hq', hJ⟩, htp⟩, hu⟩ := hQ
  exact ⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hD, h0, h30, ⟨q'.1, { q'.2 with toS := { q'.2.toS with } }⟩, hq', hJ⟩,
    htp⟩, hu⟩

/-- **The box store's landing with the child's stack unmapped is in `MS`'s
allocation fragment** (`RootUL.HLand1U`'s body; `Land.hnew0_R`'s `hland1`
given `U r1Of`): `GsW`'s landing at `refW` is one at `MS`
(`Land.at_bX_xa`), a `Box` (`Hxa.box_landing`), in `inv1` by `hB1`. -/
theorem hland1_U {E : Entry} {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {F0 : MachineData → Prop}
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    /- `h1`'s `Box ⊆ inv1` clause and `wc_main`'s frame inside `F0` -/
    (hB1 : ∀ l b n, L0T (Ly).Λ l = none → Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n →
      ∀ s c, Spike.Lib.X64.Flow.WakeWc.Box (Ly) (MS) F0 l b n s c → inv1 l b n s c [])
    (hF0 : ∀ v m0 σC m, wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC m → F0 m) :
    ∀ Lnd, GsW (Ly) c0W (REF) Lnd → ∀ l A s' c', L0T (Ly).Λ l = none → Lnd l A 1 s' c' → U R1 s' →
      (MS).xa l A 1 s' c' := by
  rintro Lnd ⟨v, m0, σC, rfl⟩ l A s c hl ⟨-, hA, htp⟩ hU
  have hA' : At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8))
      (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC) (bX (MS) (Ly).lab ((JW) σC) l A) s c :=
    at_bX_xa rfl hA
  have hB := Spike.Lib.X64.WakePh.Hxa.box_landing hpw i hA13 hF0 hA' htp hU
  obtain ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩ := hA'
  obtain ⟨hu, hf⟩ := units_off (Λ := (Ly).Λ) q.2.toS.accs
  have hu' : 1 ≤ (MS).units 1 q.1.τ := hu
  have hf' : (MS).off 1 q.1.τ = 8 := hf
  have hcl : (MS).cells = 4194304 := rfl
  have hAL : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells A 1 := by
    show (MS).heap + 8 ≤ A ∧ A + 8 * 1 ≤ (MS).heap + 16 * (MS).cells ∧ 1 + 1 ≤ (MS).cells
    rw [hf'] at hAo; omega
  exact ⟨hAL, .inr ⟨l, A, 1, hl, hAL, rfl, rfl, hB1 l A 1 hl hAL s c hB⟩⟩

end Spike.Lib.X64.WakePh.Land

/-- info: 'Spike.Lib.X64.WakePh.Land.hland_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.hland_seg

/-- info: 'Spike.Lib.X64.WakePh.Land.hland_segU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.hland_segU

/-- info: 'Spike.Lib.X64.WakePh.Land.hland1_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.hland1_U
