/-
**The counter add's tail `HLand` at the root** (wake.w, AArch64): at
`i := IW`, a counter add of `GcW` (a box call from `wc_main` on the first
stack, returning to `.sp0`) at the allocator's `n4`, under main's thread
pointer, is in `inv0R` at the frames `[]`.

- `hland_seg`: the segment at any `ms` equal to `msBot E []` but for `xa`.
- `hland_R`: `WakeWc.wake_wc_n4_segW` at `msBot E []` (`hWp`/`hWs`/`hxa` as
  `StartH0R.hst0_ofW` takes them), the first stack's top pinned by the
  frame condition (any other base: no memory satisfies `wF`), its memory
  premises as `Land.hwr_R`/`hctx_R` compute them (`hmemB_of_wordsNone`,
  `hcellB_of_wordsNone`, `wordsNoneP_swFSL_fstable`), to `QabW`; then
  `Land5.inv0_of_habW`. The `n4` state at `ms0` (`refW` but for `xa`) is
  one at `msBot E []` (no node reads `xa`).
-/
import Spike.Lib.A64WakeWcN4
import Spike.Lib.A64WakeLand5
import Spike.Lib.A64WakeJ0

namespace Spike.Lib.A64.WakePh.Land

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakeWf (DtW X0W)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W bX AGB wAR WcCtx)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)
open Spike.Lib (MemSide SegW)
open Spike.Lib.A64Consumer (Lsize)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)

set_option hygiene false in
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "MS" => Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxR hp IW ls0) E []

set_option hygiene false in
local notation "WSE" => WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hp IW) wakeSrc DtW
  (Spike.Lib.WakeOD.ClW hp IW) (CtxR hp IW ls0 E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E)
  (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

/-- **`HLand`'s segment at any memory side `ms` that is `msBot E []` but
for `xa`** (`hms`; e.g. `msBot` itself, `StartH0U.msU`): from the allocator's
`n4` for a box call `q` of `wc_main` returning to `.sp0` (`hq`, `hra`) under
main's thread pointer, `wake_wc_n4_segW` to `QabW`. `hWp`/`hWs`/`hxa` at
`tpXa ms`; the region, arena and memory facts computed. -/
theorem hland_seg (E : Entry) {ms : MemSide isaLSE2} (hms : ms = { MS with xa := ms.xa })
    (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (TV) (WSE))
        (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (tpXa ms (TV)) ((JW) σC) ((JW) σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (TV) (WSE))
        (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (tpXa ms (TV)) ((JW) σC))
    (hxa : ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
        (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (bX ms (Ly).lab ((JW) σC) l A) s c →
      TP (TV) s → ms.xa l A 1 s c) :
    ∀ v m0 σC (q : Spike.Lib.A64.Alloc.Call), q.OKB ms (Ly).lab → q.ra = ((Ly).lab ".L21_wc_main.sp0").toBitVec →
    SegW WSE (Spike.Lib.A64.PhRec.K (Ly) RS) wakeSrc (L0T (Ly).Λ) ms
      (fun s c => Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (wAR (wR (swR v (-384) 0) 336))
        (fun m => wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC m ∧
          CallerCells (wR (swR v (-384) 0) 336) (-80) (-160) 0 m ∧
          WcCtx ms (Ly).lab (wR (swR v (-384) 0) 336) ((JW) σC) q m)
        (Spike.Lib.A64.Alloc.N (Ly).lab ms q .n4) s c ∧ TP (TV) s)
      (Spike.Lib.A64.WakePh.StartH0B.QabW hp IW ls0 (CtxR hp IW ls0) E) := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { MS with xa := X } := ⟨_, hms⟩
  intro v m0 σC q hqX hra
  have hqM : q.OKB MS (Ly).lab := { hqX with toS := { hqX.toS with } }
  by_cases hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64
  case neg =>
    exact ⟨fun _ _ => False, fun _ _ ⟨⟨_, _, _, _, _, _, hD, _⟩, _⟩ => hv hD.1.1.2.1.1, fun _ _ h => h.elim,
      fun _ _ h => h.elim⟩
  subst hv
  -- the layout's facts
  have e : SccCode.wakeProg = wakeProg := by decide +kernel
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp IW hpa hwp
  have hL : Scc.Cert.Rt.A64.Lays (Ly).exe SccCode.wakeProg (Ly).pfx := e ▸ hprog ▸ (Ly).lays
  have hend : (Ly).endPc = Scc.Cert.Rt.A64.endOf (Ly).exe SccCode.wakeProg (Ly).pfx := by rw [e, ← hprog]
  -- the region and the frame condition at the first stack's top
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW IW hp
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hok' : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
  have hF0 := Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable
    (a := Spike.Lib.A64.Flow.Ret0.limA (TV))
    (v := Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) hwf hsub hok' (by decide) (by decide)
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by decide) (by decide))
    (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
        exact Spike.Lib.A64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
  obtain ⟨hR, hal, hF⟩ := Spike.Lib.A64.Flow.WakeM.wR_ok (D := 336) (by decide) (by decide) hok'
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _) hF0
    (by show (-384 : Int) ≤ -48 - 336; decide) (by show (0 : Int) ≤ 0; decide) m0 σC
  -- the memory side's arena
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link IW hp)
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.heap_below_of_placeW (Spike.Lib.PlaceW.link IW hp)
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link IW hp)
  obtain ⟨hc1, hc2, -⟩ := Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceW.link IW hp) hc
  have hc1' : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := hc1
  have hc2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := hc2
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : (MS).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MS).cells = 4194304 := rfl
  have hct : (MS).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hu2 : (MS).units 1 .int = 2 := rfl
  have hf1 : (MS).off 1 .int = 8 :=
    Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) (n := 1) (τ := .int) ⟨_, rfl⟩
  have hoff : ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB MS (Ly).lab → (MS).off q.n q.τ ≤ 16 * (MS).units q.n q.τ :=
    fun q hq => by
      have hu : 1 ≤ (MS).units 1 q.τ := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) hq.toS.accs
      have hf : (MS).off 1 q.τ = 8 := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) hq.toS.accs
      rw [hq.one, hf]; omega
  have hH : (Ly).Λ.heap.lo ≤ (MS).heap := Nat.le_of_eq hh.symm
  have hHi : (MS).heap + 16 * (MS).cells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size := by rw [hh, hcl]; omega
  have hroom : (MS).heap + 16 * (MS).cells ≤ 2 ^ 64 := by rw [hh, hcl]; omega
  have hctr : Spike.Lib.DmemPriv.WordIn (Ly).Λ.heap (MS).ctr ∨ Spike.Lib.DmemPriv.WordIn (Ly).Λ.data (MS).ctr :=
    .inr (by unfold Spike.Lib.DmemPriv.WordIn Scc.Sem.Range.contains; rw [hct]; omega)
  have hmem := Spike.Lib.A64.WakePh.StartGlue.hmemB_of_wordsNone (ms := MS) (lab := (Ly).lab)
    (F := wF (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0) 336
      (FS (Ly) RS 384 0#64 (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64)) m0 σC)
    hwf (fun _ h => h.1.1.wn) hH hHi hctr hoff q hqM
  have hc0 : ∀ q : AGB MS (Ly).lab, (∃ σ, (JW) σC σ q.1.c0) → q.1.c0 = c0W := fun q h =>
    let ⟨σ, h'⟩ := Spike.Lib.A64.Flow.WakeWc.hj_J0 h
    Spike.Lib.A64.WakePh.MainWf.ctl_mainE0 (P := fun c => c = c0W) rfl σ _ h'
  have hcell := Spike.Lib.A64.WakePh.StartGlue.hcellB_of_wordsNone
    (F := wF (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0) 336
      (FS (Ly) RS 384 0#64 (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64)) m0 σC)
    (P := fun q => q.c0 = c0W) (ms := MS)
    (fun _ h => h.1.1.wn) hH hHi hroom
    (fun q hq => by obtain ⟨_, hτ', -⟩ := box_c0W q hq; rw [hτ', hf1, hu2]; omega)
    (fun q _ o h1 h2 => Spike.Lib.A64.WakePh.StartH0.mp_cellW hp IW q o h1 h2)
  refine (Spike.Lib.A64.Flow.WakeWc.wake_wc_n4_segW (p := wakeSrc) (lbl := L0T (Ly).Λ) (ms := { MS with xa := X }) rfl hL hend
    hF hR hal (by show (-336 : Int) ≤ -240; decide) (by show (0 : Int) ≤ 0; decide)
    (hWp _ m0 σC) (hWs _ m0 σC) hqX hra hmem ?_ (fun q h o h1 h2 => hcell ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩
      (hc0 ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩ h) o h1 h2)
    (hxa _ m0 σC)).mono_post
    fun _ _ ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hx0, hx30, q, hJf, σe, hJ⟩, ht⟩ =>
      ⟨_, m0, σC, ⟨he, hn, hdc, hpc, σ, hA, hD, hx0, hx30, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, hJf, σe, hJ⟩,
        ht⟩
  intro q h
  obtain ⟨w, hτ, hws, hw0⟩ := box_c0W ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩
    (hc0 ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩ h)
  exact ⟨w, hws, by rw [hτ]; rfl, by rw [hw0]; exact ⟨by decide, rfl⟩⟩


/-- **`HLand` at `IW`**: `hland_seg` at `msBot E []`, then
`Land5.inv0_of_habW`. Premises: the loader's facts, and `wc_main`'s
`hWp`/`hWs`/`hxa` at `CtxR` as `StartH0R.hst0_ofW` takes them. -/
theorem hland_R (E : Entry) (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (TV) (WSE))
        (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (tpXa MS (TV)) ((JW) σC) ((JW) σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (TV) (WSE))
        (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (tpXa MS (TV)) ((JW) σC))
    (hxa : ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
        (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (bX MS (Ly).lab ((JW) σC) l A) s c →
      TP (TV) s → (MS).xa l A 1 s c) :
    HLand hp IW ls0 frM E := by
  intro ms0 R F q hms hG hok s c hAt htp
  obtain ⟨X, rfl⟩ : ∃ X, ms0 = { refW hp IW ls0 E with xa := X } := ⟨_, hms⟩
  obtain ⟨v, m0, σC, rfl, rfl, hra⟩ := hG
  exact Spike.Lib.A64.WakePh.Land5.inv0_of_habW hp ls0 (CtxR hp IW ls0) frM E hpa hwp hlo0
    (hland_seg hp ls0 frM E rfl hpa hwp hlo0 hc hWp hWs hxa v m0 σC q
      { hok.okb with toS := { hok.okb.toS with } } hra) s c ⟨hAt, htp⟩

end Spike.Lib.A64.WakePh.Land

/-- info: 'Spike.Lib.A64.WakePh.Land.hland_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.hland_seg

/-- info: 'Spike.Lib.A64.WakePh.Land.hland_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.hland_R
