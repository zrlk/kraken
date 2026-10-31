/-
**The box store's write obligation and the counter add's context at
`CtxR`** (wake, x86-64): the two premises of `WcWfS.wcSp0W_WSO` (`hwr`)
and `WcWfS.wcPreW_WSO` (`hctx`) at the root's context `CtxR`
(`X64WakeLand`) at `refW`, in `wc_main`'s frame (`hWp`/`hWs`'s region and
frame condition), at any memory side that is `refW` but for `xa`
(`tpXa (msOfA …) t` among them), both under main's thread pointer.

- `box_c0`: the allocator's ghost at a start control boxing a zero
  (`StartH0.C0Box`) boxes the `int` word `0`.
- `hwr_R`: at the box's store under main's thread pointer, `NoWrC` at
  `CtxR`: the store is `StAt` (`Alloc.newStM_nd`, its landing `GsW`'s via
  `bXR_rebase`, the thread pointer carried by the node), so in `CtxR`, and
  writes no counter (`WakeCtr.stAt_noWr`).
- `fstable_wAR`: the allocator's frame condition at `wc_main`'s call
  (`F ∧ CallerCells ∧ WcCtx`) is stable in its region.
- `hctx_R`: at the counter add of a call from `wc_main` returning to
  `.Lwc_main.x18` under main's thread pointer, `CtxR` (its `CtrAt`
  disjunct: `GcW` by construction, `CtrOk` by `fstable_wAR` at the first
  stack's top and `WordsNoneP` at the counter).

x86-64 twin of `Spike/Lib/A64WakeLand3.lean` (namespace
`Spike.Lib.X64.WakePh.Land`). **Unlike AArch64**:
- generic in `wc_main`'s entry control `c0` with `hbx : C0Box c0` (A64 at
  `c0W`, `box_c0W`); `c0_of_wcJ` is `WcPl.c0_wJ0` under `wcJ`;
- the store is `movq %rax, (%rcx)` at `.Lwc_main.x18 + 15` (A64: `str x9,
  [x10]` at `.L21_wc_main.sp0 + 12`), its landing `bXR` on `R`, moved to
  `GsW`'s `bX` on `R.fp (-8)` by `bXR_rebase`; the value's
  representation is `ValRep lbl w.val 0` (`%rax = 0`);
- the frame is `wR (RS wcLsw v) wcD` with `CallerCells … 8` (A64:
  `wR (swR v (-384) 0) 336`, `… 0`); the region facts at the top come from
  `mainEF_ok` and `WakeM.wR_ok`; `fstable_wAR` needs `R.lo ≤ -240`,
  `8 ≤ R.hi` (A64 `0 ≤ R.hi`);
- `hprog : (Ly).prog = wakeCells` replaces A64's `hpa`/`hwp`.
-/
import Spike.Lib.X64WakeLand
import Spike.Lib.X64NewSt
import Spike.Lib.X64WakeStartGlue
import Spike.Lib.X64WakeWcPl
import Spike.Lib.X64WakeWcWfR

namespace Spike.Lib.X64.WakePh.Land

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (code_field)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64 (ND NodeW FStable)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (sN bX bXR AGB wAR WcCtx oWR)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.WakeCtr (StAt)
open Spike.Lib.X64.WakePh.StartH0 (C0Box)
open Spike.Lib (MemSide PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeT1 (wakeSrc)

/-- **The box at a start control boxing a zero**: an allocator ghost at
`c0` boxes the `int` word `w` of value `0`. -/
theorem box_c0 {c0 : Ctl} (hbx : C0Box c0) {ms : MemSide isa} {lab : Label → Int64} (q : AGB ms lab)
    (hc0 : q.1.c0 = c0) : ∃ w : TermRun.Word, q.1.τ = .int ∧ q.1.ws = [w] ∧ w.val = .num 0 := by
  obtain ⟨e0, he0⟩ := hbx.term
  obtain ⟨w, hw, hw0⟩ := hbx.ev
  obtain ⟨_, ht⟩ := q.2.term; rw [hc0, he0] at ht
  obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
  have ha' := (Op.new.inj ha).1
  have hev := q.2.ev; rw [hc0, ← ha', hw] at hev
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hev)
  exact ⟨w, h1.symm, h2.symm, hw0⟩

/-- **The allocator's frame condition at `wc_main`'s call is stable** in
its region `wAR R`: `F` by `FStable.callee`, the caller's cells (held and
as at the call) outside it untouched (`Region.callee_sep`). -/
theorem fstable_wAR {R : Spike.Lib.Region} {F : MachineData → Prop} {ms : MemSide isa} {lab : Label → Int64}
    {J : Spike.Lib.X64.AS → Ctl → Prop} {q : Spike.Lib.X64.Alloc.Call}
    (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi) :
    FStable (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 8 m ∧ WcCtx ms lab R J q m) := by
  rintro m m' ⟨h1, h2, mC, σC', c', hA, hJ1, hJ2, hK⟩ hd
  have hsep : ∀ k, R.Off k → ¬ (R.callee (-80) (-160) 8).Off (k - -80) →
      Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 := fun k hk hn =>
    hd _ (Spike.Lib.Region.addr_fit hR hk) (Spike.Lib.Region.callee_sep hR (show R.lo ≤ -80 + -160 by omega)
      (by decide) (by omega) (by decide) (by decide) (by decide) hk hn)
  exact ⟨Spike.Lib.X64.FStable.callee hR (by omega) (by decide) (by omega) (by omega) hF m m' h1 hd,
    fun k hk hn => by rw [hsep k hk hn]; exact h2 k hk hn, mC, σC', c', hA, hJ1, hJ2,
    fun k hk hn => (hsep k hk hn).trans (hK k hk hn)⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (c0 : Ctl) (ls0 : Entry → Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- The first stack. -/
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- `wc_main`'s entry invariant from the caller's state. -/
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC

set_option hygiene false in
/-- Main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option maxHeartbeats 800000 in
/-- **`WcWfS.wcSp0W_WSO`'s `hwr` at `CtxR`**: at the box's store under
main's thread pointer, the store is `StAt` (so in `CtxR`) writing no
counter. -/
theorem hwr_R (hprog : (Ly).prog = SccCode.wakeCells) (hc : Spike.Lib.X64.Rt.CtrZ o) (hbx : C0Box c0)
    (E : Entry) {ms : MemSide isa} (hms : ms = { refW asm hp i ls0 E with xa := ms.xa })
    (v : BitVec 64) (m0 : MachineData) (σC : Spike.Lib.X64.AS) :
    NodeW (fun s c => TP (TV) s → Spike.Lib.X64.WakeWf.NoWrC (Spike.Lib.X64.WakeOD.arW hp i) wakeSrc
        (L0T (Ly).Λ) (ls0T (ls0 E)) (CtxR (Ly) c0 (refW asm hp i ls0 E)) [] s c)
      (fun _ _ => False) (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD)
      (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC)
      (sN ms (Ly).lab (wR (RS wcLsw v) wcD) ((JW) σC) .st) := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { refW asm hp i ls0 E with xa := X } := ⟨_, hms⟩
  intro s c hAt
  refine ⟨fun htp => ?_, fun _ h => h⟩
  -- the layout's facts
  haveI := (Ly).valid
  have hpS : Scc.Cert.Rt.X64.Lays (Ly).exe SccCode.wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = Scc.Cert.Rt.X64.endOf (Ly).exe SccCode.wakeCells (Ly).pfx := by
    show Scc.Cert.Rt.X64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  have hin := Spike.Lib.X64.Flow.WakeWc.wake_wcS0In
  simp only [Spike.Lib.X64.Flow.WakeWc.wcS0In, Bool.and_eq_true] at hin
  have hL := Spike.Lib.PlaceWX.link i hp
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hL
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW hL
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hu2 : (refW asm hp i ls0 E).units 1 .int = 2 := rfl
  have hf1 : (refW asm hp i ls0 E).off 1 .int = 8 := rfl
  -- the store's premises
  have hSt : StAt (refW asm hp i ls0 E) wakeSrc (L0T (Ly).Λ) (GsW (Ly) c0 (refW asm hp i ls0 E)) s c [] := by
    refine ⟨rfl, fun l A n s c => n = 1 ∧ Spike.Lib.X64.At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8))
      (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC) (bX (refW asm hp i ls0 E) (Ly).lab ((JW) σC) l A) s c ∧
      TP (TV) s, ⟨v, m0, σC, rfl⟩, ?_⟩
    refine Spike.Lib.X64.Alloc.newStM_nd (b := .rcx) (r := .rax) (k := 0) (z := 3) (R := wR (RS wcLsw v) wcD)
      (F := wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC)
      (n := ⟨(Ly).lab ".Lwc_main.x18" + Int64.ofNat 15, oWR, fun σ c =>
        (sN { refW asm hp i ls0 E with xa := X } (Ly).lab (wR (RS wcLsw v) wcD) ((JW) σC) .st).J σ c ∧
          σ.regs.fsBase = TV⟩)
      (fun l A => ⟨(Ly).lab ".Lwc_main.x18" + Int64.ofNat 18, oWR, fun σ c =>
        (bXR (refW asm hp i ls0 E) (Ly).lab ((JW) σC) l A).J σ c ∧ σ.regs.fsBase = TV⟩)
      (code_field hpS hendS hin.2 rfl) ?_ ?_ ?_
    · rintro l A s' c' - ⟨he, hn, hdc, hpc, σ, hA', hD, hJ, htp'⟩
      exact ⟨rfl, Spike.Lib.X64.Flow.WakeWc.bXR_rebase ⟨he, hn, hdc, hpc, σ, hA', hD, hJ⟩,
        by show s'.st.1.regs.fsBase = _; rw [hA'.regs]; exact htp'⟩
    · rintro m σ c' - hD ⟨⟨q, o', hwc, rfl, h0, hcx, hA24, hle, hlo'⟩, htp'⟩
      have hc0 : q.1.c0 = c0 := by
        obtain ⟨σe, hJe, -⟩ := hwc
        exact Spike.Lib.X64.WakePh.WcPl.c0_wJ0 hJe
      obtain ⟨w, hτ, hws, hw0⟩ := box_c0 hbx q hc0
      have hcell := Spike.Lib.X64.WakePh.StartGlue.hcellB_of_wordsNone
        (F := wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC) (P := fun q => q.c0 = c0)
        (ms := { refW asm hp i ls0 E with xa := X })
        (fun _ h => h.1.1.1.wn) (Nat.le_refl _)
        (by show (Ly).Λ.heap.lo + 16 * 4194304 ≤ _; omega)
        (by show (Ly).Λ.heap.lo + 16 * 4194304 ≤ _; omega)
        (fun q hq => by
          obtain ⟨_, hτ', -⟩ := box_c0 hbx q hq
          rw [hτ']
          show (refW asm hp i ls0 E).off 1 .int + 16 ≤ 16 * (refW asm hp i ls0 E).units 1 .int
          rw [hf1, hu2]; omega)
        (fun q _ o h1 h2 => Spike.Lib.X64.WakePh.StartH0.mp_cellW hp i
          (⟨q.1, { q.2 with toS := { q.2.toS with } }⟩ : AGB (refW asm hp i ls0 E) (Ly).lab) o h1 h2)
        q hc0 o'.toNat hlo' hle
      have ha : Spike.Lib.X64.bAddr σ.regs .rcx 0 = σ.slot (-24) := by
        rw [← hcx]; simp [Spike.Lib.X64.bAddr, Reg64s.get64]
      have ha' : Spike.Lib.X64.bAddr σ.regs .rcx 0 = BitVec.ofNat 64
          ((refW asm hp i ls0 E).heap + 16 * o'.toNat + (refW asm hp i ls0 E).off 1 q.1.τ) := by
        rw [ha, ← hA24, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      obtain ⟨hmp, hun⟩ := hcell
      refine ⟨q.2.newOk, ha' ▸ hmp, ha' ▸ hun m hD, q.1.x, q.1.a, q.1.τ, q.1.e, w, TermRun.cst (.num o'.toNat),
        o'.toNat, q.2.term, hws ▸ q.2.ev, by rw [hτ]; rfl, ?_, rfl, rfl, by rw [ha, hA24], hle, fun l _ =>
        ⟨?_, rfl, ⟨⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, hwc, by rw [ha], rfl, o'.toNat, by rw [ha, hA24],
          hle⟩, htp'⟩⟩
      · have : (σ.regs.get64 .rax).toNat = 0 := by simp [Reg64s.get64, h0]
        rw [this, hw0]; exact ⟨by decide, rfl⟩
      · show (Ly).lab ".Lwc_main.x18" + Int64.ofNat 18 = (Ly).lab ".Lwc_main.x18" + Int64.ofNat 15 + Int64.ofNat 3
        rw [Int64.add_assoc]; rfl
    · obtain ⟨he, hn, hdc, hpc, σ, hA', hD, hJ⟩ := hAt
      exact ⟨he, hn, hdc, hpc, σ, hA', hD, hJ, by rw [← hA'.regs]; exact htp⟩
  have hnw := Spike.Lib.X64.WakeCtr.stAt_noWr (hlt_R hp i hc)
    (Spike.Lib.X64.WakeOD.hok_W hp i E (Spike.Lib.X64WakeHG.cTW hp i) (fun _ => False) (ls0 E)
      (fun _ _ _ => False) (fun _ _ _ => False) (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) hc).ctr_lt
    s c [] hSt
  exact ⟨fun _ _ _ _ _ _ => .inr ⟨Or.inr hSt, hnw⟩, fun _ => Or.inr hSt⟩

set_option linter.unusedSimpArgs false in
/-- **`WcWfS.wcPreW_WSO`'s `hctx` at `CtxR`**: a counter add of a box call
from `wc_main` (on the first stack) returning to `.Lwc_main.x18`, under
main's thread pointer, is `CtxR`'s `CtrAt`. -/
theorem hctx_R (hc : Spike.Lib.X64.Rt.CtrZ o) (E : Entry)
    {ms : MemSide isa} (hms : ms = { refW asm hp i ls0 E with xa := ms.xa })
    (v : BitVec 64) (m0 : MachineData) (σC : Spike.Lib.X64.AS) :
    ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB ms (Ly).lab → q.ra = ((Ly).lab ".Lwc_main.x18").toBitVec →
      ∀ s c, Spike.Lib.X64.At (Ly).exe (Ly).endPc (wAR (wR (RS wcLsw v) wcD))
        (fun m => wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC m ∧
          CallerCells (wR (RS wcLsw v) wcD) (-80) (-160) 8 m ∧
          WcCtx ms (Ly).lab (wR (RS wcLsw v) wcD) ((JW) σC) q m)
        (Spike.Lib.X64.Alloc.N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxR (Ly) c0 (refW asm hp i ls0 E) s c [] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { refW asm hp i ls0 E with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt htp
  refine .inl ⟨⟨rfl, _, _, _, q, rfl, ⟨v, m0, σC, rfl, rfl, hra⟩, ⟨hq, ?_, fun m hm => ?_⟩, hAt⟩, htp⟩
  · by_cases hv : v = topS (Ly) 0#64
    case neg => exact fun m _ hm _ => (hv (Spike.Lib.X64.WakePh.WcWfR.v_top hm.1)).elim
    subst hv
    have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hp
    have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
    have hok : (Spike.Lib.X64.swR (topS (Ly) 0#64) (-wcLsw) 0).OK := by
      (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
      exact Spike.Lib.X64.Rt.rt_hokD _ (by decide) (by decide)
    have hFwS := Spike.Lib.X64.Rt.wordsNoneP_swFSL_fstable
      (a := Spike.Lib.X64.Flow.Ret0.limA (tpOf (tcbS (Ly)))) (v := topS (Ly) 0#64) hwf hsub hok (by decide)
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
    exact fstable_wAR hR hF (by show -wcD ≤ -240; decide) (by show (8 : Int) ≤ 8; decide)
  · have hL := Spike.Lib.PlaceWX.link i hp
    obtain ⟨hc1, hc2, -⟩ := Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW hL hc
    have hc1' : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := hc1
    have hc2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := hc2
    have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW hL
    show Mem.loadInt m.dmem (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) 8 = none
    refine hm.1.1.1.1.wn _ (.inr ?_)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold Spike.Lib.DmemPriv.WordIn Scc.Sem.Range.contains; omega

end Spike.Lib.X64.WakePh.Land

/-- info: 'Spike.Lib.X64.WakePh.Land.box_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.box_c0

/-- info: 'Spike.Lib.X64.WakePh.Land.fstable_wAR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.fstable_wAR

/-- info: 'Spike.Lib.X64.WakePh.Land.hwr_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.hwr_R

/-- info: 'Spike.Lib.X64.WakePh.Land.hctx_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land.hctx_R
