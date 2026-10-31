/-
**The box store's write obligation and the counter add's context at
`CtxR`** (wake.w, AArch64): the two premises of `WcWfS.wcSp0W_WS`
(`hwr`) and `WcWfS.wcPreW_WS` (`hctx`) at the root's context `CtxR`
(`A64WakeLand`), at `IW`, in `wc_main`'s frame on the first stack (`hWp`/
`hWs`'s region and frame condition), at any memory side that is `refW` but
for `xa` (`tpXa (msBot E []) t` among them).

- `hwr_R`: at the box's store under main's thread pointer, `NoWrC` at
  `CtxR`: the store is `StAt` (`Alloc.newStM_nd`, its landing `GsW`'s, the
  thread pointer carried by the node), so in `CtxR`, and writes no counter
  (`WakeCtr.stAt_noWr`).
- `fstable_wAR`: the allocator's frame condition at `wc_main`'s call
  (`F ∧ CallerCells ∧ WcCtx`) is stable in its region.
- `hctx_R`: at the counter add of a call from `wc_main` returning to
  `.sp0` under main's thread pointer, `CtxR` (its `CtrAt` disjunct: `GcW` by construction, `CtrOk` by
  `fstable_wAR` at the first stack's top and `WordsNone` at the counter).
-/
import Spike.Lib.A64WakeLand2
import Spike.Lib.A64NewSt
import Spike.Lib.A64WakeStartGlue
import Spike.Lib.A64WakeC0
import Spike.Lib.A64WakeMainWf

namespace Spike.Lib.A64.WakePh.Land

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow (swR ND NodeW)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (sN bX AGB wAR WcCtx)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.WakeCtr (StAt)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)
open Spike.Lib (MemSide)
open Spike.Lib.A64Consumer (Lsize)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (ls0 : Entry → Lsize)

set_option hygiene false in
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "LyW" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RSW" => Spike.Lib.A64.Rt.rS0 (LyW)

set_option hygiene false in
local notation "JWW" => fun σC => wJ0 (wNC (LyW).lab (JS (LyW) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TV" => UInt64.ofBitVec (pinA (LyW).lab + 0#64 + 8#64)

/-- **The box at `c0W`**: an allocator ghost at `c0W` boxes `int` word `w`. -/
theorem box_c0W {ms : MemSide isaLSE2} {lab : Label → Int64} (q : AGB ms lab) (hc0 : q.1.c0 = c0W) :
    ∃ w : TermRun.Word, q.1.τ = .int ∧ q.1.ws = [w] ∧ w.val = .num 0 := by
  obtain ⟨e0, he0⟩ := Spike.Lib.WakeC0.c0W_box.term
  obtain ⟨w, hw, hw0⟩ := Spike.Lib.WakeC0.c0W_box.ev
  obtain ⟨_, ht⟩ := q.2.term; rw [hc0, he0] at ht
  obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
  have ha' := (Op.new.inj ha).1
  have hev := q.2.ev; rw [hc0, ← ha', hw] at hev
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hev)
  exact ⟨w, h1.symm, h2.symm, hw0⟩

/-- **The control at `wc_main`'s entry is `c0W`** (`wJ0 (wNC (JS …))`, through `wcJ`). -/
private theorem c0_of_wcJ {L : RuntimeLayout} {σC σ : Spike.Lib.A64.Flow.AS} {c : Spike.Lib.Ctl}
    (h : Spike.Lib.A64.Flow.WakeWc.wcJ (wJ0 (wNC L.lab (JS L 0#64 c0W)).J σC) σ c) : c = c0W := by
  obtain ⟨σe0, hJe0, -⟩ := h
  obtain ⟨-, ⟨σe, hJe, -⟩, -⟩ := hJe0
  exact Spike.Lib.A64.WakePh.MainWf.ctl_mainE0 (P := fun c => c = c0W) rfl σe _ hJe

/-- **`WcWfS.wcSp0W_WS`'s `hwr` at `CtxR`** (at `IW`): at the box's store
under main's thread pointer, the store is `StAt` (so in `CtxR`) writing no
counter. -/
theorem hwr_R (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hc : Spike.Lib.A64.Rt.CtrZ o) (E : Entry)
    {ms : MemSide isaLSE2} (hms : ms = { refW hp IW ls0 E with xa := ms.xa })
    (v : BitVec 64) (m0 : MachineData) (σC : Spike.Lib.A64.Flow.AS) :
    NodeW (fun s c => TP (TV) s → Spike.Lib.A64.WakeWf.NoWrC (Spike.Lib.WakeOD.arW hp IW) wakeSrc (L0T (LyW).Λ)
        (ls0T (ls0 E)) (CtxR hp IW ls0 E) [] s c)
      (fun _ _ => False) (LyW).exe (LyW).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC) (sN ms (LyW).lab ((JWW) σC) .st) := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { refW hp IW ls0 E with xa := X } := ⟨_, hms⟩
  intro s c hAt
  refine ⟨fun htp => ?_, fun _ h => h⟩
  -- the layout's facts
  have e : SccCode.wakeProg = wakeProg := by decide +kernel
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp IW hpa hwp
  have hL : Scc.Cert.Rt.A64.Lays (LyW).exe SccCode.wakeProg (LyW).pfx := e ▸ hprog ▸ (LyW).lays
  have hend : (LyW).endPc = Scc.Cert.Rt.A64.endOf (LyW).exe SccCode.wakeProg (LyW).pfx := by rw [e, ← hprog]
  have hin := Spike.Lib.A64.Flow.WakeWc.wake_wcS0In
  simp only [Spike.Lib.A64.Flow.WakeWc.wcS0In, Bool.and_eq_true] at hin
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (LyW).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link IW hp)
  have hb : (LyW).Λ.heap.lo + (LyW).Λ.heap.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.heap_below_of_placeW (Spike.Lib.PlaceW.link IW hp)
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : (refW hp IW ls0 E).heap = (LyW).Λ.heap.lo := rfl
  have hcl : (refW hp IW ls0 E).cells = 4194304 := rfl
  have hu2 : (refW hp IW ls0 E).units 1 .int = 2 := rfl
  have hf1 : (refW hp IW ls0 E).off 1 .int = 8 :=
    Spike.Lib.LowerA64.arOf_off_eq (Λ := (LyW).Λ) (n := 1) (τ := .int) ⟨_, rfl⟩
  -- the store's premises
  have hSt : StAt (refW hp IW ls0 E) wakeSrc (L0T (LyW).Λ) (GsW hp IW ls0 E) s c [] := by
    refine ⟨rfl, fun l A n s c => n = 1 ∧ Spike.Lib.A64.Flow.At (LyW).exe (LyW).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC) (bX (refW hp IW ls0 E) (LyW).lab ((JWW) σC) l A) s c ∧
      TP (TV) s, ⟨v, m0, σC, rfl⟩, ?_⟩
    refine Spike.Lib.A64.Alloc.newStM_nd (t := .X9) (b := .X10) (i := 0) (R := wR (swR v (-384) 0) 336)
      (F := wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC)
      (n := ⟨(LyW).lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 3), ⟨-80, []⟩, fun σ c =>
        (sN { refW hp IW ls0 E with xa := X } (LyW).lab ((JWW) σC) .st).J σ c ∧ σ.regs.TPIDR_EL0 = TV⟩)
      (fun l A => ⟨(LyW).lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 4), ⟨-80, []⟩, fun σ c =>
        (bX (refW hp IW ls0 E) (LyW).lab ((JWW) σC) l A).J σ c ∧ σ.regs.TPIDR_EL0 = TV⟩)
      (Spike.Lib.A64.Flow.code_of hL hend (Spike.Lib.A64.Flow.WakeWc.boxSt_eq ▸ hin.2) rfl) ?_ ?_ ?_
    · rintro l A s' c' - ⟨he, hn, hdc, hpc, σ, hA', hD, hJ, htp'⟩
      exact ⟨rfl, ⟨he, hn, hdc, hpc, σ, hA', hD, hJ⟩, by show s'.st.1.regs.TPIDR_EL0 = _; rw [hA'.regs]; exact htp'⟩
    · rintro m σ c' - hD ⟨⟨q, o', hwc, rfl, h9, h10, hA72, hle, hlo'⟩, htp'⟩
      have hc0 := c0_of_wcJ hwc
      obtain ⟨w, hτ, hws, hw0⟩ := box_c0W q hc0
      have hcell := Spike.Lib.A64.WakePh.StartGlue.hcellB_of_wordsNone
        (F := wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC) (P := fun q => q.c0 = c0W)
        (ms := { refW hp IW ls0 E with xa := X })
        (fun _ h => h.1.1.wn) (Nat.le_refl _) (by rw [hh, hcl]; omega) (by rw [hh, hcl]; omega)
        (fun q hq => by obtain ⟨_, hτ', -⟩ := box_c0W q hq; rw [hτ']; show (refW hp IW ls0 E).off 1 .int + 16 ≤
          16 * (refW hp IW ls0 E).units 1 .int; rw [hf1, hu2]; omega)
        (fun q _ o h1 h2 => Spike.Lib.A64.WakePh.StartH0.mp_cellW hp IW
          (⟨q.1, { q.2 with toS := { q.2.toS with } }⟩ : AGB (refW hp IW ls0 E) (LyW).lab) o h1 h2)
        q hc0 o'.toNat hlo' hle
      have ha : Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 = σ.slot (-72) := by
        rw [Spike.Lib.A64.Flow.Ret0.rAddr_x10 h10]; simp
      have ha' : Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 = BitVec.ofNat 64
          ((refW hp IW ls0 E).heap + 16 * o'.toNat + (refW hp IW ls0 E).off 1 q.1.τ) := by
        rw [ha, ← hA72, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      obtain ⟨hmp, hun⟩ := hcell
      refine ⟨q.2.newOk, ha' ▸ hmp, ha' ▸ hun m hD, q.1.x, q.1.a, q.1.τ, q.1.e, w, TermRun.cst (.num o'.toNat),
        o'.toNat, q.2.term, hws ▸ q.2.ev, by rw [hτ]; rfl, ?_, rfl, rfl, by rw [ha, hA72], hle, fun l _ => ⟨?_, rfl,
        ⟨⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, hwc, by rw [ha], rfl, o'.toNat, by rw [ha, hA72], hle⟩, htp'⟩⟩
      · rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9, hw0]; exact ⟨by decide, rfl⟩
      · show (LyW).lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 4) =
          (LyW).lab ".L21_wc_main.sp0" + Int64.ofNat (4 * 3) + Int64.ofNat 4
        rw [Int64.add_assoc]; rfl
    · obtain ⟨he, hn, hdc, hpc, σ, hA', hD, hJ⟩ := hAt
      exact ⟨he, hn, hdc, hpc, σ, hA', hD, hJ, by rw [← hA'.regs]; exact htp⟩
  have hnw := Spike.Lib.A64.WakeCtr.stAt_noWr (hlt_R hp IW ls0 hc E)
    (Spike.Lib.WakeOD.hok_W hp IW E (Spike.Lib.WakeHG.cTW hp IW) Spike.Lib.A64.WakeWf.DtW (ls0 E)
      (fun _ _ _ => False) (fun _ _ _ => False) (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) hc).ctr_lt
    s c [] hSt
  exact ⟨fun _ _ _ _ _ _ => .inr ⟨Or.inr hSt, hnw⟩, fun _ => Or.inr hSt⟩

/-- **The allocator's frame condition at `wc_main`'s call is stable** in
its region `wAR R`: `F` by `FStable.callee`, the caller's cells (held and
as at the call) outside it untouched (`Region.callee_sep`). -/
theorem fstable_wAR {R : Spike.Lib.Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {lab : Label → Int64}
    {J : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {q : Spike.Lib.A64.Alloc.Call}
    (hR : R.OK) (hF : Spike.Lib.A64.Flow.FStable R F) (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi) :
    Spike.Lib.A64.Flow.FStable (wAR R)
      (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms lab R J q m) := by
  rintro m m' ⟨h1, h2, mC, σC', c', hA, hJ1, hJ2, hK⟩ hd
  have hsep : ∀ k, R.Off k → ¬ (R.callee (-80) (-160) 0).Off (k - -80) →
      Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 := fun k hk hn =>
    hd _ (Spike.Lib.Region.addr_fit hR hk) (Spike.Lib.Region.callee_sep hR (show R.lo ≤ -80 + -160 by omega)
      (by decide) (by omega) (by decide) (by decide) (by decide) hk hn)
  exact ⟨Spike.Lib.A64.Flow.FStable.callee hR (by omega) (by decide) (by omega) (by omega) hF m m' h1 hd,
    fun k hk hn => by rw [hsep k hk hn]; exact h2 k hk hn, mC, σC', c', hA, hJ1, hJ2,
    fun k hk hn => (hsep k hk hn).trans (hK k hk hn)⟩

/-- **`WcWfS.wcPreW_WS`'s `hctx` at `CtxR`** (at `IW`): a counter add of a
box call from `wc_main` (on the first stack) returning to `.sp0`, under
main's thread pointer, is `CtxR`'s `CtrAt`. -/
theorem hctx_R (hc : Spike.Lib.A64.Rt.CtrZ o) (E : Entry)
    {ms : MemSide isaLSE2} (hms : ms = { refW hp IW ls0 E with xa := ms.xa })
    (v : BitVec 64) (m0 : MachineData) (σC : Spike.Lib.A64.Flow.AS) :
    ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms (LyW).lab → q.ra = ((LyW).lab ".L21_wc_main.sp0").toBitVec →
      ∀ s c, Spike.Lib.A64.Flow.At (LyW).exe (LyW).endPc (wAR (wR (swR v (-384) 0) 336))
        (fun m => wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC m ∧
          CallerCells (wR (swR v (-384) 0) 336) (-80) (-160) 0 m ∧
          WcCtx ms (LyW).lab (wR (swR v (-384) 0) 336) ((JWW) σC) q m)
        (Spike.Lib.A64.Alloc.N (LyW).lab ms q .rmw) s c → TP (TV) s → CtxR hp IW ls0 E s c [] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { refW hp IW ls0 E with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt htp
  refine .inl ⟨⟨rfl, _, _, _, q, rfl, ⟨v, m0, σC, rfl, rfl, hra⟩, ⟨hq, ?_, fun m hm => ?_⟩, hAt⟩, htp⟩
  · by_cases hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (LyW).lab + 0#64 + 16384#64
    case neg => exact fun m _ hm => (hv hm.1.1.2.1.1).elim
    subst hv
    have hwf := Spike.Lib.PlaceW.wf_link_of_placeW IW hp
    have hsub := Spike.Lib.A64.Rt.rS0_sub (LyW)
    have hok : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (LyW).lab + 0#64 + 16384#64) (-384) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
    have hF0 := Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable
      (a := Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (LyW).lab + 0#64 + 8#64)))
      (v := Spike.Lib.A64.Flow.Ret0.stacksA (LyW).lab + 0#64 + 16384#64) hwf hsub hok (by decide) (by decide)
      (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by decide) (by decide))
      (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
      (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
          exact Spike.Lib.A64.Rt.rt_houtD _ (by decide) (by decide))
      (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
    obtain ⟨hR, -, hF⟩ := Spike.Lib.A64.Flow.WakeM.wR_ok (D := 336) (by decide) (by decide) hok
      (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _) hF0
      (by show (-384 : Int) ≤ -48 - 336; decide) (by show (0 : Int) ≤ 0; decide) m0 σC
    exact fstable_wAR hR hF (by show (-336 : Int) ≤ -240; decide) (by show (0 : Int) ≤ 0; decide)
  · obtain ⟨hc1, hc2, -⟩ := Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceW.link IW hp) hc
    have hc1' : (LyW).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (LyW).Λ := hc1
    have hc2' : Scc.Cert.PlaceOK.heapUseOf (LyW).Λ + 8 ≤ (LyW).Λ.data.lo + (LyW).Λ.data.size := hc2
    have hdb : (LyW).Λ.data.lo + (LyW).Λ.data.size ≤ 2 ^ 32 :=
      Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link IW hp)
    show Mem.loadInt m.dmem (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (LyW).Λ)) 8 = none
    refine hm.1.1.1.wn _ (.inr ?_)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold Spike.Lib.DmemPriv.WordIn Scc.Sem.Range.contains; omega

end Spike.Lib.A64.WakePh.Land

/-- info: 'Spike.Lib.A64.WakePh.Land.hwr_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.hwr_R

/-- info: 'Spike.Lib.A64.WakePh.Land.fstable_wAR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.fstable_wAR

/-- info: 'Spike.Lib.A64.WakePh.Land.hctx_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.hctx_R
