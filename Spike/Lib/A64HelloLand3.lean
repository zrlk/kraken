/-
**hello's box store and the allocator's frame condition** (AArch64; the
twins of `Spike/Lib/A64WakeLand3.lean`'s `hwr_R` and `fstable_wAR`, layout-
and context-generic).

- `fstable_aRG`: the allocator's frame condition at a call of frame `fr`
  (`CallerCells`, `PlacedAlloc.CtxG`) is stable in the callee's region; the
  instances `fstable_wARH` (`wc_main`'s box call, frame 144, `WcCtxH`) and
  `fstable_aRH` (`wc_rodata`'s buffer call, frame 48, `HelloRd.RdCtx`).
- `hwr_stH`: `WcWfS.wcSp0W_WSH`'s `hwr` (guarded by the thread pointer `t`)
  in any valid layout of `helloProg`: at `wc_main`'s box store
  (`sNH .st`) the store is `StAt ref … Gs` (so in `Ctx`, `hCtx`) and writes
  no counter (`hlt`, `h64`). The landing family `Gs` admits is the box's
  landing `bXH ref` under `t` (`hGs`); the box's word and cell are
  `hello_wc_sp0_segW`'s `hbox`, `hcell`.

The root context (`hctx_R`'s twin) needs hello's root `Ctx`, which does not
exist yet; `hwr_stH` takes it as `hCtx`.
-/
import Spike.Lib.A64WakeLand3
import Spike.Lib.A64HelloWcSp0
import Spike.Lib.A64HelloPlacedAlloc

namespace Spike.Lib.A64.HelloPh.Land

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Region MemSide Arena FragS Frag)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (NodeW At FStable)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Flow.WakeWc (AGB BoxW)
open Spike.Lib.A64.Flow.HelloWc (sNH bXH)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.WakeCtr (StAt)
open Spike.Lib.A64.WakeWf (NoWrC)
open Spike.Lib.A64.HelloPh.PlacedAlloc (CtxG)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **The allocator's frame condition at a call of frame `fr` is stable** in
its region `R.callee fr (-160) 0`: `F` by `FStable.callee`, the caller's
cells (held and as at the call) outside it untouched (`Region.callee_sep`). -/
theorem fstable_aRG {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {lab : Label → Int64}
    {fr : Int} {Jn : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {q : Call}
    (hR : R.OK) (hF : FStable R F) (hfr8 : fr % 8 = 0) (hfr : fr < 0) (hlo : R.lo ≤ fr + -160)
    (hhi : 0 ≤ R.hi) :
    FStable (R.callee fr (-160) 0) (fun m => F m ∧ CallerCells R fr (-160) 0 m ∧ CtxG ms lab R fr Jn q m) := by
  rintro m m' ⟨h1, h2, mC, σC', c', hA, hJ1, hJ2, hK⟩ hd
  have hsep : ∀ k, R.Off k → ¬ (R.callee fr (-160) 0).Off (k - fr) →
      Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 := fun k hk hn =>
    hd _ (Spike.Lib.Region.addr_fit hR hk) (Spike.Lib.Region.callee_sep hR hlo
      (by decide) (by omega) hfr8 (by decide) (by decide) hk hn)
  exact ⟨Spike.Lib.A64.Flow.FStable.callee hR hlo (by decide) (by omega) (by omega) hF m m' h1 hd,
    fun k hk hn => by rw [hsep k hk hn]; exact h2 k hk hn, mC, σC', c', hA, hJ1, hJ2,
    fun k hk hn => (hsep k hk hn).trans (hK k hk hn)⟩

/-- **`wc_main`'s box call's frame condition is stable** (frame 144,
`WcCtxH`, `wARH`): `fstable_aRG` at `fr = -144`. -/
theorem fstable_wARH {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {lab : Label → Int64}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {q : Call}
    (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) :
    FStable (Spike.Lib.A64.Flow.HelloWc.wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ Spike.Lib.A64.Flow.HelloWc.WcCtxH ms lab R J0 J1 q m) :=
  fstable_aRG hR hF (by decide) (by decide) (by omega) hhi

/-- **`wc_rodata`'s buffer call's frame condition is stable** (frame 48,
`HelloRd.RdCtx`, `Hello1.aR`): `fstable_aRG` at `fr = -48`. -/
theorem fstable_aRH {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {lab : Label → Int64}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {q : Call}
    (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi) :
    FStable (Spike.Lib.A64.Flow.Hello1.aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧ Spike.Lib.A64.Flow.HelloRd.RdCtx ms lab R J0 J1 q m) :=
  fstable_aRG hR hF (by decide) (by decide) (by omega) hhi

section Wr

variable {p : Prog} {lbl : Lbl} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ar : Arena} {lsize : Lsize} {Ctx : FragS isaLSE2}

/-- **`WcWfS.wcSp0W_WSH`'s `hwr`** under the thread pointer `t`, in any
valid layout of `helloProg`: at `wc_main`'s box store (`sNH .st`) the store
is `StAt ref p lbl Gs` (its landing `bXH ref` under `t`, `hGs`), so in `Ctx`
(`hCtx`), writing no counter (the counter below `ref`'s heap, `hlt`).
- The value boxed is one word represented by `0` (`hbox`).
- Every cell the allocator may return is mapped for writing and unmapped
  in private memory under `F` (`hcell`). -/
theorem hwr_stH {kp : Nat} (hL : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    {ref ms : MemSide isaLSE2} (hms : ms = { ref with xa := ms.xa })
    {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {t : UInt64}
    {Gs : (WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2) → Prop}
    (hGs : Gs fun l A n s c => n = 1 ∧
      At exe endPc R F (bXH ref (_root_.Executable.labels exe).label J1 l A) s c ∧ TP t s)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) →
      ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hCtx : ∀ s c, StAt ref p lbl Gs s c [] → Ctx s c [])
    (hlt : ar.ctr + 8 ≤ ref.heap) (h64 : ar.ctr < 2 ^ 64) :
    NodeW (fun s c => TP t s → NoWrC ar p lbl lsize Ctx [] s c) (fun _ _ => False) exe endPc R F
      (sNH ms (_root_.Executable.labels exe).label J1 .st) := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { ref with xa := X } := ⟨_, hms⟩
  intro s c hAt
  refine ⟨fun htp => ?_, fun _ h => h⟩
  have hin := Spike.Lib.A64.Flow.HelloWc.hello_wcS0InH
  simp only [Spike.Lib.A64.Flow.HelloWc.wcS0InH, Bool.and_eq_true] at hin
  have hSt : StAt ref p lbl Gs s c [] := by
    refine ⟨rfl, _, hGs, ?_⟩
    refine Spike.Lib.A64.Alloc.newStM_nd (t := .X9) (b := .X10) (i := 0) (R := R) (F := F)
      (n := ⟨(_root_.Executable.labels exe).label ".L22_wc_main.sp0" + Int64.ofNat (4 * 3), ⟨-144, []⟩,
        fun σ c => (sNH { ref with xa := X } (_root_.Executable.labels exe).label J1 .st).J σ c ∧
          σ.regs.TPIDR_EL0 = t⟩)
      (fun l A => ⟨(_root_.Executable.labels exe).label ".L22_wc_main.sp0" + Int64.ofNat (4 * 4), ⟨-144, []⟩,
        fun σ c => (bXH ref (_root_.Executable.labels exe).label J1 l A).J σ c ∧ σ.regs.TPIDR_EL0 = t⟩)
      (Spike.Lib.A64.Flow.code_of hL hend (Spike.Lib.A64.Flow.WakeWc.boxSt_eq ▸ hin.2) rfl) ?_ ?_ ?_
    · rintro l A s' c' - ⟨he, hn, hdc, hpc, σ, hA', hD, hJ, htp'⟩
      exact ⟨rfl, ⟨he, hn, hdc, hpc, σ, hA', hD, hJ⟩, by show s'.st.1.regs.TPIDR_EL0 = _; rw [hA'.regs]; exact htp'⟩
    · rintro m σ c' - hD ⟨⟨q, o, hwc, rfl, h9, h10, hA104, hle, hlo'⟩, htp'⟩
      have hj : ∃ σ, J1 σ q.1.c0 := let ⟨σe, hJe, _⟩ := hwc; ⟨σe, hJe⟩
      obtain ⟨w, hws, hacc, hrep⟩ := hbox q hj
      have ha : Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 = σ.slot (-104) := by
        rw [Spike.Lib.A64.Flow.Ret0.rAddr_x10 h10]; simp
      have ha' : Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 = BitVec.ofNat 64
          (ref.heap + 16 * o.toNat + ref.off 1 q.1.τ) := by
        rw [ha, ← hA104, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      obtain ⟨hmp, hun⟩ := hcell q hj o.toNat hlo' hle
      refine ⟨q.2.newOk, ha' ▸ hmp, ha' ▸ hun m hD, q.1.x, q.1.a, q.1.τ, q.1.e, w, TermRun.cst (.num o.toNat),
        o.toNat, q.2.term, hws ▸ q.2.ev, hacc, ?_, rfl, rfl, by rw [ha, hA104], hle, fun l _ => ⟨?_, rfl,
        ⟨⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, hwc, by rw [ha], rfl, o.toNat, by rw [ha, hA104], hle⟩,
        htp'⟩⟩
      · rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hrep
      · show (_root_.Executable.labels exe).label ".L22_wc_main.sp0" + Int64.ofNat (4 * 4) =
          (_root_.Executable.labels exe).label ".L22_wc_main.sp0" + Int64.ofNat (4 * 3) + Int64.ofNat 4
        rw [Int64.add_assoc]; rfl
    · obtain ⟨he, hn, hdc, hpc, σ, hA', hD, hJ⟩ := hAt
      exact ⟨he, hn, hdc, hpc, σ, hA', hD, hJ, by rw [← hA'.regs]; exact htp⟩
  have hnw := Spike.Lib.A64.WakeCtr.stAt_noWr hlt h64 s c [] hSt
  exact ⟨fun _ _ _ _ _ _ => .inr ⟨hCtx _ _ hSt, hnw⟩, fun _ => hCtx _ _ hSt⟩

end Wr

end Spike.Lib.A64.HelloPh.Land

/-- info: 'Spike.Lib.A64.HelloPh.Land.fstable_aRG' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.fstable_aRG

/-- info: 'Spike.Lib.A64.HelloPh.Land.fstable_wARH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.fstable_wARH

/-- info: 'Spike.Lib.A64.HelloPh.Land.fstable_aRH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.fstable_aRH

/-- info: 'Spike.Lib.A64.HelloPh.Land.hwr_stH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.hwr_stH
