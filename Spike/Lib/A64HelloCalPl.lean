/-
**main's source placed in `wc_main`'s runtime callees past the box** (AArch64; rows hP-res, hP-tcb, the `hpl`
halves; the hello twin of wake's `WakePlacedCal` at frame 144): at every node of
`scc_rt_thread_reserve` called at `.sp0` (region `rARH R`, the call context `ResCtxH`) and of the second
`scc_rt_alloc_tcb` called at `.sp3` (region `R.callee (-144) (-192) 0`, the call context `TcbCtxH`), main's source
is placed (`PlacedSE`) wherever the clone's source is placed at `wc_main`'s five slots (`Hs`, as
`WcPl2.wcMainW_plH` takes it; `SpawnPl.hpl_GJ1H` at a box ghost).

The callee's nodes keep the call's control, and the five slots (`-104`, `-112`, `-144`, `-128`, `-120`) sit at or
above the callee's region, kept from the call's abstract state (`CKept`, `DFrame`; `slotRd_kept`).

- `slotRd_kept`: a slot at or above a callee's region reads the call's abstract word.
- `slots_kept`: the five slots, below a callee at `-144`.
- `placed_resH`, `reserveW_placedH`: the reserve's (`H1GAH0V.res`'s placement half).
- `placed_tcbH`, `tcbWG_placedH`: the second TCB's (`H1GAH0V.tcb`'s placement half).

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloSpawnPl
import Spike.Lib.A64HelloWcSp3
import Spike.Lib.A64WakePlacedCal

namespace Spike.Lib.A64.HelloPh.CalPl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Region Ctl)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW CKept)
open Spike.Lib.A64.Flow.WakeWc (MidG)
open Spike.Lib.A64.Flow.HelloWc (FrMGH rNH rARH ResCtxH TcbCtxH wcNCH tcb2QH)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Rt.Reserve (ReserveW rvN)
open Spike.Lib.A64.Rt (TcbWG tcbNG)
open Spike.Lib.A64.HelloPh.Ti2 (SlotPH SlotSlH SlotRdH)
open Spike.Lib.A64.WakePh.PlacedCal (rvN_ctl tcbN_ctl)
open Spike.Lib.HelloHMid (SBH QBH)

/-- **A slot at or above a callee's region reads the call's abstract word**: at the call `σC` abstracts `mC`
(`Abs R o`), the callee's frame condition keeps the caller's cells off its region (`CKept`), and a callee's state
`m` differs from `m'` only inside it (`DFrame`). -/
theorem slotRd_kept {R : Region} {o : Spike.Lib.A64.Flow.SO} {kc lo' : Int} {mC m' m : MachineData}
    {σC : Spike.Lib.A64.Flow.AS} (hA : Spike.Lib.A64.Flow.Abs R o mC σC) (hK : CKept R kc lo' 0 mC m')
    (hD : Spike.Lib.A64.Flow.DFrame (R.callee kc lo' 0) m' m) (hR : R.OK) (hlo : R.lo ≤ kc) (hhi : 0 ≤ R.hi)
    (hkc : kc < 0)
    {k : Int} (hk : R.Off k) (hk' : kc ≤ k) : SlotRdH R k (σC.slot k).toNat m := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee kc lo' 0).Off (k - kc) := fun ⟨_, _, h3⟩ => by
    simp only [Spike.Lib.Region.callee] at h3; omega
  have hkc' := Spike.Lib.Region.addr_toNat_of hR (k := kc) hlo (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Spike.Lib.Region.callee]; omega))
  exact ⟨j, by rw [e, hK k hk hc, hj], by rw [hv]⟩

/-- **The five slots read the call's abstract words** below a callee at `-144`. -/
theorem slots_kept {R : Region} {o : Spike.Lib.A64.Flow.SO} {lo' : Int} {mC m' m : MachineData}
    {σC : Spike.Lib.A64.Flow.AS} (hA : Spike.Lib.A64.Flow.Abs R o mC σC) (hK : CKept R (-144) lo' 0 mC m')
    (hD : Spike.Lib.A64.Flow.DFrame (R.callee (-144) lo' 0) m' m) (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) :
    SlotPH R (σC.slot (-104)).toNat (σC.slot (-112)).toNat m ∧
      SlotSlH R (σC.slot (-144)).toNat (σC.slot (-128)).toNat (σC.slot (-120)).toNat m := by
  have r := fun k (h8 : k % 8 = 0) (h1 : -144 ≤ k) (h2 : k < 0) =>
    slotRd_kept hA hK hD hR hlo hhi (by decide) (k := k) ⟨h8, by omega, by omega⟩ h1
  obtain ⟨j104, e104, v104⟩ := r (-104) (by decide) (by decide) (by decide)
  obtain ⟨j112, e112, v112⟩ := r (-112) (by decide) (by decide) (by decide)
  exact ⟨⟨j104, j112, e104, v104, e112, v112⟩, r (-144) (by decide) (by decide) (by decide),
    r (-128) (by decide) (by decide) (by decide), r (-120) (by decide) (by decide) (by decide)⟩

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {Λ : Scc.Sem.Layout}
  {lbl : Lbl} {ms : Spike.Lib.MemSide isaLSE2} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {l : WeakMem.AllocLabel}
  {b : Nat} {ws : List TermRun.Word}

/-! ## The reserve -/

section Res

variable {g : Spike.Lib.A64.Flow.Reserve.G × Ctl}

set_option hygiene false in
/-- The reserve's frame condition at the call (`WcResWH.res`'s). -/
local notation "FR" => fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧
  ResCtxH (_root_.Executable.labels exe).label R
    (rNH ms (_root_.Executable.labels exe).label J1 (SBH l b ws) (QBH l b ws) .call).J g m

/-- **Placed in the reserve** at a state whose memory is outside the callee's region as at `m'` (a node's), with
`FR m'`: the call's control `g.2`, placed by `Hs` at the call's slots. -/
theorem placed_resH (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    {m' : MachineData} (hF : FR m') {s : State} (hD : Spike.Lib.A64.Flow.DFrame (rARH R) m' s.st.1) :
    PlacedSE Λ lbl s g.2 [] := by
  obtain ⟨-, -, mC, σC, c, hA, ⟨⟨l', A, hS, q, ⟨σe, hJ1, -, -, h144, -, h128, h120, h112⟩, hAq⟩, -⟩, hE, hK⟩ := hF
  have hc : c = g.2 := hE.1
  subst hc
  have hs := slots_kept hA hK hD hR hlo hhi
  rw [hAq, hS.2.1, h112, h144, h128, h120] at hs
  exact Hs g.2 _ _ (σC.slot (-104)) (σe.regs.X29.toBitVec, σe.regs.X30.toBitVec)
    ⟨⟨l', A, hS, hAq⟩, σe, q.1.c0, hJ1, rfl, rfl, rfl⟩ s hs

/-- (row hP-res, `hpl`) **main's source placed at every node of `scc_rt_thread_reserve`**
(`H1GAH0V.res`'s placement half), from the clone's source placed at the slots (`Hs`). -/
theorem reserveW_placedH (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    (nd : Spike.Lib.A64.Rt.Reserve.RN) :
    ReserveW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (rARH R) FR ⟨g.1, 0#64, g.2⟩ nd := by
  have hB : ∀ i blk, BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (rARH R) FR
      (rvN (_root_.Executable.labels exe).label ⟨g.1, 0#64, g.2⟩ i) blk := by
    intro i blk s σ c _ _ _ _ _ hF hj _ _ m _ hD
    obtain rfl := rvN_ctl i σ c hj
    exact ⟨placed_resH (s := { s with st := (m, _) }) hR hlo hhi Hs hF hD, fun _ h => h⟩
  have hN : ∀ i, NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (rARH R) FR
      (rvN (_root_.Executable.labels exe).label ⟨g.1, 0#64, g.2⟩ i) := by
    rintro i s c ⟨-, -, -, -, σ, -, hF, hj⟩
    obtain rfl := rvN_ctl i σ c hj
    exact ⟨placed_resH hR hlo hhi Hs hF (Spike.Lib.A64.Flow.DFrame.refl _ _), fun _ h => h⟩
  cases nd <;> first | exact hB _ _ | exact hN _

end Res

/-! ## The second TCB -/

section Tcb

variable {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
  {fr : BitVec 64 × BitVec 64} {g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G}

set_option hygiene false in
/-- The second TCB's frame condition at the call (`WcSp3WH.tcb`'s). -/
local notation "FT" => fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧
  TcbCtxH (_root_.Executable.labels exe).label R
    (wcNCH (_root_.Executable.labels exe).label c0 sl me cA fr).J c0 g mm

/-- **Placed in the second TCB call** at a state whose memory is outside the callee's region as at `m'` (a
node's), with `FT m'`: the call's control `c0`, placed by `Hs` at the call's slots (the frame's words `FrWH`). -/
theorem placed_tcbH (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    (hM : MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me) {m' : MachineData} (hF : FT m') {s : State}
    (hD : Spike.Lib.A64.Flow.DFrame (R.callee (-144) (-192) 0) m' s.st.1) : PlacedSE Λ lbl s c0 [] := by
  obtain ⟨-, -, mC, σC, c, hA, ⟨-, -, -, -, ⟨h144, -, h128, h120, h112, h104, -, -⟩, -⟩, -, hK⟩ := hF
  have hs := slots_kept hA hK hD hR hlo hhi
  obtain ⟨_, _, ⟨-, hAb, -⟩, hcA⟩ := hM.1
  rw [h104, h112, h144, h128, h120, hcA, hAb] at hs
  exact Hs c0 sl me cA fr hM s hs

/-- (row hP-tcb, `hpl`) **main's source placed at every node of the second `scc_rt_alloc_tcb`**
(`H1GAH0V.tcb`'s placement half), at every ghost it quantifies (`MidG (SBH …)`, `FrMGH J1`), from the clone's
source placed at the slots (`Hs`). -/
theorem tcbWG_placedH (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    (hM : MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me) (nd : Spike.Lib.A64.Flow.Ret0.TN) :
    TcbWG (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee (-144) (-192) 0) FT
      (tcb2QH g c0) nd := by
  have hB : ∀ i blk, BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc
      (R.callee (-144) (-192) 0) FT (tcbNG (_root_.Executable.labels exe).label (tcb2QH g c0) i) blk := by
    intro i blk s σ c _ _ _ _ _ hF hj _ _ m _ hD
    obtain rfl := tcbN_ctl i σ c hj
    exact ⟨placed_tcbH (s := { s with st := (m, _) }) hR hlo hhi Hs hM hF hD, fun _ h => h⟩
  have hN : ∀ i, NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc
      (R.callee (-144) (-192) 0) FT (tcbNG (_root_.Executable.labels exe).label (tcb2QH g c0) i) := by
    rintro i s c ⟨-, -, -, -, σ, -, hF, hj⟩
    obtain rfl := tcbN_ctl i σ c hj
    exact ⟨placed_tcbH hR hlo hhi Hs hM hF (Spike.Lib.A64.Flow.DFrame.refl _ _), fun _ h => h⟩
  cases nd <;> first | exact hB _ _ | exact hN _

end Tcb

end Spike.Lib.A64.HelloPh.CalPl

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.HelloPh.CalPl.slots_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalPl.slots_kept

/-- info: 'Spike.Lib.A64.HelloPh.CalPl.reserveW_placedH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalPl.reserveW_placedH

/-- info: 'Spike.Lib.A64.HelloPh.CalPl.tcbWG_placedH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalPl.tcbWG_placedH
