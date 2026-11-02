/-
**main's source placed in `wc_main`'s runtime callees past the box** (x86-64; the twin of
`Spike/Lib/A64HelloCalPl.lean`, and the hello twin of wake's `X64WakePlacedCal`): at every node of
`scc_rt_thread_reserve` called at `.x23`'s call block (region `rARH R = R.callee (-136) (-40) 8`, the call context
`ResCtxH`) and of the second `scc_rt_alloc_tcb` called at `.x23` (region `R.callee (-136) (-184) 8`, the call
context `TcbCtxH`), main's source is placed (`PlacedSE`) wherever the clone's source is placed at `wc_main`'s five
slots (`Hs`, as `Ti2Hat.hti_H`'s `hpl` takes it; `SpawnPl.hplQ_GJ1H` at a box ghost).

The callee's nodes keep the call's control, and the five slots (`-48`, `-40`, `-8`, `-24`, `-32`) sit above the
callee's region, kept from the call's abstract state (`CKept`, `DFrame`; `slotRd_kept`).

- `slotRd_kept`: a slot above a callee's region reads the call's abstract word.
- `slots_kept`: the five slots, above a callee at `-136`.
- `placed_resH`, `reserveW_placedH`: the reserve's (`HMidPAH.res`'s placement half).
- `placed_tcbH`, `tcbWG_placedH`: the second TCB's (`HMidPAH.tcb`'s placement half).

No absolute address appears in this file.

**Unlike AArch64**: the callees are based at the pushed return address `-136` with the return address above
(`hi' = 8`; AArch64: `-144`, `hi' = 0`), so a slot is above the callee from `-128` on (`slotRd_kept`'s
`kc + 8 ≤ k`); main's slots are `-48` (the box's cell) and `-40` (main's id), the slice's `-8`, `-24`, `-32`
(AArch64: `-104`, `-112`; `-144`, `-128`, `-120`); the reserve's call node's source is `rJH … (QBH l b ws)` (the
spills `wcJFH`, the cell at `-48`), the second TCB's call node is `wcNCRH` (`wcNCH` and `%rbp`), its frame's
words `FrWH`; the source facts are at `QBH` (the box's fence).
-/
import Spike.Lib.X64HelloSpawnPl
import Spike.Lib.X64HelloWcSp3
import Spike.Lib.X64HelloTi2Slot
import Spike.Lib.X64HelloTi2SlotSl
import Spike.Lib.X64WakePlacedCal

namespace Spike.Lib.X64.HelloPh.CalPl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Region Ctl)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW CKept)
open Spike.Lib.X64.Flow.WakeWc (MidG)
open Spike.Lib.X64.Flow.HelloWc (FrMGH rNH rARH ResCtxH TcbCtxH wcNCRH tcb2QH)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Rt.Reserve (ReserveW rvN)
open Spike.Lib.X64.Rt (TcbWG tcbNG)
open Spike.Lib.X64.HelloPh.Ti2 (SlotPH SlotSlH SlotRdH)
open Spike.Lib.X64.WakePh.PlacedCal (rvN_ctl tcbN_ctl)
open Spike.Lib.X64HelloHMid (QBH)

/-- **A slot above a callee's region reads the call's abstract word**: at the call `σC` abstracts `mC`
(`Abs R o`), the callee's frame condition keeps the caller's cells off its region (`CKept`), and a callee's state
`m` differs from `m'` only inside it (`DFrame`). -/
theorem slotRd_kept {R : Region} {o : Spike.Lib.X64.SO} {kc lo' : Int} {mC m' m : MachineData}
    {σC : Spike.Lib.X64.AS} (hA : Spike.Lib.X64.Abs R o mC σC) (hK : CKept R kc lo' 8 mC m')
    (hD : Spike.Lib.X64.DFrame (R.callee kc lo' 8) m' m) (hR : R.OK) (hlo : R.lo ≤ kc) (hhi : 0 ≤ R.hi)
    (hkc : kc < 0)
    {k : Int} (hk : R.Off k) (hk' : kc + 8 ≤ k) : SlotRdH R k (σC.slot k).toNat m := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee kc lo' 8).Off (k - kc) := fun ⟨_, _, h3⟩ => by
    simp only [Spike.Lib.Region.callee] at h3; omega
  have hkc' := Spike.Lib.Region.addr_toNat_of hR (k := kc) hlo (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Spike.Lib.Region.callee]; omega))
  exact ⟨j, by rw [e, hK k hk hc, hj], by rw [hv]⟩

/-- **The five slots read the call's abstract words** above a callee at `-136`. -/
theorem slots_kept {R : Region} {o : Spike.Lib.X64.SO} {lo' : Int} {mC m' m : MachineData}
    {σC : Spike.Lib.X64.AS} (hA : Spike.Lib.X64.Abs R o mC σC) (hK : CKept R (-136) lo' 8 mC m')
    (hD : Spike.Lib.X64.DFrame (R.callee (-136) lo' 8) m' m) (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 0 ≤ R.hi) :
    SlotPH R (σC.slot (-48)).toNat (σC.slot (-40)).toNat m ∧
      SlotSlH R (σC.slot (-8)).toNat (σC.slot (-24)).toNat (σC.slot (-32)).toNat m := by
  have r := fun k (h8 : k % 8 = 0) (h1 : -128 ≤ k) (h2 : k < 0) =>
    slotRd_kept hA hK hD hR hlo hhi (by decide) (k := k) ⟨h8, by omega, by omega⟩ (by omega)
  obtain ⟨j48, e48, v48⟩ := r (-48) (by decide) (by decide) (by decide)
  obtain ⟨j40, e40, v40⟩ := r (-40) (by decide) (by decide) (by decide)
  exact ⟨⟨j48, j40, e48, v48, e40, v40⟩, r (-8) (by decide) (by decide) (by decide),
    r (-24) (by decide) (by decide) (by decide), r (-32) (by decide) (by decide) (by decide)⟩

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {Λ : Scc.Sem.Layout}
  {lbl : Lbl} {ms : Spike.Lib.MemSide isa} {J1 : Spike.Lib.X64.AS → Ctl → Prop} {l : WeakMem.AllocLabel}
  {b : Nat} {ws : List TermRun.Word}

/-! ## The reserve -/

section Res

variable {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Ctl}

set_option hygiene false in
/-- The reserve's frame condition at the call (`HMidPAH.res`'s). -/
local notation "FR" => fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧
  ResCtxH (_root_.Executable.labels exe).label R
    (rNH ms (_root_.Executable.labels exe).label R J1 (QBH l b ws) .call).J g m

/-- **Placed in the reserve** at a state whose memory is outside the callee's region as at `m'` (a node's), with
`FR m'`: the call's control `g.2`, placed by `Hs` at the call's slots (the spills `wcJFH`, the cell at `-48`). -/
theorem placed_resH (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    {m' : MachineData} (hF : FR m') {s : State} (hD : Spike.Lib.X64.DFrame (rARH R) m' s.st.1) :
    PlacedSE Λ lbl s g.2 [] := by
  obtain ⟨-, -, mC, σC, c, hA, ⟨⟨l', A, ⟨q, ⟨σe, hJ1, -, -, h8, -, h24, h32, h40⟩, hA48, -, -⟩, hQ⟩, -, -⟩,
    hE, hK⟩ := hF
  have hc : c = g.2 := hE.1
  subst hc
  have hs := slots_kept hA hK hD hR hlo hhi
  rw [hA48, hQ.2.1, h40, h8, h24, h32] at hs
  exact Hs g.2 _ _ (σC.slot (-48)) (σe.regs.rbp.toBitVec, σe.slot 0)
    ⟨⟨l', A, hQ, hA48⟩, σe, q.1.c0, hJ1, rfl, rfl, rfl⟩ s hs

/-- **main's source placed at every node of `scc_rt_thread_reserve`** (`HMidPAH.res`'s placement half), from
the clone's source placed at the slots (`Hs`). -/
theorem reserveW_placedH (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    (nd : Spike.Lib.X64.Rt.Reserve.RN) :
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
    exact ⟨placed_resH hR hlo hhi Hs hF (Spike.Lib.X64.DFrame.refl _ _), fun _ h => h⟩
  cases nd <;> first | exact hB _ _ | exact hN _

end Res

/-! ## The second TCB -/

section Tcb

variable {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
  {fr : BitVec 64 × BitVec 64} {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G}

set_option hygiene false in
/-- The second TCB's frame condition at the call (`HMidPAH.tcb`'s). -/
local notation "FT" => fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
  TcbCtxH (_root_.Executable.labels exe).label R
    (wcNCRH (_root_.Executable.labels exe).label c0 sl me cA fr).J c0 g mm

/-- **Placed in the second TCB call** at a state whose memory is outside the callee's region as at `m'` (a
node's), with `FT m'`: the call's control `c0`, placed by `Hs` at the call's slots (the frame's words `FrWH`). -/
theorem placed_tcbH (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    (hM : MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me) {m' : MachineData} (hF : FT m') {s : State}
    (hD : Spike.Lib.X64.DFrame (R.callee (-136) (-184) 8) m' s.st.1) : PlacedSE Λ lbl s c0 [] := by
  obtain ⟨-, -, mC, σC, c, hA, ⟨⟨-, -, -, -, ⟨h8, -, h24, h32, h40, h48, -, -⟩, -⟩, -⟩, -, hK⟩ := hF
  have hs := slots_kept hA hK hD hR hlo hhi
  obtain ⟨_, _, ⟨-, hAb, -⟩, hcA⟩ := hM.1
  rw [h48, h40, h8, h24, h32, hcA, hAb] at hs
  exact Hs c0 sl me cA fr hM s hs

/-- **main's source placed at every node of the second `scc_rt_alloc_tcb`** (`HMidPAH.tcb`'s placement half),
at every ghost it quantifies (`MidG (QBH …)`, `FrMGH J1`), from the clone's source placed at the slots (`Hs`). -/
theorem tcbWG_placedH (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    (hM : MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me) (nd : Spike.Lib.X64.Flow.Ret0.TN) :
    TcbWG (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee (-136) (-184) 8) FT
      (tcb2QH g c0) nd := by
  have hB : ∀ i blk, BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc
      (R.callee (-136) (-184) 8) FT (tcbNG (_root_.Executable.labels exe).label (tcb2QH g c0) i) blk := by
    intro i blk s σ c _ _ _ _ _ hF hj _ _ m _ hD
    obtain rfl := tcbN_ctl i σ c hj
    exact ⟨placed_tcbH (s := { s with st := (m, _) }) hR hlo hhi Hs hM hF hD, fun _ h => h⟩
  have hN : ∀ i, NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc
      (R.callee (-136) (-184) 8) FT (tcbNG (_root_.Executable.labels exe).label (tcb2QH g c0) i) := by
    rintro i s c ⟨-, -, -, -, σ, -, hF, hj⟩
    obtain rfl := tcbN_ctl i σ c hj
    exact ⟨placed_tcbH hR hlo hhi Hs hM hF (Spike.Lib.X64.DFrame.refl _ _), fun _ h => h⟩
  cases nd <;> first | exact hB _ _ | exact hN _

end Tcb

end Spike.Lib.X64.HelloPh.CalPl

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.CalPl.slots_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalPl.slots_kept

/-- info: 'Spike.Lib.X64.HelloPh.CalPl.reserveW_placedH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalPl.reserveW_placedH

/-- info: 'Spike.Lib.X64.HelloPh.CalPl.tcbWG_placedH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalPl.tcbWG_placedH
