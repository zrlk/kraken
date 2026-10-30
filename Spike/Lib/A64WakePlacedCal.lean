/-
**main's source placed in `wc_main`'s runtime callees past the box**
(AArch64; `reserveW_wf`'s `hpl`): at every node of
`scc_rt_thread_reserve` called at `.sp0` (region `rAR R`, the call context
`ResCtx`), main's source is placed (`PlacedSE`) under `upd (L0T Λ) l b`:
the callee's nodes keep the call's control (`SpawnSrc l`), and main's frame
slots `-72` (the box's cell `b`) and `-80` (main's `ThreadId`) sit below
the callee's region, kept (`CKept`, `DFrame`; `placeVal_slot_kept`).

- `rvN_ctl`: every reserve node's control is the call's.
- `placed_res`: at a state whose memory is outside the callee's region as
  at a node's, under `ResCtx`.
- `reserveW_placed`: the instance (`HMidP.res`'s placement half).
- `hti_placed`: `hti_W`'s `hpl` (the source at `SB l b`, main's slots read).
- `placeVal_slot_keptC`: `placeVal_slot_kept` below any callee region
  `R.callee (-80) kc 0`.
- `tcbN_ctl`, `placed_tcb`, `tcbWG_placed`: the same for the second
  `scc_rt_alloc_tcb` called at `.sp3` (region `R.callee (-80) (-192) 0`, the
  call context `TcbCtx`; `HMidP.tcb`'s placement half): main's slots from
  the call node's `FrW`, the box's cell `cA = b` (`MidG`), main's word
  `m = tcb0` (`FrMG`).

No absolute address appears in this file.
-/
import Spike.Lib.A64WakePlacedLy

namespace Spike.Lib.A64.WakePh.PlacedCal

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (rN rAR ResCtx rNe)
open Spike.Lib.A64.Rt.Reserve (ReserveW rvN ResG)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.WakeLoadT (L0T tcb0)
open Spike.Lib.WakeHMid (SB)
open Spike.Lib.WakeSrcCtl (placedSE_spawnAt placeVal_slot_kept)
open Spike.Lib.A64.WakePh.PlacedLy (lblL lbl_l lbl_me)

/-- **Every reserve node's control is the call's.** -/
theorem rvN_ctl {lab : Label → Int64} {q : ResG} :
    ∀ (i : Spike.Lib.A64.Rt.Reserve.RN) (σ : Flow.AS) (c : Ctl), (rvN lab q i).J σ c → c = q.c0 := by
  intro i σ c h; cases i <;> exact h.1

section Inst

variable {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {J0 : Flow.AS → Ctl → Prop}
  {g : Spike.Lib.A64.Flow.Reserve.G × Ctl}

set_option hygiene false in
/-- The reserve's frame condition at the call (`WcResW.res`'s). -/
local notation "FR" => fun m => F m ∧ Ret0.CallerCells R (-80) (-48) 0 m ∧
  ResCtx (_root_.Executable.labels exe).label R (rN ms (_root_.Executable.labels exe).label J0 (SB l b) .call).J g m

/-- **Placed in the reserve** at a state whose memory is outside the
callee's region as at `m'` (a node's), with `FR m'`: the call's control
`g.2` at main's slots. -/
theorem placed_res (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hl : l ≠ mainTidLbl 2)
    (hJ0 : ∀ σe c, J0 σe c → σe.regs.X0.toNat = tcb0 Λ) {m' : MachineData} (hF : FR m') {s : State}
    (hD : Flow.DFrame (rAR R) m' s.st.1) : PlacedSE Λ (lblL Λ l b) s g.2 [] := by
  obtain ⟨-, -, mC, σC, c, hA, ⟨⟨l', A, ⟨e1, e2, hs⟩, q, ⟨σe, hj, -, -, h80⟩, h72⟩, -⟩, ⟨hc, -⟩, hK⟩ := hF
  subst e1 e2
  have hc : c = g.2 := hc
  subst hc
  have o72 : R.Off (-72) := ⟨by decide, by omega, by omega⟩
  have o80 : R.Off (-80) := ⟨by decide, by omega, by omega⟩
  refine placedSE_spawnAt _ _ hs ⟨_, placeVal_slot_kept hA hK hD hR hlo hhi o72 (by omega), ?_⟩
    ⟨_, placeVal_slot_kept hA hK hD hR hlo hhi o80 (Int.le_refl _), ?_⟩
  · rw [lbl_l]; exact congrArg some h72.symm
  · rw [lbl_me _ hl, h80]; exact congrArg some (hJ0 σe _ hj).symm

/-- **main's source placed at every node of `scc_rt_thread_reserve`**
(`reserveW_wf`'s `hpl`, `HMidP.res`'s placement half). -/
theorem reserveW_placed (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hl : l ≠ mainTidLbl 2)
    (hJ0 : ∀ σe c, J0 σe c → σe.regs.X0.toNat = tcb0 Λ) (nd : Spike.Lib.A64.Rt.Reserve.RN) :
    ReserveW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc (rAR R) FR
      ⟨g.1, 0#64, g.2⟩ nd := by
  have hB : ∀ i blk, BlkW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc (rAR R) FR
      (rvN (_root_.Executable.labels exe).label ⟨g.1, 0#64, g.2⟩ i) blk := by
    intro i blk s σ c _ _ _ _ _ hF hj _ _ m _ hD
    obtain rfl := rvN_ctl i σ c hj
    exact ⟨placed_res (s := { s with st := (m, _) }) hR hlo hhi hl hJ0 hF hD, fun _ h => h⟩
  have hN : ∀ i, NodeW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc (rAR R) FR
      (rvN (_root_.Executable.labels exe).label ⟨g.1, 0#64, g.2⟩ i) := by
    rintro i s c ⟨-, -, -, -, σ, -, hF, hj⟩
    obtain rfl := rvN_ctl i σ c hj
    exact ⟨placed_res hR hlo hhi hl hJ0 hF (Flow.DFrame.refl _ _), fun _ h => h⟩
  cases nd <;> first | exact hB _ _ | exact hN _

end Inst

/-- **The thread init's placement** (`hti_W`'s `hpl`, the slot form): at
the clone's source `SB l b`, any state reading the box's cell `b` at main's
slot `-72` and main's id at `-80` places it (`l` fresh at the start). -/
theorem hti_placed {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {R : Region} (hl : L0T Λ l = none) :
    ∀ c0, (∃ l' A', SB l b l' A' c0) → ∀ s : State,
      placeVal (machine (kernel 1)) s (.slot (R.addr (-72)).toNat) = some b →
      placeVal (machine (kernel 1)) s (.slot (R.addr (-80)).toNat) = some (tcb0 Λ) →
      PlacedSE Λ (lblL Λ l b) s c0 [] := by
  rintro c0 ⟨l', A', rfl, rfl, hs⟩ s h72 h80
  exact placedSE_spawnAt _ _ hs ⟨_, h72, lbl_l _ _ _⟩
    ⟨_, h80, lbl_me _ (Spike.Lib.A64.WakePh.PlacedLy.ne_of_fresh hl)⟩

/-- **A slot of main's frame read below a callee's region**
(`placeVal_slot_kept` at any callee size `kc`): the caller's abstraction's
slot `k ≥ -80`, kept by the call (`CKept`) and the callee's states
(`DFrame`). -/
theorem placeVal_slot_keptC {R : Region} {o : Flow.SO} {m1 m' : MachineData} {σC : Flow.AS} {s : State}
    {kc : Int} (hA : Flow.Abs R o m1 σC) (hK : Flow.CKept R (-80) kc 0 m1 m')
    (hD : Flow.DFrame (R.callee (-80) kc 0) m' s.st.1) (hR : R.OK) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : -80 ≤ k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-80) kc 0).Off (k - -80) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  have h80 := Spike.Lib.Region.addr_toNat_of hR (k := -80) hlo (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Region.callee]; omega))
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.A64.privLoad, e, hK k hk hc, hj, hv]

/-- **Every second-TCB node's control is the call's.** -/
theorem tcbN_ctl {lab : Label → Int64} {q : Spike.Lib.A64.Rt.TcbGG} :
    ∀ (i : Ret0.TN) (σ : Flow.AS) (c : Ctl), (Spike.Lib.A64.Rt.tcbNG lab q i).J σ c → c = q.c0 := by
  intro i σ c h; cases i <;> exact h.1

section Tcb

variable {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {J0 : Flow.AS → Ctl → Prop} {c0 : Ctl} {cA m : BitVec 64}
  {fr : BitVec 64 × BitVec 64} {g : Ret0.AllocTcb.G}

set_option hygiene false in
/-- The second TCB's frame condition at the call (`WcSp3W.tcb`'s). -/
local notation "FT" => fun mm => F mm ∧ Ret0.CallerCells R (-80) (-192) 0 mm ∧
  Spike.Lib.A64.Flow.WakeWc.TcbCtx (_root_.Executable.labels exe).label R
    (Spike.Lib.A64.Flow.WakeWc.wcNC' (_root_.Executable.labels exe).label c0 cA m fr).J c0 g mm

/-- **Placed in the second TCB call** at a state whose memory is outside
the callee's region as at `m'` (a node's), with `FT m'`: the call's control
`c0` (`SpawnSrc l c0`) at main's slots, the box's cell `cA = b` and main's
word `m = tcb0`. -/
theorem placed_tcb (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hl : l ≠ mainTidLbl 2)
    (hs : Spike.Lib.WakeBoxW.SpawnSrc l c0) (hcA : cA.toNat = b) (hm : m.toNat = tcb0 Λ)
    {m' : MachineData} (hF : FT m') {s : State} (hD : Flow.DFrame (R.callee (-80) (-192) 0) m' s.st.1) :
    PlacedSE Λ (lblL Λ l b) s c0 [] := by
  obtain ⟨-, -, mC, σC, c, hA, ⟨-, ⟨h72, h80, -, -⟩, -⟩, -, hK⟩ := hF
  have o72 : R.Off (-72) := ⟨by decide, by omega, by omega⟩
  have o80 : R.Off (-80) := ⟨by decide, by omega, by omega⟩
  refine placedSE_spawnAt _ _ hs ⟨_, placeVal_slot_keptC hA hK hD hR hlo hhi o72 (by omega), ?_⟩
    ⟨_, placeVal_slot_keptC hA hK hD hR hlo hhi o80 (Int.le_refl _), ?_⟩
  · rw [lbl_l, h72, hcA]
  · rw [lbl_me _ hl, h80, hm]

/-- **main's source placed at every node of the second `scc_rt_alloc_tcb`**
(`HMidP.tcb`'s placement half), at every ghost `HMidP.tcb` quantifies
(`MidG (SB l b)`, `FrMG J0`), `J0`'s `x0` main's `tcb0`. -/
theorem tcbWG_placed (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hl : l ≠ mainTidLbl 2)
    (hJ0 : ∀ σe c, J0 σe c → σe.regs.X0.toNat = tcb0 Λ)
    (hM : Spike.Lib.A64.Flow.WakeWc.MidG (SB l b) c0 cA ∧ Spike.Lib.A64.Flow.WakeWc.FrG J0 fr ∧
      Spike.Lib.A64.Flow.WakeWc.FrMG J0 fr m) (nd : Ret0.TN) :
    Spike.Lib.A64.Rt.TcbWG (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc
      (R.callee (-80) (-192) 0) FT (Spike.Lib.A64.WakePh.Tcb2Call.tcb2Q g c0) nd := by
  obtain ⟨⟨l', A, ⟨e1, e2, hs⟩, hcA⟩, -, σe, ce, hj, -, hm⟩ := hM
  subst l'
  replace hcA : cA.toNat = b := e2 ▸ hcA
  have hm' : m.toNat = tcb0 Λ := by rw [hm]; exact hJ0 σe ce hj
  have hB : ∀ i blk, BlkW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc
      (R.callee (-80) (-192) 0) FT (Spike.Lib.A64.Rt.tcbNG (_root_.Executable.labels exe).label
        (Spike.Lib.A64.WakePh.Tcb2Call.tcb2Q g c0) i) blk := by
    intro i blk s σ c _ _ _ _ _ hF hj _ _ m _ hD
    obtain rfl := tcbN_ctl i σ c hj
    exact ⟨placed_tcb (s := { s with st := (m, _) }) hR hlo hhi hl hs hcA hm' hF hD, fun _ h => h⟩
  have hN : ∀ i, NodeW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc
      (R.callee (-80) (-192) 0) FT (Spike.Lib.A64.Rt.tcbNG (_root_.Executable.labels exe).label
        (Spike.Lib.A64.WakePh.Tcb2Call.tcb2Q g c0) i) := by
    rintro i s c ⟨-, -, -, -, σ, -, hF, hj⟩
    obtain rfl := tcbN_ctl i σ c hj
    exact ⟨placed_tcb hR hlo hhi hl hs hcA hm' hF (Flow.DFrame.refl _ _), fun _ h => h⟩
  cases nd <;> first | exact hB _ _ | exact hN _

end Tcb

end Spike.Lib.A64.WakePh.PlacedCal

/-- info: 'Spike.Lib.A64.WakePh.PlacedCal.reserveW_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedCal.reserveW_placed

/-- info: 'Spike.Lib.A64.WakePh.PlacedCal.hti_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedCal.hti_placed

/-- info: 'Spike.Lib.A64.WakePh.PlacedCal.tcbWG_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedCal.tcbWG_placed
