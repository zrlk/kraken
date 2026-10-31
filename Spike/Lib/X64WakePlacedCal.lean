/-
**main's source placed in `wc_main`'s runtime callees past the box**
(x86-64; the twin of `Spike/Lib/A64WakePlacedCal.lean`; `reserveW_wf`'s and
`tcbWG_wf`'s `hpl`): at every node of `scc_rt_thread_reserve` called at
`.x18` (region `rAR R`, the call context `ResCtx`) and of the second
`scc_rt_alloc_tcb` called at `.x19` (region `R.callee (-72) (-184) 8`, the
call context `TcbCtx`), main's source is placed (`PlacedSE`) under
`upd (L0T Λ) l b`: the callee's nodes keep the call's control (at `boxTerm`,
`QB l b`), and main's frame slots `-16` (the box's cell `b`) and `-8`
(main's `ThreadId`) sit above the callee's region, kept (`CKept`, `DFrame`;
`placeVal_slot_keptC`).

- `placeVal_slot_keptC`: a slot of main's frame at `-64` or above read
  below any callee region `R.callee (-72) kc 8`.
- `rvN_ctl`, `placed_res`, `reserveW_placed`: the reserve (main's slots
  from the call node's `bX`, the box's cell, and `wcJF`'s saved `%rdi`).
- `tcbN_ctl`, `placed_tcb`, `tcbWG_placed`: the second TCB (main's slots
  from the call node's `FrV`, the box's cell `cA = b` (`MidG`), main's word
  `m = tcb0` (`FrMG`)).
- `hti_placed`: the thread init's placement (the source at `QB l b`, main's
  slots read).

**Unlike AArch64**: main's slots are `-16`, `-8` (A64 `-72`, `-80`), above
the callees' regions, which are based at the pushed return address `-72`
with `8` above it (A64: at `-80`, `0` above); the source at the callees is
at `boxTerm` with `QB l b`'s facts (`PlacedLy.placedSE_boxAt`; A64:
`SpawnSrc l` and `placedSE_spawnAt`), so `hti_placed` is at `QB l b` (A64:
`SB l b`); `J0`'s main word is `%rdi` (A64: `x0`); the reserve returns to
`.x19` with the frame `[-40, 8]` and the TCB to `.x20` with `[-184, 8]`
(A64: `.sp0`/`.sp3`, `[-48, 0]`/`[-192, 0]`).

No absolute address appears in this file.
-/
import Spike.Lib.X64WakePlacedLy

namespace Spike.Lib.X64.WakePh.PlacedCal

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (rN rAR ResCtx MidG FrG FrMG TcbCtx wcNCR)
open Spike.Lib.X64.Rt.Reserve (ReserveW rvN ResG)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.X64WakeBoxDefs (boxTerm)
open Spike.Lib.X64.WakeHMid (QB)
open Spike.Lib.X64.WakePh.PlacedLy (lblL lbl_l lbl_me placedSE_boxAt)

/-- **A slot of main's frame read below a callee's region** (any callee
size `kc`, based at `-72`, `8` above): the caller's abstraction's slot
`k ≥ -64`, kept by the call (`CKept`) and the callee's states (`DFrame`). -/
theorem placeVal_slot_keptC {R : Region} {o : SO} {m1 m' : MachineData} {σC : AS} {s : State}
    {kc : Int} (hA : Abs R o m1 σC) (hK : CKept R (-72) kc 8 m1 m')
    (hD : DFrame (R.callee (-72) kc 8) m' s.st.1) (hR : R.OK) (hlo : R.lo ≤ -80)
    (hhi : 16 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : -64 ≤ k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-72) kc 8).Off (k - -72) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  have h72 := Region.addr_toNat_of hR (k := -72) (by omega) (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Region.callee]; omega))
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.X64.privLoad, e, hK k hk hc, hj, hv]

/-! ## The reserve -/

/-- **Every reserve node's control is the call's.** -/
theorem rvN_ctl {lab : Label → Int64} {q : ResG} :
    ∀ (i : Spike.Lib.X64.Rt.Reserve.RN) (σ : AS) (c : Ctl), (rvN lab q i).J σ c → c = q.c0 := by
  intro i σ c h; cases i <;> exact h.1

section Res

variable {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {J0 : AS → Ctl → Prop}
  {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Ctl}

set_option hygiene false in
/-- The reserve's frame condition at the call (`WcResW.res`'s). -/
local notation "FR" => fun m => F m ∧ Ret0.CallerCells R (-72) (-40) 8 m ∧
  ResCtx (_root_.Executable.labels exe).label R
    (rN ms (_root_.Executable.labels exe).label R J0 (QB l b) .call).J g m

/-- **Placed in the reserve** at a state whose memory is outside the
callee's region as at `m'` (a node's), with `FR m'`: the call's control
`g.2` (at `boxTerm`, `QB l b`) at main's slots. -/
theorem placed_res (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi) (hl : l ≠ mainTidLbl 2)
    (hJ0 : ∀ σe c, J0 σe c → σe.regs.rdi.toNat = tcb0 Λ) {m' : MachineData} (hF : FR m') {s : State}
    (hD : DFrame (rAR R) m' s.st.1) : PlacedSE Λ (lblL Λ l b) s g.2 [] := by
  obtain ⟨-, -, mC, σC, c, hA, ⟨⟨l', A, ⟨q, ⟨σe, hj, -, -, h8⟩, hA16, -⟩, e1, e2, ht, -, ho, hme⟩, -, -⟩,
    ⟨hc, -⟩, hK⟩ := hF
  subst e1 e2
  have hc : c = g.2 := hc
  subst hc
  have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  have o8 : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  refine placedSE_boxAt _ _ ht ho hme ⟨_, placeVal_slot_keptC hA hK hD hR hlo hhi o16 (by omega), ?_⟩
    ⟨_, placeVal_slot_keptC hA hK hD hR hlo hhi o8 (by omega), ?_⟩
  · rw [lbl_l, hA16]
  · rw [lbl_me _ hl, h8]; exact congrArg some (hJ0 σe _ hj).symm

/-- **main's source placed at every node of `scc_rt_thread_reserve`**
(`reserveW_wf`'s `hpl`, `HMidP.res`'s placement half). -/
theorem reserveW_placed (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi) (hl : l ≠ mainTidLbl 2)
    (hJ0 : ∀ σe c, J0 σe c → σe.regs.rdi.toNat = tcb0 Λ) (nd : Spike.Lib.X64.Rt.Reserve.RN) :
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
    exact ⟨placed_res hR hlo hhi hl hJ0 hF (DFrame.refl _ _), fun _ h => h⟩
  cases nd <;> first | exact hB _ _ | exact hN _

end Res

/-! ## The second TCB -/

/-- **Every second-TCB node's control is the call's.** -/
theorem tcbN_ctl {lab : Label → Int64} {q : Spike.Lib.X64.Rt.TcbGG} :
    ∀ (i : Ret0.TN) (σ : AS) (c : Ctl), (Spike.Lib.X64.Rt.tcbNG lab q i).J σ c → c = q.c0 := by
  intro i σ c h; cases i <;> exact h.1

section Tcb

variable {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {c0 : Ctl} {cA m : BitVec 64}
  {fr : BitVec 64 × BitVec 64} {g : Ret0.AllocTcb.G}

set_option hygiene false in
/-- The second TCB's frame condition at the call (`WcSp3W.tcb`'s). -/
local notation "FT" => fun mm => F mm ∧ Ret0.CallerCells R (-72) (-184) 8 mm ∧
  TcbCtx (_root_.Executable.labels exe).label R (wcNCR (_root_.Executable.labels exe).label c0 cA m fr).J c0 g mm

/-- **Placed in the second TCB call** at a state whose memory is outside
the callee's region as at `m'` (a node's), with `FT m'`: the call's control
`c0` (at `boxTerm`, `o` at `l`) at main's slots, the box's cell `cA = b`
and main's word `m = tcb0`. -/
theorem placed_tcb (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi) (hl : l ≠ mainTidLbl 2) {ty : Ty}
    (ht : c0.term = boxTerm)
    (ho : TermRun.evalAt c0.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hme : TermRun.evalAt c0.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (hcA : cA.toNat = b) (hm : m.toNat = tcb0 Λ)
    {m' : MachineData} (hF : FT m') {s : State} (hD : DFrame (R.callee (-72) (-184) 8) m' s.st.1) :
    PlacedSE Λ (lblL Λ l b) s c0 [] := by
  obtain ⟨-, -, mC, σC, c, hA, ⟨⟨-, ⟨h16, h8, -⟩, -⟩, -⟩, -, hK⟩ := hF
  have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  have o8 : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  refine placedSE_boxAt _ _ ht ho hme ⟨_, placeVal_slot_keptC hA hK hD hR hlo hhi o16 (by omega), ?_⟩
    ⟨_, placeVal_slot_keptC hA hK hD hR hlo hhi o8 (by omega), ?_⟩
  · rw [lbl_l, h16, hcA]
  · rw [lbl_me _ hl, h8, hm]

/-- **main's source placed at every node of the second `scc_rt_alloc_tcb`**
(`tcbWG_wf`'s `hpl`, `HMidP.tcb`'s placement half), at every ghost it
quantifies (`MidG (QB l b)`, `FrMG J0`), `J0`'s `%rdi` main's `tcb0`. -/
theorem tcbWG_placed (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi) (hl : l ≠ mainTidLbl 2)
    (hJ0 : ∀ σe c, J0 σe c → σe.regs.rdi.toNat = tcb0 Λ)
    (hM : MidG (QB l b) c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m) (nd : Ret0.TN) :
    Spike.Lib.X64.Rt.TcbWG (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc
      (R.callee (-72) (-184) 8) FT (Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q g c0) nd := by
  obtain ⟨⟨l', A, ⟨e1, e2, ht, -, ho, hme⟩, hcA⟩, -, σe, ce, hj, -, hm⟩ := hM
  subst l'
  replace hcA : cA.toNat = b := e2 ▸ hcA
  have hm' : m.toNat = tcb0 Λ := by rw [hm]; exact hJ0 σe ce hj
  have hB : ∀ i blk, BlkW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc
      (R.callee (-72) (-184) 8) FT (Spike.Lib.X64.Rt.tcbNG (_root_.Executable.labels exe).label
        (Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q g c0) i) blk := by
    intro i blk s σ c _ _ _ _ _ hF hj _ _ m _ hD
    obtain rfl := tcbN_ctl i σ c hj
    exact ⟨placed_tcb (s := { s with st := (m, _) }) hR hlo hhi hl ht ho hme hcA hm' hF hD, fun _ h => h⟩
  have hN : ∀ i, NodeW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc
      (R.callee (-72) (-184) 8) FT (Spike.Lib.X64.Rt.tcbNG (_root_.Executable.labels exe).label
        (Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q g c0) i) := by
    rintro i s c ⟨-, -, -, -, σ, -, hF, hj⟩
    obtain rfl := tcbN_ctl i σ c hj
    exact ⟨placed_tcb hR hlo hhi hl ht ho hme hcA hm' hF (DFrame.refl _ _), fun _ h => h⟩
  cases nd <;> first | exact hB _ _ | exact hN _

end Tcb

/-- **The thread init's placement** (`hti_W`'s `hpl`, the slot form): at
the source `QB l b`, any state reading the box's cell `b` at main's slot
`-16` and main's id at `-8` places it (`l` fresh at the start). -/
theorem hti_placed {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {R : Region} (hl : L0T Λ l = none) :
    ∀ c0, (∃ l' A', QB l b l' A' c0) → ∀ s : State,
      placeVal (machine (kernel 1)) s (.slot (R.addr (-16)).toNat) = some b →
      placeVal (machine (kernel 1)) s (.slot (R.addr (-8)).toNat) = some (tcb0 Λ) →
      PlacedSE Λ (lblL Λ l b) s c0 [] := by
  rintro c0 ⟨l', A', -, -, ht, -, ho, hme⟩ s h16 h8
  exact placedSE_boxAt _ _ ht ho hme ⟨_, h16, lbl_l _ _ _⟩
    ⟨_, h8, lbl_me _ (Spike.Lib.X64.WakePh.PlacedLy.ne_of_fresh hl)⟩

end Spike.Lib.X64.WakePh.PlacedCal

/-- info: 'Spike.Lib.X64.WakePh.PlacedCal.placeVal_slot_keptC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedCal.placeVal_slot_keptC

/-- info: 'Spike.Lib.X64.WakePh.PlacedCal.reserveW_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedCal.reserveW_placed

/-- info: 'Spike.Lib.X64.WakePh.PlacedCal.tcbWG_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedCal.tcbWG_placed

/-- info: 'Spike.Lib.X64.WakePh.PlacedCal.hti_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedCal.hti_placed
