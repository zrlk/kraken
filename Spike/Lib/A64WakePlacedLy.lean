/-
**`wc_main`'s source placed past the box's store** (AArch64; the `PlacedSE`
half of `HMidP.wcWf`): at every node of `WcMainW` from the fence to the
clone's arguments, main's source is placed (`PlacedSE`) under the labels
`upd (L0T Λ) l b` (`l` at `b`, main's id at `tcb0 Λ`), its words in main's
frame slots `-72` (the box's cell) and `-80` (main's `ThreadId`).

- `lbl_l`, `lbl_me`: the labels at `l` and at main's id (`l ≠ mainTidLbl 2`).
- `keeps_main`: `wc_main`'s blocks past the box keep slots `-72`, `-80`.
- `blkW_slots`, `nodeW_slots`: the generic block/node instance from a node
  invariant pinning `SpawnSrc l` and the two slots' labels.
- `placedSE_boxAt`: at `boxTerm` (`QB`'s facts), `o` and `me` at any two places.
- `f_placed` (at `rNQ … (QB l b) .f`), `bl_placed` (`rN … (SB l b) .bl`):
  the reserve segment's nodes; `wcJ`'s saved `x0` is `J0`'s, main's id by
  `hJ0` (`BoxPure`'s, `boxPure_slots`).
- `mid_placed`: `.sp3` to the clone's arguments at every ghost with
  `MidG (SB l b) c0 cA` and `FrMG J0 fr m` (the strengthened guard).
- `placed_of_box`: all three at `Box`'s ghosts (`BoxPure`, `L0T Λ l = none`);
  `wcMainW_placed`: as `WcMainW … J0 (SB l b) (QB l b)` (`HMidP.wcWf`'s shape).
- `placed_at_box`: non-vacuity at `h0`'s `Box` (its ghosts meet `BoxPure`; the
  box's own state placed).

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeHMid
import Spike.Lib.A64WakeSrcCtl

namespace Spike.Lib.A64.WakePh.PlacedLy

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (rN rNQ bX MidG FrMG boxTerm resB aN bN j3 wcJ wFr WcMainW)
open Spike.Lib.A64.WakePh.WcSp4 (FrW wcNI sp4A initCall sp6A cloneArgs)
open Spike.Lib.A64.WakePh.Tcb2Call (oW wcN3 tcb2Call)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.WakeBoxW (SpawnSrc)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.WakeLoadT (L0T tcb0)
open Spike.Lib.WakeHMid (BoxPure QB SB)
open Spike.Lib.WakeSrcCtl (keepsSlot arun_slot_keep placeVal_slot_abs placedSE_spawnAt placedSE_of_tbl rep_at)

/-- The labels past the box: `l` at `b` over the start's (`L0T`). -/
abbrev lblL (Λ : Scc.Sem.Layout) (l : WeakMem.AllocLabel) (b : Nat) : Lbl := A64ConsumerA.upd (L0T Λ) l b

theorem lbl_l (Λ : Scc.Sem.Layout) (l : WeakMem.AllocLabel) (b : Nat) : lblL Λ l b l = some b := by
  simp [A64ConsumerA.upd]

theorem lbl_me {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} (b : Nat) (hl : l ≠ mainTidLbl 2) :
    lblL Λ l b (mainTidLbl 2) = some (tcb0 Λ) := by
  simp [A64ConsumerA.upd, Ne.symm hl, L0T]

/-- A label fresh at the start (`h1`'s `hl`) is not main's id. -/
theorem ne_of_fresh {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} (hl : L0T Λ l = none) : l ≠ mainTidLbl 2 := by
  rintro rfl; simp [L0T, A64ConsumerA.upd] at hl

/-- **`BoxPure`'s facts this file takes**: main's slots in `R`, `J0`'s `x0`
main's id. -/
theorem boxPure_slots {L : Spike.Lib.A64.Rt.RuntimeLayout} {F0 : MachineData → Prop} {n : Nat} {R : Region}
    {F : MachineData → Prop} {J0 : Flow.AS → Ctl → Prop} {t : UInt64} (h : BoxPure L F0 n R F J0 t) :
    R.lo ≤ -80 ∧ 0 ≤ R.hi ∧ ∀ σe c, J0 σe c → σe.regs.X0.toNat = tcb0 L.Λ := by
  obtain ⟨⟨-, -, -, hlo, hhi, -, -⟩, -, -, ⟨-, hx0, -⟩, -⟩ := h
  exact ⟨by omega, hhi, hx0⟩

/-- `wc_main`'s blocks past the box keep main's slots `-72`, `-80`. -/
theorem keeps_main : ∀ blk ∈ [tcb2Call, sp4A, initCall, sp6A, cloneArgs, resB],
    keepsSlot (-72) oW blk = true ∧ keepsSlot (-80) oW blk = true := by
  decide +kernel

section Gen

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {n : ND}

set_option hygiene false in
/-- A node invariant pinning the source at `SpawnSrc l` and main's slots'
labels. -/
local notation "HS" => ∀ σ c, n.J σ c → SpawnSrc l c ∧ lbl l = some (σ.slot (-72)).toNat ∧
  lbl (mainTidLbl 2) = some (σ.slot (-80)).toNat

/-- **Placed on a block keeping main's slots**. -/
theorem blkW_slots {blk : List Directive} (h72 : R.Off (-72)) (h80 : R.Off (-80)) (hJ : HS)
    (hk : keepsSlot (-72) n.o blk = true ∧ keepsSlot (-80) n.o blk = true) :
    BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hj k _ m hA _
  obtain ⟨hsrc, h1, h2⟩ := hJ σ c hj
  refine ⟨placedSE_spawnAt (.slot (R.addr (-72)).toNat) (.slot (R.addr (-80)).toNat) hsrc
    ⟨_, placeVal_slot_abs hA h72, ?_⟩ ⟨_, placeVal_slot_abs hA h80, ?_⟩, fun _ h => h⟩
  · rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k hk.1]; exact h1
  · rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k hk.2]; exact h2

/-- **Placed at a node**. -/
theorem nodeW_slots (h72 : R.Off (-72)) (h80 : R.Off (-80)) (hJ : HS) :
    NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, hA, -, hj⟩
  obtain ⟨hsrc, h1, h2⟩ := hJ σ c hj
  exact ⟨placedSE_spawnAt _ _ hsrc ⟨_, placeVal_slot_abs hA h72, h1⟩ ⟨_, placeVal_slot_abs hA h80, h2⟩,
    fun _ h => h⟩

/-- `HS` from the frame's words `FrW cA m fr` at the source `c0`. -/
theorem hs_of_frW {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hmid : SpawnSrc l c0 ∧ lbl l = some cA.toNat ∧ lbl (mainTidLbl 2) = some m.toNat)
    (hJF : ∀ σ c, n.J σ c → c = c0 ∧ FrW cA m fr σ) : HS := by
  intro σ c hj
  obtain ⟨rfl, h1, h2, -, -⟩ := hJF σ c hj
  exact ⟨hmid.1, by rw [h1]; exact hmid.2.1, by rw [h2]; exact hmid.2.2⟩

end Gen

/-- **main's source at the box placed at any two places**: `o` at `po`,
`me` at `pm`, given `lbl` puts `l` at `po`'s word and main's id at `pm`'s. -/
theorem placedSE_boxAt {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l : WeakMem.AllocLabel}
    (po pm : Place (machine (kernel 1)).I.RegId) (ht : c.term = boxTerm)
    (ho : TermRun.evalAt c.env (.var "o") = some (.ptr .own .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hme : TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (h9 : ∃ v, placeVal (machine (kernel 1)) s po = some v ∧ lbl l = some v)
    (h10 : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s c [] := by
  simp only [TermRun.evalAt] at ho hme
  refine placedSE_of_tbl [("o", [.one po]), ("me", [.one pm])] ?_ ?_ ?_
  · intro x hx ty ws hl
    rw [ht, show exprFv boxTerm = ["o", "me"] by decide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [ho] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hme] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty ws hpl hl k wp wd hwp hwd
    by_cases eo : x = "o"
    · subst eo; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [ho] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h9
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      rw [hme] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h10
    · simp [List.lookup, beq_false_of_ne eo, beq_false_of_ne em] at hpl
  · intro x pls k n hpl hn'
    by_cases eo : x = "o"
    · subst eo; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    · simp [List.lookup, beq_false_of_ne eo, beq_false_of_ne em] at hpl

section Ly

variable {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {lab : Label → Int64} {J0 : Flow.AS → Ctl → Prop}
  (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hl : l ≠ mainTidLbl 2)
  (hJ0 : ∀ σe c, J0 σe c → σe.regs.X0.toNat = tcb0 Λ)
include hlo hhi hl hJ0

/-- **Placed at the fence** (`rNQ`'s, the box's facts `QB l b`): `o` at slot
`-72` (`bX`'s cell `b`), `me` at slot `-80` (`wcJ`'s saved `x0`). -/
theorem f_placed : NodeW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc R F
    (rNQ ms lab J0 (SB l b) (QB l b) .f) := by
  rintro s c ⟨-, -, -, -, σ, hA, -, l', A, ⟨q, ⟨σe, hj, -, -, h80⟩, h72, -⟩, e1, e2, ht, -, ho, hme⟩
  subst e1
  refine ⟨placedSE_boxAt (.slot (R.addr (-72)).toNat) (.slot (R.addr (-80)).toNat) ht ho hme
    ⟨_, placeVal_slot_abs hA ⟨by decide, by omega, by omega⟩, ?_⟩
    ⟨_, placeVal_slot_abs hA ⟨by decide, by omega, by omega⟩, ?_⟩, fun _ h => h⟩
  · rw [lbl_l]; exact congrArg some (by omega)
  · rw [lbl_me _ hl, h80]; exact congrArg some (hJ0 σe _ hj).symm

/-- **Placed on the reserve's call block** (`rN`'s `.bl` at `SB l b`). -/
theorem bl_placed : BlkW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc R F
    (rN ms lab J0 (SB l b) .bl) resB :=
  blkW_slots (l := l) ⟨by decide, by omega, by omega⟩ ⟨by decide, by omega, by omega⟩
    (by
      rintro σ c ⟨l', A, ⟨e1, e2, hs⟩, q, ⟨σe, hj, -, -, h80⟩, h72⟩
      subst e1
      exact ⟨hs, by rw [lbl_l]; exact congrArg some (by omega), by rw [lbl_me _ hl, h80]; exact congrArg some (hJ0 σe _ hj).symm⟩)
    (keeps_main resB (by simp))

/-- **Placed from `.sp3` to the clone's arguments** at a ghost with the
strengthened guard (`MidG (SB l b) c0 cA`, `FrMG J0 fr m`): `WcMainW`'s
`sp3`, `n4`, `n4s`, `n5`, `nI`, `n6`, `n6f`, `n6a` (any `F`, so `F₂`'s too). -/
theorem mid_placed {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hG : MidG (SB l b) c0 cA) (hM : FrMG J0 fr m) :
    let W := fun s c => PlacedSE Λ (lblL Λ l b) s c []
    BlkW W (fun _ _ => False) exe endPc R F (wcN3 lab (j3 cA m fr) c0) tcb2Call ∧
    BlkW W (fun _ _ => False) exe endPc R F (aN lab c0 t cA m fr .n4) sp4A ∧
    NodeW W (fun _ _ => False) exe endPc R F (aN lab c0 t cA m fr .n4s) ∧
    BlkW W (fun _ _ => False) exe endPc R F (aN lab c0 t cA m fr .n5) initCall ∧
    NodeW W (fun _ _ => False) exe endPc R F (wcNI lab c0 t cA m fr) ∧
    BlkW W (fun _ _ => False) exe endPc R F (bN lab c0 t cA m fr .n6) sp6A ∧
    NodeW W (fun _ _ => False) exe endPc R F (bN lab c0 t cA m fr .n6f) ∧
    BlkW W (fun _ _ => False) exe endPc R F (bN lab c0 t cA m fr .n6a) cloneArgs := by
  have hmid : SpawnSrc l c0 ∧ lblL Λ l b l = some cA.toNat ∧
      lblL Λ l b (mainTidLbl 2) = some m.toNat := by
    obtain ⟨l', A, ⟨e1, e2, hs⟩, hA⟩ := hG
    subst e1
    obtain ⟨σe, c, hj, -, rfl⟩ := hM
    exact ⟨hs, by rw [lbl_l]; exact congrArg some (by omega), by rw [lbl_me _ hl]; exact congrArg some (hJ0 σe c hj).symm⟩
  have h72 : R.Off (-72) := ⟨by decide, by omega, by omega⟩
  have h80 : R.Off (-80) := ⟨by decide, by omega, by omega⟩
  refine ⟨blkW_slots h72 h80 (hs_of_frW hmid fun _ _ h => ⟨h.1, h.2.2⟩) (keeps_main _ (by simp)),
    blkW_slots h72 h80 (hs_of_frW hmid fun _ _ h => ⟨h.1.1, h.1.2.2⟩) (keeps_main _ (by simp)),
    nodeW_slots h72 h80 (hs_of_frW hmid fun _ _ h => ⟨h.1.1, h.1.2.2.2.2⟩),
    blkW_slots h72 h80 (hs_of_frW hmid fun _ _ h => ⟨h.1, h.2.2⟩) (keeps_main _ (by simp)),
    nodeW_slots h72 h80 (hs_of_frW hmid fun _ _ h => ⟨h.1, h.2.2.2.2⟩),
    blkW_slots h72 h80 (hs_of_frW hmid fun _ _ h => ⟨h.1, h.2.2.2⟩) (keeps_main _ (by simp)),
    nodeW_slots h72 h80 (hs_of_frW hmid fun _ _ h => ⟨h.1, h.2.2.2.2⟩),
    blkW_slots h72 h80 (hs_of_frW hmid fun _ _ h => ⟨h.1, h.2.2.2.2⟩) (keeps_main _ (by simp))⟩

end Ly

/-- **The reserve segment and `.sp3` to the clone's arguments placed at
`Box`'s ghosts** (`BoxPure`, `l` fresh at the start): the premises of
`f_placed`, `bl_placed`, `mid_placed` discharged. -/
theorem placed_of_box {L : Spike.Lib.A64.Rt.RuntimeLayout} {F0 : MachineData → Prop} {n : Nat} {R : Region}
    {F : MachineData → Prop} {J0 : Flow.AS → Ctl → Prop} {t : UInt64} {l : WeakMem.AllocLabel} {b : Nat}
    {exe : _root_.Executable} {endPc : Int64} {ms : MemSide isaLSE2} {lab : Label → Int64}
    (hB : BoxPure L F0 n R F J0 t) (hl : L0T L.Λ l = none) :
    NodeW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F
      (rNQ ms lab J0 (SB l b) (QB l b) .f) ∧
    BlkW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F
      (rN ms lab J0 (SB l b) .bl) resB ∧
    ∀ (F' : MachineData → Prop) c0 t' cA m fr, MidG (SB l b) c0 cA → FrMG J0 fr m →
      BlkW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F'
        (wcN3 lab (j3 cA m fr) c0) tcb2Call ∧
      BlkW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F'
        (aN lab c0 t' cA m fr .n4) sp4A ∧
      NodeW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F'
        (aN lab c0 t' cA m fr .n4s) ∧
      BlkW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F'
        (aN lab c0 t' cA m fr .n5) initCall ∧
      NodeW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F'
        (wcNI lab c0 t' cA m fr) ∧
      BlkW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F'
        (bN lab c0 t' cA m fr .n6) sp6A ∧
      NodeW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F'
        (bN lab c0 t' cA m fr .n6f) ∧
      BlkW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F'
        (bN lab c0 t' cA m fr .n6a) cloneArgs := by
  obtain ⟨hlo, hhi, hJ0⟩ := boxPure_slots hB
  exact ⟨f_placed hlo hhi (ne_of_fresh hl) hJ0, bl_placed hlo hhi (ne_of_fresh hl) hJ0,
    fun _ _ _ _ _ _ hG hM => mid_placed hlo hhi (ne_of_fresh hl) hJ0 hG hM⟩

/-- **`WcMainW` placed** (the `PlacedSE` half of `HMidP.wcWf`): every node
at `Box`'s ghosts, `S := SB l b`, `Q := QB l b`. -/
theorem wcMainW_placed {L : Spike.Lib.A64.Rt.RuntimeLayout} {F0 : MachineData → Prop} {n : Nat} {R : Region}
    {F F₂ : MachineData → Prop} {J0 : Flow.AS → Ctl → Prop} {t : UInt64} {l : WeakMem.AllocLabel} {b : Nat}
    {exe : _root_.Executable} {endPc : Int64} {ms : MemSide isaLSE2}
    (hB : BoxPure L F0 n R F J0 t) (hl : L0T L.Λ l = none) :
    WcMainW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F F₂ ms J0
      (SB l b) (QB l b) := by
  have h := placed_of_box (exe := exe) (endPc := endPc) (ms := ms) (b := b)
    (lab := (_root_.Executable.labels exe).label) hB hl
  have hm := fun F' c0 cA m fr (g : MidG (SB l b) c0 cA ∧ WakeWc.FrG J0 fr ∧ FrMG J0 fr m) =>
    h.2.2 F' c0 (WakeWc.t2 (_root_.Executable.labels exe).label) cA m fr g.1 g.2.2
  exact ⟨h.1, h.2.1, fun _ _ _ _ g => (hm F _ _ _ _ g).1, fun _ _ _ _ g => (hm F _ _ _ _ g).2.1,
    fun _ _ _ _ g => (hm F _ _ _ _ g).2.2.1, fun _ _ _ _ g => (hm F _ _ _ _ g).2.2.2.1,
    fun _ _ _ _ g => (hm F _ _ _ _ g).2.2.2.2.1, fun _ _ _ _ g => (hm F₂ _ _ _ _ g).2.2.2.2.2.1,
    fun _ _ _ _ g => (hm F₂ _ _ _ _ g).2.2.2.2.2.2.1, fun _ _ _ _ g => (hm F₂ _ _ _ _ g).2.2.2.2.2.2.2⟩

/-- **Non-vacuity at the real box** (`h0`'s `Box` at wake.w's landing, `l`
fresh at the start, as `hB_box` takes it): `Box`'s ghosts meet `BoxPure`, so
`wcMainW_placed` applies there, and the box's own state is placed (it is
`f_placed`'s node: `bX` at `l`, `b` and `QB l b`'s facts). -/
theorem placed_at_box {L : Spike.Lib.A64.Rt.RuntimeLayout} {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl} (hBx : WakeWc.Box L ms0 F0 l b n s c)
    (hl : L0T L.Λ l = none) :
    PlacedSE L.Λ (lblL L.Λ l b) s c [] ∧ ∃ R F J0 t, BoxPure L F0 n R F J0 t ∧
      ∀ F₂ : MachineData → Prop, WcMainW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False)
        L.exe L.endPc R F F₂ ms0 J0 (SB l b) (QB l b) := by
  obtain ⟨R, F, J0, t, h1, h2, h3, h4, ⟨⟨he, hn, hd, hpc, σ, hA, hF, hj⟩, -, ht⟩, hn1, ⟨htm, hh, ho, hme⟩, -, h5⟩ :=
    hBx
  have hB : BoxPure L F0 n R F J0 t := ⟨h1, h2, h3, h4, ht, hn1, h5⟩
  refine ⟨(wcMainW_placed (F₂ := F) (ms := ms0) hB hl).f s c
    ⟨he, hn, hd, hpc, σ, hA, hF, l, b, hj, rfl, rfl, htm, hh, ho, hme⟩ |>.1,
    R, F, J0, t, hB, fun _ => wcMainW_placed hB hl⟩

end Spike.Lib.A64.WakePh.PlacedLy

/-- info: 'Spike.Lib.A64.WakePh.PlacedLy.keeps_main' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedLy.keeps_main

/-- info: 'Spike.Lib.A64.WakePh.PlacedLy.f_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedLy.f_placed

/-- info: 'Spike.Lib.A64.WakePh.PlacedLy.bl_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedLy.bl_placed

/-- info: 'Spike.Lib.A64.WakePh.PlacedLy.mid_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedLy.mid_placed

/-- info: 'Spike.Lib.A64.WakePh.PlacedLy.placed_of_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedLy.placed_of_box

/-- info: 'Spike.Lib.A64.WakePh.PlacedLy.wcMainW_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedLy.wcMainW_placed

/-- info: 'Spike.Lib.A64.WakePh.PlacedLy.placed_at_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedLy.placed_at_box
