/-
**hello.w's `wc_worker` placed** (the `hz`, `hZE`, `hZC`, `hZW`, `hZU`
fields of `SegRP.WcObl` at `X := PlacedSE Λ lbl · · []`): every node of `wc_worker` (its prologue, its
`.0_entry` block, the call to `print`, the store's tail) and of the `unpark` it calls runs at a control reading
packet words (`Hello.PlacedZ`'s `placed_wcP`, `placed_wcR`, `placed_cS1`, `placed_cS2`) kept where the code
keeps them: the argument registers `x0`, `x2`..`x5` through the prologue (which writes only `x9`, `x10`, `sp`,
`x29` and the frame's cells), the frame's cells `-96`, `-80`, `-72`, `-64`, `-56` after the spills (the
`.0_entry` block writes only the cells `-48`..`-24`), `x0` and then the cell `-48` of `unpark`'s frame.

- `ArgR`, `keepA_*`, `proW_args` (the argument registers kept by a prologue; a prologue's states inside `W`
  from its entry's argument registers): in `A64HelloProArgs`, shared with `A64HelloPlacedZKid`.
- `keepE_slot`, `wkSl_keepW`: the packet's frame cells kept by the `.0_entry` block.
- `pR`, `pS`, `pT`: the packet's places (registers, frame cells, the tail's cells); `pkRep_pR`, `pkRep_pS`,
  `pkRep_pT`, `pkRep_one`: `PkRep` from their values.
- `wz_placed`, `wZE_placed`, `wZC_placed`, `wZW_placed`, `wZU_placed`: `WcObl`'s `hz`, `hZE`, `hZC`, `hZW`,
  `hZU` at `PlacedSE`.
-/
import Spike.Lib.A64HelloPlacedZEnv
import Spike.Lib.A64HelloWorkerSegRP
import Spike.Lib.A64HelloProArgs
import Spike.Lib.A64HelloWkTailNN
import Spike.Lib.A64WakeWorkerNNA

namespace Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Place WordPlace placeVal ValRep)
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.HelloSplit (wcP wcR)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ wcPs)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (cS1 cS2)
open Spike.Lib.A64WakeMainW (M1 placeVal_x placeVal_cell)
open Spike.Lib.A64Consumer (Lbl Placed)
open Spike.Lib.A64ConsumerS (PlacedSE)

/-! ## The `.0_entry` block keeps the packet's cells -/

section Entry

set_option linter.unusedSimpArgs false

variable {lab : Label → Int64}

/-- **The packet's frame cells kept by the `.0_entry` block** (its stores at `-48`..`-24`), the offsets
kept as well. -/
theorem keepE_slot (j : Int) (hj : j = -96 ∨ j = -80 ∨ j = -72 ∨ j = -64 ∨ j = -56) :
    ∀ d ∈ Body.wkE, ∀ pc σ, (dstep lab ⟨pc, ⟨-96, []⟩, σ⟩ d).so = ⟨-96, []⟩ ∧
      (dstep lab ⟨pc, ⟨-96, []⟩, σ⟩ d).σ.slot j = σ.slot j := by
  rintro d hd pc σ
  simp only [Body.wkE, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> dstep_keep <;>
    (try simp [Spike.Lib.upd_apply, Spike.Lib.rm, Spike.Lib.A64.Flow.regDst]) <;> (try rfl)

/-- **`wkSl` keeps the packet's frame cells.** -/
theorem wkSl_keepW (σ : AS) (j : Int) (hj : j = -96 ∨ j = -80 ∨ j = -72 ∨ j = -64 ∨ j = -56) :
    Body.wkSl σ j = σ.slot j := by
  have h := arun_take_slotO (lab := fun _ => 0) (blk := Body.wkE) ⟨-96, []⟩ j (keepE_slot j hj)
    Body.wkE.length 0 σ
  rw [List.take_length] at h
  exact h

end Entry

/-! ## The packet's places -/

section Places

variable {lbl : Lbl} {s : State} {w : Words} {w0 w1 w2 w3 w4 : TermRun.Word}

/-- The packet's registers at `wc_worker`'s entry: `x0`, `x2`, `x3`, `x4`, `x5`. -/
def pR : Nat → Place M1.I.RegId
  | 0 => .reg (.x XReg.X0.idx) | 1 => .reg (.x XReg.X2.idx) | 2 => .reg (.x XReg.X3.idx)
  | 3 => .reg (.x XReg.X4.idx) | _ => .reg (.x XReg.X5.idx)

/-- The packet's frame cells in `wc_worker`'s frame: `-96`, `-80`, `-72`, `-64`, `-56`. -/
def pS (R : Region) : Nat → Place M1.I.RegId
  | 0 => .slot (R.addr (-96)).toNat | 1 => .slot (R.addr (-80)).toNat | 2 => .slot (R.addr (-72)).toNat
  | 3 => .slot (R.addr (-64)).toNat | _ => .slot (R.addr (-56)).toNat

/-- The tail's cells of words `3`, `4`: `-64`, `-56`. -/
def pT (R : Region) : Nat → Place M1.I.RegId
  | 3 => .slot (R.addr (-64)).toNat | _ => .slot (R.addr (-56)).toNat

variable (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
  (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat)

include hv0 hv1 hv2 hv hvu in
/-- `PkRep` at the argument registers. -/
theorem pkRep_pR (h0 : (s.st.1.regs.getXReg .X0).toBitVec = w.w0) (h2 : (s.st.1.regs.getXReg .X2).toBitVec = w.w2)
    (h3 : (s.st.1.regs.getXReg .X3).toBitVec = w.w3) (h4 : (s.st.1.regs.getXReg .X4).toBitVec = w.w4)
    (h5 : (s.st.1.regs.getXReg .X5).toBitVec = w.w5) : PkRep lbl s pR (fun _ => True) w0 w1 w2 w3 w4 := by
  intro i wd _ hwd
  rcases i with _ | _ | _ | _ | _ | i <;> simp at hwd <;> subst hwd
  · exact ⟨_, (placeVal_x s .X0).trans (by rw [h0]), hv0⟩
  · exact ⟨_, (placeVal_x s .X2).trans (by rw [h2]), hv1⟩
  · exact ⟨_, (placeVal_x s .X3).trans (by rw [h3]), hv2⟩
  · exact ⟨_, (placeVal_x s .X4).trans (by rw [h4]), hv⟩
  · exact ⟨_, (placeVal_x s .X5).trans (by rw [h5]), hvu⟩

include hv0 hv1 hv2 hv hvu in
/-- `PkRep` at the frame's cells. -/
theorem pkRep_pS {R : Region} (h96 : placeVal M1 s (.slot (R.addr (-96)).toNat) = some w.w0.toNat)
    (h80 : placeVal M1 s (.slot (R.addr (-80)).toNat) = some w.w2.toNat)
    (h72 : placeVal M1 s (.slot (R.addr (-72)).toNat) = some w.w3.toNat)
    (h64 : placeVal M1 s (.slot (R.addr (-64)).toNat) = some w.w4.toNat)
    (h56 : placeVal M1 s (.slot (R.addr (-56)).toNat) = some w.w5.toNat) :
    PkRep lbl s (pS R) (fun _ => True) w0 w1 w2 w3 w4 := by
  intro i wd _ hwd
  rcases i with _ | _ | _ | _ | _ | i <;> simp at hwd <;> subst hwd
  · exact ⟨_, h96, hv0⟩
  · exact ⟨_, h80, hv1⟩
  · exact ⟨_, h72, hv2⟩
  · exact ⟨_, h64, hv⟩
  · exact ⟨_, h56, hvu⟩

include hv hvu in
/-- `PkRep` of words `3`, `4` at the tail's cells. -/
theorem pkRep_pT {R : Region} (h64 : placeVal M1 s (.slot (R.addr (-64)).toNat) = some w.w4.toNat)
    (h56 : placeVal M1 s (.slot (R.addr (-56)).toNat) = some w.w5.toNat) :
    PkRep lbl s (pT R) (fun i => 3 ≤ i) w0 w1 w2 w3 w4 := by
  intro i wd hi hwd
  rcases i with _ | _ | _ | _ | _ | i
  all_goals first | omega | simp at hwd
  · subst hwd; exact ⟨_, h64, hv⟩
  · subst hwd; exact ⟨_, h56, hvu⟩

include hvu in
/-- `PkRep` of word `4` at one place. -/
theorem pkRep_one {p : Place M1.I.RegId} (hp : placeVal M1 s p = some w.w5.toNat) :
    PkRep lbl s (fun _ => p) (fun i => i = 4) w0 w1 w2 w3 w4 := by
  intro i wd hi hwd
  subst hi; simp at hwd; subst hwd; exact ⟨_, hp, hvu⟩

end Places

/-! ## `WcObl`'s fields -/

section Nodes

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R' : Region}
  {F' : MachineData → Prop} {x29 ra : BitVec 64} {w : Words} {tp sp0 : BitVec 64}
  {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}

/-- **`WcObl.hz` at `PlacedSE`**: the prologue's states at `wcP`, the packet in the argument registers. -/
theorem wz_placed {ms : List TermRun.Frame → MemSide isaLSE2} (_hlo : R'.lo ≤ -192) (_hhi : 0 ≤ R'.hi)
    (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
    (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ProW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R' F' (ms [])
      ((_root_.Executable.labels exe).label "wc_worker") 96 8 ".L20_wc_worker.stack_grow" wcPs
      (fun σ c => wcJE (wcP w0 w1 w2 w3 w4) w x29 ra tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec) := by
  refine proW_args fun σ c hJ s hs => ?_
  obtain ⟨⟨rfl, h0, -, h2, h3, h4, h5, -⟩, -⟩ := hJ
  refine placedSE_nil (placed_wcP (A := fun _ => True) (fun _ _ => trivial)
    (pkRep_pR hv0 hv1 hv2 hv hvu ?_ ?_ ?_ ?_ ?_))
  · rw [hs .X0 (by simp [ArgR])]; exact h0
  · rw [hs .X2 (by simp [ArgR])]; exact h2
  · rw [hs .X3 (by simp [ArgR])]; exact h3
  · rw [hs .X4 (by simp [ArgR])]; exact h4
  · rw [hs .X5 (by simp [ArgR])]; exact h5

/-- **`WcObl.hZE` at `PlacedSE`**: the `.0_entry` block's states at `wcP`, the packet in the frame's cells. -/
theorem wZE_placed (hlo : R'.lo ≤ -192) (hhi : 0 ≤ R'.hi)
    (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
    (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R' F'
      (Body.wN (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (fun _ => PrW w0 w2 n m) .e) Body.wkE := by
  intro s σ c _ _ _ _ _ _ hJ k _ m' hA' _
  obtain ⟨rfl, h96, -, h80, h72, h64, h56, -⟩ := hJ
  have tk : ∀ j, (j = -96 ∨ j = -80 ∨ j = -72 ∨ j = -64 ∨ j = -56) → R'.Off j →
      placeVal M1 { s with st := (m', (Body.wN (_root_.Executable.labels exe).label
        (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp) (fun _ => PrW w0 w2 n m) .e).pc + Int64.ofNat (4 * k)) }
        (.slot (R'.addr j).toNat) = some (σ.slot j).toNat := by
    intro j hj hR
    erw [placeVal_cell hA' hR _ rfl, arun_take_slotO (blk := Body.wkE) ⟨-96, []⟩ j (keepE_slot j hj) k]
  refine ⟨placedSE_nil (placed_wcP (A := fun _ => True) (fun _ _ => trivial)
    (pkRep_pS (R := R') hv0 hv1 hv2 hv hvu ?_ ?_ ?_ ?_ ?_)), fun _ h => h⟩
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h96]
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h80]
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h72]
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h64]
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h56]

/-- **`WcObl.hZC` at `PlacedSE`**: the call node's states at `wcP` (`KcW`), the packet in the frame's cells
the `.0_entry` block keeps (`wkSl_keepW`). -/
theorem wZC_placed (hlo : R'.lo ≤ -192) (hhi : 0 ≤ R'.hi)
    (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
    (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R' F'
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)) := by
  rintro s c ⟨-, -, -, -, σ, hA, -, ⟨σ0, c0, hJ0, rfl⟩, hK⟩
  obtain ⟨rfl, -⟩ := hK
  obtain ⟨-, h96, -, h80, h72, h64, h56, -⟩ := hJ0
  have tk : ∀ j, (j = -96 ∨ j = -80 ∨ j = -72 ∨ j = -64 ∨ j = -56) → R'.Off j →
      placeVal M1 s (.slot (R'.addr j).toNat) = some (σ0.slot j).toNat := by
    intro j hj hR
    rw [placeVal_cell hA hR _ rfl, Body.wkC_eq, Body.wkSl_eq, wkSl_keepW _ j hj]
  refine ⟨placedSE_nil (placed_wcP (A := fun _ => True) (fun _ _ => trivial)
    (pkRep_pS (R := R') hv0 hv1 hv2 hv hvu ?_ ?_ ?_ ?_ ?_)), fun _ h => h⟩
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h96]
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h80]
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h72]
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h64]
  · rw [tk _ (by simp) ⟨by decide, by omega, by omega⟩, h56]

/-- **`WcObl.hZW` at `PlacedSE`**: the store's tail at `wcR`, `cS1` (words `3`, `4` in the cells `-64`, `-56`),
then `cS2` (reading nothing). -/
theorem wZW_placed (hlo : R'.lo ≤ -192) (hhi : 0 ≤ R'.hi) (hv : ValRep lbl w3.val w.w4.toNat)
    (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ i, NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R' F'
      (HelloTail.N (_root_.Executable.labels exe).label (wcR w0 w1 w2 w3 w4) (cS1 w0 w1 w2 w3 w4)
        (cS2 w0 w1 w2 w3 w4) w.w4 w.w5 x29 ra tp i) (HelloTail.blkN i) := by
  have hR64 : R'.Off (-64) := ⟨by decide, by omega, by omega⟩
  have hR56 : R'.Off (-56) := ⟨by decide, by omega, by omega⟩
  intro i
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k _ m' hA' _
    obtain ⟨rfl, -, -, h64, h56, -⟩ := hJ
    refine ⟨placedSE_nil (placed_wcR (A := fun i => 3 ≤ i) (by decide) (by decide)
      (pkRep_pT (R := R') hv hvu ?_ ?_)), fun _ h => h⟩
    · rw [placeVal_cell hA' hR64 _ rfl,
        arun_take_slot (-64) (by keep_blk [HelloTail.blkN, HelloTail.b0]) k, h64]
    · rw [placeVal_cell hA' hR56 _ rfl,
        arun_take_slot (-56) (by keep_blk [HelloTail.blkN, HelloTail.b0]) k, h56]
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨⟨rfl, -, -, h64, h56, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [HelloTail.blkN] using hk
    refine ⟨placedSE_nil (placed_wcR (A := fun i => 3 ≤ i) (by decide) (by decide)
      (pkRep_pT (R := R') hv hvu ?_ ?_)), fun _ h => h⟩
    · rw [placeVal_cell hA' hR64 _ rfl]; exact congrArg _ (congrArg _ h64)
    · rw [placeVal_cell hA' hR56 _ rfl]; exact congrArg _ (congrArg _ h56)
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨rfl, -, -, -, h56, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [HelloTail.blkN, HelloTail.b1] using hk
    refine ⟨placedSE_nil (placed_cS1 (A := fun i => i = 4) rfl (pkRep_one (p := .slot (R'.addr (-56)).toNat) hvu ?_)),
      fun _ h => h⟩
    rw [placeVal_cell hA' hR56 _ rfl]; exact congrArg _ (congrArg _ h56)
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨⟨rfl, -, -, -, h56, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [HelloTail.blkN, HelloTail.b2] using hk
    refine ⟨placedSE_nil (placed_cS1 (A := fun i => i = 4) rfl (pkRep_one (p := .slot (R'.addr (-56)).toNat) hvu ?_)),
      fun _ h => h⟩
    rw [placeVal_cell hA' hR56 _ rfl]; exact congrArg _ (congrArg _ h56)
  · exact fun _ _ _ _ _ _ _ _ _ _ k hk => absurd hk (by simp [HelloTail.blkN])
  · intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
    obtain ⟨rfl, -⟩ := hJ
    exact ⟨placedSE_nil placed_cS2, fun _ h => h⟩

/-- **`WcObl.hZU` at `PlacedSE`**: `unpark`'s nodes at `cS1` (word `4` in `x0` at entry, in the cell `-48`
after the spill), then `cS2`. -/
theorem wZU_placed (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ (R'' : Region) (F'' : MachineData → Prop), R''.OK → R''.base.toNat % 16 = 0 → R''.lo ≤ -48 →
      0 ≤ R''.hi → FStable R'' F'' → (∀ m, F'' m → F' m) → ∀ x29' ra',
      Int64.ofBitVec ra' = (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" → ∀ i,
      NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R'' F''
        (Unpark.N (_root_.Executable.labels exe).label (cS1 w0 w1 w2 w3 w4) (cS2 w0 w1 w2 w3 w4) w.w5 x29' ra' tp i)
        (Unpark.blkN i) := by
  intro R'' F'' _ _ hlo hhi _ _ x29' ra' _ i
  have hR : R''.Off (-48) := ⟨by decide, hlo, by omega⟩
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k _ m' hA' _
    obtain ⟨rfl, h0, -⟩ := hJ
    refine ⟨placedSE_nil (placed_cS1 (A := fun i => i = 4) rfl
      (pkRep_one (p := .reg (.x XReg.X0.idx)) hvu ?_)), fun _ h => h⟩
    rw [placeVal_x]; show some (m'.regs.getXReg .X0).toBitVec.toNat = _
    rw [hA'.regs, arun_take_reg .X0 (by keep_blk [Unpark.blkN, Unpark.b0]) k]
    exact congrArg _ (congrArg _ h0)
  · intro s σ c _ _ _ _ _ _ hJ k _ m' hA' _
    obtain ⟨rfl, -, -, h48, -⟩ := hJ
    refine ⟨placedSE_nil (placed_cS1 (A := fun i => i = 4) rfl
      (pkRep_one (p := .slot (R''.addr (-48)).toNat) hvu ?_)), fun _ h => h⟩
    rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-48) (by keep_blk [Unpark.blkN, Unpark.b1]) k, h48]
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨⟨rfl, -, -, h48, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [Unpark.blkN] using hk
    refine ⟨placedSE_nil (placed_cS1 (A := fun i => i = 4) rfl
      (pkRep_one (p := .slot (R''.addr (-48)).toNat) hvu ?_)), fun _ h => h⟩
    rw [placeVal_cell hA' hR _ rfl]; exact congrArg _ (congrArg _ h48)
  all_goals
    intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
    first | obtain ⟨rfl, -⟩ := hJ | obtain ⟨⟨rfl, -⟩, -⟩ := hJ
    exact ⟨placedSE_nil placed_cS2, fun _ h => h⟩

end Nodes

end Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepE_slot' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepE_slot

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wkSl_keepW' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wkSl_keepW

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_pR' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_pR

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_pS' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_pS

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_pT' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_pT

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_one' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_one

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wz_placed' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wz_placed

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wZE_placed' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wZE_placed

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wZC_placed' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wZC_placed

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wZW_placed' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wZW_placed

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wZU_placed' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.wZU_placed
