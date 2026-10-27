/-
**A block's states placed** (x86-64; the twin of
`Spike/Lib/LowerA64/PlacedBlk.lean`): `PlacedS` at every state of a block
node (`BlkW`) and of a node (`NodeW`), `W2Part`'s placement
(`Spike/Lib/LowerX64/W2Blk.lean`), from the node invariant's placement of
its control (`SlotRepAt`, `Spike/Lib/SlotRepAt.lean`) in the abstract slot
file and the suspended frames placed under the frame condition.

Before the last instruction of a construct's block nothing writes a slot
(the destination's store, a `callq`'s push end it), so the abstract slot
file at each state of the block is the node's (`arun_slot_noSlotWr`), and
the region's cells hold it (`Abs.slot`).

- `AI.slotWr`, `noSlotWr`: the instructions writing a slot (`st`, `push`,
  `call`), a block without one;
- `arun_slot_noSlotWr`, `noSlotWr_take`: the slot file kept along a block
  without one, and along every proper prefix of a block whose last
  instruction alone may write one;
- `blkW_placedS`, `nodeW_placedS`: the states placed;
- `placedS_of_abs_upd`, `blkW_placedS_upd`: at a pending store, the slot
  file updated to a register's word (that slot's words at the register).
-/
import Spike.Lib.LowerX64.W2Blk
import Spike.Lib.X64PlacedSlot

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib (Region)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (NodeW BlkW ND At AI AM arun dstep classify Abs DFrame FStable)
open Spike.Lib.LowerNode (SlotRepAt)

/-! ## Slot writes -/

/-- **The instructions writing a slot**: a store, a push, a call (its
return address). -/
def _root_.Spike.Lib.X64.AI.slotWr : AI → Bool
  | .st .. | .push _ | .call _ => true
  | _ => false

/-- **A block writing no slot.** -/
def noSlotWr (blk : List (Directive × Nat)) : Bool :=
  blk.all fun d => match classify d.1 with
    | some a => !a.slotWr
    | none => true

/-- **An instruction writing no slot keeps the slot file.** -/
theorem _root_.Spike.Lib.X64.AI.step_slot {a : AI} (h : a.slotWr = false) (o : Spike.Lib.X64.SO) (fall : Int64)
    (σ : Spike.Lib.X64.AS) : (a.step o fall σ).slot = σ.slot := by
  cases a <;> first | rfl | cases h

/-- **A block writing no slot keeps the slot file.** -/
theorem arun_slot_noSlotWr (lab : String → Int64) :
    ∀ {blk : List (Directive × Nat)} {am : AM}, noSlotWr blk = true → (arun lab blk am).σ.slot = am.σ.slot
  | [], _, _ => rfl
  | (d, z) :: ds, am, h => by
    simp only [noSlotWr, List.all_cons, Bool.and_eq_true] at h
    show (arun lab ds (dstep lab am (d, z))).σ.slot = am.σ.slot
    rw [arun_slot_noSlotWr lab (am := dstep lab am (d, z)) h.2]
    simp only [dstep]
    split
    · next a ha =>
      rw [ha] at h
      exact AI.step_slot (by simpa using h.1) _ _ _
    · rfl

/-- **Every proper prefix of a block writes no slot** when its last
instruction alone may. -/
theorem noSlotWr_take {blk : List (Directive × Nat)} (h : noSlotWr blk.dropLast = true) {k : Nat}
    (hk : k < blk.length) : noSlotWr (blk.take k) = true := by
  have he : blk.take k = blk.dropLast.take k := by
    rw [List.dropLast_eq_take, List.take_take]
    congr 1
    omega
  rw [he]
  simp only [noSlotWr, List.all_eq_true] at h ⊢
  exact fun x hx => h x (List.mem_of_mem_take hx)

/-! ## The states placed -/

section Placed

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {Λ : Scc.Sem.Layout} {lbl : Lbl} {rs : Scc.IR.Reg → Option Int} {fs : List TermRun.Frame}
  {B : Nat → Prop}

/-- **A state whose region's cells hold the slot file `sl` is placed** at
a control `SlotRepAt` places in `sl` (every slot a cell of the region,
`hrs`), the suspended frames placed under the frame condition (`hfp`). -/
theorem placedS_of_abs {s : State} {o : Spike.Lib.X64.SO} {σ : Spike.Lib.X64.AS} {c : Ctl}
    (hA : Abs R o s.st.1 σ) (h : SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : FramesPlacedInI Λ lbl s fs B) : PlacedS Λ lbl s c fs := by
  have hcell : ∀ r k, rs r = some k → privLoad s (R.addr k) = some (σ.slot k) := by
    intro r k hk
    obtain ⟨j, hj, he⟩ := hA.slot k (hrs r k hk)
    simp only [privLoad, hj, Option.map_some, he]
  exact placedS_of_slotPlacedI (slotPlacedI_of_slotRep (A := fun _ => True) h hcell fun _ _ _ => trivial) hfp

/-- **A block's states placed** (`W2Part`'s placement): the node's
controls placed in the abstract slot file (`hJ`, every slot a cell of the
region), the suspended frames placed at every state of the frame condition
(`hfp`, kept off the region, `FStable`), no slot written before the
block's last instruction (`hnw`). -/
theorem blkW_placedS (hFS : FStable R F) {n : ND} {blk : List (Directive × Nat)}
    (hJ : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) (hnw : noSlotWr blk.dropLast = true) :
    BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ hF hJn k hk m hA' hD
  refine ⟨?_, fun _ h => h⟩
  have hsl := arun_slot_noSlotWr (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩)
    (noSlotWr_take hnw hk)
  refine placedS_of_abs (s := { s with st := (m, _) }) hA' ?_ hrs (hfp _ (hFS _ _ hF hD)).choose_spec
  rw [hsl]
  exact hJ σ c hJn

/-- **A node's states placed** (as `blkW_placedS`, nothing run). -/
theorem nodeW_placedS {n : ND} (hJ : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c)
    (hrs : ∀ r k, rs r = some k → R.Off k) (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) :
    NodeW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨_, _, _, _, σ, hA, hF, hJn⟩ => ⟨placedS_of_abs hA (hJ σ c hJn) hrs (hfp s hF).choose_spec, fun _ h => h⟩

/-- **A state placed at a pending store** (`pendN2`'s `SlotRepAt`): a
control placed in the slot file with slot `k0` updated to register `r`'s
word is placed, slot `k0`'s words at `r` and every other slot at its cell
(`hrs`), the suspended frames placed under the frame condition (`hfp`). -/
theorem placedS_of_abs_upd {s : State} {o : Spike.Lib.X64.SO} {σ : Spike.Lib.X64.AS} {c : Ctl} {k0 : Int}
    {r : Reg64} (hA : Abs R o s.st.1 σ)
    (h : SlotRepAt Λ.imms lbl rs (Spike.Lib.upd σ.slot k0 (σ.regs.get64 r)) c)
    (hrs : ∀ r k, rs r = some k → R.Off k) (hfp : FramesPlacedInI Λ lbl s fs B) : PlacedS Λ lbl s c fs := by
  refine PlacedS.ofFrames (placed_of_slotRep (pf := fun k => if k = k0 then .reg (.r r) else
    .slot (R.addr k).toNat) h fun r' k hk => ?_) hfp.toFramesPlaced
  by_cases hk0 : k = k0
  · subst hk0
    simp only [Spike.Lib.upd_apply, ite_true]
    show some (s.st.1.regs.get64 r).toNat = _
    rw [hA.regs]
  · simp only [hk0, Spike.Lib.upd_apply, ite_false]
    obtain ⟨j, hj, he⟩ := hA.slot k (hrs r' k hk)
    show (privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [privLoad, hj, Option.map_some, he]

/-- **A one-instruction block's state placed at a pending store**
(`placedS_of_abs_upd` at the block's only state, nothing run). -/
theorem blkW_placedS_upd (hFS : FStable R F) {n : ND} {blk : List (Directive × Nat)} {k0 : Int} {r : Reg64}
    (h1 : blk.length ≤ 1)
    (hJ : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs (Spike.Lib.upd σ.slot k0 (σ.regs.get64 r)) c)
    (hrs : ∀ r k, rs r = some k → R.Off k) (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) :
    BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ hF hJn k hk m hA' hD
  refine ⟨?_, fun _ h => h⟩
  obtain rfl : k = 0 := by omega
  exact placedS_of_abs_upd (s := { s with st := (m, _) }) hA' (hJ σ c hJn) hrs (hfp _ (hFS _ _ hF hD)).choose_spec

end Placed

/--
info: 'Spike.Lib.LowerX64.blkW_placedS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_placedS

end Spike.Lib.LowerX64
