/-
**hello.w's `wc_worker` placed** (x86-64; the twin of `Spike/Lib/A64HelloPlacedZWc.lean`): the `hz`, `hZE`, `hZC`,
`hZW`, `hZU` fields of `SegRP.WcObl` at `X := PlacedSE Λ lbl · · []`. Every node of `wc_worker` (its prologue, its
`.entry` block, the call into `scc_rt_print`'s first block, the store's tail) and of the `scc_rt_unpark` it calls
runs at a control reading packet words (`Hello.PlacedZ`'s `placed_wcP`, `placed_wcR`, `placed_cS1`, `placed_cS2`)
kept where the code keeps them:

    the prologue (`wcJE`)                  %rdi, %rdx, %rcx, %r8, %r9   (`xProW_args`)
    the `.entry` block, the call (`wkJ`)   −16, −32, −40, −48, −56
    the store's tail (`HelloTail.JI`)      −48, −56 (words 3, 4)
    `scc_rt_unpark` (`Unpark.JE`, `JI`)    %rdi, then −16 (word 4)

- `keepE1_slot`, `mul_slot`, `keepE2_slot`, `keepX0_slot`, `wkS1_keepW`, `wkSl_keepW`, `tb0_slot`, `tb1_slot`:
  the packet's frame cells kept by the `.entry` block's pieces, `scc_rt_print`'s first block and the tail's blocks.
- `pR`, `pS`, `pT`: the packet's places (registers, frame cells, the tail's cells); `pkRep_pR`, `pkRep_pS`,
  `pkRep_pT`, `pkRep_one`: `PkRep` from their values; `placed_cells`: `wcP` placed from the frame's cells.
- `wz_placed`, `wZE_placed`, `wZC_placed`, `wZW_placed`, `wZU_placed`: `WcObl`'s `hz`, `hZE`, `hZC`, `hZW`,
  `hZU` at `PlacedSE`.

## Differences from the AArch64 version

- The packet's registers are `%rdi`, `%rdx .. %r9` (AArch64 `x0`, `x2 .. x5`) and its frame cells `−16`,
  `−32 .. −56` (AArch64 `−96`, `−80 .. −56`); the tail's cells are `−48`, `−56` (AArch64 `−64`, `−56`) and
  `scc_rt_unpark`'s `−16` (AArch64 `−48`).
- The `.entry` block is three nodes (`imulq` leaves the flags undefined), so `wZE_placed` is a conjunction of three
  `NodeZA`s and its keep facts are per piece (`keepE1_slot`, `mul_slot`, `keepE2_slot`; AArch64 `keepE_slot`).
- `WcObl.hZC` is a `NodeZA` at `scc_rt_print`'s first block (AArch64 a `NodeW` at the call node), so the call
  node's cells are kept through that block as well (`keepX0_slot`).
- The block keep facts are concrete `arun` evaluations (as in `X64WakePlacedZ`) for AArch64's `dstep_keep`,
  `keep_blk`; `scc_rt_unpark`'s are `X64WakePlacedZ`'s `unB0_rdi`, `unB1_slot`.
- `wZU_placed` takes `WcObl.hZU`'s `CallerF` premise (the region's bounds) for AArch64's explicit bounds.
- `placed_cells` and `wkS1_keepW`, `mul_slot`, `tb0_slot`, `tb1_slot`, `keepX0_slot` are new.
-/
import Spike.Lib.X64HelloPlacedZEnv
import Spike.Lib.X64HelloWorkerSegRP
import Spike.Lib.X64HelloProArgs
import Spike.Lib.X64HelloWkTailNN
import Spike.Lib.X64WakeWorkerNNA
import Spike.Lib.X64WakePlacedZ

namespace Spike.Lib.X64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Place WordPlace placeVal ValRep)
open Spike.Lib (Region)
open Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64HelloSplit (wcP wcR)
open Spike.Lib.X64HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words wcJE)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ wcPs)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (cS1 cS2)
open Spike.Lib.X64WakeMainW (M1 placeVal_cell placeVal_reg)
open Spike.Lib.X64Consumer (Lbl Placed)
open Spike.Lib.X64ConsumerS (PlacedSE)

/-! ## The blocks keep the packet's cells -/

section Blk

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over concrete blocks (as in `X64WakePlacedZ`). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.X64.arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly,
    Spike.Lib.X64.AI.so, Spike.Lib.X64.soReg,
    Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp, AddrExpr.interp, Spike.Lib.X64.SO.get,
    Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply,
    Spike.Lib.X64.Reg64s.get_low64, Spike.Lib.X64.BlockSpec.AI.step_ld',
    Spike.Lib.X64.BlockSpec.AI.step_st', Spike.Lib.X64.BlockSpec.AI.step_push',
    Spike.Lib.X64.BlockSpec.AI.step_pop', Spike.Lib.X64.BlockSpec.AI.step_reg',
    Spike.Lib.X64.BlockSpec.AI.step_jmp', Spike.Lib.X64.BlockSpec.AI.step_jcc',
    Spike.Lib.X64.BlockSpec.AI.step_call', Spike.Lib.X64.Reg64s.get64_set64_ne,
    Spike.Lib.X64.Reg64s.get64_set64_self])

variable (l : String → Int64) (pc : Int64) (σ : AS) {j : Int}

/-- **The `.entry` block's first piece keeps the packet's cells** (it writes `−64`, `−72`), every prefix. -/
theorem keepE1_slot {k : Nat} (hk : k ≤ Body.wkE1.length)
    (hj : j = -16 ∨ j = -32 ∨ j = -40 ∨ j = -48 ∨ j = -56) :
    (arun l (Body.wkE1.take k) ⟨pc, Body.oB, σ⟩).σ.slot j = σ.slot j := by
  simp only [Body.wkE1] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    rcases k with _|_|_|_|_|_|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- **The multiply keeps the cells.** -/
theorem mul_slot (fl : StatusFlags) : (Body.wkMul.step σ fl).slot = σ.slot := by
  simp [FI.step]

/-- **The `.entry` block's second piece keeps the packet's cells** (it writes `−80`, `−88`, the call `−96`),
every prefix. -/
theorem keepE2_slot {k : Nat} (hk : k ≤ Body.wkE2.length)
    (hj : j = -16 ∨ j = -32 ∨ j = -40 ∨ j = -48 ∨ j = -56) :
    (arun l (Body.wkE2.take k) ⟨pc, Body.oB, σ⟩).σ.slot j = σ.slot j := by
  simp only [Body.wkE2] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    rcases k with _|_|_|_|_|_|_|_|_|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- **`scc_rt_print`'s first block keeps the caller's cells** (from `%rsp` at `−96` it writes below). -/
theorem keepX0_slot {k : Nat} (hk : k < Spike.Lib.X64.Print.x0.length)
    (hj : j = -16 ∨ j = -32 ∨ j = -40 ∨ j = -48 ∨ j = -56) :
    (arun l (Spike.Lib.X64.Print.x0.take k) ⟨pc, ⟨-96, []⟩, σ⟩).σ.slot j = σ.slot j := by
  simp only [Spike.Lib.X64.Print.x0] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- **`wkS1` keeps the packet's cells.** -/
theorem wkS1_keepW (hj : j = -16 ∨ j = -32 ∨ j = -40 ∨ j = -48 ∨ j = -56) :
    (Body.wkS1 l σ).slot j = σ.slot j := by
  have h := keepE1_slot l (l ".Lwc_worker.entry") σ (k := Body.wkE1.length) (Nat.le_refl _) hj
  rw [List.take_length] at h
  exact h

/-- **`wkSl` keeps the packet's cells.** -/
theorem wkSl_keepW (hj : j = -16 ∨ j = -32 ∨ j = -40 ∨ j = -48 ∨ j = -56) :
    Body.wkSl l σ j = σ.slot j := by
  have h := keepE2_slot l (l ".Lwc_worker.entry" + 40) (Body.wkMul.step (Body.wkS1 l σ) σ.status)
    (k := Body.wkE2.length) (Nat.le_refl _) hj
  rw [List.take_length] at h
  rw [Body.wkSl, Body.wkC_eq, h, mul_slot, wkS1_keepW l σ hj]

/-- **The tail's first block keeps the cells** (loads). -/
theorem tb0_slot {k : Nat} (hk : k < HelloTail.b0.length) :
    (arun l (HelloTail.b0.take k) ⟨pc, HelloTail.oI, σ⟩).σ.slot = σ.slot := by
  simp only [HelloTail.b0] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|k <;> (try omega) <;> arun_simp

/-- **The tail's unpark-call prefixes keep the cells.** -/
theorem tb1_slot {k : Nat} (hk : k < HelloTail.b1.length) :
    (arun l (HelloTail.b1.take k) ⟨pc, HelloTail.oI, σ⟩).σ.slot = σ.slot := by
  simp only [HelloTail.b1] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|k <;> (try omega) <;> arun_simp

end Blk

/-! ## The packet's places -/

section Places

variable {lbl : Lbl} {s : State} {w : Words} {w0 w1 w2 w3 w4 : TermRun.Word}

/-- The packet's registers at `wc_worker`'s entry: `%rdi`, `%rdx`, `%rcx`, `%r8`, `%r9`. -/
def pR : Nat → Place M1.I.RegId
  | 0 => .reg (.r .rdi) | 1 => .reg (.r .rdx) | 2 => .reg (.r .rcx) | 3 => .reg (.r .r8) | _ => .reg (.r .r9)

/-- The packet's frame cells in `wc_worker`'s frame: `−16`, `−32`, `−40`, `−48`, `−56`. -/
def pS (R : Region) : Nat → Place M1.I.RegId
  | 0 => .slot (R.addr (-16)).toNat | 1 => .slot (R.addr (-32)).toNat | 2 => .slot (R.addr (-40)).toNat
  | 3 => .slot (R.addr (-48)).toNat | _ => .slot (R.addr (-56)).toNat

/-- The tail's cells of words `3`, `4`: `−48`, `−56`. -/
def pT (R : Region) : Nat → Place M1.I.RegId
  | 3 => .slot (R.addr (-48)).toNat | _ => .slot (R.addr (-56)).toNat

variable (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
  (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat)

include hv0 hv1 hv2 hv hvu in
/-- `PkRep` at the argument registers. -/
theorem pkRep_pR (h0 : (s.st.1.regs.get64 .rdi) = w.w0) (h2 : (s.st.1.regs.get64 .rdx) = w.w2)
    (h3 : (s.st.1.regs.get64 .rcx) = w.w3) (h4 : (s.st.1.regs.get64 .r8) = w.w4)
    (h5 : (s.st.1.regs.get64 .r9) = w.w5) : PkRep lbl s pR (fun _ => True) w0 w1 w2 w3 w4 := by
  refine pkRep_of hv0 hv1 hv2 hv hvu fun i _ => ?_
  rcases i with _ | _ | _ | _ | i <;> simp only [pR, placeVal_reg, wv] <;>
    first | rw [h0] | rw [h2] | rw [h3] | rw [h4] | rw [h5]

include hv0 hv1 hv2 hv hvu in
/-- `PkRep` at the frame's cells. -/
theorem pkRep_pS {R : Region} (h16 : placeVal M1 s (.slot (R.addr (-16)).toNat) = some w.w0.toNat)
    (h32 : placeVal M1 s (.slot (R.addr (-32)).toNat) = some w.w2.toNat)
    (h40 : placeVal M1 s (.slot (R.addr (-40)).toNat) = some w.w3.toNat)
    (h48 : placeVal M1 s (.slot (R.addr (-48)).toNat) = some w.w4.toNat)
    (h56 : placeVal M1 s (.slot (R.addr (-56)).toNat) = some w.w5.toNat) :
    PkRep lbl s (pS R) (fun _ => True) w0 w1 w2 w3 w4 := by
  refine pkRep_of hv0 hv1 hv2 hv hvu fun i _ => ?_
  rcases i with _ | _ | _ | _ | i
  · exact h16
  · exact h32
  · exact h40
  · exact h48
  · exact h56

include hv hvu in
/-- `PkRep` of words `3`, `4` at the tail's cells. -/
theorem pkRep_pT {R : Region} (h48 : placeVal M1 s (.slot (R.addr (-48)).toNat) = some w.w4.toNat)
    (h56 : placeVal M1 s (.slot (R.addr (-56)).toNat) = some w.w5.toNat) :
    PkRep lbl s (pT R) (fun i => 3 ≤ i) w0 w1 w2 w3 w4 := by
  intro i wd hi hwd
  rcases i with _ | _ | _ | _ | _ | i
  all_goals first | omega | simp at hwd
  · subst hwd; exact ⟨_, h48, hv⟩
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
  {F' : MachineData → Prop} {rbp ra : BitVec 64} {w : Words} {tp sp0 : BitVec 64}
  {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}

/-- **`wcP` placed from the frame's cells**: at a state whose cells `−16`, `−32 .. −56` are those of a state `σ0`
holding the packet (`wkJ`'s cells). -/
theorem placed_cells {o : SO} {m' : MachineData} {σ' σ0 : AS} {s : State} (hlo : R'.lo ≤ -56) (hhi : -8 ≤ R'.hi)
    (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
    (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat)
    (hA : Abs R' o m' σ') (hs : s.st.1 = m')
    (hk : ∀ j : Int, (j = -16 ∨ j = -32 ∨ j = -40 ∨ j = -48 ∨ j = -56) → σ'.slot j = σ0.slot j)
    (h16 : σ0.slot (-16) = w.w0) (h32 : σ0.slot (-32) = w.w2) (h40 : σ0.slot (-40) = w.w3)
    (h48 : σ0.slot (-48) = w.w4) (h56 : σ0.slot (-56) = w.w5) :
    PlacedSE Λ lbl s (wcP w0 w1 w2 w3 w4) [] := by
  refine placedSE_nil (placed_wcP (A := fun _ => True) (fun _ _ => trivial)
    (pkRep_pS (R := R') hv0 hv1 hv2 hv hvu ?_ ?_ ?_ ?_ ?_))
  · rw [placeVal_cell hA ⟨by decide, by omega, by omega⟩ s hs, hk _ (by simp), h16]
  · rw [placeVal_cell hA ⟨by decide, by omega, by omega⟩ s hs, hk _ (by simp), h32]
  · rw [placeVal_cell hA ⟨by decide, by omega, by omega⟩ s hs, hk _ (by simp), h40]
  · rw [placeVal_cell hA ⟨by decide, by omega, by omega⟩ s hs, hk _ (by simp), h48]
  · rw [placeVal_cell hA ⟨by decide, by omega, by omega⟩ s hs, hk _ (by simp), h56]

/-- **`WcObl.hz` at `PlacedSE`**: the prologue's states at `wcP`, the packet in the argument registers. -/
theorem wz_placed {ms : List TermRun.Frame → MemSide isa}
    (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
    (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    XProW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R' F' (ms [])
      ((_root_.Executable.labels exe).label "wc_worker") 80 8 ".Lwc_worker.stk" 5 9 3 6 4 wcPs
      (fun σ c => wcJE (wcP w0 w1 w2 w3 w4) w rbp ra tp σ c ∧ σ.regs.rsp.toBitVec = sp0 - 80#64) := by
  refine xProW_args fun σ c hJ s hs => ?_
  obtain ⟨⟨rfl, h0, -, h2, h3, h4, h5, -⟩, -⟩ := hJ
  refine placedSE_nil (placed_wcP (A := fun _ => True) (fun _ _ => trivial)
    (pkRep_pR hv0 hv1 hv2 hv hvu ?_ ?_ ?_ ?_ ?_))
  · erw [hs .rdi (.inl rfl)]; exact h0
  · erw [hs .rdx (.inr (.inl rfl))]; exact h2
  · erw [hs .rcx (.inr (.inr (.inl rfl)))]; exact h3
  · erw [hs .r8 (.inr (.inr (.inr (.inl rfl))))]; exact h4
  · erw [hs .r9 (.inr (.inr (.inr (.inr rfl))))]; exact h5

/-- **`WcObl.hZE` at `PlacedSE`**: the `.entry` block's three nodes at `wcP`, the packet in the frame's cells. -/
theorem wZE_placed (hlo : R'.lo ≤ -56) (hhi : -8 ≤ R'.hi)
    (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
    (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R' F'
        (Body.wN (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
          (fun _ => PrW w0 w2 n m) .e) Body.wkE1 ∧
      NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R' F'
        (Body.wN (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
          (fun _ => PrW w0 w2 n m) .mul) [(Body.wkMul.toDir, 4)] ∧
      NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R' F'
        (Body.wN (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
          (fun _ => PrW w0 w2 n m) .e2) Body.wkE2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨rfl, h16, -, h32, h40, h48, h56, -⟩ := hJ
    refine ⟨placed_cells hlo hhi hv0 hv1 hv2 hv hvu hA' rfl ?_ h16 h32 h40 h48 h56, fun _ h => h⟩
    intro j hj
    exact keepE1_slot _ _ _ (Nat.le_of_lt hk) hj
  · rintro s σ c _ _ _ _ _ _ ⟨σ0, hJ, rfl⟩ k hk m' hA' _
    obtain ⟨rfl, h16, -, h32, h40, h48, h56, -⟩ := hJ
    obtain rfl : k = 0 := by simpa using hk
    refine ⟨placed_cells hlo hhi hv0 hv1 hv2 hv hvu hA' rfl ?_ h16 h32 h40 h48 h56, fun _ h => h⟩
    intro j hj
    simp only [List.take_zero, arun, List.foldl_nil]
    exact wkS1_keepW _ σ0 hj
  · rintro s σ c _ _ _ _ _ _ ⟨σ0, fl, hJ, rfl⟩ k hk m' hA' _
    obtain ⟨rfl, h16, -, h32, h40, h48, h56, -⟩ := hJ
    refine ⟨placed_cells hlo hhi hv0 hv1 hv2 hv hvu hA' rfl ?_ h16 h32 h40 h48 h56, fun _ h => h⟩
    intro j hj
    refine (keepE2_slot _ _ _ (Nat.le_of_lt hk) hj).trans ?_
    rw [mul_slot, wkS1_keepW _ σ0 hj]

/-- **`WcObl.hZC` at `PlacedSE`**: the call node's states at `wcP` (`KcW`) through `scc_rt_print`'s first block,
the packet in the frame's cells the `.entry` block keeps (`wkSl_keepW`, `keepX0_slot`). -/
theorem wZC_placed (hlo : R'.lo ≤ -56) (hhi : -8 ≤ R'.hi)
    (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
    (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R' F'
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
        (KcW w0 w1 w2 w3 w4 n m)) Spike.Lib.X64.Print.x0 := by
  rintro s σ c _ _ _ _ _ _ ⟨⟨σ0, c0, fl, hJ0, rfl⟩, hK⟩ k hk m' hA' _
  obtain ⟨rfl, -⟩ := hK
  obtain ⟨-, h16, -, h32, h40, h48, h56, -⟩ := hJ0
  refine ⟨placed_cells hlo hhi hv0 hv1 hv2 hv hvu hA' rfl ?_ h16 h32 h40 h48 h56, fun _ h => h⟩
  intro j hj
  refine (keepX0_slot _ _ _ hk hj).trans ?_
  rw [Body.wkC_slot, wkSl_keepW _ σ0 hj]

/-- **`WcObl.hZW` at `PlacedSE`**: the store's tail at `wcR`, `cS1` (words `3`, `4` in the cells `−48`, `−56`),
then `cS2` (reading nothing). -/
theorem wZW_placed (hlo : R'.lo ≤ -56) (hhi : -8 ≤ R'.hi) (hv : ValRep lbl w3.val w.w4.toNat)
    (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ i, NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R' F'
      (HelloTail.NA (_root_.Executable.labels exe).label (wcR w0 w1 w2 w3 w4) (cS1 w0 w1 w2 w3 w4)
        (cS2 w0 w1 w2 w3 w4) w.w4 w.w5 rbp ra tp (R'.addr 0) i) (HelloTail.blkN i) := by
  have hR48 : R'.Off (-48) := ⟨by decide, by omega, by omega⟩
  have hR56 : R'.Off (-56) := ⟨by decide, by omega, by omega⟩
  intro i
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨rfl, -, -, h48, h56, -⟩ := hJ
    refine ⟨placedSE_nil (placed_wcR (A := fun i => 3 ≤ i) (by decide) (by decide)
      (pkRep_pT (R := R') hv hvu ?_ ?_)), fun _ h => h⟩
    · erw [placeVal_cell hA' hR48 _ rfl, tb0_slot _ _ _ hk, h48]
    · erw [placeVal_cell hA' hR56 _ rfl, tb0_slot _ _ _ hk, h56]
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨⟨rfl, -, -, h48, h56, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [HelloTail.blkN] using hk
    refine ⟨placedSE_nil (placed_wcR (A := fun i => 3 ≤ i) (by decide) (by decide)
      (pkRep_pT (R := R') hv hvu ?_ ?_)), fun _ h => h⟩
    · rw [placeVal_cell hA' hR48 _ rfl]; exact congrArg _ (congrArg _ h48)
    · rw [placeVal_cell hA' hR56 _ rfl]; exact congrArg _ (congrArg _ h56)
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨rfl, -, -, -, h56, -⟩ := hJ
    refine ⟨placedSE_nil (placed_cS1 (A := fun i => i = 4) rfl
      (pkRep_one (p := .slot (R'.addr (-56)).toNat) hvu ?_)), fun _ h => h⟩
    erw [placeVal_cell hA' hR56 _ rfl, tb1_slot _ _ _ hk, h56]
  · exact fun _ _ _ _ _ _ _ _ _ _ k hk => absurd hk (by simp [HelloTail.blkN])
  · intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
    obtain ⟨rfl, -⟩ := hJ
    exact ⟨placedSE_nil placed_cS2, fun _ h => h⟩

/-- **`WcObl.hZU` at `PlacedSE`**: `scc_rt_unpark`'s nodes at `cS1` (word `4` in `%rdi` at entry, in the cell
`−16` after the spill), then `cS2`; the region's bounds from `CallerF`. -/
theorem wZU_placed (hvu : ValRep lbl w4.val w.w5.toNat) :
    ∀ (R'' : Region) (F'' : MachineData → Prop),
      CallerF R' F' (HelloTail.N (_root_.Executable.labels exe).label (wcR w0 w1 w2 w3 w4) (cS1 w0 w1 w2 w3 w4)
        (cS2 w0 w1 w2 w3 w4) w.w4 w.w5 rbp ra tp (R'.addr 0) .unpk) 0 (-40) 8 R'' F'' →
      ∀ rbp1 ra1 i, NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R'' F''
        (Unpark.N (_root_.Executable.labels exe).label (cS1 w0 w1 w2 w3 w4) (cS2 w0 w1 w2 w3 w4) w.w5 rbp1 ra1 tp i)
        (Unpark.blkN i) := by
  intro R'' F'' hC rbp1 ra1 i
  have hR : R''.Off (-16) := ⟨by decide, by have := hC.lo; omega, by have := hC.hi; omega⟩
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨rfl, h0, -⟩ := hJ
    refine ⟨placedSE_nil (placed_cS1 (A := fun i => i = 4) rfl
      (pkRep_one (p := .reg (.r .rdi)) hvu ?_)), fun _ h => h⟩
    show some (m'.regs.get64 .rdi).toNat = _
    erw [hA'.regs, Wake.PlacedZ.unB0_rdi _ _ _ hk, h0]
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨rfl, -, -, h16, -⟩ := hJ
    refine ⟨placedSE_nil (placed_cS1 (A := fun i => i = 4) rfl
      (pkRep_one (p := .slot (R''.addr (-16)).toNat) hvu ?_)), fun _ h => h⟩
    erw [placeVal_cell hA' hR _ rfl, Wake.PlacedZ.unB1_slot _ _ _ hk, h16]
  · intro s σ c _ _ _ _ _ _ hJ k hk m' hA' _
    obtain ⟨⟨rfl, -, -, h16, -⟩, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [Unpark.blkN] using hk
    refine ⟨placedSE_nil (placed_cS1 (A := fun i => i = 4) rfl
      (pkRep_one (p := .slot (R''.addr (-16)).toNat) hvu ?_)), fun _ h => h⟩
    rw [placeVal_cell hA' hR _ rfl]; exact congrArg _ (congrArg _ h16)
  all_goals
    intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
    first | obtain ⟨rfl, -⟩ := hJ | obtain ⟨⟨rfl, -⟩, -⟩ := hJ
    exact ⟨placedSE_nil placed_cS2, fun _ h => h⟩

end Nodes

end Spike.Lib.X64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.keepE1_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.keepE1_slot

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.keepE2_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.keepE2_slot

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.keepX0_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.keepX0_slot

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wkSl_keepW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wkSl_keepW

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.pkRep_pR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.pkRep_pR

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.pkRep_pS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.pkRep_pS

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.pkRep_pT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.pkRep_pT

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.pkRep_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.pkRep_one

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.placed_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.placed_cells

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wz_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wz_placed

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wZE_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wZE_placed

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wZC_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wZC_placed

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wZW_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wZW_placed

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wZU_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.wZU_placed
