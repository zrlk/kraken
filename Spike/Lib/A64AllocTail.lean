/-
**The allocator's tail past the counter's add** (AArch64): `scc_rt_alloc`
(`Spike/Lib/A64Alloc.lean`) from the node `n4` after the counter's add
(`ldaddal`) on, as one segment inside a predicate `W` asked only at the
tail's nodes (`AllocWT`), not at the add nor before it.

**No back edge to the add.** The tail's nodes `TN` (`n4`, `n5`, `slow`,
`n7`, `full`, `ok`, `ok1`, `ok2`, `n12`, `hdr`, `n13`, `ret`) are closed
under the allocator's edges: from each, the code's next node is again a
tail node or an exit (`n4 → slow | n5`, `n5 → ok`, `slow → n7` (the `spin`
branch dead within the cells), `n7 → full`, `full → abort`, `ok → ok1 → ok2
→ n12 → hdr → n13 → ret → return`). `seg_allocW_tail` proves it: its
node graph is `TN` alone (`fn_segW` at `fun i => N … i.an`), each node's
edge landing at a `TN` node or an exit, so no tail node reaches `cnt` or
the add `rmw` (nor `e`, `entry`, `n2`, `cnt1`, `cnt2`).

- `TN`, `TN.an`: the tail's nodes among `AN`;
- `AllocWT`: the tail's states inside `W`, none moved by `K`; `AllocW.tail`:
  from `AllocW`;
- `seg_allocW_tailA`: the tail one segment inside `W` from any tail node to
  the heap abort alone (`EA`: the return's row is the allocation, landing in
  `xa`); `seg_allocW_tail`: to the allocator's exits.
-/
import Spike.Lib.A64Alloc

namespace Spike.Lib.A64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

/-- **The tail's nodes**: `scc_rt_alloc`'s nodes from the counter's add's
successor `n4` on. -/
inductive TN where
  | n4 | n5 | slow | n7 | full | ok | ok1 | ok2 | n12 | hdr | n13 | ret

/-- A tail node as an allocator node. -/
def TN.an : TN → AN
  | .n4 => .n4 | .n5 => .n5 | .slow => .slow | .n7 => .n7 | .full => .full | .ok => .ok | .ok1 => .ok1
  | .ok2 => .ok2 | .n12 => .n12 | .hdr => .hdr | .n13 => .n13 | .ret => .ret

section Spec

variable (ms : MemSide isaLSE2) (q : Call) {lab : Label → Int64}

/-- **The tail's states inside `W`**, none moved by `K`: `AllocW`'s
obligations at the tail's nodes only. -/
structure AllocWT (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  n4 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n4) b4
  n5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n5) b5
  slow : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .slow) b6
  n7 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n7) b7
  full : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .full) b9
  ok : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ok) b11
  ok1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ok1)
  ok2 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ok2)
  n12 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n12) b12
  hdr : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .hdr)
  n13 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n13) b13
  ret : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ret)

variable {ms q}

/-- **`AllocW`'s tail.** -/
theorem AllocW.tail {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} (h : AllocW ms q W K exe endPc R F) :
    AllocWT ms q W K exe endPc R F :=
  ⟨h.n4, h.n5, h.slow, h.n7, h.full, h.ok, h.ok1, h.ok2, h.n12, h.hdr, h.n13, h.ret⟩

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {q : Call}

/-- **The tail's exits**: the allocator's heap abort (`E`'s), and no state
at its return (`ret`'s row is the allocation, landing in `xa`). -/
def EA (lab : Label → Int64) (ms : MemSide isaLSE2) (q : Call) (lbl : WeakMem.AllocLabel → Option Nat) :
    AX → ND
  | .ret => ⟨Int64.ofBitVec q.ra, oE, fun _ _ => False⟩
  | .abort => E lab ms q lbl .abort

/-- **`scc_rt_alloc`'s tail is one segment inside `W` from any tail node
`i0` to its heap abort alone**, `W` asked at the tail's nodes only
(`AllocWT`): the node graph is `TN` (no tail node reaches the counter's add,
the module's note), each node's edge as `seg_allocW_at`'s; the return's row
is the allocation (`alloc_ndW`), whose successor is in `ms.xa` (`hxa`), so
no state leaves at the return. -/
theorem seg_allocW_tailA {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OK ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocWT ms q W K exe endPc R F) (i0 : TN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0.an))
      (At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl .abort)) := by
  refine (fn_segW (N := fun i : TN => N _ ms q i.an) (E := EA (_root_.Executable.labels exe).label ms q lbl)
    (fun i => ?_) i0).mono_post ?_
  rotate_left
  · rintro s c ⟨x, h⟩
    cases x
    · obtain ⟨-, -, -, -, -, -, -, ⟨⟩⟩ := h
    · exact h
  cases i
  case n4 =>
    anode b4 b4_ok n4; rw [TN.an, N, b4_run]
    obtain ⟨o, rfl, ho, hF, hn28, h11⟩ := hJ
    have hu := Call.u_toNat hq.units
    have hc := hq.cells
    have hU := hq.units
    have hsum : (o + q.u ms).toNat = o.toNat + ms.units q.n q.τ := by
      rw [BitVec.toNat_add, hu]; exact Nat.mod_eq_of_lt (by omega)
    simp only [h11, hF.2.2.2.2, subs_hi, hsum]
    split
    · rename_i h
      refine .inl ⟨TN.slow, rfl, rfl, o, rfl, ho, ?_, ?_, ?_⟩
      · simp only [BitVec.toNat_ofNat] at h; omega
      · simp_all [Fr, upd_apply]
      · simp [upd_apply]
    · rename_i h
      refine .inl ⟨TN.n5, rfl, rfl, o, rfl, ?_, ?_, hn28, ?_⟩
      · simp only [BitVec.toNat_ofNat] at h; omega
      · simp_all [Fr, upd_apply]
      · simp [upd_apply]
  case n5 => anode b5 b5_ok n5; rw [TN.an, N, b5_run]; exact .inl ⟨TN.ok, rfl, rfl, hJ⟩
  case slow =>
    anode b6 b6_ok slow; rw [TN.an, N, b6_run]
    obtain ⟨o, hJ⟩ := hJ
    have ⟨_, ho, _, _, h128⟩ := hJ
    have hc := hq.cells
    simp only [h128, subs_hi]
    split
    · rename_i h
      simp only [BitVec.toNat_ofNat] at h; omega
    · exact .inl ⟨TN.n7, rfl, rfl, o, hJ⟩
  case n7 =>
    anode b7 b7_ok n7; rw [TN.an, N, b7_run]
    obtain ⟨o, hc, ho, hu, -⟩ := hJ
    exact .inl ⟨TN.full, rfl, rfl, .inr ⟨o, hc, ho, hu⟩⟩
  case full => anode b9 b9_ok full; rw [TN.an, N, b9_run]; exact .inr ⟨AX.abort, rfl, rfl, rfl, hJ⟩
  case ok =>
    anode b11 b11_ok ok; rw [TN.an, N, b11_run]
    obtain ⟨o, hc, hle, hF, hn28, h128⟩ := hJ
    refine .inl ⟨TN.ok1, rfl, rfl, o, ⟨hc, hle, ?_, hn28, ?_⟩, ?_⟩
    · simp_all [Fr, upd_apply]
    · simp [upd_apply, h128]
    · simp [upd_apply, mOf, hF.2.2.1]
  case ok1 =>
    refine si_ndW (si := iAdrpH) hF (fun s he hn => hcode.ok1 s he hn) hW.ok1
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.ok2, rfl, rfl, ?_⟩⟩
    obtain ⟨o, hJ, h104⟩ := hJ
    exact ⟨o, hJ, h104, by simp [SI.step, SI.regs, iAdrpH]⟩
  case ok2 =>
    refine si_ndW (si := iAddH) hF (fun s he hn => hcode.ok2 s he hn) hW.ok2
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.n12, rfl, rfl, ?_⟩⟩
    obtain ⟨o, hJ, h104, h9⟩ := hJ
    refine ⟨o, hJ, h104, ?_⟩
    simp only [SI.step, SI.regs, iAddH]
    simp [h9]
    exact adrp_lo12 _
  case n12 =>
    anode b12 b12_ok n12; rw [TN.an, N, b12_run]
    obtain ⟨o, ⟨hc, hle, hF, hn28, h128⟩, h104, h9⟩ := hJ
    obtain ⟨h16, h8, h160, h152, h144⟩ := hF
    refine .inl ⟨TN.hdr, rfl, rfl, o, ⟨hc, hle, ?_, hn28, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · simp_all [Fr, upd_apply]
    · simp [upd_apply, h128]
    · simp [upd_apply, h128, h9]
    · simp [upd_apply, h152, h104]
    · simp [h160, h152, Call.hdr]
    · simp [h9, h128, h152, h104]
  case hdr =>
    refine rtst_ndW (fun s he hn => hcode.hdr s he hn) hW.hdr fun m σ c hA hD hJ => ?_
    obtain ⟨o, ⟨hc, hle, hF, hn28, h128⟩, hb, h9, h10⟩ := hJ
    have hk := Call.k_toNat hq.n_lt
    have hcl := hq.cells
    have hra : rAddr σ.regs .X10 0 = H (_root_.Executable.labels exe).label + o <<< 4 + (q.k * mOf q.h) <<< 3 := by
      rw [← h10]; simp [rAddr, Reg64s.getXReg]
    have hAeq : (rAddr σ.regs .X10 0).toNat = q.hdrAt ms o.toNat := by
      rw [hra, base_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk]
      rfl
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = rAddr σ.regs .X10 0 := by
      rw [← hAeq]; simp
    obtain ⟨hrt, hmp, hG⟩ := hq.hdr o.toNat hle
    have hnone := hmem _ (.inr ⟨o.toNat, hle, hAeq⟩)
    refine ⟨hAeq ▸ hrt, hofn ▸ hmp, ?_, hnone _ hD, c, .refl c, .inl ⟨TN.n13, rfl, rfl, o,
      ⟨hc, hle, hF, hn28, h128⟩, hb⟩⟩
    rw [← hofn, getRegOrZr_x]
    simpa [Reg64s.getXReg, h9] using hG
  case n13 =>
    anode b13 b13_ok n13; rw [TN.an, N, b13_run]
    obtain ⟨o, ⟨hc, hle, hF, hn28, h128⟩, h80, h64⟩ := hJ
    obtain ⟨h16, h8, h160, h152, h144⟩ := hF
    refine .inl ⟨TN.ret, ?_, ?_, o, hc, hle, hn28, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · simp [h80, h64]
    · simp [h16]
    · simp [h8]
  case ret =>
    refine alloc_ndW (Ea ms q) (a := iRet) (lo := -160) (hi := 0) rfl (by rintro w op ⟨⟩) hF
      hR hal hlo hhi (fun s he hn => hcode.ret s he hn) hxa hW.ret fun σ c hJ => ?_
    obtain ⟨o, rfl, hle, hn28, h0, h29, h30⟩ := hJ
    have hk := Call.k_toNat hq.n_lt
    have hcl := hq.cells
    have hA : σ.regs.X0.toBitVec.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ := by
      rw [h0, base8_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk, hq.off]
    obtain ⟨us, hus⟩ := hq.accs
    refine ⟨σ.regs.X0.toBitVec, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, TermRun.cst (.num o.toNat), o.toNat, us, hq.term,
      hq.ev, hq.num, rfl, rfl, hA, hle, hus, fun l ini _ =>
      ⟨?_, rfl, ini, o.toNat, rfl, rfl, hA, hle, h29, h30, us, hus, rfl⟩⟩
    simp [Ea, iRet, AI.tgt, Reg64s.getXReg, h30]

/-- **`scc_rt_alloc`'s tail is one segment inside `W` from any tail node
`i0`** to its return or its heap abort, `W` asked at the tail's nodes only
(`AllocWT`): `seg_allocW_tailA`, the abort one of the exits. -/
theorem seg_allocW_tail {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OK ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocWT ms q W K exe endPc R F) (i0 : TN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0.an))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl x) s c) :=
  (seg_allocW_tailA hF hR hal hlo hhi hq hcode hmem hxa hW i0).mono_post fun _ _ h => ⟨.abort, h⟩

end Proof

/-- info: 'Spike.Lib.A64.Alloc.AllocW.tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocW.tail

/-- info: 'Spike.Lib.A64.Alloc.seg_allocW_tailA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_allocW_tailA

/-- info: 'Spike.Lib.A64.Alloc.seg_allocW_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_allocW_tail

end Spike.Lib.A64.Alloc
