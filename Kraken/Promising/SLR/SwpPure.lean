/-
(O5) `PromisePure` for the SWP spinlock worker (AArch64 `swpWorker`).

`SwpReach P st`: the thread runs the laid-out worker with `X0 = l`,
`X1 = c` (`Frame`) at one of its cells, with `W3 = 1` inside the acquire
loop (positions 3, 4, 6, 7, 8). Every machine step keeps it
(`swpReach_stepPreserves`, through the cells' event trees of
`SLR/SwpTrees.lean`), so it holds at every reachable configuration
(`configInv_reachable`).

At such a state the next instruction writes no `(Lk, 0)` message (`SWPA`
writes `W3 = 1`; `STR` writes the counter, `c ≠ l`) or is the release store
`STLR wzr, [x0]`; `promisePure_of_cells` (`SLR/PromiseFulfil.lean`) then
gives `swp_promisePure` for any release predicates that are pure off
`(Lk, 0)`, e.g. `lockPred` at the lock and pure predicates elsewhere.
-/
import Kraken.Promising.SLR.SwpCells
import Kraken.Promising.SLR.PromiseFulfil

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-- The reachable thread states of the worker: `Frame`, at a cell, with
`W3 = 1` inside the acquire loop. -/
def SwpReach (P : Params) (st : State) : Prop :=
  Frame P st ∧ ∃ i, AtPos st i ∧
    (i = 1 ∨ ((i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8) ∧ BitVec.setWidth 32 st.st.1.regs.X3.toBitVec = 1#32) ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 16)

omit hv in
/-- At the end address the worker has halted. -/
theorem exec_end {P : Params} {st : State} (h : Frame P st) (hp : AtPos st 16) : isa.exec st = none := by
  show exec st = none
  have : st.st.2 = st.endPc := by rw [hp, h.endPc]
  simp [exec, this]

/-- A thread at the start of the worker (position `0`, the label `worker`)
is at position `1`. -/
theorem swpReach_start {P : Params} {st : State} (h : Frame P st) (hp : AtPos st 0) : SwpReach P st :=
  ⟨h, 1, by rw [AtPos, addrOf_label (i := 0) (l := "worker") rfl]; exact hp, .inl rfl⟩

omit layout hv in
/-- `W3` after setting `X2`. -/
private theorem x3_setX2 (m : MachineData) (v : BitVec 64) :
    (m.regs.setXReg .X2 v).X3 = m.regs.X3 := by simp [Reg64s.setXReg]

/-- **Every machine step keeps `SwpReach`.** -/
theorem swpReach_stepPreserves (P : Params) (A : Arch) :
    StepPreserves (I := isa) A (fun _ _ => True) (fun _ st => SwpReach P st) := by
  intro tid t mem outs o ⟨hF, i, hp, hi⟩ _ hstep ho
  refine ⟨stepOne_leaf A hstep ho fun tree hex => ?_, ⟨fun _ => trivial, fun _ _ => trivial⟩⟩
  rcases hi with rfl | ⟨hi, h3⟩ | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_mov t.st (hF.at hp (by decide))] at hex
    cases hex
    exact ⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl (by simp [Reg64s.setXReg]), 3, addr_3.symm,
      .inr (.inl ⟨.inl rfl, by simp [Reg64s.setXReg]⟩)⟩
  · rcases hi with rfl | rfl | rfl | rfl | rfl
    · have hx3 := hF.x3_at hp (by decide)
      rw [exec_swpa t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
      cases hex
      intro v
      exact ⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 4, rfl,
        .inr (.inl ⟨.inr (.inl rfl), by rw [x3_setX2]; exact h3⟩)⟩
    · have hx3 := hF.x3_at hp (by decide)
      rw [exec_cbz t.st (hF.at hp (by decide))] at hex
      cases hex
      have hF' := hF.goto (m := t.st.st.1) (pc := if BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec = 0#32 then
        (layout swpWorker).addrOf 10 else (layout swpWorker).addrOf 5) rfl rfl rfl
      by_cases hz : BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec = 0#32
      · exact ⟨hF', 10, by simp [AtPos, hz], .inr (.inr (.inl rfl))⟩
      · exact ⟨hF', 6, by simp [AtPos, hz, addr_6], .inr (.inl ⟨.inr (.inr (.inl rfl)), h3⟩)⟩
    · have hx3 := hF.x3_at hp (by decide)
      rw [exec_ldr_spin t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
      cases hex
      intro v
      exact ⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 7, rfl,
        .inr (.inl ⟨.inr (.inr (.inr (.inl rfl))), by rw [x3_setX2]; exact h3⟩)⟩
    · have hx3 := hF.x3_at hp (by decide)
      rw [exec_cbnz t.st (hF.at hp (by decide))] at hex
      cases hex
      have hF' := hF.goto (m := t.st.st.1) (pc := if BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec = 0#32 then
        (layout swpWorker).addrOf 8 else (layout swpWorker).addrOf 6) rfl rfl rfl
      by_cases hz : BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec = 0#32
      · exact ⟨hF', 8, by simp [AtPos, hz], .inr (.inl ⟨.inr (.inr (.inr (.inr rfl))), h3⟩)⟩
      · exact ⟨hF', 6, by simp [AtPos, hz], .inr (.inl ⟨.inr (.inr (.inl rfl)), h3⟩)⟩
    · have hx3 := hF.x3_at hp (by decide)
      rw [exec_b_try t.st (hF.at hp (by decide))] at hex
      cases hex
      exact ⟨hF.goto rfl rfl rfl, 3, rfl, .inr (.inl ⟨.inl rfl, h3⟩)⟩
  · have hx3 := hF.x3_at hp (by decide)
    rw [exec_ldr_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hex
    cases hex
    intro v
    exact ⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 11, rfl, by simp⟩
  · have hx3 := hF.x3_at hp (by decide)
    rw [exec_add t.st (hF.at hp (by decide))] at hex
    cases hex
    exact ⟨hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl, 12, rfl, by simp⟩
  · have hx3 := hF.x3_at hp (by decide)
    rw [exec_str_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hex
    cases hex
    intro _
    exact ⟨hF.goto rfl rfl rfl, 13, rfl, by simp⟩
  · have hx3 := hF.x3_at hp (by decide)
    rw [exec_stlr t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
    cases hex
    intro _
    exact ⟨hF.goto rfl rfl rfl, 14, rfl, by simp⟩
  · have hx3 := hF.x3_at hp (by decide)
    rw [exec_b_done t.st (hF.at hp (by decide))] at hex
    cases hex
    exact ⟨hF.goto rfl rfl rfl, 16, rfl, by simp⟩
  · rw [exec_end hF hp] at hex
    cases hex

/-- At a reachable state the next instruction writes no `(Lk, 0)` message,
or is the release store `STLR wzr, [x0]`. -/
theorem swp_cell (P : Params) (A : Arch) (hne : P.c ≠ P.l) (st : State) (tree : EvTree State)
    (h : SwpReach P st) (hex : isa.exec st = some tree) :
    tree.Writes (fun l v => ¬ (l = P.Lk ∧ BitVec.setWidth 32 v = 0#32)) ∨
      ∃ k l v s, A.storeKind k = .rel ∧ tree = .store k false l v (fun _ => .done s) := by
  obtain ⟨hF, i, hp, hi⟩ := h
  rcases hi with rfl | ⟨hi, h3⟩ | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_mov st (hF.at hp (by decide))] at hex
    cases hex; exact .inl trivial
  · rcases hi with rfl | rfl | rfl | rfl | rfl
    · rw [exec_swpa st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
      cases hex
      refine .inl ⟨fun _ new hnew => ?_, fun _ => trivial⟩
      simp only [Option.some.injEq] at hnew
      subst hnew
      rintro ⟨-, h0⟩
      rw [h3] at h0
      exact absurd h0 (by decide)
    · rw [exec_cbz st (hF.at hp (by decide))] at hex
      cases hex; exact .inl trivial
    · rw [exec_ldr_spin st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
      cases hex; exact .inl fun _ => trivial
    · rw [exec_cbnz st (hF.at hp (by decide))] at hex
      cases hex; exact .inl trivial
    · rw [exec_b_try st (hF.at hp (by decide))] at hex
      cases hex; exact .inl trivial
  · rw [exec_ldr_c st (hF.at hp (by decide)) hF.x1 hF.dc] at hex
    cases hex; exact .inl fun _ => trivial
  · rw [exec_add st (hF.at hp (by decide))] at hex
    cases hex; exact .inl trivial
  · rw [exec_str_c st (hF.at hp (by decide)) hF.x1 hF.dc] at hex
    cases hex
    refine .inl ⟨fun ⟨hl, _⟩ => hne ?_, fun _ => trivial⟩
    exact congrArg Loc.addr hl
  · rw [exec_stlr st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
    cases hex
    exact .inr ⟨_, _, _, _, rfl, rfl⟩
  · rw [exec_b_done st (hF.at hp (by decide))] at hex
    cases hex; exact .inl trivial
  · rw [exec_end hF hp] at hex
    cases hex

/-- **(O5) for the SWP spinlock**: from initial threads in `SwpReach`
(e.g. at the start of the worker, `swpReach_start`) and release predicates
pure off `(Lk, 0)`, every promise not fulfilled by a release store is pure. -/
theorem swp_promisePure (P : Params) (hne : P.c ≠ P.l) {A : Arch} {fuel : Nat} {states : List isa.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred}
    (hrel : ∀ l v, ¬ (l = P.Lk ∧ BitVec.setWidth 32 v = 0#32) → Pred.Pure (rel l) v)
    (h0 : ∀ (tid : Nat) (t : Thread isa), (Config.init states initMem).threads[tid]? = some t → SwpReach P t.st) :
    PromisePure (I := isa) A fuel states initMem rel :=
  promisePure_of_cells _ hrel (SwpReach P)
    (fun _ hc tid t ht => (configInv_reachable (swpReach_stepPreserves P A)
      ⟨⟨fun _ => trivial, fun _ _ => trivial⟩, fun tid t ht => h0 tid t ht⟩ hc).2 tid t ht)
    (swp_cell P A hne)

end Kraken.Promising.SLR.SwpInv
