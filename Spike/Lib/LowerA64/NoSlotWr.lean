/-
**No slot written before a block's last instruction** (AArch64; the twin
of `Spike/Lib/LowerX64/NoSlotWr.lean`): the premise `noSlotWr blk.dropLast`
of `blkW_placedS` (`Spike/Lib/LowerA64/PlacedBlk.lean`) for the blocks of
an `Accepted2` body's code.

- `noSlotWr_of_ne`: a block none of whose directives is an `sp`-based `str`
  writes no slot;
- `noSlotWr_getOp`, `noSlotWr_getReg`, `noSlotWr_retLoads`: an operand's
  loads write no slot;
- `noSlotWr_kind1`, `noSlotWr_kind2`: a construct's block writes no slot
  before its last instruction (the slot store alone writes one, as its
  last);
- `noSlotWr_single`: a one-instruction block.
-/
import Spike.Lib.LowerA64.PlacedBlk
import Spike.Lib.LowerA64.BlocksC2Code

namespace Spike.Lib.LowerA64

open Kraken.Promising.AArch64
open Spike.Lib.A64.Flow (AI classify)
open Scc.Emit.A64

theorem noSlotWr_append {a b : List Directive} : noSlotWr (a ++ b) = (noSlotWr a && noSlotWr b) := by
  simp [noSlotWr, List.all_append]

theorem noSlotWr_dropLast {ds : List Directive} (h : noSlotWr ds = true) : noSlotWr ds.dropLast = true := by
  simp only [noSlotWr, List.all_eq_true] at h ⊢
  exact fun x hx => h x (List.dropLast_subset _ hx)

/-- **A block with no `sp`-based `str` writes no slot.** -/
theorem noSlotWr_of_ne {ds : List Directive}
    (h : ∀ d ∈ ds, ∀ t n, d ≠ .instr ⟨.W64, .STR t ⟨.SP, .imm ⟨.int64 n, none⟩⟩⟩) : noSlotWr ds = true := by
  simp only [noSlotWr, List.all_eq_true]
  intro d hd
  split
  · next a ha =>
    cases a with
    | str t n => exact absurd (Spike.Lib.A64.Flow.classify_sound ha).1 (h d hd t n)
    | _ => rfl
  · rfl

theorem noSlotWr_movDs (d : XReg) : ∀ L, noSlotWr (movDs d L) = true
  | [] => rfl
  | p :: rest => by
    refine noSlotWr_of_ne fun x hx t n => ?_
    simp only [movDs, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨q, -, rfl⟩ <;> simp [movzD, movkD]

theorem noSlotWr_movImm (d : XReg) (n : Int) : noSlotWr (directives (movImm d n)) = true := by
  rw [directives_movImm]; exact noSlotWr_movDs _ _

/-- **A `w`-sized load writes no slot.** -/
theorem noSlotWr_ldrOff (w : RegWidth) (rt : XReg) (base : RegOrSp .W64) (off : Int) :
    noSlotWr (directives (ldrOff w rt base off)) = true := by
  unfold ldrOff
  split
  · exact noSlotWr_of_ne fun x hx t n => by simp [directives, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)
  · split
    · exact noSlotWr_of_ne fun x hx t n => by simp [directives, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)
    · rw [directives_append, noSlotWr_append, noSlotWr_movImm]
      exact noSlotWr_of_ne fun x hx t n => by simp [directives, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)

/-- **A store off a register (not `sp`) writes no slot.** -/
theorem noSlotWr_strOff_reg (w : RegWidth) (rt b : XReg) (off : Int) :
    noSlotWr (directives (strOff w rt (xs b) off)) = true := by
  unfold strOff
  split
  · exact noSlotWr_of_ne fun x hx t n => by simp [directives, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)
  · split
    · exact noSlotWr_of_ne fun x hx t n => by simp [directives, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)
    · rw [directives_append, noSlotWr_append, noSlotWr_movImm]
      exact noSlotWr_of_ne fun x hx t n => by simp [directives, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)

/-- **An immediate add writes no slot.** -/
theorem noSlotWr_addImm (d b : RegOrSp .W64) (n : Int) : noSlotWr (directives (addImm d b n)) = true := by
  unfold addImm
  split
  · exact noSlotWr_of_ne fun x hx t n => by simp [directives, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)
  · exact noSlotWr_of_ne fun x hx t n => by simp [directives, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)
  · rw [directives_append, noSlotWr_append, noSlotWr_movImm]
    exact noSlotWr_of_ne fun x hx t n => by simp [directives, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)

/-- **The frame's exit and `ret` write no slot.** -/
theorem noSlotWr_leave (cx : FnCtx) : noSlotWr (directives (cx.leave ++ [ret])) = true := by
  rw [FnCtx.leave, directives_append, directives_append, directives_append, noSlotWr_append, noSlotWr_append,
    noSlotWr_append, noSlotWr_ldrOff, noSlotWr_ldrOff, noSlotWr_addImm]
  exact noSlotWr_of_ne fun x hx t n => by simp [directives, ret, ins] at hx; subst hx; simp; try (rintro rfl h; cases h)

theorem noSlotWr_getReg {cx : FnCtx} {t : XReg} {r : Scc.IR.Reg} {l : List Item} (h : cx.getReg t r = .ok l) :
    noSlotWr (directives l) = true := by
  simp only [FnCtx.getReg, bind, Except.bind] at h
  split at h
  · cases h
  · cases h; exact noSlotWr_ldrOff _ _ _ _

/-- **An operand's load writes no slot.** -/
theorem noSlotWr_getOp {cx : FnCtx} {t : XReg} {a : Scc.IR.Operand} {l : List Item} (h : cx.getOp t a = .ok l) :
    noSlotWr (directives l) = true := by
  cases a with
  | reg r => exact noSlotWr_getReg h
  | imm v => cases h; exact noSlotWr_movImm _ _

/-- **A `ret`'s loads write no slot.** -/
theorem noSlotWr_retLoads {cx : FnCtx} :
    ∀ {ps : List (Scc.IR.Operand × XReg)} {l : List Item}, retLoads cx ps = .ok l → noSlotWr (directives l) = true
  | [], l, h => by cases h; rfl
  | (v, r) :: ps, l, h => by
    simp only [retLoads, bind, Except.bind] at h
    split at h
    · cases h
    · next lv hv =>
      split at h
      · cases h
      · next ls hs =>
        cases h
        rw [directives_append, noSlotWr_append, noSlotWr_getOp hv, noSlotWr_retLoads hs]; rfl

/-- **A construct's block writes no slot before its last instruction.** -/
theorem noSlotWr_kind1 {cx : FnCtx} {blk : List Directive} (hk : Kind1 cx blk) : noSlotWr blk.dropLast = true := by
  rcases hk with ⟨a, b, la, lb, ha, hb, rfl | rfl | ⟨T, rfl⟩⟩ | ⟨d, o, -, rfl⟩ | ⟨F, rfl⟩ | ⟨w, lw, hg, rfl⟩
  · refine noSlotWr_dropLast ?_
    rw [addDirs, directives_append, directives_append, noSlotWr_append, noSlotWr_append, noSlotWr_getOp ha,
      noSlotWr_getOp hb]
    exact noSlotWr_of_ne fun x hx t n => by
      simp [addChecked, directives, ins] at hx; rcases hx with rfl | rfl <;> simp
  · refine noSlotWr_dropLast ?_
    rw [subDirs, directives_append, directives_append, noSlotWr_append, noSlotWr_append, noSlotWr_getOp ha,
      noSlotWr_getOp hb]
    exact noSlotWr_of_ne fun x hx t n => by
      simp [subSat, directives, ins] at hx; rcases hx with rfl | rfl | rfl <;> simp
  · refine noSlotWr_dropLast ?_
    rw [brDirs, directives_append, directives_append, noSlotWr_append, noSlotWr_append, noSlotWr_getOp ha,
      noSlotWr_getOp hb]
    exact noSlotWr_of_ne fun x hx t n => by
      simp [cmpReg, jcc, directives, ins] at hx; rcases hx with rfl | rfl <;> simp
  · rfl
  · rfl
  · refine noSlotWr_dropLast ?_
    rw [List.append_assoc, directives_append, noSlotWr_append, noSlotWr_getOp hg, noSlotWr_leave]; rfl

/-- **An `Accepted2` construct's block writes no slot before its last
instruction.** -/
theorem noSlotWr_kind2 {cx : FnCtx} {blk : List Directive} (hk : Kind2 cx blk) : noSlotWr blk.dropLast = true := by
  rcases hk with hk | ⟨vs, ls, -, hl, rfl⟩
  · exact noSlotWr_kind1 hk
  · refine noSlotWr_dropLast ?_
    rw [List.append_assoc, directives_append, noSlotWr_append, noSlotWr_retLoads hl, noSlotWr_leave]; rfl

/-- **A one-instruction block writes no slot before its last** (a slot
store, a `bl`). -/
theorem noSlotWr_single (d : Directive) : noSlotWr [d].dropLast = true := rfl

/--
info: 'Spike.Lib.LowerA64.noSlotWr_kind2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noSlotWr_kind2

end Spike.Lib.LowerA64
