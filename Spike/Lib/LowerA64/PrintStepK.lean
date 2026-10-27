/-
**The slots along `print`'s argument block** (AArch64; the twin of
`Spike/Lib/LowerX64/PrintStepK.lean`): every prefix of the block's
directives with its `bl` keeps the body's offsets `oF` and every slot but
the block's fresh registers' (`lo`, `s`, `cap`, `k`).

- `StepK`, `stepK_of`, `arun_take_stepK`: a directive keeping the offsets
  `⟨sp, []⟩` and the slots off a set `W` (from its classification: the
  offsets kept, a store only into `W`); every prefix of a block of such
  directives;
- `stepK_getOp`, `stepK_setReg9`, `stepK_ext32`, `stepK_binAdd`,
  `stepK_binMul`, `stepK_cmp`, `stepK_csel`, `stepK_bl`: the pieces of the
  block;
- `printArgs_take`: the prefixes of `print`'s argument block with its `bl`.
-/
import Spike.Lib.LowerA64.PrintCall

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64

set_option linter.unusedSimpArgs false

/-- **A directive keeping the offsets `⟨sp, []⟩` and the slots off `W`**,
at any pc and state. -/
def StepK (lab : Label → Int64) (sp : Int) (W : Int → Prop) (d : Directive) : Prop :=
  ∀ pc σ, (Spike.Lib.A64.Flow.dstep lab ⟨pc, ⟨sp, []⟩, σ⟩ d).so = ⟨sp, []⟩ ∧
    ∀ j, ¬ W j → (Spike.Lib.A64.Flow.dstep lab ⟨pc, ⟨sp, []⟩, σ⟩ d).σ.slot j = σ.slot j

/-- **`StepK` from the classification**: the covered instruction keeps the
offsets, and a store writes into `W`. -/
theorem stepK_of {lab : Label → Int64} {sp : Int} {W : Int → Prop} {d : Directive}
    (h : ∀ a, classify d = some a → a.so ⟨sp, []⟩ = ⟨sp, []⟩ ∧ ∀ t n, a = .str t n → W (sp + n.toInt)) :
    StepK lab sp W d := by
  intro pc σ
  unfold Spike.Lib.A64.Flow.dstep
  cases hc : classify d with
  | none => exact ⟨rfl, fun _ _ => rfl⟩
  | some a =>
    obtain ⟨hso, hst⟩ := h a hc
    refine ⟨hso, fun j hj => ?_⟩
    cases a with
    | str t n =>
      have hne : ¬ j = sp + n.toInt := fun e => hj (e ▸ hst t n rfl)
      simp only [AI.step, upd_apply, hne, ↓reduceIte]
    | _ => rfl

/-- **Every prefix of a block of `StepK` directives** keeps the offsets and
the slots off `W`. -/
theorem arun_take_stepK {lab : Label → Int64} {sp : Int} {W : Int → Prop} :
    ∀ {ds : List Directive}, (∀ d ∈ ds, StepK lab sp W d) → ∀ (k : Nat) (pc : Int64) (σ : AS),
      (arun lab (ds.take k) ⟨pc, ⟨sp, []⟩, σ⟩).so = ⟨sp, []⟩ ∧
        ∀ j, ¬ W j → (arun lab (ds.take k) ⟨pc, ⟨sp, []⟩, σ⟩).σ.slot j = σ.slot j
  | [], _, k, pc, σ => by simp [arun]
  | _ :: _, _, 0, pc, σ => by simp [arun]
  | d :: ds, h, k + 1, pc, σ => by
    obtain ⟨h1, h2⟩ := h d (List.mem_cons_self ..) pc σ
    generalize e : Spike.Lib.A64.Flow.dstep lab ⟨pc, ⟨sp, []⟩, σ⟩ d = am at h1 h2
    obtain ⟨pc1, o1, σ1⟩ := am
    simp only at h1 h2
    subst h1
    obtain ⟨h3, h4⟩ := arun_take_stepK (fun d hd => h d (List.mem_cons_of_mem _ hd)) k pc1 σ1
    have e2 : arun lab ((d :: ds).take (k + 1)) ⟨pc, ⟨sp, []⟩, σ⟩ = arun lab (ds.take k) ⟨pc1, ⟨sp, []⟩, σ1⟩ := by
      rw [List.take_succ_cons]
      show List.foldl (dstep lab) (Spike.Lib.A64.Flow.dstep lab ⟨pc, ⟨sp, []⟩, σ⟩ d) (ds.take k) = _
      rw [e]; rfl
    rw [e2]
    exact ⟨h3, fun j hj => (h4 j hj).trans (h2 j hj)⟩

section Pieces

variable {lab : Label → Int64} {sp : Int} {W : Int → Prop}

theorem stepK_movz {d : XReg} (p : Nat × Nat) : StepK lab sp W (movzD d p) :=
  stepK_of fun a h => by
    simp [movzD, classify, RegOnly, xz, i64] at h
    subst h
    simp [AI.so, soReg, regDst, zrB, SO.write, SO.kill, rm, xz]

theorem stepK_movk {d : XReg} (p : Nat × Nat) : StepK lab sp W (movkD d p) :=
  stepK_of fun a h => by
    simp [movkD, classify, RegOnly, xz, i64] at h
    subst h
    simp [AI.so, soReg, regDst, zrB, SO.write, SO.kill, rm, xz]

theorem stepK_movImm (d : XReg) (n : Int) : ∀ x ∈ directives (movImm d n), StepK lab sp W x := by
  rw [directives_movImm]
  generalize nzHw _ 0 = hs
  intro x hx
  cases hs with
  | nil =>
    simp only [movDs, List.mem_singleton] at hx
    subst hx; exact stepK_movz _
  | cons p rest =>
    simp only [movDs, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨q, -, rfl⟩
    · exact stepK_movz _
    · exact stepK_movk _

theorem stepK_rw {r : XReg} {w : RW} : StepK lab sp W (w.dir r) :=
  stepK_of fun a h => by
    cases w <;> simp [RW.dir, AI.toDir, classify, RegOnly] at h <;> subst h <;>
      simp [AI.so, soReg, regDst, zrB, SO.write, SO.kill, SO.killZ, rm]

/-- An operand's load keeps the offsets and every slot. -/
theorem stepK_getOp {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) {t : XReg} {a : Scc.IR.Operand}
    {l : List Item} (ha : c.getOp t a = .ok l) : ∀ x ∈ directives l, StepK lab sp W x := by
  rcases getOp_cases hf h1 ha with ⟨r, off, rfl, hs, hl⟩ | ⟨v, rfl, rfl⟩
  · rw [hl]
    intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact stepK_rw
  · exact stepK_movImm t _

theorem stepK_ext32 : ∀ x ∈ directives (extOp false .w32), StepK lab sp W x := by
  intro x hx
  simp only [directives_ext32, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;>
  exact stepK_of fun a h => by
    simp [xz, classify, RegOnly] at h; subst h
    simp [AI.so, soReg, regDst, zrB, SO.write, SO.kill, SO.killZ, rm, xz]

theorem stepK_binAdd : ∀ x ∈ directives (binOp .add), StepK lab sp W x := by
  intro x hx
  simp only [binOp, addReg, directives, ins, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  subst hx
  exact stepK_of fun a h => by
    simp [xz, zr, rz, classify, RegOnly] at h; subst h
    simp [AI.so, soReg, regDst, zrB, SO.write, SO.kill, SO.killZ, rm, xz, zr, rz]

theorem stepK_binMul : ∀ x ∈ directives (binOp .mul), StepK lab sp W x := by
  intro x hx
  simp only [binOp, directives, ins, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  subst hx
  exact stepK_of fun a h => by
    simp [xz, zr, rz, classify, RegOnly] at h; subst h
    simp [AI.so, soReg, regDst, zrB, SO.write, SO.kill, SO.killZ, rm, xz, zr, rz]

theorem stepK_cmp : ∀ x ∈ directives [cmpReg .W64 .X9 .X10], StepK lab sp W x := by
  intro x hx
  simp only [cmpReg, directives, ins, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  subst hx
  exact stepK_of fun a h => by
    simp [xz, zr, rz, classify, RegOnly] at h; subst h
    simp [AI.so, soReg, regDst, zrB, SO.write, SO.kill, SO.killZ, rm, xz, zr, rz]

theorem stepK_csel :
    ∀ x ∈ directives [ins (.CSEL (xz .X9) (xz .X11) (xz .X12) (condCode .ult))], StepK lab sp W x := by
  intro x hx
  simp only [directives, ins, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  subst hx
  exact stepK_of fun a h => by
    simp [condCode, xz, zr, rz, classify, RegOnly] at h; subst h
    simp [AI.so, soReg, regDst, zrB, SO.write, SO.kill, SO.killZ, rm, xz, zr, rz]

theorem stepK_bl : ∀ x ∈ blPrintD, StepK lab sp W x := by
  intro x hx
  rw [blPrintD_eq, List.mem_singleton] at hx
  subst hx
  exact stepK_of fun a h => by
    simp [classify] at h; subst h
    simp [AI.so, SO.kill, rm]

/-- The store of `x9` into `d`'s slot writes `d`'s slot only. -/
theorem stepK_setReg9 {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) {d : Scc.IR.Reg} {off : Int}
    (hd : c.slotOff d = .ok off) {l : List Item} (hl : c.setReg d .X9 = .ok l)
    (hW : W (-(c.frame : Int) + off)) : ∀ x ∈ directives l, StepK lab (-(c.frame : Int)) W x := by
  rw [setReg_eq hf (by omega) hd] at hl
  cases hl
  obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hds : directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)] =
      [spStr .X9 (Int64.ofInt off)] := rfl
  rw [hds]
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  refine stepK_of fun a h => ?_
  have hc : classify (spStr .X9 (Int64.ofInt off)) = some (AI.str (.low (.reg .X9) .W64) (Int64.ofInt off)) := rfl
  rw [hc] at h
  cases h
  refine ⟨rfl, fun t n hn => ?_⟩
  cases hn
  rw [ho]; exact hW

end Pieces

section Block

variable {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095)

/-- The slots of the block's fresh registers. -/
def FreshW (c : FnCtx) (lo s cap kk : Scc.IR.Reg) (j : Int) : Prop :=
  ¬ ∀ q, rsOf c q = some j → q ≠ lo ∧ q ≠ s ∧ q ≠ cap ∧ q ≠ kk

theorem freshW_of {lo s cap kk d : Scc.IR.Reg} {off : Int} (hd : c.slotOff d = .ok off)
    (hq : d = lo ∨ d = s ∨ d = cap ∨ d = kk) : FreshW c lo s cap kk (-(c.frame : Int) + off) := by
  intro h
  have := h d (by simp [rsOf, hd]; omega)
  rcases hq with rfl | rfl | rfl | rfl <;> simp_all

include hf h1 in
/-- A store instruction's dest among the fresh registers: its directives keep
the slots off them (the pieces of `okBlk_inst_*`). -/
theorem stepK_setOf {d : Scc.IR.Reg} {lo s cap kk : Scc.IR.Reg} (hq : d = lo ∨ d = s ∨ d = cap ∨ d = kk)
    {l : List Item} (hl : c.setReg d .X9 = .ok l) (lab : Label → Int64) :
    ∀ x ∈ directives l, StepK lab (-(c.frame : Int)) (FreshW c lo s cap kk) x := by
  have ⟨off, hd⟩ : ∃ off, c.slotOff d = .ok off := by
    cases hd : c.slotOff d
    · simp [FnCtx.setReg, hd, bind, Except.bind] at hl
    · exact ⟨_, rfl⟩
  exact stepK_setReg9 hf h1 hd hl (freshW_of hd hq)

include hf h1 in
/-- **Every prefix of `print`'s argument block with its `bl`** keeps the
body's offsets and every slot off the block's fresh registers'. -/
theorem printArgs_take {i1 i2 i3 i4 : Nat} {lo s cap kk : Scc.IR.Reg} {b o m n : Scc.IR.Operand}
    {l1 l2 l3 l4 l5 : List Item}
    (c1 : c.inst i1 (.ext false .w32 lo o) = .ok l1) (c2 : c.inst i2 (.bin .add s b (.reg lo)) = .ok l2)
    (c3 : c.inst i3 (.bin .mul cap m (Scc.Lower.imm 8)) = .ok l3)
    (c4 : c.inst i4 (.select .ult kk n (.reg cap) n (.reg cap)) = .ok l4)
    (c5 : c.getArgs [.reg s, .reg kk] = .ok l5) (lab : Label → Int64) (k : Nat) (pc : Int64) (σ : AS) :
    (arun lab ((directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD).take k) ⟨pc, oF c, σ⟩).so = oF c ∧
      ∀ j, (∀ q, rsOf c q = some j → q ≠ lo ∧ q ≠ s ∧ q ≠ cap ∧ q ≠ kk) →
        (arun lab ((directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD).take k) ⟨pc, oF c, σ⟩).σ.slot j =
          σ.slot j := by
  have hK : ∀ x ∈ directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD,
      StepK lab (-(c.frame : Int)) (FreshW c lo s cap kk) x := by
    -- the pieces of each instruction
    simp only [FnCtx.inst] at c1 c2 c3 c4
    obtain ⟨la1, ha1, c1⟩ := exc_bind_ok c1
    obtain ⟨ls1, hs1, c1⟩ := exc_bind_ok c1
    obtain ⟨la2, ha2, c2⟩ := exc_bind_ok c2
    obtain ⟨lb2, hb2, c2⟩ := exc_bind_ok c2
    obtain ⟨ls2, hs2, c2⟩ := exc_bind_ok c2
    obtain ⟨la3, ha3, c3⟩ := exc_bind_ok c3
    obtain ⟨lb3, hb3, c3⟩ := exc_bind_ok c3
    obtain ⟨ls3, hs3, c3⟩ := exc_bind_ok c3
    obtain ⟨la4, ha4, c4⟩ := exc_bind_ok c4
    obtain ⟨lb4, hb4, c4⟩ := exc_bind_ok c4
    obtain ⟨lt4, ht4, c4⟩ := exc_bind_ok c4
    obtain ⟨lf4, hf4, c4⟩ := exc_bind_ok c4
    obtain ⟨ls4, hs4, c4⟩ := exc_bind_ok c4
    simp only [pure, Except.pure, Except.ok.injEq] at c1 c2 c3 c4
    subst c1 c2 c3 c4
    rw [getArgs_two] at c5
    obtain ⟨la5, ha5, c5⟩ := exc_bind_ok c5
    obtain ⟨lb5, hb5, c5⟩ := exc_bind_ok c5
    simp only [pure, Except.pure, Except.ok.injEq] at c5
    subst c5
    intro x hx
    simp only [directives_append, List.mem_append] at hx
    rcases hx with ((((((hx | hx) | hx) | (((hx | hx) | hx) | hx)) | (((hx | hx) | hx) | hx)) |
      (((((((hx | hx) | hx) | hx) | hx) | hx) | hx))) | (hx | hx)) | hx
    · exact stepK_getOp hf h1 ha1 x hx
    · exact stepK_ext32 x hx
    · exact stepK_setOf hf h1 (.inl rfl) hs1 lab x hx
    · exact stepK_getOp hf h1 ha2 x hx
    · exact stepK_getOp hf h1 hb2 x hx
    · exact stepK_binAdd x hx
    · exact stepK_setOf hf h1 (.inr (.inl rfl)) hs2 lab x hx
    · exact stepK_getOp hf h1 ha3 x hx
    · exact stepK_getOp hf h1 hb3 x hx
    · exact stepK_binMul x hx
    · exact stepK_setOf hf h1 (.inr (.inr (.inl rfl))) hs3 lab x hx
    · exact stepK_getOp hf h1 ha4 x hx
    · exact stepK_getOp hf h1 hb4 x hx
    · exact stepK_cmp x hx
    · exact stepK_getOp hf h1 ht4 x hx
    · exact stepK_getOp hf h1 hf4 x hx
    · exact stepK_csel x hx
    · exact stepK_setOf hf h1 (.inr (.inr (.inr rfl))) hs4 lab x hx
    · exact stepK_getOp hf h1 ha5 x hx
    · exact stepK_getOp hf h1 hb5 x hx
    · exact stepK_bl x hx
  obtain ⟨h3, h4⟩ := arun_take_stepK hK k pc σ
  exact ⟨h3, fun j hj => h4 j fun h => h hj⟩

end Block

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.arun_take_stepK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.arun_take_stepK

/-- info: 'Spike.Lib.LowerA64.printArgs_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printArgs_take
