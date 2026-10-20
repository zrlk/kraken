/-
Transport of a directive's transformer into the baseline interpreter.
`Directive.interp_sound` turns each disjunct of a cell's step, the
fall-through tree and the jump tree, into the interpreter with real
continuations, by a per-primitive dictionary and one case analysis over the
instruction set. The machine-founded weakest precondition
(Kraken/MachineWP.lean) consumes it at every step of its bridge to
`straightlineStep`.
-/
import Kraken.Blocks
import Kraken.SegmentExtract

open Kraken
open Std.WP

namespace InterpSound

variable {P₁ P₂ : MachineState → Prop}

private theorem load_sound {s : MachineData} {addr : BitVec 64} {w : Width}
    {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.load addr w r₁).All P₁) : (s.load addr w r₂).All P₂ := by
  unfold MachineData.load at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ _ h

private theorem store_sound {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (s.store addr v r₁).All P₁) : (s.store addr v r₂).All P₂ := by
  unfold MachineData.store at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ h

private theorem storeNT_sound {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (s.storeNT addr v r₁).All P₁) : (s.storeNT addr v r₂).All P₂ := by
  unfold MachineData.storeNT at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ h

private theorem regOrMem_sound [Labels] [AddressSize] {w} {o : RegOrMem w}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (o.interp s p r₁).All P₁) : (o.interp s p r₂).All P₂ := by
  cases o with
  | reg r => exact hk _ _ h
  | mem a => exact load_sound hk h

private theorem operand_sound [Labels] [AddressSize] {w} {o : Operand w}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (o.interp s p r₁).All P₁) : (o.interp s p r₂).All P₂ := by
  cases o with
  | regOrMem rm => exact regOrMem_sound hk h
  | imm v => exact hk _ _ h

private theorem relRegOrMem_sound [Labels] [AddressSize] {o : RelRegOrMem}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : BitVec 64 → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (o.interp s p r₁).All P₁) : (o.interp s p r₂).All P₂ := by
  cases o with
  | rel c => exact hk _ _ h
  | reg r => exact hk _ _ h
  | mem a => exact load_sound hk h

private theorem set_sound [Labels] [AddressSize] {w} {d : Dst w} {v : w.type}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (s.set d v p r₁).All P₁) : (s.set d v p r₂).All P₂ := by
  cases d with
  | reg r => exact hk _ h
  | mem a => exact store_sound hk h

private theorem undefined_sound {α} [NondetSupportingType α] {r₁ r₂ : α → Effects}
    (hk : ∀ v, (r₁ v).All P₁ → (r₂ v).All P₂)
    (h : (Effects.undefined r₁).All P₁) : (Effects.undefined r₂).All P₂ :=
  fun v => hk v (h v)

private theorem rmwK_sound {s : MachineData} {k : Kraken.RmwKind} {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.rmwK k addr w op r₁).All P₁) : (s.rmwK k addr w op r₂).All P₂ := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · cases ho : op _ <;> simp only [ho] at h ⊢ <;> exact hk _ _ h

private theorem rmwPlain_sound {s : MachineData} {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.rmwPlain addr w op r₁).All P₁) : (s.rmwPlain addr w op r₂).All P₂ := by
  unfold MachineData.rmwPlain at h ⊢
  refine load_sound (fun v s' h => ?_) h
  cases ho : op v <;> simp only [ho] at h ⊢
  · exact hk _ _ h
  · exact store_sound (fun s'' h => hk _ _ h) h

private theorem rmw_sound [Labels] [AddressSize] {w} {o : RegOrMem w} {lock : Bool}
    {s : MachineData} {p : Std.Rco Int64} {op : w.type → Option w.type}
    {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (o.rmw lock s p op r₁).All P₁) : (o.rmw lock s p op r₂).All P₂ := by
  cases o with
  | reg r =>
    unfold RegOrMem.rmw at h ⊢
    cases ho : op (s.regs.get r) <;> simp only [ho] at h ⊢ <;> exact hk _ _ h
  | mem a =>
    unfold RegOrMem.rmw at h ⊢
    cases lock with
    | true => exact rmwK_sound hk h
    | false => exact rmwPlain_sound hk h


/-! ## Propositional characterizations for the AVX primitives

The AVX widths make definitional unification evaluate `2^512`-scale type
indices; these equations let the avx branch rewrite `Effects.All` into small
propositions and close by monotonicity instead. -/

theorem _root_.All_loadAvx {P : MachineState → Prop} {s : MachineData} {addr : BitVec 64}
    {w : AvxWidth} {r : w.type → MachineData → Effects} {b ac : Bool} :
    (s.loadAvx addr w r b ac).All P ↔
      (b = true → isAligned w.bytes addr = true)
        ∧ ∃ i, Mem.loadInt s.dmem addr w.bytes = some i ∧ (r (.ofInt _ i) s).All P := by
  unfold MachineData.loadAvx
  by_cases hal : b && !(isAligned w.bytes addr)
  · rw [if_pos hal]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hal
    simp [Effects.All, hal.1, hal.2]
  · rw [if_neg hal]
    simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at hal
    cases hm : Mem.loadInt s.dmem addr w.bytes <;>
      simp_all [Effects.All] <;> grind

theorem _root_.All_storeAvx {P : MachineState → Prop} {s : MachineData} {addr : BitVec 64}
    {w : AvxWidth} {v : w.type} {r : MachineData → Effects} {b ac : Bool} :
    (s.storeAvx addr v r b ac).All P ↔
      (b = true → isAligned w.bytes addr = true)
        ∧ ∃ i, Mem.loadInt s.dmem addr w.bytes = some i
            ∧ (r { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All P := by
  unfold MachineData.storeAvx
  by_cases hal : b && !(isAligned w.bytes addr)
  · rw [if_pos hal]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hal
    simp [Effects.All, hal.1, hal.2]
  · rw [if_neg hal]
    simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at hal
    cases hm : Mem.loadInt s.dmem addr w.bytes <;>
      simp_all [Effects.All] <;> grind

/-- The proposition "the AVX operand read delivers `v`, and `K v s`". -/
def _root_.AvxRegOrMem.wpRead [Labels] [AddressSize] {w} (o : AvxRegOrMem w) (s : MachineData)
    (p : Std.Rco Int64) (b : Bool) (K : w.type → MachineData → Prop) : Prop :=
  match o with
  | .avx r => K (s.zmms.get r) s
  | .mem a => (b = true → isAligned w.bytes ((a.interp s.regs p).zeroExtend _) = true)
      ∧ ∃ i, Mem.loadInt s.dmem ((a.interp s.regs p).zeroExtend _) w.bytes = some i
          ∧ K (.ofInt _ i) s

theorem _root_.All_avxRegOrMem [Labels] [AddressSize] {w} {o : AvxRegOrMem w} {s : MachineData}
    {p : Std.Rco Int64} {r : w.type → MachineData → Effects} {P : MachineState → Prop}
    {b ac : Bool} :
    (o.interp s p r b ac).All P ↔ o.wpRead s p b (fun v s' => (r v s').All P) := by
  cases o <;> simp only [AvxRegOrMem.interp, AvxRegOrMem.wpRead, All_loadAvx]

theorem _root_.AvxRegOrMem.wpRead_mono [Labels] [AddressSize] {w} {o : AvxRegOrMem w} {s : MachineData}
    {p : Std.Rco Int64} {K₁ K₂ : w.type → MachineData → Prop}
    {b : Bool}
    (hK : ∀ v s', K₁ v s' → K₂ v s') : o.wpRead s p b K₁ → o.wpRead s p b K₂ := by
  cases o with
  | avx r => exact hK _ _
  | mem a => exact fun ⟨hal, i, hi, hk⟩ => ⟨hal, i, hi, hK _ _ hk⟩

/-- The proposition "the AVX destination write succeeds, and `K` holds". -/
def _root_.AvxDst.wpWrite [Labels] [AddressSize] {w} (d : AvxDst w) (v : w.type) (s : MachineData)
    (p : Std.Rco Int64) (legacy : Bool) (b : Bool) (K : MachineData → Prop) : Prop :=
  match d with
  | .avx r => K (if legacy then s.setAvxLegacyReg r v else s.setAvxReg r v)
  | .mem a => (b = true → isAligned w.bytes ((a.interp s.regs p).zeroExtend _) = true)
      ∧ ∃ i, Mem.loadInt s.dmem ((a.interp s.regs p).zeroExtend _) w.bytes = some i
          ∧ K { s with dmem := Mem.storeInt s.dmem ((a.interp s.regs p).zeroExtend _) w.bytes v.toInt }

theorem _root_.All_setAvx [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type} {s : MachineData}
    {p : Std.Rco Int64} {r : MachineData → Effects} {P : MachineState → Prop} {b ac : Bool} :
    (s.setAvx d v p r b ac).All P ↔ d.wpWrite v s p false b (fun s' => (r s').All P) := by
  cases d <;> simp only [MachineData.setAvx, AvxDst.wpWrite, All_storeAvx, if_false,
    Bool.false_eq_true]

theorem _root_.All_setAvxLegacy [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type} {s : MachineData}
    {p : Std.Rco Int64} {r : MachineData → Effects} {P : MachineState → Prop} {b ac : Bool} :
    (s.setAvxLegacy d v p r b ac).All P ↔ d.wpWrite v s p true b (fun s' => (r s').All P) := by
  cases d <;> simp only [MachineData.setAvxLegacy, AvxDst.wpWrite, All_storeAvx, if_true]

theorem _root_.AvxDst.wpWrite_mono [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type}
    {s : MachineData} {p : Std.Rco Int64} {legacy b : Bool} {K₁ K₂ : MachineData → Prop}
    (hK : ∀ s', K₁ s' → K₂ s') : d.wpWrite v s p legacy b K₁ → d.wpWrite v s p legacy b K₂ := by
  cases d with
  | avx r => exact hK _
  | mem a => exact fun ⟨hal, i, hi, hk⟩ => ⟨hal, i, hi, hK _ hk⟩

private theorem rmw16K_sound {s : MachineData} {k : Kraken.RmwKind} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {r₁ r₂ : BitVec 128 → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.rmw16K k addr op r₁).All P₁) : (s.rmw16K k addr op r₂).All P₂ := by
  unfold MachineData.rmw16K at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr 16 <;> simp only [hm] at h ⊢
  · exact h
  · cases ho : op _ <;> simp only [ho] at h ⊢ <;> exact hk _ _ h

private theorem rmw16Plain_sound {s : MachineData} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {r₁ r₂ : BitVec 128 → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.rmw16Plain addr op r₁).All P₁) : (s.rmw16Plain addr op r₂).All P₂ := by
  unfold MachineData.rmw16Plain at h ⊢
  rw [All_loadAvx] at h ⊢
  obtain ⟨hal, i, hi, h⟩ := h
  refine ⟨hal, i, hi, ?_⟩
  revert h
  split <;> intro h
  · rw [All_storeAvx] at h ⊢
    obtain ⟨hal', j, hj, h⟩ := h
    exact ⟨hal', j, hj, hk _ _ h⟩
  · exact hk _ _ h

/- The transport lemmas below are applied by search: at each goal the tactic
tries them in turn. An attempt that does not apply must still unify the lemma's
conclusion with the goal, and with the interpreter unfolding that unification
reduces a machine step looking for a head symbol to compare. Sealing the
definitions the lemmas are keyed on makes a mismatch a comparison of two head
symbols instead. -/
set_option allowUnsafeReducibility true in
attribute [local irreducible] RegOrMem.interp Operand.interp RelRegOrMem.interp
  AvxRegOrMem.interp MachineData.set MachineData.setAvx MachineData.setAvxLegacy
  MachineData.load MachineData.store MachineData.storeNT MachineData.loadAvx MachineData.storeAvx
  MachineData.rmwK MachineData.rmwPlain RegOrMem.rmw

/-- The transport search over one instruction's interpretation: reduce the
interpreter, split the disjunction and apply the dictionary lemmas until the
continuation hypotheses close every leaf. -/
local macro "op_sound_search" w:ident hnext:ident hjmp:ident h:ident : tactic =>
  `(tactic| (
    simp only [Operation.interp, Reg.interp, Effects.All] at $h:ident ⊢ <;>
    rcases $h:ident with $h:ident | $h:ident <;>
    repeat' first
      | exact $hnext:ident _ $h:ident
      | exact $hjmp:ident _ $h:ident
      | exact ($h:ident).elim
      | exact $hnext:ident _ ($h:ident v)
      | exact (($h:ident) v).elim
      | exact Width.noConfusion hcond
      | refine operand_sound (fun v s' $h:ident => ?_) $h:ident
      | refine regOrMem_sound (fun v s' $h:ident => ?_) $h:ident
      | refine relRegOrMem_sound (fun v s' $h:ident => ?_) $h:ident
      | refine set_sound (fun s' $h:ident => ?_) $h:ident
      | refine load_sound (fun v s' $h:ident => ?_) $h:ident
      | refine store_sound (fun s' $h:ident => ?_) $h:ident
      | refine storeNT_sound (fun s' $h:ident => ?_) $h:ident
      | refine rmwK_sound (fun v s' $h:ident => ?_) $h:ident
      | refine rmw_sound (fun v s' $h:ident => ?_) $h:ident
      | refine undefined_sound (fun v $h:ident => ?_) $h:ident
      | refine fun v => ?_
      | (split <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, if_true, if_false] at $h:ident ⊢)
      | (split <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, if_true, if_false] at $h:ident)
      | (split at $h:ident <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, if_true, if_false])
      | simp only [Effects.All] at $h:ident ⊢
      | simp only [] at $h:ident ⊢
      | cases $w:ident))

-- Each case fits the default budget; together (since `movnti`) they do not.
set_option maxHeartbeats 400000 in
private theorem operation_sound {w} [Labels] [AddressSize] {P : MachineState → Prop}
    {op : Operation w} {p : Std.Rco Int64} {s : MachineData}
    {next : MachineData → Prop} {jmp : MachineState → Prop}
    {k : MachineData → Effects}
    (hnext : ∀ s', next s' → (k s').All P)
    (hjmp : ∀ st, jmp st → P st)
    (h : (Operation.interp op p s (fun s' => .done (s', 0))
            (fun _ _ => .unimplemented "jump")).All (fun st => next st.1)
       ∨ (Operation.interp op p s (fun _ => .unimplemented "fallthrough")
            (fun pc' s' => .done (s', pc'))).All jmp) :
    (Operation.interp op p s k (fun pc' s' => .done (s', pc'))).All P := by
  cases op
  -- `xadd` branches on the destination's shape before any access (the
  -- register form writes `src` first); split it before the common search.
  case xadd lock dst src => cases dst <;> op_sound_search w hnext hjmp h
  all_goals op_sound_search w hnext hjmp h

end InterpSound

section WP1Sound

open InterpSound

/-- Transport one directive's transformer disjunction into the baseline
interpreter with real continuations. -/
theorem Directive.interp_sound [Labels] {P : MachineState → Prop}
    {d : Directive} {p : Std.Rco Int64} {s : MachineData}
    {next : MachineData → Prop} {jmp : MachineState → Prop} {k : MachineData → Effects}
    (hnext : ∀ s', next s' → (k s').All P) (hjmp : ∀ st, jmp st → P st)
    (h : (d.interp s p (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All
           (fun st => next st.1)
       ∨ (d.interp s p (fun _ => .unimplemented "fallthrough")
           (fun pc' s' => .done (s', pc'))).All jmp) :
    (d.interp s p k (fun pc' s' => .done (s', pc'))).All P := by
  cases d with
  | label l =>
    simp only [Directive.interp, Effects.All] at h ⊢
    rcases h with h | h
    · exact hnext _ h
    · exact h.elim
  | byteArray bs =>
    simp only [Directive.interp, Effects.All] at h
    rcases h with h | h <;> exact h.elim
  | instr i =>
    simp only [Directive.interp] at h ⊢
    cases i with
    | regular asz osz op =>
      simp only [Instr.interp, Effects.All] at h ⊢
      generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
      exact operation_sound hnext hjmp h
    | avx asz osz aop =>
      simp only [Instr.interp, Effects.All] at h ⊢
      generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
      cases aop
      -- `cmpxchg16b` checks the alignment, then reads and maybe writes.
      case cmpxchg16b lock dst =>
        simp only [AvxOperation.interp] at h ⊢
        split
        · rename_i hal
          simp only [hal, if_true] at h
          rcases h with h | h <;> cases lock <;>
            simp only [if_true, if_false, Bool.false_eq_true] at h ⊢
          · refine rmw16Plain_sound (fun v s' h => ?_) h; exact hnext _ h
          · refine rmw16K_sound (fun v s' h => ?_) h; exact hnext _ h
          · refine rmw16Plain_sound (fun v s' h => ?_) h; exact h.elim
          · refine rmw16K_sound (fun v s' h => ?_) h; exact h.elim
        · rename_i hal
          simp only [hal, if_false, Bool.false_eq_true, Effects.All] at h
          rcases h with h | h <;> exact h.elim
      all_goals
        simp only [AvxOperation.interp, All_avxRegOrMem, All_setAvx,
          All_setAvxLegacy, Effects.All] at h ⊢ <;>
        rcases h with h | h <;>
        repeat' first
          | exact hnext _ h
          | exact h.elim
          | refine AvxRegOrMem.wpRead_mono (fun v s' h => ?_) h
          | refine AvxDst.wpWrite_mono (fun s' h => ?_) h
          | simp only [] at h ⊢

end WP1Sound

/-! ## Label cells

Shared by the bridges to the segment judgment (`Kraken/MachineWP.lean`) and the
Promising links (`Kraken/Promising/EnvWPX64.lean`, `Kraken/Promising/SeqLinkX64Step.lean`). -/

theorem Int64.add_ofNat_zero (pc : Int64) : pc + Int64.ofNat 0 = pc := by simp

/-- A run of label cells at the head of the cells changes nothing. -/
theorem Directives.interp_label_prefix [Labels] :
    ∀ (ls X : List (Directive × Nat)) (s : MachineData) (pc : Int64)
      (ret : Int64 → MachineData → Effects),
      (∀ c ∈ ls, c.1.isLabel = true ∧ c.2 = 0) →
      Directives.interp (ls ++ X) s pc ret = Directives.interp X s pc ret := by
  intro ls
  induction ls with
  | nil => intro X s pc ret _; rfl
  | cons c ls ih =>
    intro X s pc ret hls
    obtain ⟨hlab, hz⟩ := hls c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    cases d with
    | label l =>
      simp only at hz
      subst hz
      simp only [List.cons_append, Directives.interp, Directive.interp, Int64.add_ofNat_zero]
      exact ih X s pc ret (fun c hc => hls c (List.mem_cons_of_mem _ hc))
    | instr i => simp [Directive.isLabel] at hlab
    | byteArray a => simp [Directive.isLabel] at hlab

/- The fold transport unifies `Directive.interp` applications of a symbolic
directive; sealing the interpreters keeps that unification a comparison of
stuck applications instead of a symbolic machine run. -/
section InterpSealed

set_option allowUnsafeReducibility true in
attribute [local irreducible] Directive.interp Directives.interp

end InterpSealed

/- `straightlineStep` is the API boundary: every proof enters through
`apply straightlineStep_of_wp`. Sealing it keeps that apply fast: whenever a
goal or expected type is headed by `straightlineStep` of a concrete
executable, the elaborator's whnf otherwise partially evaluates the
interpreter, getting stuck only after seconds of symbolic
`withAddresses`/`idxOf` reduction. An equality spelling applied with `rw`
sidesteps the same reduction even without the seal, since `kabstract` matches
at reducible transparency; keep it in mind for a use site the apply rule
cannot serve. -/
set_option allowUnsafeReducibility true in
attribute [irreducible] straightlineStep

/- Same seal for the segment computation: reducing `directivesFromAddress` on
a concrete executable partially evaluates `withAddresses` and `idxOf` over a
symbolic layout. Its API is the extraction equations
(Kraken/SegmentExtract.lean), which rewrite syntactically. -/
set_option allowUnsafeReducibility true in
attribute [irreducible] Kraken.Executable.directivesFromAddress

