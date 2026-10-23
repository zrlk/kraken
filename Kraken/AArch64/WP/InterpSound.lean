/-
Copied from x64's `Kraken/InterpSound.lean` at commit `86cde85`, adapted for
AArch64: the statement of `Directive.interp_sound` and the seals are x64's; the
proof is new, by a per-primitive dictionary over AArch64's memory and
addressing primitives and one search over the `Operation` constructors (the
technique of `Kraken.Promising.AArch64.operation_sim`). AArch64 has no vector
unit, so x64's AVX section has no counterpart.

Transport of a directive's transformer into the baseline interpreter.
`Directive.interp_sound` turns each disjunct of a cell's step, the
fall-through tree and the jump tree, into the interpreter with real
continuations. The machine-founded weakest precondition
(Kraken/AArch64/WP/Bridge.lean) consumes it at every step of its bridge to
`straightlineStep`.

The dictionary proves the more general fact behind it: the interpreter is
monotone in its continuations (`InterpSound.operation_mono`). Every primitive
passes control to its continuation with values and states that do not depend
on the continuation, so a continuation that is at least as good everywhere
gives an effect tree that is at least as good.
-/
import Kraken.AArch64.WP.MachineWP

open Kraken
open Std.WP

namespace InterpSound

variable {P₁ P₂ : MachineState → Prop}

/-! ## The dictionary: one monotonicity lemma per primitive -/

theorem load_mono {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.load addr w r₁).All P₁) : (s.load addr w r₂).All P₂ := by
  unfold MachineData.load at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ _ h

theorem store_mono {s : MachineData} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (s.store addr v r₁).All P₁) : (s.store addr v r₂).All P₂ := by
  unfold MachineData.store at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ h

theorem loadK_mono {s : MachineData} {k : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.loadK k xcl addr w r₁).All P₁) : (s.loadK k xcl addr w r₂).All P₂ := by
  unfold MachineData.loadK at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · exact hk _ _ h

theorem storeK_mono {s : MachineData} {k : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {v : w.type} {r₁ r₂ : Bool → MachineData → Effects}
    (hk : ∀ b s', (r₁ b s').All P₁ → (r₂ b s').All P₂)
    (h : (s.storeK k xcl addr v r₁).All P₁) : (s.storeK k xcl addr v r₂).All P₂ := by
  unfold MachineData.storeK at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · cases xcl with
    | false => exact hk _ _ h
    | true =>
      simp only [ite_true, Effects.All] at h ⊢
      intro b
      cases b with
      | true => exact hk _ _ (h true)
      | false => exact hk _ _ (h false)

theorem rmwK_mono {s : MachineData} {k : Kraken.RmwKind} {noRet : Bool} {addr : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (s.rmwK k noRet addr w op r₁).All P₁) : (s.rmwK k noRet addr w op r₂).All P₂ := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
  · exact h
  · cases ho : op _ <;> simp only [ho] at h ⊢ <;> exact hk _ _ h

theorem loadPairK_mono {s : MachineData} {k : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {r₁ r₂ : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ s', (r₁ v₁ v₂ s').All P₁ → (r₂ v₁ v₂ s').All P₂)
    (h : (s.loadPairK k xcl addr w r₁).All P₁) : (s.loadPairK k xcl addr w r₂).All P₂ := by
  unfold MachineData.loadPairK at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hm₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [hm₁, hm₂, Effects.All] at h ⊢
  exact hk _ _ _ h

theorem storePairK_mono {s : MachineData} {k : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {v₁ v₂ : w.type} {r₁ r₂ : Bool → MachineData → Effects}
    (hk : ∀ b s', (r₁ b s').All P₁ → (r₂ b s').All P₂)
    (h : (s.storePairK k xcl addr v₁ v₂ r₁).All P₁) : (s.storePairK k xcl addr v₁ v₂ r₂).All P₂ := by
  unfold MachineData.storePairK at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hm₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [hm₁, hm₂, Effects.All] at h ⊢
  cases xcl with
  | false => exact hk _ _ h
  | true =>
    simp only [ite_true, Effects.All] at h ⊢
    intro b
    cases b with
    | true => exact hk _ _ (h true)
    | false => exact hk _ _ (h false)

theorem rmwPairK_mono {s : MachineData} {k : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c₁ c₂ n₁ n₂ : w.type} {r₁ r₂ : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ s', (r₁ v₁ v₂ s').All P₁ → (r₂ v₁ v₂ s').All P₂)
    (h : (s.rmwPairK k addr c₁ c₂ n₁ n₂ r₁).All P₁) : (s.rmwPairK k addr c₁ c₂ n₁ n₂ r₂).All P₂ := by
  unfold MachineData.rmwPairK at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hm₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [hm₁, hm₂, Effects.All] at h ⊢
  split at h
  · rename_i hc; rw [if_pos hc]; exact hk _ _ _ h
  · rename_i hc; rw [if_neg hc]; exact hk _ _ _ h

theorem AddrExpr.checkSPAlignment_mono {a : AddrExpr} {s : MachineData}
    {ok₁ ok₂ : Unit → Effects} (hk : (ok₁ ()).All P₁ → (ok₂ ()).All P₂)
    (h : (a.checkSPAlignment s ok₁).All P₁) : (a.checkSPAlignment s ok₂).All P₂ := by
  unfold AddrExpr.checkSPAlignment at h ⊢
  generalize a.base = b at h ⊢
  cases b with
  | low x w' =>
    cases x with
    | reg x => exact hk h
    | SP =>
      simp only at h ⊢
      split at h
      · exact h.elim
      · rename_i hc
        rw [ite_eq_right hc]
        exact hk h

theorem UnscaledAddrExpr.checkSPAlignment_mono {a : UnscaledAddrExpr} {s : MachineData}
    {ok₁ ok₂ : Unit → Effects} (hk : (ok₁ ()).All P₁ → (ok₂ ()).All P₂)
    (h : (a.checkSPAlignment s ok₁).All P₁) : (a.checkSPAlignment s ok₂).All P₂ := by
  unfold UnscaledAddrExpr.checkSPAlignment at h ⊢
  generalize a.base = b at h ⊢
  cases b with
  | low x w' =>
    cases x with
    | reg x => exact hk h
    | SP =>
      simp only at h ⊢
      split at h
      · exact h.elim
      · rename_i hc
        rw [ite_eq_right hc]
        exact hk h

theorem interpBase_mono {base : RegOrSp .W64} {s : MachineData}
    {ok₁ ok₂ : BitVec 64 → Effects} (hk : ∀ a, (ok₁ a).All P₁ → (ok₂ a).All P₂)
    (h : (base.interpBase s ok₁).All P₁) : (base.interpBase s ok₂).All P₂ := by
  unfold RegOrSp.interpBase at h ⊢
  cases base with
  | low x w' =>
    cases x with
    | reg x => exact hk _ h
    | SP =>
      simp only at h ⊢
      split at h
      · exact h.elim
      · rename_i hc
        rw [ite_eq_right hc]
        exact hk _ h

theorem AddrExpr.interpLoad_mono [Labels] {w : MemWidth} {a : AddrExpr} {s : MachineData}
    {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (a.interpLoad s p r₁).All P₁) : (a.interpLoad s p r₂).All P₂ := by
  unfold AddrExpr.interpLoad at h ⊢
  refine AddrExpr.checkSPAlignment_mono (fun h => ?_) h
  exact load_mono hk h

theorem AddrExpr.interpStore_mono [Labels] {w : MemWidth} {a : AddrExpr} {s : MachineData}
    {p : Std.Rco Int64} {v : w.type} {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (a.interpStore s p v r₁).All P₁) : (a.interpStore s p v r₂).All P₂ := by
  unfold AddrExpr.interpStore at h ⊢
  refine AddrExpr.checkSPAlignment_mono (fun h => ?_) h
  exact store_mono hk h

theorem UnscaledAddrExpr.interpLoad_mono [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (a.interpLoad s p r₁).All P₁) : (a.interpLoad s p r₂).All P₂ := by
  unfold UnscaledAddrExpr.interpLoad at h ⊢
  exact UnscaledAddrExpr.checkSPAlignment_mono (fun h => load_mono hk h) h

theorem UnscaledAddrExpr.interpStore_mono [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {s : MachineData} {p : Std.Rco Int64} {v : w.type} {r₁ r₂ : MachineData → Effects}
    (hk : ∀ s', (r₁ s').All P₁ → (r₂ s').All P₂)
    (h : (a.interpStore s p v r₁).All P₁) : (a.interpStore s p v r₂).All P₂ := by
  unfold UnscaledAddrExpr.interpStore at h ⊢
  exact UnscaledAddrExpr.checkSPAlignment_mono (fun h => store_mono hk h) h

theorem AddrOrLit.interpLoad_mono [Labels] {w : MemWidth} {a : AddrOrLit} {s : MachineData}
    {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hk : ∀ v s', (r₁ v s').All P₁ → (r₂ v s').All P₂)
    (h : (a.interpLoad s p r₁).All P₁) : (a.interpLoad s p r₂).All P₂ := by
  cases a with
  | addr a => exact AddrExpr.interpLoad_mono hk h
  | lit l =>
    cases l with
    | addr a => exact load_mono hk h
    | pool q => exact hk _ _ h

/-! ## The search over the instruction set -/

/- The dictionary lemmas are applied by search: at each goal the tactic tries
them in turn. Sealing the primitives they are keyed on makes a failed attempt
a comparison of head symbols instead of a reduction of a machine step (see
x64's `Kraken/InterpSound.lean`). -/
set_option allowUnsafeReducibility true in
attribute [local irreducible] MachineData.load MachineData.store MachineData.loadK
  MachineData.storeK MachineData.rmwK MachineData.loadPairK MachineData.storePairK MachineData.rmwPairK
  AddrExpr.interpLoad AddrExpr.interpStore
  UnscaledAddrExpr.interpLoad UnscaledAddrExpr.interpStore AddrOrLit.interpLoad
  AddrExpr.checkSPAlignment UnscaledAddrExpr.checkSPAlignment RegOrSp.interpBase

set_option hygiene false in
/-- Reduce the interpreter on both sides and apply the dictionary until the
continuation hypotheses `hk`/`hj` close every leaf. -/
local macro "mono_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp] at h ⊢ <;>
    repeat' first
      | exact hk _ h
      | exact hj _ _ h
      | refine AddrOrLit.interpLoad_mono (fun v s' h => ?_) h
      | refine AddrExpr.interpLoad_mono (fun v s' h => ?_) h
      | refine UnscaledAddrExpr.interpLoad_mono (fun v s' h => ?_) h
      | refine AddrExpr.interpStore_mono (fun s' h => ?_) h
      | refine UnscaledAddrExpr.interpStore_mono (fun s' h => ?_) h
      | refine AddrExpr.checkSPAlignment_mono (fun h => ?_) h
      | refine load_mono (fun v s' h => ?_) h
      | refine store_mono (fun s' h => ?_) h
      | refine loadK_mono (fun v s' h => ?_) h
      | refine storeK_mono (fun b s' h => ?_) h
      | refine rmwK_mono (fun v s' h => ?_) h
      | refine loadPairK_mono (fun v₁ v₂ s' h => ?_) h
      | refine storePairK_mono (fun b s' h => ?_) h
      | refine rmwPairK_mono (fun v₁ v₂ s' h => ?_) h
      | refine interpBase_mono (fun a h => ?_) h
      | (simp only [Effects.All] at h ⊢; exact h)
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setRegOrZr, MachineData.setRegOrSp] at h ⊢))

/-- The interpreter of one operation is monotone in its continuations. -/
theorem operation_mono [Labels] {w : RegWidth} {op : Operation w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s', (k₁ s').All P₁ → (k₂ s').All P₂)
    (hj : ∀ pc s', (j₁ pc s').All P₁ → (j₂ pc s').All P₂)
    (h : (Operation.interp op p s k₁ j₁).All P₁) :
    (Operation.interp op p s k₂ j₂).All P₂ := by
  cases op
  -- `SVC` halts (`MachineData.pendingSyscall`): nothing holds past it.
  case SVC imm => simp only [Operation.interp, MachineData.pendingSyscall, Effects.All] at h
  all_goals mono_search

end InterpSound

section WP1Sound

open InterpSound

/-- A directive's interpreter is monotone in its continuations. -/
theorem Directive.interp_mono [Labels] {P₁ P₂ : MachineState → Prop}
    {d : Directive} {p : Std.Rco Int64} {s : MachineData}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s', (k₁ s').All P₁ → (k₂ s').All P₂)
    (hj : ∀ pc s', (j₁ pc s').All P₁ → (j₂ pc s').All P₂)
    (h : (d.interp s p k₁ j₁).All P₁) : (d.interp s p k₂ j₂).All P₂ := by
  cases d with
  | label l => exact hk _ h
  | byteArray bs => simp only [Directive.interp, Effects.All] at h
  | instr i =>
    simp only [Directive.interp, Instr.interp, Effects.All] at h ⊢
    exact operation_mono hk hj h

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
  rcases h with h | h
  · exact Directive.interp_mono (P₁ := fun st => next st.1)
      (k₁ := fun s' => .done (s', 0)) (j₁ := fun _ _ => .unimplemented "jump")
      (fun s' h => hnext s' h) (fun _ _ h => h.elim) h
  · exact Directive.interp_mono (P₁ := jmp)
      (k₁ := fun _ => .unimplemented "fallthrough") (j₁ := fun pc' s' => .done (s', pc'))
      (fun _ h => h.elim) (fun pc' s' h => hjmp (s', pc') h) h

end WP1Sound

/-! ## Label cells

Shared by the bridges to the segment judgment (`Kraken/AArch64/WP/Bridge.lean`) and the
Promising links (`Kraken/Promising/EnvWPAArch64.lean`, `Kraken/Promising/SeqLinkAArch64Step.lean`). -/

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

/- `straightlineStep` is the API boundary: on x64 every proof enters through
`apply straightlineStep_of_wp`, here through `Program.run_of_triple`
(Kraken/AArch64/WP/Bridge.lean). Sealing it keeps that apply fast: whenever a
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
(Kraken/AArch64/WP/SegmentExtract.lean), which rewrite syntactically. -/
set_option allowUnsafeReducibility true in
attribute [irreducible] Kraken.Executable.directivesFromAddress
