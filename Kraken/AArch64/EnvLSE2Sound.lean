/-
Transport of a cell's `AllEnvLSE2` step into the LSE2 interpreter with real
continuations (`Directive.interpLSE2_sound`), the `AllEnvLSE2` counterpart of
`Directive.interp_sound` (`Kraken/AArch64/WP/InterpSound.lean`), whose
dictionary and search this copies with `AllEnvLSE2` for `All`. The link of
the LSE2 judgment to `isaLSE2` (`Kraken.Promising.EnvLSE2AArch64`) consumes
it at every step.

The dictionary proves the more general fact behind it: the interpreter is
monotone in its continuations for `AllEnvLSE2` (`EnvLSE2Sound.operation_mono`,
`Directive.interpLSE2_mono`), every primitive passing control to its
continuation with values, states and environment states that do not depend on
the continuation.
-/
import Kraken.AArch64.EnvLSE2

open Kraken

namespace EnvLSE2Sound

variable {D : SharedEnv.Layout} {env : SharedEnv} {P₁ P₂ : MachineState → env.State → Prop}

/-! ## The dictionary: one monotonicity lemma per primitive -/

theorem load_mono {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {r₁ r₂ : w.type → MachineData → Effects} {g : env.State}
    (hk : ∀ v s' g, (r₁ v s').AllEnvLSE2 D env g P₁ → (r₂ v s').AllEnvLSE2 D env g P₂)
    (h : (s.load addr w r₁).AllEnvLSE2 D env g P₁) : (s.load addr w r₂).AllEnvLSE2 D env g P₂ := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllEnvLSE2] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnvLSE2] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs)⟩
  · exact hk _ _ _ h

theorem store_mono {s : MachineData} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    {r₁ r₂ : MachineData → Effects} {g : env.State}
    (hk : ∀ s' g, (r₁ s').AllEnvLSE2 D env g P₁ → (r₂ s').AllEnvLSE2 D env g P₂)
    (h : (s.store addr v r₁).AllEnvLSE2 D env g P₁) : (s.store addr v r₂).AllEnvLSE2 D env g P₂ := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllEnvLSE2] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnvLSE2] at h ⊢
  · exact ⟨h.1, fun b g' hs => hk _ _ (h.2 b g' hs)⟩
  · exact hk _ _ h

theorem loadK_mono {s : MachineData} {k : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {r₁ r₂ : w.type → MachineData → Effects} {g : env.State}
    (hk : ∀ v s' g, (r₁ v s').AllEnvLSE2 D env g P₁ → (r₂ v s').AllEnvLSE2 D env g P₂)
    (h : (s.loadK k xcl addr w r₁).AllEnvLSE2 D env g P₁) :
    (s.loadK k xcl addr w r₂).AllEnvLSE2 D env g P₂ := by
  unfold MachineData.loadK at h ⊢
  simp only [Effects.AllEnvLSE2] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnvLSE2] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs)⟩
  · exact hk _ _ _ h

theorem storeK_mono {s : MachineData} {k : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {v : w.type} {r₁ r₂ : Bool → MachineData → Effects} {g : env.State}
    (hk : ∀ b s' g, (r₁ b s').AllEnvLSE2 D env g P₁ → (r₂ b s').AllEnvLSE2 D env g P₂)
    (h : (s.storeK k xcl addr v r₁).AllEnvLSE2 D env g P₁) :
    (s.storeK k xcl addr v r₂).AllEnvLSE2 D env g P₂ := by
  unfold MachineData.storeK at h ⊢
  simp only [Effects.AllEnvLSE2] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnvLSE2] at h ⊢
  · exact ⟨h.1, fun b g' hs => hk _ _ _ (h.2 b g' hs)⟩
  · cases xcl with
    | false => exact hk _ _ _ h
    | true =>
      simp only [ite_true, Effects.AllEnvLSE2] at h ⊢
      intro b
      cases b with
      | true => exact hk _ _ _ (h true)
      | false => exact hk _ _ _ (h false)

theorem rmwK_mono {s : MachineData} {k : Kraken.RmwKind} {noRet : Bool} {addr : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {r₁ r₂ : w.type → MachineData → Effects} {g : env.State}
    (hk : ∀ v s' g, (r₁ v s').AllEnvLSE2 D env g P₁ → (r₂ v s').AllEnvLSE2 D env g P₂)
    (h : (s.rmwK k noRet addr w op r₁).AllEnvLSE2 D env g P₁) :
    (s.rmwK k noRet addr w op r₂).AllEnvLSE2 D env g P₂ := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllEnvLSE2] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnvLSE2] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs)⟩
  · cases ho : op _ <;> simp only [ho] at h ⊢ <;> exact hk _ _ _ h

theorem loadPairK_mono {s : MachineData} {k : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {r₁ r₂ : w.type → w.type → MachineData → Effects} {g : env.State}
    (hk : ∀ v₁ v₂ s' g, (r₁ v₁ v₂ s').AllEnvLSE2 D env g P₁ → (r₂ v₁ v₂ s').AllEnvLSE2 D env g P₂)
    (h : (s.loadPairK k xcl addr w r₁).AllEnvLSE2 D env g P₁) :
    (s.loadPairK k xcl addr w r₂).AllEnvLSE2 D env g P₂ := by
  unfold MachineData.loadPairK at h ⊢
  simp only [Effects.AllEnvLSE2] at h ⊢
  cases hm₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hm₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [hm₁, hm₂, Effects.AllEnvLSE2] at h ⊢
  · obtain ⟨hx, h1, h2⟩ := h
    exact ⟨hx, fun hm => ⟨(h1 hm).1, fun v g' hs => hk _ _ _ _ ((h1 hm).2 v g' hs)⟩,
      fun hm => ⟨(h2 hm).1, fun v₁ g₁ hs₁ => ⟨((h2 hm).2 v₁ g₁ hs₁).1,
        fun v₂ g₂ hs₂ => hk _ _ _ _ (((h2 hm).2 v₁ g₁ hs₁).2 v₂ g₂ hs₂)⟩⟩⟩
  · exact ⟨h.1, fun v g' hs => hk _ _ _ _ (h.2 v g' hs)⟩
  · exact ⟨h.1, fun v g' hs => hk _ _ _ _ (h.2 v g' hs)⟩
  · exact hk _ _ _ _ h

theorem storePairK_mono {s : MachineData} {k : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {v₁ v₂ : w.type} {r₁ r₂ : Bool → MachineData → Effects} {g : env.State}
    (hk : ∀ b s' g, (r₁ b s').AllEnvLSE2 D env g P₁ → (r₂ b s').AllEnvLSE2 D env g P₂)
    (h : (s.storePairK k xcl addr v₁ v₂ r₁).AllEnvLSE2 D env g P₁) :
    (s.storePairK k xcl addr v₁ v₂ r₂).AllEnvLSE2 D env g P₂ := by
  unfold MachineData.storePairK at h ⊢
  simp only [Effects.AllEnvLSE2] at h ⊢
  cases hm₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hm₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [hm₁, hm₂, Effects.AllEnvLSE2] at h ⊢
  · obtain ⟨hx, h1, h2⟩ := h
    exact ⟨hx, fun hm => ⟨(h1 hm).1, fun b g' hs => hk _ _ _ ((h1 hm).2 b g' hs)⟩,
      fun hm => ⟨(h2 hm).1, fun b₁ g₁ hs₁ => ⟨((h2 hm).2 b₁ g₁ hs₁).1,
        fun b₂ g₂ hs₂ => hk _ _ _ (((h2 hm).2 b₁ g₁ hs₁).2 b₂ g₂ hs₂)⟩⟩⟩
  · refine ⟨h.1, fun b g' hs => ?_⟩
    have h' := h.2 b g' hs
    cases b with
    | true => exact hk _ _ _ h'
    | false => exact hk _ _ _ h'
  · refine ⟨h.1, fun b g' hs => ?_⟩
    have h' := h.2 b g' hs
    cases b with
    | true => exact hk _ _ _ h'
    | false => exact hk _ _ _ h'
  · cases xcl with
    | false => exact hk _ _ _ h
    | true =>
      simp only [ite_true, Effects.AllEnvLSE2] at h ⊢
      intro b
      cases b with
      | true => exact hk _ _ _ (h true)
      | false => exact hk _ _ _ (h false)

theorem rmwPairK_mono {s : MachineData} {k : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c₁ c₂ n₁ n₂ : w.type} {r₁ r₂ : w.type → w.type → MachineData → Effects} {g : env.State}
    (hk : ∀ v₁ v₂ s' g, (r₁ v₁ v₂ s').AllEnvLSE2 D env g P₁ → (r₂ v₁ v₂ s').AllEnvLSE2 D env g P₂)
    (h : (s.rmwPairK k addr c₁ c₂ n₁ n₂ r₁).AllEnvLSE2 D env g P₁) :
    (s.rmwPairK k addr c₁ c₂ n₁ n₂ r₂).AllEnvLSE2 D env g P₂ := by
  unfold MachineData.rmwPairK at h ⊢
  simp only [Effects.AllEnvLSE2] at h ⊢
  cases hm₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hm₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [hm₁, hm₂, Effects.AllEnvLSE2] at h ⊢
  · exact SharedEnv.CaspEnv.mono (fun o₁ o₂ g' => hk _ _ _ g') h
  all_goals try (refine ⟨h.1, fun v g' hs => ?_⟩; replace h := h.2 v g' hs)
  all_goals
    split at h
    · rename_i hc; simp only [hc]; exact hk _ _ _ _ h
    · rename_i hc; simp only [hc]; exact hk _ _ _ _ h

theorem AddrExpr.checkSPAlignment_mono {a : AddrExpr} {s : MachineData} {g : env.State}
    {ok₁ ok₂ : Unit → Effects} (hk : (ok₁ ()).AllEnvLSE2 D env g P₁ → (ok₂ ()).AllEnvLSE2 D env g P₂)
    (h : (a.checkSPAlignment s ok₁).AllEnvLSE2 D env g P₁) : (a.checkSPAlignment s ok₂).AllEnvLSE2 D env g P₂ := by
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

theorem UnscaledAddrExpr.checkSPAlignment_mono {a : UnscaledAddrExpr} {s : MachineData} {g : env.State}
    {ok₁ ok₂ : Unit → Effects} (hk : (ok₁ ()).AllEnvLSE2 D env g P₁ → (ok₂ ()).AllEnvLSE2 D env g P₂)
    (h : (a.checkSPAlignment s ok₁).AllEnvLSE2 D env g P₁) : (a.checkSPAlignment s ok₂).AllEnvLSE2 D env g P₂ := by
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

theorem interpBase_mono {base : RegOrSp .W64} {s : MachineData} {g : env.State}
    {ok₁ ok₂ : BitVec 64 → Effects} (hk : ∀ a, (ok₁ a).AllEnvLSE2 D env g P₁ → (ok₂ a).AllEnvLSE2 D env g P₂)
    (h : (base.interpBase s ok₁).AllEnvLSE2 D env g P₁) : (base.interpBase s ok₂).AllEnvLSE2 D env g P₂ := by
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
    {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects} {g : env.State}
    (hk : ∀ v s' g, (r₁ v s').AllEnvLSE2 D env g P₁ → (r₂ v s').AllEnvLSE2 D env g P₂)
    (h : (a.interpLoad s p r₁).AllEnvLSE2 D env g P₁) : (a.interpLoad s p r₂).AllEnvLSE2 D env g P₂ := by
  unfold AddrExpr.interpLoad at h ⊢
  refine AddrExpr.checkSPAlignment_mono (fun h => ?_) h
  exact load_mono hk h

theorem AddrExpr.interpStore_mono [Labels] {w : MemWidth} {a : AddrExpr} {s : MachineData}
    {p : Std.Rco Int64} {v : w.type} {r₁ r₂ : MachineData → Effects} {g : env.State}
    (hk : ∀ s' g, (r₁ s').AllEnvLSE2 D env g P₁ → (r₂ s').AllEnvLSE2 D env g P₂)
    (h : (a.interpStore s p v r₁).AllEnvLSE2 D env g P₁) : (a.interpStore s p v r₂).AllEnvLSE2 D env g P₂ := by
  unfold AddrExpr.interpStore at h ⊢
  refine AddrExpr.checkSPAlignment_mono (fun h => ?_) h
  exact store_mono hk h

theorem UnscaledAddrExpr.interpLoad_mono [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects} {g : env.State}
    (hk : ∀ v s' g, (r₁ v s').AllEnvLSE2 D env g P₁ → (r₂ v s').AllEnvLSE2 D env g P₂)
    (h : (a.interpLoad s p r₁).AllEnvLSE2 D env g P₁) : (a.interpLoad s p r₂).AllEnvLSE2 D env g P₂ := by
  unfold UnscaledAddrExpr.interpLoad at h ⊢
  exact UnscaledAddrExpr.checkSPAlignment_mono (fun h => load_mono hk h) h

theorem UnscaledAddrExpr.interpStore_mono [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {s : MachineData} {p : Std.Rco Int64} {v : w.type} {r₁ r₂ : MachineData → Effects} {g : env.State}
    (hk : ∀ s' g, (r₁ s').AllEnvLSE2 D env g P₁ → (r₂ s').AllEnvLSE2 D env g P₂)
    (h : (a.interpStore s p v r₁).AllEnvLSE2 D env g P₁) : (a.interpStore s p v r₂).AllEnvLSE2 D env g P₂ := by
  unfold UnscaledAddrExpr.interpStore at h ⊢
  exact UnscaledAddrExpr.checkSPAlignment_mono (fun h => store_mono hk h) h

theorem AddrOrLit.interpLoad_mono [Labels] {w : MemWidth} {a : AddrOrLit} {s : MachineData}
    {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects} {g : env.State}
    (hk : ∀ v s' g, (r₁ v s').AllEnvLSE2 D env g P₁ → (r₂ v s').AllEnvLSE2 D env g P₂)
    (h : (a.interpLoad s p r₁).AllEnvLSE2 D env g P₁) : (a.interpLoad s p r₂).AllEnvLSE2 D env g P₂ := by
  cases a with
  | addr a => exact AddrExpr.interpLoad_mono hk h
  | lit l =>
    cases l with
    | addr a => exact load_mono hk h
    | pool q => exact hk _ _ _ h

/-! ## The search over the instruction set -/

/- As in `Kraken/AArch64/WP/InterpSound.lean`: the dictionary lemmas are
applied by search, the primitives they are keyed on sealed. -/
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
      | exact hk _ _ h
      | exact hj _ _ _ h
      | refine AddrOrLit.interpLoad_mono (fun v s' g h => ?_) h
      | refine AddrExpr.interpLoad_mono (fun v s' g h => ?_) h
      | refine UnscaledAddrExpr.interpLoad_mono (fun v s' g h => ?_) h
      | refine AddrExpr.interpStore_mono (fun s' g h => ?_) h
      | refine UnscaledAddrExpr.interpStore_mono (fun s' g h => ?_) h
      | refine AddrExpr.checkSPAlignment_mono (fun h => ?_) h
      | refine load_mono (fun v s' g h => ?_) h
      | refine store_mono (fun s' g h => ?_) h
      | refine loadK_mono (fun v s' g h => ?_) h
      | refine storeK_mono (fun b s' g h => ?_) h
      | refine rmwK_mono (fun v s' g h => ?_) h
      | refine loadPairK_mono (fun v₁ v₂ s' g h => ?_) h
      | refine storePairK_mono (fun b s' g h => ?_) h
      | refine rmwPairK_mono (fun v₁ v₂ s' g h => ?_) h
      | refine interpBase_mono (fun a h => ?_) h
      | (simp only [Effects.AllEnvLSE2] at h ⊢; exact h)
      | (refine ⟨h.1, fun g' hs => ?_⟩; replace h := h.2 g' hs)
      | (refine fun v => ?_; specialize h v)
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllEnvLSE2] at h ⊢))

/-- The interpreter of one operation is monotone in its continuations, for
`AllEnvLSE2`. -/
theorem operation_mono [Labels] {w : RegWidth} {op : Operation w} {p : Std.Rco Int64}
    {s : MachineData} {g : env.State} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s' g, (k₁ s').AllEnvLSE2 D env g P₁ → (k₂ s').AllEnvLSE2 D env g P₂)
    (hj : ∀ pc s' g, (j₁ pc s').AllEnvLSE2 D env g P₁ → (j₂ pc s').AllEnvLSE2 D env g P₂)
    (h : (Operation.interp op p s k₁ j₁).AllEnvLSE2 D env g P₁) :
    (Operation.interp op p s k₂ j₂).AllEnvLSE2 D env g P₂ := by
  cases op <;> mono_search

/-- The FEAT_LSE2 reading of an aligned `LDP`/`STP` is monotone in its
continuation. -/
theorem interpLSE2?_mono [Labels] {d : Directive} {p : Std.Rco Int64} {s : MachineData} {g : env.State}
    {k₁ k₂ : MachineData → Effects} {e₁ e₂ : Effects}
    (hk : ∀ s' g, (k₁ s').AllEnvLSE2 D env g P₁ → (k₂ s').AllEnvLSE2 D env g P₂)
    (h₁ : d.interpLSE2? s p k₁ = some e₁) (h₂ : d.interpLSE2? s p k₂ = some e₂)
    (h : e₁.AllEnvLSE2 D env g P₁) : e₂.AllEnvLSE2 D env g P₂ := by
  unfold Directive.interpLSE2? at h₁ h₂
  split at h₁
  · rename_i d₁ d₂ a
    rcases hev : a.eval s p with ⟨addr, s'⟩
    simp only [hev] at h₁ h₂
    split at h₁
    · cases h₁
    · rename_i hal
      simp only [hal, Bool.false_eq_true, ite_false, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      refine AddrExpr.checkSPAlignment_mono (fun h => ?_) h
      refine loadPairK_mono (fun v₁ v₂ s'' g h => ?_) h
      simp only [MachineData.setRegOrZr] at h ⊢
      exact hk _ _ h
  · rename_i s₁ s₂ a
    rcases hev : a.eval s p with ⟨addr, s'⟩
    simp only [hev] at h₁ h₂
    split at h₁
    · cases h₁
    · rename_i hal
      simp only [hal, Bool.false_eq_true, ite_false, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      refine AddrExpr.checkSPAlignment_mono (fun h => ?_) h
      exact storePairK_mono (fun b s'' g h => hk _ _ h) h
  · cases h₁

end EnvLSE2Sound

section Sound

open EnvLSE2Sound

variable {D : SharedEnv.Layout} {env : SharedEnv}

/-- A directive's interpreter is monotone in its continuations, for
`AllEnvLSE2`. -/
theorem Directive.interp_mono_lse2 [Labels] {P₁ P₂ : MachineState → env.State → Prop}
    {d : Directive} {p : Std.Rco Int64} {s : MachineData} {g : env.State}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s' g, (k₁ s').AllEnvLSE2 D env g P₁ → (k₂ s').AllEnvLSE2 D env g P₂)
    (hj : ∀ pc s' g, (j₁ pc s').AllEnvLSE2 D env g P₁ → (j₂ pc s').AllEnvLSE2 D env g P₂)
    (h : (d.interp s p k₁ j₁).AllEnvLSE2 D env g P₁) : (d.interp s p k₂ j₂).AllEnvLSE2 D env g P₂ := by
  cases d with
  | label l => exact hk _ _ h
  | byteArray bs => simp only [Directive.interp, Effects.AllEnvLSE2] at h
  | instr i =>
    simp only [Directive.interp, Instr.interp, Effects.AllEnvLSE2] at h ⊢
    exact operation_mono hk hj h

/-- The LSE2 interpreter of a directive is monotone in its continuations. -/
theorem Directive.interpLSE2_mono [Labels] {P₁ P₂ : MachineState → env.State → Prop}
    {d : Directive} {p : Std.Rco Int64} {s : MachineData} {g : env.State}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s' g, (k₁ s').AllEnvLSE2 D env g P₁ → (k₂ s').AllEnvLSE2 D env g P₂)
    (hj : ∀ pc s' g, (j₁ pc s').AllEnvLSE2 D env g P₁ → (j₂ pc s').AllEnvLSE2 D env g P₂)
    (h : (d.interpLSE2 s p k₁ j₁).AllEnvLSE2 D env g P₁) :
    (d.interpLSE2 s p k₂ j₂).AllEnvLSE2 D env g P₂ := by
  unfold Directive.interpLSE2 at h ⊢
  cases h₁ : d.interpLSE2? s p k₁ <;> cases h₂ : d.interpLSE2? s p k₂ <;>
    simp only [h₁, Option.getD_none, Option.getD_some] at h ⊢
  · exact Directive.interp_mono_lse2 hk hj h
  · -- whether the reading applies does not depend on the continuation
    exfalso
    unfold Directive.interpLSE2? at h₁ h₂
    split at h₁ <;> simp_all
  · exfalso
    unfold Directive.interpLSE2? at h₁ h₂
    split at h₁ <;> simp_all
  · exact interpLSE2?_mono hk h₁ h₂ h

/-- **Transport.** A cell's `AllEnvLSE2` step, either disjunct, is the LSE2
interpreter with real continuations: the `AllEnvLSE2` counterpart of
`Directive.interp_sound`. -/
theorem Directive.interpLSE2_sound [Labels] {P : MachineState → env.State → Prop}
    {d : Directive} {p : Std.Rco Int64} {s : MachineData} {g : env.State}
    {next : MachineData → env.State → Prop} {jmp : MachineState → env.State → Prop}
    {k : MachineData → Effects}
    (hnext : ∀ s' g', next s' g' → (k s').AllEnvLSE2 D env g' P) (hjmp : ∀ st g', jmp st g' → P st g')
    (h : (d.interpLSE2 s p (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).AllEnvLSE2 D env g
           (fun st g' => next st.1 g')
       ∨ (d.interpLSE2 s p (fun _ => .unimplemented "fallthrough")
           (fun pc' s' => .done (s', pc'))).AllEnvLSE2 D env g jmp) :
    (d.interpLSE2 s p k (fun pc' s' => .done (s', pc'))).AllEnvLSE2 D env g P := by
  rcases h with h | h
  · exact Directive.interpLSE2_mono (P₁ := fun st g' => next st.1 g')
      (k₁ := fun s' => .done (s', 0)) (j₁ := fun _ _ => .unimplemented "jump")
      (fun s' g' h => hnext s' g' h) (fun _ _ _ h => h.elim) h
  · exact Directive.interpLSE2_mono (P₁ := jmp)
      (k₁ := fun _ => .unimplemented "fallthrough") (j₁ := fun pc' s' => .done (s', pc'))
      (fun _ _ h => h.elim) (fun pc' s' g' h => hjmp (s', pc') g' h) h

end Sound
