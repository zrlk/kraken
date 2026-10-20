/-
The invariant environment and the full Promising machine, AArch64 (design note
`Kraken/Promising/EnvWP.md`, "Invariant environment").

A thread proved by `vcgen`/`cfgEnv` (a `TripleEnv`, `PartialTripleEnv`, or any
`Eventually`/`Safely` judgment of `instrStepEnv`) in `SharedEnv.inv S G` is a
`ThreadSpec`: a code `e`, an end address, a postcondition `P` and an inductive
invariant `Inv` of the environment step relation (`Safely` itself is one,
`ThreadSpec.ofSafely`). `ThreadSpec.Holds` reads it at a thread state of the
Promising machine. Then:

- `isim` (per primitive, then `operation_isim` by search, as `esim` in
  `EnvWPAArch64.lean`): an `AllEnv (inv S G)` judgment of a cell's step is an
  `EvTree.AllInv G` judgment of the adapter's tree with real continuations.
  `CASP` with both halves shared is `CaspEnv` against `caspTree` (two
  per-half `rmw`s, in either order, success chosen up front).
- `threadSpec_stepPreserves`: one instruction from a state where the spec
  holds, against a memory satisfying `MemInv G`, keeps the spec and
  `MemInv G`.
- `inv_reachable` (Links A and B): if every thread of `c0` satisfies its spec
  and `MemInv G c0.mem`, then at every `Reachable` configuration (any number
  of threads, each its own program, promises included) `MemInv G` holds and
  every thread still satisfies its spec, so its invariant holds, and at its
  end address its postcondition (`inv_reachable_post`). `inv_writesPreserve`:
  the premise of `write_invariant`.
-/
import Kraken.Promising.EnvLinkTermAArch64
import Kraken.Promising.CertifyAArch64
import Kraken.Promising.InvLink
import Kraken.SharedEnvInv

open Kraken

namespace Kraken.Promising.AArch64

/-! ## The simulation, per primitive -/

section ISim

variable {S : SharedEnv.Layout} {G : Loc → Val → Prop} {P₁ : MachineState → Unit → Prop}
  {Q : MachineState → Prop}

local notation "IE" => SharedEnv.inv S G

theorem load_isim {s : MachineData} {addr : BitVec 64} {w : MemWidth} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (h : (MachineData.load s addr w k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.load s addr w k₂)).AllInv G Q := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact fun v hv => hk _ _ (h.2 v () hv)

theorem loadK_isim {s : MachineData} {lk : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (h : (MachineData.loadK s lk xcl addr w k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.loadK s lk xcl addr w k₂)).AllInv G Q := by
  unfold MachineData.loadK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact fun v hv => hk _ _ (h.2 v () hv)

theorem store_isim {s : MachineData} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s, (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (h : (MachineData.store s addr v k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.store s addr v k₂)).AllInv G Q := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact ⟨h.1.2, fun b _ => hk _ (h.2 true () (.inl rfl))⟩

theorem storeK_isim {s : MachineData} {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {v : w.type} {k₁ k₂ : Bool → MachineData → Effects}
    (hk : ∀ b s, (k₁ b s).AllEnv IE () P₁ → (toEv {} (k₂ b s)).AllInv G Q)
    (h : (MachineData.storeK s sk xcl addr v k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.storeK s sk xcl addr v k₂)).AllInv G Q := by
  unfold MachineData.storeK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases xcl with
    | false => exact hk _ _ h
    | true =>
      simp only [ite_true, Effects.AllEnv, toEv, EvTree.AllInv] at h ⊢
      intro i
      have hi := h (i.val == 1)
      split at hi <;> rename_i hb <;> simp only [hb, ite_true, ite_false, Bool.false_eq_true] <;>
        exact hk _ _ hi
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact ⟨h.1.2, fun b hb => hk _ _ (h.2 b () hb)⟩

theorem rmwK_isim {s : MachineData} {rk : Kraken.RmwKind} {nr : Bool} {addr : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (h : (MachineData.rmwK s rk nr addr w op k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.rmwK s rk nr addr w op k₂)).AllInv G Q := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt w.bits x) <;> rw [hop] at h <;> exact hk _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact fun old hold => ⟨fun v hv => h.1.2 old hold v hv, hk _ _ (h.2 old () hold)⟩

/-- The pair primitives. A pair with both halves outside `dmem` is `False` in
`AllEnv`, except `CASP` (`CaspEnv` against `caspTree`); one with a half in
`dmem` is a single access on the other half. -/
theorem loadPairK_isim {s : MachineData} {lk : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {k₁ k₂ : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ s, (k₁ v₁ v₂ s).AllEnv IE () P₁ → (toEv {} (k₂ v₁ v₂ s)).AllInv G Q)
    (h : (MachineData.loadPairK s lk xcl addr w k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.loadPairK s lk xcl addr w k₂)).AllInv G Q := by
  unfold MachineData.loadPairK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hd₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    rw [hd₁, hd₂] at h <;> simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
  · exact fun v hv => hk _ _ _ (h.2 v () hv)
  · exact fun v hv => hk _ _ _ (h.2 v () hv)
  · exact hk _ _ _ h

theorem storePairK_isim {s : MachineData} {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {v₁ v₂ : w.type} {k₁ k₂ : Bool → MachineData → Effects}
    (hk : ∀ b s, (k₁ b s).AllEnv IE () P₁ → (toEv {} (k₂ b s)).AllInv G Q)
    (h : (MachineData.storePairK s sk xcl addr v₁ v₂ k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.storePairK s sk xcl addr v₁ v₂ k₂)).AllInv G Q := by
  unfold MachineData.storePairK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hd₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    rw [hd₁, hd₂] at h <;> simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
  · refine ⟨h.1.2, fun b hb => ?_⟩
    have h' := h.2 b () hb
    cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h' ⊢ <;> exact hk _ _ h'
  · refine ⟨h.1.2, fun b hb => ?_⟩
    have h' := h.2 b () hb
    cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h' ⊢ <;> exact hk _ _ h'
  · cases xcl with
    | false => exact hk _ _ h
    | true =>
      simp only [ite_true, Effects.AllEnv, toEv, EvTree.AllInv] at h ⊢
      intro i
      have hi := h (i.val == 1)
      split at hi <;> rename_i hb <;> simp only [hb, ite_true, ite_false, Bool.false_eq_true] <;>
        exact hk _ _ hi

/-- A `guard` of `caspTree`: an empty `choose` has no run. -/
theorem allInv_guard {σ : Type} {Q : σ → Prop} {b : Bool} {t : EvTree σ} {k : Fin 0 → EvTree σ}
    (h : b = true → t.AllInv G Q) : (if b = true then t else EvTree.choose 0 k).AllInv G Q := by
  cases b
  · exact fun i => i.elim0
  · exact h rfl

/-- `CASP` with both halves shared: `CaspEnv` in `inv S G` is `AllInv` of
`caspTree`, for every success bit and order. -/
theorem caspTree_isim {k : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth} {c₁ c₂ n₁ n₂ : w.type}
    {K : w.type → w.type → Unit → Prop} {ret : w.type → w.type → EvTree MachineState}
    (hk : ∀ o₁ o₂, K o₁ o₂ () → (ret o₁ o₂).AllInv G Q)
    (h : (IE).CaspEnv k addr w c₁ c₂ n₁ n₂ () K) :
    (caspTree {} k addr c₁ c₂ n₁ n₂ ret).AllInv G Q := by
  unfold caspTree
  simp only [EvTree.AllInv, EvTree.access_empty]
  rintro ⟨sv, hsv⟩ ⟨rv, hrv⟩
  obtain rfl | rfl : sv = 0 ∨ sv = 1 := (by omega)
  all_goals obtain rfl | rfl : rv = 0 ∨ rv = 1 := (by omega)
  · have hs := h false false
    simp only [Bool.false_eq_true, ite_false, ite_true, SharedEnv.inv_ok_rmw, 
      rmwOpBits, Nat.reduceBEq] at hs ⊢
    intro o₁ h₁
    obtain ⟨⟨-, hop₁⟩, hs⟩ := hs
    obtain ⟨⟨-, hop₂⟩, hs⟩ := hs o₁ () h₁
    refine ⟨hop₁ o₁ h₁, fun o₂ h₂ => ⟨hop₂ o₂ h₂, ?_⟩⟩
    exact allInv_guard fun hc => hk _ _ (hs o₂ () h₂ (beq_iff_eq.mp hc))
  · have hs := h false true
    simp only [Bool.false_eq_true, ite_false, ite_true, SharedEnv.inv_ok_rmw, 
      rmwOpBits, Nat.reduceBEq] at hs ⊢
    intro o₁ h₁
    obtain ⟨⟨-, hop₂⟩, hs⟩ := hs
    obtain ⟨⟨-, hop₁⟩, hs⟩ := hs o₁ () h₁
    refine ⟨hop₂ o₁ h₁, fun o₂ h₂ => ⟨hop₁ o₂ h₂, ?_⟩⟩
    exact allInv_guard fun hc => hk _ _ (hs o₂ () h₂ (beq_iff_eq.mp hc))
  · have hs := h true false
    simp only [Bool.false_eq_true, ite_false, ite_true, SharedEnv.inv_ok_rmw, 
      rmwOpBits, Nat.reduceBEq] at hs ⊢
    intro o₁ h₁
    obtain ⟨⟨-, hop₁⟩, hs⟩ := hs
    obtain ⟨⟨-, hop₂⟩, hs⟩ := hs o₁ () h₁
    refine ⟨hop₁ o₁ h₁, fun o₂ h₂ => ⟨hop₂ o₂ h₂, ?_⟩⟩
    exact allInv_guard fun hc => hk _ _ (hs o₂ () h₂ (beq_iff_eq.mp hc))
  · have hs := h true true
    simp only [Bool.false_eq_true, ite_false, ite_true, SharedEnv.inv_ok_rmw, 
      rmwOpBits, Nat.reduceBEq] at hs ⊢
    intro o₁ h₁
    obtain ⟨⟨-, hop₂⟩, hs⟩ := hs
    obtain ⟨⟨-, hop₁⟩, hs⟩ := hs o₁ () h₁
    refine ⟨hop₂ o₁ h₁, fun o₂ h₂ => ⟨hop₁ o₂ h₂, ?_⟩⟩
    exact allInv_guard fun hc => hk _ _ (hs o₂ () h₂ (beq_iff_eq.mp hc))
theorem rmwPairK_isim {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c₁ c₂ n₁ n₂ : w.type} {k₁ k₂ : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ s, (k₁ v₁ v₂ s).AllEnv IE () P₁ → (toEv {} (k₂ v₁ v₂ s)).AllInv G Q)
    (h : (MachineData.rmwPairK s rk addr c₁ c₂ n₁ n₂ k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.rmwPairK s rk addr c₁ c₂ n₁ n₂ k₂)).AllInv G Q := by
  unfold MachineData.rmwPairK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hd₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    rw [hd₁, hd₂] at h <;> simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
  · exact caspTree_isim (fun o₁ o₂ h => hk _ _ _ h) h
  · intro old hold
    refine ⟨fun v hv => h.1.2 old hold v hv, ?_⟩
    have h' := h.2 old () hold
    split at h' <;> rename_i hc <;> simp only [hc, ite_true, ite_false, Bool.false_eq_true] <;> exact hk _ _ _ h'
  · intro old hold
    refine ⟨fun v hv => h.1.2 old hold v hv, ?_⟩
    have h' := h.2 old () hold
    split at h' <;> rename_i hc <;> simp only [hc, ite_true, ite_false, Bool.false_eq_true] <;> exact hk _ _ _ h'
  · split at h <;> rename_i hc <;> simp only [hc, ite_true, ite_false, Bool.false_eq_true] <;> exact hk _ _ _ h

/-! ### Per addressing form -/

theorem AddrExpr.checkSPAlignment_isim {a : AddrExpr} {s : MachineData} {ok₁ ok₂ : Unit → Effects}
    (hk : (ok₁ ()).AllEnv IE () P₁ → (toEv {} (ok₂ ())).AllInv G Q)
    (h : (a.checkSPAlignment s ok₁).AllEnv IE () P₁) : (toEv {} (a.checkSPAlignment s ok₂)).AllInv G Q := by
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

theorem UnscaledAddrExpr.checkSPAlignment_isim {a : UnscaledAddrExpr} {s : MachineData}
    {ok₁ ok₂ : Unit → Effects}
    (hk : (ok₁ ()).AllEnv IE () P₁ → (toEv {} (ok₂ ())).AllInv G Q)
    (h : (a.checkSPAlignment s ok₁).AllEnv IE () P₁) : (toEv {} (a.checkSPAlignment s ok₂)).AllInv G Q := by
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

theorem interpBase_isim {base : RegOrSp .W64} {s : MachineData} {ok₁ ok₂ : BitVec 64 → Effects}
    (hk : ∀ a, (ok₁ a).AllEnv IE () P₁ → (toEv {} (ok₂ a)).AllInv G Q)
    (h : (base.interpBase s ok₁).AllEnv IE () P₁) : (toEv {} (base.interpBase s ok₂)).AllInv G Q := by
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

theorem AddrExpr.interpLoad_isim [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64} {s : MachineData}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (h : (a.interpLoad s p k₁).AllEnv IE () P₁) : (toEv {} (a.interpLoad s p k₂)).AllInv G Q := by
  unfold AddrExpr.interpLoad at h ⊢
  refine AddrExpr.checkSPAlignment_isim (fun h => ?_) h
  exact load_isim hk h

theorem AddrExpr.interpStore_isim [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64}
    {s : MachineData} {v : w.type} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s, (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (h : (a.interpStore s p v k₁).AllEnv IE () P₁) : (toEv {} (a.interpStore s p v k₂)).AllInv G Q := by
  unfold AddrExpr.interpStore at h ⊢
  refine AddrExpr.checkSPAlignment_isim (fun h => ?_) h
  exact store_isim hk h

theorem UnscaledAddrExpr.interpLoad_isim [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (h : (a.interpLoad s p k₁).AllEnv IE () P₁) : (toEv {} (a.interpLoad s p k₂)).AllInv G Q := by
  unfold UnscaledAddrExpr.interpLoad at h ⊢
  refine UnscaledAddrExpr.checkSPAlignment_isim (fun h => ?_) h
  exact load_isim hk h

theorem UnscaledAddrExpr.interpStore_isim [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {s : MachineData} {v : w.type} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s, (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (h : (a.interpStore s p v k₁).AllEnv IE () P₁) : (toEv {} (a.interpStore s p v k₂)).AllInv G Q := by
  unfold UnscaledAddrExpr.interpStore at h ⊢
  refine UnscaledAddrExpr.checkSPAlignment_isim (fun h => ?_) h
  exact store_isim hk h

theorem AddrOrLit.interpLoad_isim [Labels] {w : MemWidth} {a : AddrOrLit} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (h : (a.interpLoad s p k₁).AllEnv IE () P₁) : (toEv {} (a.interpLoad s p k₂)).AllInv G Q := by
  cases a with
  | addr a => exact AddrExpr.interpLoad_isim hk h
  | lit l =>
    cases l with
    | addr a => exact load_isim hk h
    | pool q => exact hk _ _ h

/-! ### Per instruction -/

set_option allowUnsafeReducibility true in
attribute [local irreducible] MachineData.load MachineData.store MachineData.loadK MachineData.storeK
  MachineData.rmwK MachineData.loadPairK MachineData.storePairK MachineData.rmwPairK AddrExpr.interpLoad
  AddrExpr.interpStore UnscaledAddrExpr.interpLoad
  UnscaledAddrExpr.interpStore AddrOrLit.interpLoad AddrExpr.checkSPAlignment RegOrSp.interpBase

set_option hygiene false in
/-- Reduce the interpreter on both sides and apply the dictionary until the
continuation hypotheses `hk`/`hj` close every leaf. -/
local macro "isim_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllEnv,
      AddrExpr.eval_mk, toEv, EvTree.AllInv, SharedEnv.inv_ok_fence, SharedEnv.inv_step_fence,
      true_and, forall_const] at h ⊢ <;>
    repeat' first
      | exact hk _ h
      | exact hj _ _ h
      | exact h.elim
      | exact hk _ (h () trivial)
      | exact hk _ (h.2 () trivial)
      | refine AddrOrLit.interpLoad_isim (fun v s h => ?_) h
      | refine AddrExpr.interpLoad_isim (fun v s h => ?_) h
      | refine UnscaledAddrExpr.interpLoad_isim (fun v s h => ?_) h
      | refine AddrExpr.interpStore_isim (fun s h => ?_) h
      | refine UnscaledAddrExpr.interpStore_isim (fun s h => ?_) h
      | refine AddrExpr.checkSPAlignment_isim (fun h => ?_) h
      | refine load_isim (fun v s h => ?_) h
      | refine store_isim (fun s h => ?_) h
      | refine loadK_isim (fun v s h => ?_) h
      | refine storeK_isim (fun b s h => ?_) h
      | refine rmwK_isim (fun v s h => ?_) h
      | refine loadPairK_isim (fun v₁ v₂ s h => ?_) h
      | refine storePairK_isim (fun b s h => ?_) h
      | refine rmwPairK_isim (fun v₁ v₂ s h => ?_) h
      | refine interpBase_isim (fun a h => ?_) h
      | (refine fun v => ?_; specialize h v)
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllEnv,
          AddrExpr.eval_mk, toEv, EvTree.AllInv, SharedEnv.inv_ok_fence, SharedEnv.inv_step_fence,
          true_and, forall_const] at h ⊢))

theorem operation_isim [Labels] {w : RegWidth} (op : Operation w) (p : Std.Rco Int64) {s : MachineData}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s, (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hj : ∀ pc s, (j₁ pc s).AllEnv IE () P₁ → (toEv {} (j₂ pc s)).AllInv G Q)
    (h : (Operation.interp op p s k₁ j₁).AllEnv IE () P₁) :
    (toEv {} (Operation.interp op p s k₂ j₂)).AllInv G Q := by
  cases op <;> isim_search

theorem directive_isim [Labels] (dir : Directive) (p : Std.Rco Int64) {s : MachineData}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s, (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hj : ∀ pc s, (j₁ pc s).AllEnv IE () P₁ → (toEv {} (j₂ pc s)).AllInv G Q)
    (h : (dir.interp s p k₁ j₁).AllEnv IE () P₁) :
    (toEv {} (dir.interp s p k₂ j₂)).AllInv G Q := by
  cases dir with
  | instr i =>
    have h' : (i.interp s p k₁ j₁).AllEnv IE () P₁ := h
    show (toEv {} (i.interp s p k₂ j₂)).AllInv G Q
    unfold Instr.interp at h' ⊢
    exact operation_isim _ _ hk hj h'
  | label l => exact hk _ h
  | byteArray b => exact h.elim

end ISim

/-! ## Instruction steps -/

/-- **One instruction.** At a thread state whose code is `e` (validly laid
out), with no declarations, and away from its end address, an environment step
of `inv S G` from the thread's machine state makes the thread's instruction
tree satisfy `AllInv G`, with every leaf in the step's post-set (and the
code, end address and declarations unchanged). -/
theorem exec_allInv_of_instrStepEnv {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    {R : MachineState × Unit → Prop} (he : st.exe = e) (hds : st.decls = {})
    (h : e.instrStepEnv (SharedEnv.inv S G) (st.st, ()) R) :
    ∀ tree, isa.exec st = some tree →
      tree.AllInv G (fun st' : State => R (st'.st, ()) ∧ st'.exe = st.exe ∧ st'.endPc = st.endPc ∧
        st'.decls = st.decls) := by
  intro tree htree
  obtain ⟨d, sz, rest, hcode, hstep⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat hstep ⊢
  subst he hds
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls := {} } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  simp only [isa, exec, hdir, Option.isNone_some, Bool.or_false] at htree
  split at htree
  · cases htree
  · cases htree
    rw [EvTree.allInv_map]
    unfold Executable.step
    letI := Executable.labels exe
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]
    unfold Kraken.Executable.stepAtEnv at hstep
    generalize pc + Int64.ofNat sz = pc' at hstep ⊢
    rcases hstep with hstep | hstep
    · refine directive_isim d _ ?_ ?_ hstep
      · intro s' h
        exact ⟨h, trivial, trivial, trivial⟩
      · intro _ _ h
        exact h.elim
    · refine directive_isim d _ ?_ ?_ hstep
      · intro _ h
        exact h.elim
      · intro pc s' h
        exact ⟨h, trivial, trivial, trivial⟩

/-! ## Thread specifications -/

/-- What a thread's proof in `inv S G` provides: its code (validly laid
out), end address, postcondition (only at the end address) and an inductive
invariant of the environment step relation: every invariant state satisfies
the postcondition or takes an environment step into invariant states. A
`Safely` judgment is one (`ofSafely`; `TripleEnv`/`cfgEnv` conclusions give
`Eventually`, hence `Safely`). -/
structure ThreadSpec (S : SharedEnv.Layout) (G : Loc → Val → Prop) where
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Unit → Prop
  inv : MachineState × Unit → Prop
  post_end : ∀ y, post y → y.1.2 = endPc
  closed : ∀ y, inv y → post y ∨ ∃ R, e.instrStepEnv (SharedEnv.inv S G) y R ∧ ∀ z, R z → inv z

/-- The specification from a `Safely` judgment (its invariant is `Safely`
itself). -/
def ThreadSpec.ofSafely {S : SharedEnv.Layout} {G : Loc → Val → Prop} (e : Kraken.Executable Directive)
    [hv : Kraken.Executable.ValidLayout e] (endPc : Int64) (P : MachineState × Unit → Prop)
    (hPend : ∀ y, P y → y.1.2 = endPc) : ThreadSpec S G where
  e := e
  valid := hv
  endPc := endPc
  post := P
  inv := Safely (e.instrStepEnv (SharedEnv.inv S G)) P
  post_end := hPend
  closed := fun _ h => h.unfold

/-- The specification holds at a thread state of the Promising machine: its
code, end address, no declarations, and the invariant at its machine state. -/
def ThreadSpec.Holds {S : SharedEnv.Layout} {G : Loc → Val → Prop} (sp : ThreadSpec S G) (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = {} ∧ sp.inv (st.st, ())

/-- The specification of a program `p` proved by a `TripleEnv` in `inv S G`
with no exceptional exit: postcondition `Q` at the end of the text. -/
def ThreadSpec.ofTripleEnv {S : SharedEnv.Layout} {G : Loc → Val → Prop} [layout : _root_.Layout]
    (p : Program) [Kraken.Executable.ValidLayout (layout p)] (Q : MachineData → Unit → Prop) :
    ThreadSpec S G :=
  ThreadSpec.ofSafely (layout p) ((layout p).addrOf p.length)
    (fun x => (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ False)
    (fun _ h => h.elim And.left False.elim)

/-- A thread state at the start of `p`'s text, whose machine state satisfies
the `TripleEnv`'s precondition, satisfies `ofTripleEnv`. -/
theorem ThreadSpec.ofTripleEnv_holds {S : SharedEnv.Layout} {G : Loc → Val → Prop} [CodeEnv]
    [layout : _root_.Layout] {p : Program} [Kraken.Executable.ValidLayout (layout p)]
    {P Q : MachineData → Unit → Prop}
    (ht : MachineWP.TripleEnv (SharedEnv.inv S G) P p Q (fun _ _ _ => False))
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p)
    (hend : st.endPc = (layout p).addrOf p.length) (hds : st.decls = {})
    (hpc : st.st.2 = Kraken.Layout.start Directive) (hP : P st.st.1 ()) :
    (ThreadSpec.ofTripleEnv (S := S) (G := G) p Q).Holds st := by
  refine ⟨he, hend, hds, ?_⟩
  have hev := Program.instrStepEnv_of_tripleEnv ht (s := st.st.1) (g := ()) hP henv
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := Prod.ext rfl hpc
  rw [hst]
  exact Safely.of_eventually hev

/-- A thread specification is kept by every instruction against a memory
satisfying `MemInv G`, which the instruction keeps too. -/
theorem threadSpec_stepPreserves {A : Arch} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (sp : Nat → ThreadSpec S G) :
    StepPreserves (I := isa) A G (fun tid st => (sp tid).Holds st) := by
  intro tid t mem outs o ⟨he, hend, hds, hinv⟩ hm hstep ho
  have hv := (sp tid).valid
  rcases (sp tid).closed _ hinv with hP | ⟨R, hT, hR⟩
  · -- at the end address: the thread has halted
    have hpc : t.st.st.2 = (sp tid).endPc := (sp tid).post_end _ hP
    unfold stepOne at hstep
    have hex : isa.exec t.st = none := by
      show exec t.st = none
      simp [exec, hpc, hend]
    rw [hex] at hstep
    cases hstep
  · obtain ⟨⟨hRo, he', hend', hds'⟩, hm'⟩ :=
      stepOne_allInv A hstep ho (fun tree htree => exec_allInv_of_instrStepEnv he hds hT tree htree) hm
    exact ⟨⟨he'.trans he, hend'.trans hend, hds'.trans hds, hR _ hRo⟩, hm'⟩

/-! ## The links -/

/-- **Links A and B.** If the memory of `c0` satisfies `MemInv G` and every
thread `tid` of `c0` satisfies its specification `sp tid` (a proof in
`inv S G` of its own program), then at every configuration reachable from
`c0` on the full machine (any number of threads, promises included) the
memory satisfies `MemInv G` and every thread still satisfies its
specification, in particular its invariant. -/
theorem inv_reachable {A : Arch} {fuel : Nat} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (sp : Nat → ThreadSpec S G) {c0 c : Config isa} (hm0 : MemInv G c0.mem)
    (h0 : ∀ tid t, c0.threads[tid]? = some t → (sp tid).Holds t.st) (h : Reachable A fuel c0 c) :
    MemInv G c.mem ∧ ∀ tid t, c.threads[tid]? = some t → (sp tid).Holds t.st :=
  configInv_reachable (threadSpec_stepPreserves sp) ⟨hm0, h0⟩ h

/-- **Link A, through `write_invariant`**: the specifications discharge its
premise `WritesPreserve`. -/
theorem inv_writesPreserve {A : Arch} {fuel : Nat} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (sp : Nat → ThreadSpec S G) {c0 : Config isa} (hm0 : MemInv G c0.mem)
    (h0 : ∀ tid t, c0.threads[tid]? = some t → (sp tid).Holds t.st) : WritesPreserve A fuel G c0 :=
  writesPreserve_of_stepPreserves (threadSpec_stepPreserves sp) ⟨hm0, h0⟩

/-- **Link B at the end address**: in every reachable configuration, a thread
at its end address (where its code has no environment step, `hstuck`)
satisfies its postcondition. -/
theorem inv_reachable_post {A : Arch} {fuel : Nat} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (sp : Nat → ThreadSpec S G) {c0 c : Config isa} (hm0 : MemInv G c0.mem)
    (h0 : ∀ tid t, c0.threads[tid]? = some t → (sp tid).Holds t.st) (h : Reachable A fuel c0 c)
    {tid : Nat} {t : Thread isa} (ht : c.threads[tid]? = some t)
    (hstuck : ∀ x R, x.1.2 = (sp tid).endPc → ¬ (sp tid).e.instrStepEnv (SharedEnv.inv S G) x R)
    (hend : t.st.st.2 = (sp tid).endPc) : (sp tid).post (t.st.st, ()) := by
  obtain ⟨-, -, -, hinv⟩ := (inv_reachable sp hm0 h0 h).2 tid t ht
  rcases (sp tid).closed _ hinv with hP | ⟨R, hT, -⟩
  · exact hP
  · exact (hstuck _ R hend hT).elim

end Kraken.Promising.AArch64
