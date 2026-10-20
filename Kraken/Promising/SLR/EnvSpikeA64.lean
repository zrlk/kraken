/-
Prototype, AArch64 part: the simulation of `AllEnv E`
by an arbitrary tree judgment `J : TreeJ E` (`SLR/EnvSpike.lean`).

This is `InvLinkAArch64`'s `isim` with `EvTree.AllInv G Q` replaced by `J.W`
and the environment state threaded through (`isim` has `()`); the proofs
use only `J`'s laws. `exec_treeJ_of_instrStepEnv` is
`exec_allInv_of_instrStepEnv` for any `TreeJ`: one `instrStepEnv E` step of
the thread's machine state makes the thread's Promising instruction tree
satisfy `J`, with `J.Post` at the leaves.

Instantiated at `TreeJ.allInv` it is the invariant environment's link step; at `TreeJ.eraseWPR`
(`SLR/EnvSpikeSwp.lean`) it turns an `instrStepEnv (SLREnv …)` judgment into
the cell obligation `EvTree.EraseWPR`.
-/
import Kraken.Promising.InvLinkAArch64
import Kraken.Promising.SLR.EnvSpike

open Kraken

namespace Kraken.Promising.AArch64.EnvSpike

open Kraken.Promising.SLR.EnvSpike

/-! ## The simulation, per primitive -/

section JSim

variable {E : SharedEnv} (J : TreeJ E MachineState) {P₁ : MachineState → E.State → Prop}

theorem load_jsim {s : MachineData} {addr : BitVec 64} {w : MemWidth} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g) {g : E.State}
    (h : (MachineData.load s addr w k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.load s addr w k₂)) g := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.load h.1 fun v g' hs => hk _ _ _ (h.2 v g' hs)

theorem loadK_jsim {s : MachineData} {lk : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g) {g : E.State}
    (h : (MachineData.loadK s lk xcl addr w k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.loadK s lk xcl addr w k₂)) g := by
  unfold MachineData.loadK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.load h.1 fun v g' hs => hk _ _ _ (h.2 v g' hs)

theorem store_jsim {s : MachineData} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g) {g : E.State}
    (h : (MachineData.store s addr v k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.store s addr v k₂)) g := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.store h.1 fun b g' hs => hk _ _ (h.2 b g' hs)

theorem storeK_jsim {s : MachineData} {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {v : w.type} {k₁ k₂ : Bool → MachineData → Effects}
    (hk : ∀ b s g, (k₁ b s).AllEnv E g P₁ → J.W (toEv {} (k₂ b s)) g) {g : E.State}
    (h : (MachineData.storeK s sk xcl addr v k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.storeK s sk xcl addr v k₂)) g := by
  unfold MachineData.storeK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases xcl with
    | false => exact hk _ _ _ h
    | true =>
      simp only [ite_true, Effects.AllEnv, toEv] at h ⊢
      refine J.choose fun i => ?_
      have hi := h (i.val == 1)
      split at hi <;> rename_i hb <;> simp only [hb, ite_true, ite_false, Bool.false_eq_true] <;>
        exact hk _ _ _ hi
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.store h.1 fun b g' hs => hk _ _ _ (h.2 b g' hs)

theorem rmwK_jsim {s : MachineData} {rk : Kraken.RmwKind} {nr : Bool} {addr : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g) {g : E.State}
    (h : (MachineData.rmwK s rk nr addr w op k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.rmwK s rk nr addr w op k₂)) g := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt w.bits x) <;> rw [hop] at h <;> exact hk _ _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.rmw h.1 fun old g' hs => hk _ _ _ (h.2 old g' hs)

theorem loadPairK_jsim {s : MachineData} {lk : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {k₁ k₂ : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ s g, (k₁ v₁ v₂ s).AllEnv E g P₁ → J.W (toEv {} (k₂ v₁ v₂ s)) g) {g : E.State}
    (h : (MachineData.loadPairK s lk xcl addr w k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.loadPairK s lk xcl addr w k₂)) g := by
  unfold MachineData.loadPairK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hd₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    rw [hd₁, hd₂] at h <;> simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
  · exact J.load h.1 fun v g' hs => hk _ _ _ _ (h.2 v g' hs)
  · exact J.load h.1 fun v g' hs => hk _ _ _ _ (h.2 v g' hs)
  · exact hk _ _ _ _ h

theorem storePairK_jsim {s : MachineData} {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {v₁ v₂ : w.type} {k₁ k₂ : Bool → MachineData → Effects}
    (hk : ∀ b s g, (k₁ b s).AllEnv E g P₁ → J.W (toEv {} (k₂ b s)) g) {g : E.State}
    (h : (MachineData.storePairK s sk xcl addr v₁ v₂ k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.storePairK s sk xcl addr v₁ v₂ k₂)) g := by
  unfold MachineData.storePairK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hd₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    rw [hd₁, hd₂] at h <;> simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
  · refine J.store h.1 fun b g' hb => ?_
    have h' := h.2 b g' hb
    cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h' ⊢ <;> exact hk _ _ _ h'
  · refine J.store h.1 fun b g' hb => ?_
    have h' := h.2 b g' hb
    cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h' ⊢ <;> exact hk _ _ _ h'
  · cases xcl with
    | false => exact hk _ _ _ h
    | true =>
      simp only [ite_true, Effects.AllEnv, toEv] at h ⊢
      refine J.choose fun i => ?_
      have hi := h (i.val == 1)
      split at hi <;> rename_i hb <;> simp only [hb, ite_true, ite_false, Bool.false_eq_true] <;>
        exact hk _ _ _ hi

/-- `CASP` with both halves shared: `CaspEnv` is `J` of `caspTree`, for every
success bit and order, by the `choose` and `rmw` laws. -/
theorem caspTree_jsim {k : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth} {c₁ c₂ n₁ n₂ : w.type}
    {K : w.type → w.type → E.State → Prop} {ret : w.type → w.type → EvTree MachineState}
    (hk : ∀ o₁ o₂ g, K o₁ o₂ g → J.W (ret o₁ o₂) g) {g : E.State}
    (h : E.CaspEnv k addr w c₁ c₂ n₁ n₂ g K) :
    J.W (caspTree {} k addr c₁ c₂ n₁ n₂ ret) g := by
  unfold caspTree
  simp only [EvTree.access_empty]
  refine J.choose fun ⟨sv, hsv⟩ => J.choose fun ⟨rv, hrv⟩ => ?_
  have hguard : ∀ (b : Bool) (t : EvTree MachineState) (g' : E.State), (b = true → J.W t g') →
      J.W (if b = true then t else EvTree.choose 0 nofun) g' := by
    intro b t g' ht
    cases b
    · exact J.choose fun i => i.elim0
    · exact ht rfl
  obtain rfl | rfl : sv = 0 ∨ sv = 1 := (by omega)
  all_goals obtain rfl | rfl : rv = 0 ∨ rv = 1 := (by omega)
  · have hs := h false false
    simp only [Bool.false_eq_true, ite_false, ite_true, Nat.reduceBEq] at hs ⊢
    exact J.rmw hs.1 fun o₁ g₁ h₁ => J.rmw (hs.2 o₁ g₁ h₁).1 fun o₂ g₂ h₂ =>
      hguard _ _ _ fun hc => hk _ _ _ ((hs.2 o₁ g₁ h₁).2 o₂ g₂ h₂ (beq_iff_eq.mp hc))
  · have hs := h false true
    simp only [Bool.false_eq_true, ite_false, ite_true, Nat.reduceBEq] at hs ⊢
    exact J.rmw hs.1 fun o₁ g₁ h₁ => J.rmw (hs.2 o₁ g₁ h₁).1 fun o₂ g₂ h₂ =>
      hguard _ _ _ fun hc => hk _ _ _ ((hs.2 o₁ g₁ h₁).2 o₂ g₂ h₂ (beq_iff_eq.mp hc))
  · have hs := h true false
    simp only [Bool.false_eq_true, ite_false, ite_true, Nat.reduceBEq] at hs ⊢
    exact J.rmw hs.1 fun o₁ g₁ h₁ => J.rmw (hs.2 o₁ g₁ h₁).1 fun o₂ g₂ h₂ =>
      hguard _ _ _ fun hc => hk _ _ _ ((hs.2 o₁ g₁ h₁).2 o₂ g₂ h₂ (beq_iff_eq.mp hc))
  · have hs := h true true
    simp only [Bool.false_eq_true, ite_false, ite_true, Nat.reduceBEq] at hs ⊢
    exact J.rmw hs.1 fun o₁ g₁ h₁ => J.rmw (hs.2 o₁ g₁ h₁).1 fun o₂ g₂ h₂ =>
      hguard _ _ _ fun hc => hk _ _ _ ((hs.2 o₁ g₁ h₁).2 o₂ g₂ h₂ (beq_iff_eq.mp hc))

theorem rmwPairK_jsim {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c₁ c₂ n₁ n₂ : w.type} {k₁ k₂ : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ s g, (k₁ v₁ v₂ s).AllEnv E g P₁ → J.W (toEv {} (k₂ v₁ v₂ s)) g) {g : E.State}
    (h : (MachineData.rmwPairK s rk addr c₁ c₂ n₁ n₂ k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.rmwPairK s rk addr c₁ c₂ n₁ n₂ k₂)) g := by
  unfold MachineData.rmwPairK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hd₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    rw [hd₁, hd₂] at h <;> simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
  · exact caspTree_jsim J (fun o₁ o₂ g h => hk _ _ _ _ h) h
  · refine J.rmw h.1 fun old g' hold => ?_
    have h' := h.2 old g' hold
    split at h' <;> rename_i hc <;> simp only [hc, ite_true, ite_false, Bool.false_eq_true] <;> exact hk _ _ _ _ h'
  · refine J.rmw h.1 fun old g' hold => ?_
    have h' := h.2 old g' hold
    split at h' <;> rename_i hc <;> simp only [hc, ite_true, ite_false, Bool.false_eq_true] <;> exact hk _ _ _ _ h'
  · split at h <;> rename_i hc <;> simp only [hc, ite_true, ite_false, Bool.false_eq_true] <;> exact hk _ _ _ _ h

/-! ### Per addressing form -/

theorem AddrExpr.checkSPAlignment_jsim {a : AddrExpr} {s : MachineData} {ok₁ ok₂ : Unit → Effects} {g : E.State}
    (hk : (ok₁ ()).AllEnv E g P₁ → J.W (toEv {} (ok₂ ())) g)
    (h : (a.checkSPAlignment s ok₁).AllEnv E g P₁) : J.W (toEv {} (a.checkSPAlignment s ok₂)) g := by
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

theorem UnscaledAddrExpr.checkSPAlignment_jsim {a : UnscaledAddrExpr} {s : MachineData}
    {ok₁ ok₂ : Unit → Effects} {g : E.State}
    (hk : (ok₁ ()).AllEnv E g P₁ → J.W (toEv {} (ok₂ ())) g)
    (h : (a.checkSPAlignment s ok₁).AllEnv E g P₁) : J.W (toEv {} (a.checkSPAlignment s ok₂)) g := by
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

theorem interpBase_jsim {base : RegOrSp .W64} {s : MachineData} {ok₁ ok₂ : BitVec 64 → Effects} {g : E.State}
    (hk : ∀ a, (ok₁ a).AllEnv E g P₁ → J.W (toEv {} (ok₂ a)) g)
    (h : (base.interpBase s ok₁).AllEnv E g P₁) : J.W (toEv {} (base.interpBase s ok₂)) g := by
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

theorem AddrExpr.interpLoad_jsim [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64} {s : MachineData}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g) {g : E.State}
    (h : (a.interpLoad s p k₁).AllEnv E g P₁) : J.W (toEv {} (a.interpLoad s p k₂)) g := by
  unfold AddrExpr.interpLoad at h ⊢
  refine AddrExpr.checkSPAlignment_jsim J (fun h => ?_) h
  exact load_jsim J hk h

theorem AddrExpr.interpStore_jsim [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64}
    {s : MachineData} {v : w.type} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g) {g : E.State}
    (h : (a.interpStore s p v k₁).AllEnv E g P₁) : J.W (toEv {} (a.interpStore s p v k₂)) g := by
  unfold AddrExpr.interpStore at h ⊢
  refine AddrExpr.checkSPAlignment_jsim J (fun h => ?_) h
  exact store_jsim J hk h

theorem UnscaledAddrExpr.interpLoad_jsim [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g) {g : E.State}
    (h : (a.interpLoad s p k₁).AllEnv E g P₁) : J.W (toEv {} (a.interpLoad s p k₂)) g := by
  unfold UnscaledAddrExpr.interpLoad at h ⊢
  refine UnscaledAddrExpr.checkSPAlignment_jsim J (fun h => ?_) h
  exact load_jsim J hk h

theorem UnscaledAddrExpr.interpStore_jsim [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {s : MachineData} {v : w.type} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g) {g : E.State}
    (h : (a.interpStore s p v k₁).AllEnv E g P₁) : J.W (toEv {} (a.interpStore s p v k₂)) g := by
  unfold UnscaledAddrExpr.interpStore at h ⊢
  refine UnscaledAddrExpr.checkSPAlignment_jsim J (fun h => ?_) h
  exact store_jsim J hk h

theorem AddrOrLit.interpLoad_jsim [Labels] {w : MemWidth} {a : AddrOrLit} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g) {g : E.State}
    (h : (a.interpLoad s p k₁).AllEnv E g P₁) : J.W (toEv {} (a.interpLoad s p k₂)) g := by
  cases a with
  | addr a => exact AddrExpr.interpLoad_jsim J hk h
  | lit l =>
    cases l with
    | addr a => exact load_jsim J hk h
    | pool q => exact hk _ _ _ h

/-! ### Per instruction -/

set_option allowUnsafeReducibility true in
attribute [local irreducible] MachineData.load MachineData.store MachineData.loadK MachineData.storeK
  MachineData.rmwK MachineData.loadPairK MachineData.storePairK MachineData.rmwPairK AddrExpr.interpLoad
  AddrExpr.interpStore UnscaledAddrExpr.interpLoad
  UnscaledAddrExpr.interpStore AddrOrLit.interpLoad AddrExpr.checkSPAlignment RegOrSp.interpBase

set_option hygiene false in
/-- `isim_search` with the laws of `J` in place of `AllInv`'s equations. -/
local macro "jsim_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllEnv,
      AddrExpr.eval_mk, toEv] at h ⊢ <;>
    repeat' first
      | exact hk _ _ h
      | exact hj _ _ _ h
      | exact h.elim
      | exact J.fault
      | exact J.fence h.1 fun g' hs => hk _ _ (h.2 g' hs)
      | refine AddrOrLit.interpLoad_jsim J (fun v s g h => ?_) h
      | refine AddrExpr.interpLoad_jsim J (fun v s g h => ?_) h
      | refine UnscaledAddrExpr.interpLoad_jsim J (fun v s g h => ?_) h
      | refine AddrExpr.interpStore_jsim J (fun s g h => ?_) h
      | refine UnscaledAddrExpr.interpStore_jsim J (fun s g h => ?_) h
      | refine AddrExpr.checkSPAlignment_jsim J (fun h => ?_) h
      | refine load_jsim J (fun v s g h => ?_) h
      | refine store_jsim J (fun s g h => ?_) h
      | refine loadK_jsim J (fun v s g h => ?_) h
      | refine storeK_jsim J (fun b s g h => ?_) h
      | refine rmwK_jsim J (fun v s g h => ?_) h
      | refine loadPairK_jsim J (fun v₁ v₂ s g h => ?_) h
      | refine storePairK_jsim J (fun b s g h => ?_) h
      | refine rmwPairK_jsim J (fun v₁ v₂ s g h => ?_) h
      | refine interpBase_jsim J (fun a h => ?_) h
      | (refine J.choose fun i => ?_; specialize h (i.val == 1))
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllEnv,
          AddrExpr.eval_mk, toEv] at h ⊢))

theorem operation_jsim [Labels] {w : RegWidth} (op : Operation w) (p : Std.Rco Int64) {s : MachineData}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects} {g : E.State}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hj : ∀ pc s g, (j₁ pc s).AllEnv E g P₁ → J.W (toEv {} (j₂ pc s)) g)
    (h : (Operation.interp op p s k₁ j₁).AllEnv E g P₁) :
    J.W (toEv {} (Operation.interp op p s k₂ j₂)) g := by
  cases op <;> jsim_search

theorem directive_jsim [Labels] (dir : Directive) (p : Std.Rco Int64) {s : MachineData}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects} {g : E.State}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hj : ∀ pc s g, (j₁ pc s).AllEnv E g P₁ → J.W (toEv {} (j₂ pc s)) g)
    (h : (dir.interp s p k₁ j₁).AllEnv E g P₁) :
    J.W (toEv {} (dir.interp s p k₂ j₂)) g := by
  cases dir with
  | instr i =>
    have h' : (i.interp s p k₁ j₁).AllEnv E g P₁ := h
    show J.W (toEv {} (i.interp s p k₂ j₂)) g
    unfold Instr.interp at h' ⊢
    exact operation_jsim J _ _ hk hj h'
  | label l => exact hk _ _ h
  | byteArray b => exact h.elim

end JSim

/-! ## One instruction -/

/-- **One instruction, any tree judgment** (`exec_allInv_of_instrStepEnv` for
a `TreeJ`): at a thread state whose code is `e`, with no declarations, an
environment step of `E` from the thread's machine state and environment
state `g` makes the thread's instruction tree satisfy `J` at `g`, provided
the step's post-set gives `J.Post` at the state moved to the new machine
state. -/
theorem exec_treeJ_of_instrStepEnv {E : SharedEnv} (J : TreeJ E State)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hds : st.decls = {})
    (h : e.instrStepEnv E (st.st, g) R) (hR : ∀ m g', R (m, g') → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  obtain ⟨d, sz, rest, hcode, hstep⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat hstep hR ⊢
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
    let J' := J.comap (fun ms : MachineState => ({ exe, endPc, st := ms, showPc, decls := {} } : State))
    show J'.W _ g
    unfold Executable.step
    letI := Executable.labels exe
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]
    unfold Kraken.Executable.stepAtEnv at hstep
    generalize pc + Int64.ofNat sz = pc' at hstep ⊢
    rcases hstep with hstep | hstep
    · refine directive_jsim J' d _ ?_ ?_ hstep
      · intro s' g' h
        exact J'.done (hR _ _ h)
      · intro _ _ _ h
        exact h.elim
    · refine directive_jsim J' d _ ?_ ?_ hstep
      · intro _ _ h
        exact h.elim
      · intro pc s' g' h
        exact J'.done (hR _ _ h)

/-- **The invariant environment's step is an instance**: `exec_allInv_of_instrStepEnv`'s conclusion
from the generic one, at `TreeJ.allInv`. -/
theorem exec_allInv_of_instrStepEnv' {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    {R : MachineState × Unit → Prop} (he : st.exe = e) (hds : st.decls = {})
    (h : e.instrStepEnv (SharedEnv.inv S G) (st.st, ()) R) :
    ∀ tree, isa.exec st = some tree →
      tree.AllInv G (fun st' : State => R (st'.st, ()) ∧ st'.exe = st.exe ∧ st'.endPc = st.endPc ∧
        st'.decls = st.decls) :=
  exec_treeJ_of_instrStepEnv (TreeJ.allInv S G _) he hds h fun _ _ h => ⟨h, rfl, rfl, rfl⟩

end Kraken.Promising.AArch64.EnvSpike
