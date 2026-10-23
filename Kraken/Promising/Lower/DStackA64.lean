/-
**AArch64: the private memory's invariants hold along
every env run.**

`Lower/DStack.lean` reduces "a `dmem` stack beside shared memory" to the
invariant `HeapOff H dmem`. This file proves the load-bearing fact behind it
for AArch64: **a `StoreClosed` property of `dmem` (`HeapOff H`, `StackDom S`,
`StackFull lo n`, `DomEq d₀`: the domain is constant) holds at every state an
env run reaches** (`instrStepEnv_dmem`, `eventually_dmem`, `safely_dmem`).
The private memory changes only through the mapped-first primitives
(`MachineData.store`/`storeK`/`rmwK`/`storePairK`/`rmwPairK`), and each
writes only under `Mem.loadInt s.dmem a n = some _`. `Effects.AllEnv` hands
the carried `dmem` back unchanged.

The proof is the dictionary-and-search of `Kraken/AArch64/EnvLSE2Sound.lean`
(`operation_mono`): one lemma per primitive, here threading `I s.dmem` to every
continuation, then a search over the instruction set.
-/
import Kraken.AArch64.EnvWP
import Kraken.Safely
import Kraken.Promising.Lower.DStack

open Kraken Kraken.DStack

namespace Kraken.DStack.A64

variable {env : SharedEnv} {I : Mem 64 → Prop} (hI : StoreClosed I) {P₁ P₂ : MachineState → env.State → Prop}

/-! ## The dictionary: one lemma per primitive -/

-- `hI` is unused here; kept so every dictionary entry has one signature.
set_option linter.unusedSectionVars false in
include hI in
theorem load_dom {s : MachineData} {addr : BitVec 64} {w : MemWidth} {r₁ r₂ : w.type → MachineData → Effects}
    {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (s.load addr w r₁).AllEnv env g P₁) : (s.load addr w r₂).AllEnv env g P₂ := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs) hd⟩
  · exact hk _ _ _ h hd

include hI in
theorem store_dom {s : MachineData} {addr : BitVec 64} {w : MemWidth} {v : w.type} {r₁ r₂ : MachineData → Effects}
    {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (r₁ s').AllEnv env g P₁ → I s'.dmem → (r₂ s').AllEnv env g P₂)
    (h : (s.store addr v r₁).AllEnv env g P₁) : (s.store addr v r₂).AllEnv env g P₂ := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun b g' hs => hk _ _ (h.2 b g' hs) hd⟩
  · exact hk _ _ h (hI.store hd hm _)

-- `hI` is unused here; kept so every dictionary entry has one signature.
set_option linter.unusedSectionVars false in
include hI in
theorem loadK_dom {s : MachineData} {k : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {r₁ r₂ : w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (s.loadK k xcl addr w r₁).AllEnv env g P₁) : (s.loadK k xcl addr w r₂).AllEnv env g P₂ := by
  unfold MachineData.loadK at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs) hd⟩
  · exact hk _ _ _ h hd

include hI in
theorem storeK_dom {s : MachineData} {k : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {v : w.type} {r₁ r₂ : Bool → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ b s' g, (r₁ b s').AllEnv env g P₁ → I s'.dmem → (r₂ b s').AllEnv env g P₂)
    (h : (s.storeK k xcl addr v r₁).AllEnv env g P₁) : (s.storeK k xcl addr v r₂).AllEnv env g P₂ := by
  unfold MachineData.storeK at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun b g' hs => hk _ _ _ (h.2 b g' hs) hd⟩
  · cases xcl with
    | false => exact hk _ _ _ h (hI.store hd hm _)
    | true =>
      simp only [ite_true, Effects.AllEnv] at h ⊢
      intro b
      cases b with
      | true => exact hk _ _ _ (h true) (hI.store hd hm _)
      | false => exact hk _ _ _ (h false) hd

include hI in
theorem rmwK_dom {s : MachineData} {k : Kraken.RmwKind} {noRet : Bool} {addr : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {r₁ r₂ : w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (s.rmwK k noRet addr w op r₁).AllEnv env g P₁) : (s.rmwK k noRet addr w op r₂).AllEnv env g P₂ := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs) hd⟩
  · cases ho : op _ <;> simp only [ho] at h ⊢
    · exact hk _ _ _ h hd
    · exact hk _ _ _ h (hI.store hd hm _)

-- `hI` is unused here; kept so every dictionary entry has one signature.
set_option linter.unusedSectionVars false in
include hI in
theorem loadPairK_dom {s : MachineData} {k : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {r₁ r₂ : w.type → w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v₁ v₂ s' g, (r₁ v₁ v₂ s').AllEnv env g P₁ → I s'.dmem → (r₂ v₁ v₂ s').AllEnv env g P₂)
    (h : (s.loadPairK k xcl addr w r₁).AllEnv env g P₁) : (s.loadPairK k xcl addr w r₂).AllEnv env g P₂ := by
  unfold MachineData.loadPairK at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hm₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [hm₁, hm₂, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ _ (h.2 v g' hs) hd⟩
  · exact ⟨h.1, fun v g' hs => hk _ _ _ _ (h.2 v g' hs) hd⟩
  · exact hk _ _ _ _ h hd

include hI in
theorem storePairK_dom {s : MachineData} {k : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {v₁ v₂ : w.type} {r₁ r₂ : Bool → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ b s' g, (r₁ b s').AllEnv env g P₁ → I s'.dmem → (r₂ b s').AllEnv env g P₂)
    (h : (s.storePairK k xcl addr v₁ v₂ r₁).AllEnv env g P₁) :
    (s.storePairK k xcl addr v₁ v₂ r₂).AllEnv env g P₂ := by
  unfold MachineData.storePairK at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hm₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [hm₁, hm₂, Effects.AllEnv] at h ⊢
  · refine ⟨h.1, fun b g' hs => ?_⟩
    have h' := h.2 b g' hs
    cases b with
    | true => exact hk _ _ _ h' (hI.store hd hm₂ _)
    | false => exact hk _ _ _ h' hd
  · refine ⟨h.1, fun b g' hs => ?_⟩
    have h' := h.2 b g' hs
    cases b with
    | true => exact hk _ _ _ h' (hI.store hd hm₁ _)
    | false => exact hk _ _ _ h' hd
  · cases xcl with
    | false => exact hk _ _ _ h (hI.store₂ hd hm₁ hm₂ _ _)
    | true =>
      simp only [ite_true, Effects.AllEnv] at h ⊢
      intro b
      cases b with
      | true => exact hk _ _ _ (h true) (hI.store₂ hd hm₁ hm₂ _ _)
      | false => exact hk _ _ _ (h false) hd

include hI in
theorem rmwPairK_dom {s : MachineData} {k : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c₁ c₂ n₁ n₂ : w.type} {r₁ r₂ : w.type → w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v₁ v₂ s' g, (r₁ v₁ v₂ s').AllEnv env g P₁ → I s'.dmem → (r₂ v₁ v₂ s').AllEnv env g P₂)
    (h : (s.rmwPairK k addr c₁ c₂ n₁ n₂ r₁).AllEnv env g P₁) :
    (s.rmwPairK k addr c₁ c₂ n₁ n₂ r₂).AllEnv env g P₂ := by
  unfold MachineData.rmwPairK at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm₁ : Mem.loadInt s.dmem addr w.bytes <;> cases hm₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [hm₁, hm₂, Effects.AllEnv] at h ⊢
  · exact SharedEnv.CaspEnv.mono (fun o₁ o₂ g' h' => hk _ _ _ g' h' hd) h
  · refine ⟨h.1, fun v g' hs => ?_⟩
    replace h := h.2 v g' hs
    split at h
    · rename_i hc; simp only [hc]; exact hk _ _ _ _ h (hI.store hd hm₂ _)
    · rename_i hc; simp only [hc]; exact hk _ _ _ _ h hd
  · refine ⟨h.1, fun v g' hs => ?_⟩
    replace h := h.2 v g' hs
    split at h
    · rename_i hc; simp only [hc]; exact hk _ _ _ _ h (hI.store hd hm₁ _)
    · rename_i hc; simp only [hc]; exact hk _ _ _ _ h hd
  · split at h
    · rename_i hc; simp only [hc]; exact hk _ _ _ _ h (hI.store₂ hd hm₁ hm₂ _ _)
    · rename_i hc; simp only [hc]; exact hk _ _ _ _ h hd

theorem AddrExpr.checkSPAlignment_dom {a : AddrExpr} {s : MachineData} {g : env.State}
    {ok₁ ok₂ : Unit → Effects} (hk : (ok₁ ()).AllEnv env g P₁ → (ok₂ ()).AllEnv env g P₂)
    (h : (a.checkSPAlignment s ok₁).AllEnv env g P₁) : (a.checkSPAlignment s ok₂).AllEnv env g P₂ := by
  unfold AddrExpr.checkSPAlignment at h ⊢
  generalize a.base = b at h ⊢
  obtain ⟨x, w'⟩ := b
  cases x with
  | reg x => exact hk h
  | SP =>
    simp only at h ⊢
    split at h
    · exact h.elim
    · rename_i hc
      rw [ite_eq_right hc]
      exact hk h

theorem UnscaledAddrExpr.checkSPAlignment_dom {a : UnscaledAddrExpr} {s : MachineData} {g : env.State}
    {ok₁ ok₂ : Unit → Effects} (hk : (ok₁ ()).AllEnv env g P₁ → (ok₂ ()).AllEnv env g P₂)
    (h : (a.checkSPAlignment s ok₁).AllEnv env g P₁) : (a.checkSPAlignment s ok₂).AllEnv env g P₂ := by
  unfold UnscaledAddrExpr.checkSPAlignment at h ⊢
  generalize a.base = b at h ⊢
  obtain ⟨x, w'⟩ := b
  cases x with
  | reg x => exact hk h
  | SP =>
    simp only at h ⊢
    split at h
    · exact h.elim
    · rename_i hc
      rw [ite_eq_right hc]
      exact hk h

theorem interpBase_dom {base : RegOrSp .W64} {s : MachineData} {g : env.State}
    {ok₁ ok₂ : BitVec 64 → Effects} (hk : ∀ a, (ok₁ a).AllEnv env g P₁ → (ok₂ a).AllEnv env g P₂)
    (h : (base.interpBase s ok₁).AllEnv env g P₁) : (base.interpBase s ok₂).AllEnv env g P₂ := by
  unfold RegOrSp.interpBase at h ⊢
  obtain ⟨x, w'⟩ := base
  cases x with
  | reg x => exact hk _ h
  | SP =>
    simp only at h ⊢
    split at h
    · exact h.elim
    · rename_i hc
      rw [ite_eq_right hc]
      exact hk _ h

/-- Address evaluation (a base writeback at most) leaves `dmem` alone. -/
theorem AddrExpr.eval_dmem [Labels] (a : AddrExpr) (s : MachineData) (p : Std.Rco Int64) :
    (a.eval s p).2.dmem = s.dmem := by
  unfold AddrExpr.eval
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem AddrExpr.dmem_eval [Labels] {a : AddrExpr} {s : MachineData} {p : Std.Rco Int64} (hd : I s.dmem) :
    I (a.eval s p).2.dmem := by
  rw [AddrExpr.eval_dmem]; exact hd

include hI in
theorem AddrExpr.interpLoad_dom [Labels] {w : MemWidth} {a : AddrExpr} {s : MachineData} {p : Std.Rco Int64}
    {r₁ r₂ : w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (a.interpLoad s p r₁).AllEnv env g P₁) : (a.interpLoad s p r₂).AllEnv env g P₂ := by
  unfold AddrExpr.interpLoad at h ⊢
  exact AddrExpr.checkSPAlignment_dom (fun h => load_dom hI (AddrExpr.dmem_eval hd) hk h) h

include hI in
theorem AddrExpr.interpStore_dom [Labels] {w : MemWidth} {a : AddrExpr} {s : MachineData} {p : Std.Rco Int64}
    {v : w.type} {r₁ r₂ : MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (r₁ s').AllEnv env g P₁ → I s'.dmem → (r₂ s').AllEnv env g P₂)
    (h : (a.interpStore s p v r₁).AllEnv env g P₁) : (a.interpStore s p v r₂).AllEnv env g P₂ := by
  unfold AddrExpr.interpStore at h ⊢
  exact AddrExpr.checkSPAlignment_dom (fun h => store_dom hI (AddrExpr.dmem_eval hd) hk h) h

include hI in
theorem UnscaledAddrExpr.interpLoad_dom [Labels] {w : MemWidth} {a : UnscaledAddrExpr} {s : MachineData}
    {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (a.interpLoad s p r₁).AllEnv env g P₁) : (a.interpLoad s p r₂).AllEnv env g P₂ := by
  unfold UnscaledAddrExpr.interpLoad at h ⊢
  exact UnscaledAddrExpr.checkSPAlignment_dom (fun h => load_dom hI hd hk h) h

include hI in
theorem UnscaledAddrExpr.interpStore_dom [Labels] {w : MemWidth} {a : UnscaledAddrExpr} {s : MachineData}
    {p : Std.Rco Int64} {v : w.type} {r₁ r₂ : MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (r₁ s').AllEnv env g P₁ → I s'.dmem → (r₂ s').AllEnv env g P₂)
    (h : (a.interpStore s p v r₁).AllEnv env g P₁) : (a.interpStore s p v r₂).AllEnv env g P₂ := by
  unfold UnscaledAddrExpr.interpStore at h ⊢
  exact UnscaledAddrExpr.checkSPAlignment_dom (fun h => store_dom hI hd hk h) h

include hI in
theorem AddrOrLit.interpLoad_dom [Labels] {w : MemWidth} {a : AddrOrLit} {s : MachineData} {p : Std.Rco Int64}
    {r₁ r₂ : w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (a.interpLoad s p r₁).AllEnv env g P₁) : (a.interpLoad s p r₂).AllEnv env g P₂ := by
  cases a with
  | addr a => exact AddrExpr.interpLoad_dom hI hd hk h
  | lit l =>
    cases l with
    | addr a => exact load_dom hI hd hk h
    | pool q => exact hk _ _ _ h hd

/-! ## The search over the instruction set -/

set_option allowUnsafeReducibility true in
attribute [local irreducible] MachineData.load MachineData.store MachineData.loadK
  MachineData.storeK MachineData.rmwK MachineData.loadPairK MachineData.storePairK MachineData.rmwPairK
  AddrExpr.interpLoad AddrExpr.interpStore
  UnscaledAddrExpr.interpLoad UnscaledAddrExpr.interpStore AddrOrLit.interpLoad
  AddrExpr.checkSPAlignment UnscaledAddrExpr.checkSPAlignment RegOrSp.interpBase AddrExpr.eval

set_option hygiene false in
/-- `EnvLSE2Sound`'s `mono_search`, with `I s.dmem` (`hd`) threaded to every
continuation. -/
local macro "dom_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp] at h ⊢ <;>
    repeat' first
      | exact hk _ _ h hd
      | exact hj _ _ _ h hd
      | refine AddrOrLit.interpLoad_dom hI hd (fun v s' g h hd => ?_) h
      | refine AddrExpr.interpLoad_dom hI hd (fun v s' g h hd => ?_) h
      | refine UnscaledAddrExpr.interpLoad_dom hI hd (fun v s' g h hd => ?_) h
      | refine AddrExpr.interpStore_dom hI hd (fun s' g h hd => ?_) h
      | refine UnscaledAddrExpr.interpStore_dom hI hd (fun s' g h hd => ?_) h
      | refine AddrExpr.checkSPAlignment_dom (fun h => ?_) h
      | refine load_dom hI hd (fun v s' g h hd => ?_) h
      | refine store_dom hI hd (fun s' g h hd => ?_) h
      | refine load_dom hI (AddrExpr.dmem_eval hd) (fun v s' g h hd => ?_) h
      | refine store_dom hI (AddrExpr.dmem_eval hd) (fun s' g h hd => ?_) h
      | refine loadPairK_dom hI (AddrExpr.dmem_eval hd) (fun v₁ v₂ s' g h hd => ?_) h
      | refine storePairK_dom hI (AddrExpr.dmem_eval hd) (fun b s' g h hd => ?_) h
      | refine loadK_dom hI hd (fun v s' g h hd => ?_) h
      | refine storeK_dom hI hd (fun b s' g h hd => ?_) h
      | refine rmwK_dom hI hd (fun v s' g h hd => ?_) h
      | refine loadPairK_dom hI hd (fun v₁ v₂ s' g h hd => ?_) h
      | refine storePairK_dom hI hd (fun b s' g h hd => ?_) h
      | refine rmwPairK_dom hI hd (fun v₁ v₂ s' g h hd => ?_) h
      | refine interpBase_dom (fun a h => ?_) h
      | (simp only [Effects.AllEnv] at h ⊢; exact h)
      | (refine ⟨h.1, fun g' hs => ?_⟩; replace h := h.2 g' hs)
      | (refine fun v => ?_; specialize h v)
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllEnv] at h ⊢))

include hI in
/-- **One operation keeps a `StoreClosed` property of `dmem`** at every
continuation it reaches. -/
theorem operation_dom [Labels] {w : RegWidth} {op : Operation w} {p : Std.Rco Int64}
    {s : MachineData} {g : env.State} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hd : I s.dmem)
    (hk : ∀ s' g, (k₁ s').AllEnv env g P₁ → I s'.dmem → (k₂ s').AllEnv env g P₂)
    (hj : ∀ pc s' g, (j₁ pc s').AllEnv env g P₁ → I s'.dmem → (j₂ pc s').AllEnv env g P₂)
    (h : (Operation.interp op p s k₁ j₁).AllEnv env g P₁) :
    (Operation.interp op p s k₂ j₂).AllEnv env g P₂ := by
  cases op
  -- `SVC` halts (`MachineData.pendingSyscall`): nothing holds past it.
  case SVC imm => simp only [Operation.interp, MachineData.pendingSyscall, Effects.AllEnv] at h
  all_goals dom_search

include hI in
/-- **One directive keeps a `StoreClosed` property of `dmem`.** -/
theorem directive_dom [Labels] {d : Directive} {p : Std.Rco Int64} {s : MachineData} {g : env.State}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects} (hd : I s.dmem)
    (hk : ∀ s' g, (k₁ s').AllEnv env g P₁ → I s'.dmem → (k₂ s').AllEnv env g P₂)
    (hj : ∀ pc s' g, (j₁ pc s').AllEnv env g P₁ → I s'.dmem → (j₂ pc s').AllEnv env g P₂)
    (h : (d.interp s p k₁ j₁).AllEnv env g P₁) : (d.interp s p k₂ j₂).AllEnv env g P₂ := by
  cases d with
  | label l => exact hk _ _ h hd
  | byteArray bs => simp only [Directive.interp, Effects.AllEnv] at h
  | instr i =>
    simp only [Directive.interp, Instr.interp, Effects.AllEnv] at h ⊢
    exact operation_dom hI hd hk hj h

/-! ## Along every run -/

include hI in
/-- **One env step keeps a `StoreClosed` property of `dmem`.** -/
theorem instrStepEnv_dmem {e : Kraken.Executable Directive} {st : MachineState × env.State}
    {post : MachineState × env.State → Prop} (hd : I st.1.1.dmem) (h : e.instrStepEnv env st post) :
    e.instrStepEnv env st (fun x => post x ∧ I x.1.1.dmem) := by
  obtain ⟨d, z, rest, hc, hs⟩ := h
  refine ⟨d, z, rest, hc, ?_⟩
  unfold Kraken.Executable.stepAtEnv at hs ⊢
  letI : Labels := _root_.Executable.labels e
  rcases hs with hs | hs
  · refine .inl (directive_dom hI hd ?_ ?_ hs)
    · intro s' g h hd
      simp only [Effects.AllEnv] at h ⊢
      exact ⟨h, hd⟩
    · intro _ _ _ h _; simp only [Effects.AllEnv] at h
  · refine .inr (directive_dom hI hd ?_ ?_ hs)
    · intro _ _ h _; simp only [Effects.AllEnv] at h
    · intro pc s' g h hd
      simp only [Effects.AllEnv] at h ⊢
      exact ⟨h, hd⟩

include hI in
/-- **Total runs**: the property holds at the end. -/
theorem eventually_dmem {e : Kraken.Executable Directive} {Q : MachineState × env.State → Prop}
    {st : MachineState × env.State} (h : Eventually (e.instrStepEnv env) Q st) (hd : I st.1.1.dmem) :
    Eventually (e.instrStepEnv env) (fun x => Q x ∧ I x.1.1.dmem) st := by
  induction h with
  | done x hq => exact .done _ ⟨hq, hd⟩
  | step x R hT _ ih => exact .step _ _ (instrStepEnv_dmem hI hd hT) fun y hy => ih y hy.1 hy.2

include hI in
/-- **Partial runs**: the property holds at every state reached. -/
theorem safely_dmem {e : Kraken.Executable Directive} {Q : MachineState × env.State → Prop}
    {st : MachineState × env.State} (h : Safely (e.instrStepEnv env) Q st) (hd : I st.1.1.dmem) :
    Safely (e.instrStepEnv env) (fun x => Q x ∧ I x.1.1.dmem) st := by
  obtain ⟨Inv, hx, hInv⟩ := h
  refine ⟨fun y => Inv y ∧ I y.1.1.dmem, ⟨hx, hd⟩, fun y ⟨hy, hdy⟩ => ?_⟩
  rcases hInv y hy with hq | ⟨R, hT, hR⟩
  · exact .inl ⟨hq, hdy⟩
  · exact .inr ⟨_, instrStepEnv_dmem hI hdy hT, fun z hz => ⟨hR z hz.1, hz.2⟩⟩

/-- **The domain of `dmem` is constant along every partial run.** -/
theorem safely_domEq {e : Kraken.Executable Directive} {Q : MachineState × env.State → Prop}
    {st : MachineState × env.State} (h : Safely (e.instrStepEnv env) Q st) :
    Safely (e.instrStepEnv env) (fun x => Q x ∧ DomEq st.1.1.dmem x.1.1.dmem) st :=
  safely_dmem (domEq_storeClosed _) h (DomEq.refl _)

/-- **The heap stays off `dmem` along every partial run.** -/
theorem safely_heapOff {e : Kraken.Executable Directive} {Q : MachineState × env.State → Prop}
    {H : BitVec 64 → Prop} {st : MachineState × env.State} (h : Safely (e.instrStepEnv env) Q st)
    (hd : HeapOff H st.1.1.dmem) : Safely (e.instrStepEnv env) (fun x => Q x ∧ HeapOff H x.1.1.dmem) st :=
  safely_dmem (heapOff_storeClosed H) h hd

end Kraken.DStack.A64
