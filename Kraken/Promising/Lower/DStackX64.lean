/-
**X64: the private memory's invariants hold along
every env run.** The x64 twin of `Lower/DStackA64.lean`.

**A `StoreClosed` property of `dmem` (`HeapOff H`, `StackDom S`,
`StackFull lo n`, `DomEq d₀`: the domain is constant) holds at every state an
x64 env run reaches** (`instrStepEnv_dmem`, `eventually_dmem`, `safely_dmem`).
The private memory changes only through the mapped-first primitives
(`MachineData.store`/`storeNT`/`rmwK`/`storeAvx`/`rmw16K`, and `rmwPlain`/
`rmw16Plain` through them), and each writes only under
`Mem.loadInt s.dmem a n = some _`. `Effects.AllEnv` hands the carried `dmem`
back unchanged, the 8-byte pieces of a non-atomic vector access included.

The proof is the dictionary-and-search of `SLR/EnvG/X64LiveRun.lean`
(`operation_jsim`), with `AllEnv` on both sides: one lemma per primitive and
operand form, threading `I s.dmem` to every continuation, then a search over
the instruction set. `InvLinkX64.Split S d` is by definition
`HeapOff (SharedLayout.Covers S) d`, so `safely_heapOff` is the run form of
the invariant `X64LiveRun` threads by hand.
-/
import Kraken.EnvWP
import Kraken.Safely
import Kraken.Promising.Lower.DStack

open Kraken Kraken.DStack

namespace Kraken.DStack.X64

variable {env : SharedEnv} {I : Mem 64 → Prop} {P₁ P₂ : MachineState → env.State → Prop}

/-! ## The pieces of a non-atomic vector access -/

private theorem loadPieces_mono {K₁ K₂ : List (BitVec 64) → env.State → Prop}
    (hk : ∀ vs g, K₁ vs g → K₂ vs g) :
    ∀ {n : Nat} {addr : BitVec 64} {g : env.State}, env.LoadPieces addr n g K₁ → env.LoadPieces addr n g K₂ := by
  intro n
  induction n generalizing K₁ K₂ with
  | zero => exact fun h => hk _ _ h
  | succ n ih => exact fun h => ⟨h.1, fun v g' hs => ih (fun vs g'' => hk _ g'') (h.2 v g' hs)⟩

private theorem storePieces_mono {K₁ K₂ : env.State → Prop} (hk : ∀ g, K₁ g → K₂ g) :
    ∀ {ps : List (BitVec 64)} {addr : BitVec 64} {g : env.State},
      env.StorePieces addr ps g K₁ → env.StorePieces addr ps g K₂ := by
  intro ps
  induction ps with
  | nil => exact fun h => hk _ h
  | cons p ps ih => exact fun h => ⟨h.1, fun b g' hs => ih (h.2 b g' hs)⟩

/-! ## The dictionary: one lemma per primitive -/

theorem load_dom {s : MachineData} {addr : BitVec 64} {w : Width} {r₁ r₂ : w.type → MachineData → Effects}
    {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (s.load addr w r₁).AllEnv env g P₁) : (s.load addr w r₂).AllEnv env g P₂ := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs) hd⟩
  · exact hk _ _ _ h hd

theorem store_dom (hI : StoreClosed I) {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {r₁ r₂ : MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (r₁ s').AllEnv env g P₁ → I s'.dmem → (r₂ s').AllEnv env g P₂)
    (h : (s.store addr v r₁).AllEnv env g P₁) : (s.store addr v r₂).AllEnv env g P₂ := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun b g' hs => hk _ _ (h.2 b g' hs) hd⟩
  · exact hk _ _ h (hI.store hd hm _)

theorem storeNT_dom (hI : StoreClosed I) {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {r₁ r₂ : MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (r₁ s').AllEnv env g P₁ → I s'.dmem → (r₂ s').AllEnv env g P₂)
    (h : (s.storeNT addr v r₁).AllEnv env g P₁) : (s.storeNT addr v r₂).AllEnv env g P₂ := by
  unfold MachineData.storeNT at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun b g' hs => hk _ _ (h.2 b g' hs) hd⟩
  · exact hk _ _ h (hI.store hd hm _)

theorem rmwK_dom (hI : StoreClosed I) {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {r₁ r₂ : w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (s.rmwK rk addr w op r₁).AllEnv env g P₁) : (s.rmwK rk addr w op r₂).AllEnv env g P₂ := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs) hd⟩
  · cases ho : op _ <;> simp only [ho] at h ⊢
    · exact hk _ _ _ h hd
    · exact hk _ _ _ h (hI.store hd hm _)

theorem rmwPlain_dom (hI : StoreClosed I) {s : MachineData} {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {r₁ r₂ : w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (s.rmwPlain addr w op r₁).AllEnv env g P₁) : (s.rmwPlain addr w op r₂).AllEnv env g P₂ := by
  unfold MachineData.rmwPlain at h ⊢
  refine load_dom hd (fun v s' g h hd => ?_) h
  cases hop : op v <;> simp only [hop] at h ⊢
  · exact hk _ _ _ h hd
  · exact store_dom hI hd (fun s'' g h hd => hk _ _ _ h hd) h

theorem loadAvx_dom {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {r₁ r₂ : w.type → MachineData → Effects} {checkAlign atomic : Bool} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (s.loadAvx addr w r₁ checkAlign atomic).AllEnv env g P₁) :
    (s.loadAvx addr w r₂ checkAlign atomic).AllEnv env g P₂ := by
  unfold MachineData.loadAvx at h ⊢
  split
  · rename_i hc; simp only [hc, ite_true, Effects.AllEnv] at h
  · rename_i hc
    simp only [hc, Bool.false_eq_true, ite_false, Effects.AllEnv] at h ⊢
    cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
    · cases atomic <;> simp only [Effects.AllEnv] at h ⊢
      · exact loadPieces_mono (fun vs g' h' => hk _ _ _ h' hd) h
      · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs) hd⟩
    · exact hk _ _ _ h hd

theorem storeAvx_dom (hI : StoreClosed I) {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {v : w.type}
    {r₁ r₂ : MachineData → Effects} {checkAlign atomic : Bool} {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (r₁ s').AllEnv env g P₁ → I s'.dmem → (r₂ s').AllEnv env g P₂)
    (h : (s.storeAvx addr v r₁ checkAlign atomic).AllEnv env g P₁) :
    (s.storeAvx addr v r₂ checkAlign atomic).AllEnv env g P₂ := by
  unfold MachineData.storeAvx at h ⊢
  split
  · rename_i hc; simp only [hc, ite_true, Effects.AllEnv] at h
  · rename_i hc
    simp only [hc, Bool.false_eq_true, ite_false, Effects.AllEnv] at h ⊢
    cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢
    · cases atomic <;> simp only [Effects.AllEnv] at h ⊢
      · exact storePieces_mono (fun g' h' => hk _ _ h' hd) h
      · exact ⟨h.1, fun b g' hs => hk _ _ (h.2 b g' hs) hd⟩
    · exact hk _ _ h (hI.store hd hm _)

theorem rmw16K_dom (hI : StoreClosed I) {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {r₁ r₂ : BitVec 128 → MachineData → Effects} {g : env.State}
    (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (s.rmw16K rk addr op r₁).AllEnv env g P₁) : (s.rmw16K rk addr op r₂).AllEnv env g P₂ := by
  unfold MachineData.rmw16K at h ⊢
  simp only [Effects.AllEnv] at h ⊢
  cases hm : Mem.loadInt s.dmem addr 16 <;> simp only [hm, Effects.AllEnv] at h ⊢
  · exact ⟨h.1, fun v g' hs => hk _ _ _ (h.2 v g' hs) hd⟩
  · cases ho : op _ <;> simp only [ho] at h ⊢
    · exact hk _ _ _ h hd
    · exact hk _ _ _ h (hI.store hd hm _)

theorem rmw16Plain_dom (hI : StoreClosed I) {s : MachineData} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {r₁ r₂ : BitVec 128 → MachineData → Effects} {g : env.State}
    (hd : I s.dmem)
    (hk : ∀ v s' g, (r₁ v s').AllEnv env g P₁ → I s'.dmem → (r₂ v s').AllEnv env g P₂)
    (h : (s.rmw16Plain addr op r₁).AllEnv env g P₁) : (s.rmw16Plain addr op r₂).AllEnv env g P₂ := by
  unfold MachineData.rmw16Plain at h ⊢
  refine loadAvx_dom hd (fun v s' g h hd => ?_) h
  cases hop : op v <;> simp only [hop] at h ⊢
  · exact hk _ _ _ h hd
  · exact storeAvx_dom hI hd (fun s'' g h hd => hk _ _ _ h hd) h

/-! ### Operands -/

theorem regOrMem_dom [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (k₁ v s').AllEnv env g P₁ → I s'.dmem → (k₂ v s').AllEnv env g P₂)
    (h : (o.interp s p k₁).AllEnv env g P₁) : (o.interp s p k₂).AllEnv env g P₂ := by
  cases o with
  | reg x => exact hk _ _ _ h hd
  | mem a => exact load_dom hd hk h

theorem operand_dom [Labels] [AddressSize] {w : Width} {o : Operand w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (k₁ v s').AllEnv env g P₁ → I s'.dmem → (k₂ v s').AllEnv env g P₂)
    (h : (o.interp s p k₁).AllEnv env g P₁) : (o.interp s p k₂).AllEnv env g P₂ := by
  cases o with
  | regOrMem rm => exact regOrMem_dom hd hk h
  | imm v => exact hk _ _ _ h hd

theorem relRegOrMem_dom [Labels] [AddressSize] {o : RelRegOrMem} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : BitVec 64 → MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (k₁ v s').AllEnv env g P₁ → I s'.dmem → (k₂ v s').AllEnv env g P₂)
    (h : (o.interp s p k₁).AllEnv env g P₁) : (o.interp s p k₂).AllEnv env g P₂ := by
  cases o with
  | rel c => exact hk _ _ _ h hd
  | reg x => exact hk _ _ _ h hd
  | mem a => exact load_dom hd hk h

theorem set_dom (hI : StoreClosed I) [Labels] [AddressSize] {w : Width} {dst : Dst w} {v : w.type}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (k₁ s').AllEnv env g P₁ → I s'.dmem → (k₂ s').AllEnv env g P₂)
    (h : (MachineData.set s dst v p k₁).AllEnv env g P₁) : (MachineData.set s dst v p k₂).AllEnv env g P₂ := by
  cases dst with
  | reg x =>
    simp only [MachineData.set, MachineData.setReg] at h ⊢
    exact hk _ _ h hd
  | mem a => exact store_dom hI hd hk h

theorem rmw_dom (hI : StoreClosed I) [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {lock : Bool}
    {p : Std.Rco Int64} {op : w.type → Option w.type} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    {g : env.State} (hd : I s.dmem)
    (hk : ∀ v s' g, (k₁ v s').AllEnv env g P₁ → I s'.dmem → (k₂ v s').AllEnv env g P₂)
    (h : (o.rmw lock s p op k₁).AllEnv env g P₁) : (o.rmw lock s p op k₂).AllEnv env g P₂ := by
  cases o with
  | reg x =>
    unfold RegOrMem.rmw at h ⊢
    simp only [MachineData.setReg] at h ⊢
    cases hop : op (s.regs.get x) <;> simp only [hop] at h ⊢ <;> exact hk _ _ _ h hd
  | mem a =>
    unfold RegOrMem.rmw at h ⊢
    cases lock with
    | true => exact rmwK_dom hI hd hk h
    | false => exact rmwPlain_dom hI hd hk h

theorem avxRegOrMem_dom [Labels] [AddressSize] {w : AvxWidth} {o : AvxRegOrMem w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects} {checkAlign atomic : Bool} {g : env.State}
    (hd : I s.dmem)
    (hk : ∀ v s' g, (k₁ v s').AllEnv env g P₁ → I s'.dmem → (k₂ v s').AllEnv env g P₂)
    (h : (o.interp s p k₁ checkAlign atomic).AllEnv env g P₁) :
    (o.interp s p k₂ checkAlign atomic).AllEnv env g P₂ := by
  cases o with
  | avx x => exact hk _ _ _ h hd
  | mem a => exact loadAvx_dom hd hk h

theorem avxOperand_dom [Labels] [AddressSize] {w : AvxWidth} {o : AvxOperand w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects} {checkAlign : Bool} {g : env.State}
    (hd : I s.dmem)
    (hk : ∀ v s' g, (k₁ v s').AllEnv env g P₁ → I s'.dmem → (k₂ v s').AllEnv env g P₂)
    (h : (o.interp s p k₁ checkAlign).AllEnv env g P₁) : (o.interp s p k₂ checkAlign).AllEnv env g P₂ := by
  cases o with
  | regOrMem rm => exact avxRegOrMem_dom hd hk h

theorem setAvx_dom (hI : StoreClosed I) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w} {v : w.type}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : MachineData → Effects} {checkAlign atomic : Bool}
    {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (k₁ s').AllEnv env g P₁ → I s'.dmem → (k₂ s').AllEnv env g P₂)
    (h : (MachineData.setAvx s dst v p k₁ checkAlign atomic).AllEnv env g P₁) :
    (MachineData.setAvx s dst v p k₂ checkAlign atomic).AllEnv env g P₂ := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvx, MachineData.setAvxReg] at h ⊢
    exact hk _ _ h hd
  | mem a => exact storeAvx_dom hI hd hk h

theorem setAvxLegacy_dom (hI : StoreClosed I) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w}
    {v : w.type} {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : MachineData → Effects}
    {checkAlign atomic : Bool} {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (k₁ s').AllEnv env g P₁ → I s'.dmem → (k₂ s').AllEnv env g P₂)
    (h : (MachineData.setAvxLegacy s dst v p k₁ checkAlign atomic).AllEnv env g P₁) :
    (MachineData.setAvxLegacy s dst v p k₂ checkAlign atomic).AllEnv env g P₂ := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvxLegacy, MachineData.setAvxLegacyReg] at h ⊢
    exact hk _ _ h hd
  | mem a => exact storeAvx_dom hI hd hk h

/-! ## The search over the instruction set -/

private theorem allEnv_ite (c : Prop) [Decidable c] (a b : Effects) (g : env.State) :
    (if c then a else b).AllEnv env g P₁ ↔ if c then a.AllEnv env g P₁ else b.AllEnv env g P₁ := by
  split <;> rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] RegOrMem.interp Operand.interp RelRegOrMem.interp MachineData.set
  MachineData.load MachineData.store MachineData.storeNT MachineData.rmwK MachineData.rmwPlain RegOrMem.rmw
  AvxRegOrMem.interp AvxOperand.interp MachineData.setAvx MachineData.setAvxLegacy
  MachineData.loadAvx MachineData.storeAvx MachineData.rmw16K MachineData.rmw16Plain

set_option hygiene false in
/-- `X64LiveRun`'s `jsim_search` with `AllEnv` on both sides and `I s.dmem`
(`hd`) threaded to every continuation. -/
local macro "dom_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, Reg.interp, MachineData.setReg, Effects.AllEnv, allEnv_ite] at h ⊢ <;>
    repeat' first
      | exact hk _ _ h hd
      | exact hj _ _ _ h hd
      | exact h.elim
      | refine operand_dom hd (fun v s' g h hd => ?_) h
      | refine regOrMem_dom hd (fun v s' g h hd => ?_) h
      | refine relRegOrMem_dom hd (fun v s' g h hd => ?_) h
      | refine set_dom hI hd (fun s' g h hd => ?_) h
      | refine load_dom hd (fun v s' g h hd => ?_) h
      | refine store_dom hI hd (fun s' g h hd => ?_) h
      | refine storeNT_dom hI hd (fun s' g h hd => ?_) h
      | refine rmwK_dom hI hd (fun v s' g h hd => ?_) h
      | refine rmw_dom hI hd (fun v s' g h hd => ?_) h
      | (refine ⟨h.1, fun g' hs => ?_⟩; replace h := h.2 g' hs)
      | (refine fun v => ?_; specialize h v)
      | dsimp only at h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [Reg.interp, MachineData.setReg, Effects.AllEnv, allEnv_ite] at h ⊢))

set_option maxHeartbeats 1000000 in
/-- **One operation keeps a `StoreClosed` property of `dmem`** at every
continuation it reaches. -/
theorem operation_dom (hI : StoreClosed I) [Labels] [AddressSize] {w : Width} (op : Operation w)
    (p : Std.Rco Int64) {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (k₁ s').AllEnv env g P₁ → I s'.dmem → (k₂ s').AllEnv env g P₂)
    (hj : ∀ pc s' g, (j₁ pc s').AllEnv env g P₁ → I s'.dmem → (j₂ pc s').AllEnv env g P₂)
    (h : (Operation.interp op p s k₁ j₁).AllEnv env g P₁) : (Operation.interp op p s k₂ j₂).AllEnv env g P₂ := by
  cases op
  case xadd lock dst src => cases dst <;> dom_search
  case bswap dst => cases w <;> dom_search
  all_goals dom_search

set_option hygiene false in
/-- `dom_search` for the vector operations. -/
local macro "avx_dom_search" : tactic =>
  `(tactic| (
    simp only [AvxOperation.interp, MachineData.setAvxReg, Effects.AllEnv] at h ⊢ <;>
    repeat' first
      | exact hk _ _ h hd
      | exact h.elim
      | refine avxOperand_dom hd (fun v s' g h hd => ?_) h
      | refine avxRegOrMem_dom hd (fun v s' g h hd => ?_) h
      | refine setAvx_dom hI hd (fun s' g h hd => ?_) h
      | refine setAvxLegacy_dom hI hd (fun s' g h hd => ?_) h
      | refine rmw16K_dom hI hd (fun v s' g h hd => ?_) h
      | refine rmw16Plain_dom hI hd (fun v s' g h hd => ?_) h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setAvxReg, Effects.AllEnv] at h ⊢))

/-- **One vector operation keeps a `StoreClosed` property of `dmem`.** -/
theorem avxOperation_dom (hI : StoreClosed I) [Labels] [AddressSize] {w : AvxWidth} (op : AvxOperation w)
    (p : Std.Rco Int64) {s : MachineData} {k₁ k₂ : MachineData → Effects} {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (k₁ s').AllEnv env g P₁ → I s'.dmem → (k₂ s').AllEnv env g P₂)
    (h : (AvxOperation.interp op p s k₁).AllEnv env g P₁) : (AvxOperation.interp op p s k₂).AllEnv env g P₂ := by
  cases op <;> avx_dom_search

/-- **One directive keeps a `StoreClosed` property of `dmem`.** -/
theorem directive_dom (hI : StoreClosed I) [Labels] (dir : Directive) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    {g : env.State} (hd : I s.dmem)
    (hk : ∀ s' g, (k₁ s').AllEnv env g P₁ → I s'.dmem → (k₂ s').AllEnv env g P₂)
    (hj : ∀ pc s' g, (j₁ pc s').AllEnv env g P₁ → I s'.dmem → (j₂ pc s').AllEnv env g P₂)
    (h : (dir.interp s p k₁ j₁).AllEnv env g P₁) : (dir.interp s p k₂ j₂).AllEnv env g P₂ := by
  cases dir with
  | instr i =>
    cases i with
    | regular asz osz op =>
      simp only [Directive.interp, Instr.interp] at h ⊢
      generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
      exact operation_dom hI op p hd hk hj h
    | avx asz osz aop =>
      simp only [Directive.interp, Instr.interp] at h ⊢
      generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
      exact avxOperation_dom hI aop p hd hk h
  | label l => exact hk _ _ h hd
  | byteArray b => exact h.elim

/-! ## Along every run -/

/-- **One env step keeps a `StoreClosed` property of `dmem`.** -/
theorem instrStepEnv_dmem (hI : StoreClosed I) {e : Kraken.Executable Directive}
    {st : MachineState × env.State} {post : MachineState × env.State → Prop} (hd : I st.1.1.dmem)
    (h : e.instrStepEnv env st post) : e.instrStepEnv env st (fun x => post x ∧ I x.1.1.dmem) := by
  obtain ⟨d, z, rest, hc, hs⟩ := h
  refine ⟨d, z, rest, hc, ?_⟩
  unfold Kraken.Executable.stepAtEnv at hs ⊢
  letI : Labels := _root_.Executable.labels e
  rcases hs with hs | hs
  · refine .inl (directive_dom hI d _ hd ?_ ?_ hs)
    · intro s' g h hd
      simp only [Effects.AllEnv] at h ⊢
      exact ⟨h, hd⟩
    · intro _ _ _ h _; simp only [Effects.AllEnv] at h
  · refine .inr (directive_dom hI d _ hd ?_ ?_ hs)
    · intro _ _ h _; simp only [Effects.AllEnv] at h
    · intro pc s' g h hd
      simp only [Effects.AllEnv] at h ⊢
      exact ⟨h, hd⟩

/-- **Total runs**: the property holds at the end. -/
theorem eventually_dmem (hI : StoreClosed I) {e : Kraken.Executable Directive}
    {Q : MachineState × env.State → Prop} {st : MachineState × env.State}
    (h : Eventually (e.instrStepEnv env) Q st) (hd : I st.1.1.dmem) :
    Eventually (e.instrStepEnv env) (fun x => Q x ∧ I x.1.1.dmem) st := by
  induction h with
  | done x hq => exact .done _ ⟨hq, hd⟩
  | step x R hT _ ih => exact .step _ _ (instrStepEnv_dmem hI hd hT) fun y hy => ih y hy.1 hy.2

/-- **Partial runs**: the property holds at every state reached. -/
theorem safely_dmem (hI : StoreClosed I) {e : Kraken.Executable Directive}
    {Q : MachineState × env.State → Prop} {st : MachineState × env.State}
    (h : Safely (e.instrStepEnv env) Q st) (hd : I st.1.1.dmem) :
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

end Kraken.DStack.X64
