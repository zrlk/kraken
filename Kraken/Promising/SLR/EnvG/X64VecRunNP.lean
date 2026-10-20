/-
**The x64 run lemma for piece-free code, without a layout**. Generic, x64.

`X64LiveRun.exec_treeJ_of_instrStepEnv` assumes a layout `S` with
`Split S dmem` and `X64Fit S E` (or `E.within S`). Both are used only for
the adapter's *non-atomic vector pieces* (`loadPieces`/`storePieces`,
mapped-first per 8-byte piece while `AllEnv` sends every piece to the
environment) and to pin an `atomic` vector access to 16 bytes; every scalar
access, `rmw16` and atomic 16-byte access is mapped-first in both. An
environment that permits loads at any address (EnvG, whose unclean-path
values are arbitrary) fits no layout that also has a private stack in
`dmem`, so those links do not apply to code that loads through registers it
cannot pin down.

This file is `X64LiveRun`'s simulation with the vector part replaced by a
syntactic condition, **`Directive.NoPieces`**: the only vector operations are
the aligned 16-byte moves (`movaps`, `movapd`, `movdqa`, `vmovaps`,
`vmovapd`, `vmovdqa` at `W128`, the SDM's guaranteed-atomic accesses),
`lock cmpxchg16b`, and the register-only forms. With it, no `Split`, no
layout and no fit:

- `exec_treeJ_of_instrStepEnvNP`, `exec_treeJLive_of_instrStepEnvNP`: one
  `instrStepEnv E` step of a thread state with no declarations and
  piece-free code (`CodeNoPieces`) makes the tree satisfy `J`;
- `exec_treeJLive_of_instrStepEnvNPD`: the same with strict sized
  declarations (`X64VecDeclsFault`: the restricted judgment of the
  `decls = {}` tree).
-/
import Kraken.Promising.SLR.EnvG.X64LiveRun
import Kraken.Promising.SLR.EnvG.X64Link
import Kraken.Promising.SLR.EnvG.X64VecDeclsFault

open Kraken

namespace Kraken.Promising.X64

open Kraken.Promising.SLR.EnvSpike

/-- **A piece-free vector operation**: an aligned 16-byte move (one atomic
16-byte access), `lock cmpxchg16b` (one `rmw16`), or a register-only form. -/
def _root_.AvxOperation.NoPieces {w : AvxWidth} : AvxOperation w → Prop
  | .movaps .. | .movapd .. | .movdqa .. | .vmovaps .. | .vmovapd .. | .vmovdqa .. => w = .W128
  | .cmpxchg16b lock _ => lock = true
  | .vextractf128 .. | .vmovhlps .. | .vmovss .. | .vaddss .. | .vzeroupper => True
  | _ => False

/-- **A piece-free directive**: a regular instruction, a piece-free vector
operation, a label or data. -/
def _root_.Directive.NoPieces : Directive → Prop
  | .instr (.regular ..) => True
  | .instr (.avx _ _ op) => op.NoPieces
  | .label _ => True
  | .byteArray _ => True

/-- Every directive of the executable is piece-free. -/
def CodeNoPieces (e : _root_.Executable) : Prop := ∀ d z, (d, z) ∈ e.2 → d.NoPieces

namespace EnvG

/-! ## The simulation, per primitive -/

section JSimNP

variable {E : SharedEnv} (J : TreeJ E MachineState) {P₁ : MachineState → E.State → Prop}

theorem undefined_jsimNP {α : Type} {inst : NondetSupportingType α} {ret₁ ret₂ : α → Effects} {g : E.State}
    (hk : ∀ v, (ret₁ v).AllEnv E g P₁ → J.W (toEv {} (ret₂ v)) g)
    (h : ∀ v, (ret₁ v).AllEnv E g P₁) : J.W (toEv {} (Effects.undefined ret₂)) g := by
  cases inst <;> simp only [toEv]
  all_goals first | exact J.fault | exact J.choose fun i => hk _ (h _)

theorem load_jsimNP {s : MachineData} {addr : BitVec 64} {w : Width} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (MachineData.load s addr w k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.load s addr w k₂)) g := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.load h.1 fun v g' hv => hk _ _ _ (h.2 v g' hv)

theorem store_jsimNP {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    {g : E.State} (h : (MachineData.store s addr v k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.store s addr v k₂)) g := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.store h.1 fun b g' hb => hk _ _ (h.2 b g' hb)

theorem storeNT_jsimNP {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    {g : E.State} (h : (MachineData.storeNT s addr v k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.storeNT s addr v k₂)) g := by
  unfold MachineData.storeNT at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.store h.1 fun b g' hb => hk _ _ (h.2 b g' hb)

theorem rmwK_jsimNP {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (MachineData.rmwK s rk addr w op k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.rmwK s rk addr w op k₂)) g := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt w.bits x) <;> rw [hop] at h
    · exact hk _ _ _ h
    · exact hk _ _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.rmw h.1 fun old g' hold => hk _ _ _ (h.2 old g' hold)

theorem rmwPlain_jsimNP {s : MachineData} {addr : BitVec 64} {w : Width} {op : w.type → Option w.type}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (MachineData.rmwPlain s addr w op k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.rmwPlain s addr w op k₂)) g := by
  unfold MachineData.rmwPlain at h ⊢
  refine load_jsimNP J (fun v s g h => ?_) h
  cases hop : op v with
  | some new =>
    simp only [hop] at h ⊢
    exact store_jsimNP J (fun s g h => hk _ _ _ h) h
  | none =>
    simp only [hop] at h ⊢
    exact hk _ _ _ h

/-- An atomic 16-byte vector load: one event, as in `AllEnv`. -/
theorem loadAvx_jsimNP {s : MachineData} {addr : BitVec 64}
    {k₁ k₂ : (AvxWidth.W128).type → MachineData → Effects} {checkAlign : Bool}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (MachineData.loadAvx s addr .W128 k₁ checkAlign true).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.loadAvx s addr .W128 k₂ checkAlign true)) g := by
  unfold MachineData.loadAvx at h ⊢
  split
  · simp only [toEv]; exact J.fault
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllEnv, toEv] at h ⊢
    cases hd : Mem.loadInt s.dmem addr (AvxWidth.W128).bytes with
    | some x => rw [hd] at h; exact hk _ _ _ h
    | none =>
      rw [hd] at h
      simp only [Effects.AllEnv] at h
      obtain ⟨hok, h⟩ := h
      simp only [toEv, Bool.true_and, EvTree.access_empty]
      exact J.load hok fun v g' hv => hk _ _ _ (h v g' hv)

/-- An atomic 16-byte vector store: one event, as in `AllEnv`. -/
theorem storeAvx_jsimNP {s : MachineData} {addr : BitVec 64} {v : (AvxWidth.W128).type}
    {k₁ k₂ : MachineData → Effects} {checkAlign : Bool}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    {g : E.State} (h : (MachineData.storeAvx s addr v k₁ checkAlign true).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.storeAvx s addr v k₂ checkAlign true)) g := by
  unfold MachineData.storeAvx at h ⊢
  split
  · simp only [toEv]; exact J.fault
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllEnv, toEv] at h ⊢
    cases hd : Mem.loadInt s.dmem addr (AvxWidth.W128).bytes with
    | some x => rw [hd] at h; exact hk _ _ h
    | none =>
      rw [hd] at h
      simp only [Effects.AllEnv] at h
      obtain ⟨hok, h⟩ := h
      simp only [toEv, Bool.true_and, EvTree.access_empty]
      exact J.store hok fun b g' hb => hk _ _ (h b g' hb)

theorem rmw16K_jsimNP {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {k₁ k₂ : BitVec 128 → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (MachineData.rmw16K s rk addr op k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.rmw16K s rk addr op k₂)) g := by
  unfold MachineData.rmw16K at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr 16 with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt 128 x) <;> rw [hop] at h
    · exact hk _ _ _ h
    · exact hk _ _ _ h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.rmw h.1 fun old g' hold => hk _ _ _ (h.2 old g' hold)

/-! ### Operands -/

theorem avxRegOrMem_jsimNP [Labels] [AddressSize] {o : AvxRegOrMem .W128}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : (AvxWidth.W128).type → MachineData → Effects}
    {checkAlign : Bool}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (o.interp s p k₁ checkAlign true).AllEnv E g P₁) :
    J.W (toEv {} (o.interp s p k₂ checkAlign true)) g := by
  cases o with
  | avx x => exact hk _ _ _ h
  | mem a => exact loadAvx_jsimNP J hk h

theorem setAvx_jsimNP [Labels] [AddressSize] {dst : AvxDst .W128} {v : (AvxWidth.W128).type}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : MachineData → Effects} {checkAlign : Bool}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    {g : E.State} (h : (MachineData.setAvx s dst v p k₁ checkAlign true).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.setAvx s dst v p k₂ checkAlign true)) g := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvx, MachineData.setAvxReg] at h ⊢
    exact hk _ _ h
  | mem a => exact storeAvx_jsimNP J hk h

theorem setAvxLegacy_jsimNP [Labels] [AddressSize] {dst : AvxDst .W128} {v : (AvxWidth.W128).type}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : MachineData → Effects} {checkAlign : Bool}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    {g : E.State} (h : (MachineData.setAvxLegacy s dst v p k₁ checkAlign true).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.setAvxLegacy s dst v p k₂ checkAlign true)) g := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvxLegacy, MachineData.setAvxLegacyReg] at h ⊢
    exact hk _ _ h
  | mem a => exact storeAvx_jsimNP J hk h

theorem regOrMem_jsimNP [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (o.interp s p k₁).AllEnv E g P₁) :
    J.W (toEv {} (o.interp s p k₂)) g := by
  cases o with
  | reg x => exact hk _ _ _ h
  | mem a => exact load_jsimNP J hk h

theorem operand_jsimNP [Labels] [AddressSize] {w : Width} {o : Operand w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (o.interp s p k₁).AllEnv E g P₁) :
    J.W (toEv {} (o.interp s p k₂)) g := by
  cases o with
  | regOrMem rm => exact regOrMem_jsimNP J hk h
  | imm v => exact hk _ _ _ h

theorem relRegOrMem_jsimNP [Labels] [AddressSize] {o : RelRegOrMem} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : BitVec 64 → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (o.interp s p k₁).AllEnv E g P₁) :
    J.W (toEv {} (o.interp s p k₂)) g := by
  cases o with
  | rel c => exact hk _ _ _ h
  | reg x => exact hk _ _ _ h
  | mem a => exact load_jsimNP J hk h

theorem set_jsimNP [Labels] [AddressSize] {w : Width} {dst : Dst w} {v : w.type} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    {g : E.State} (h : (MachineData.set s dst v p k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.set s dst v p k₂)) g := by
  cases dst with
  | reg x =>
    simp only [MachineData.set, MachineData.setReg] at h ⊢
    exact hk _ _ h
  | mem a => exact store_jsimNP J hk h

theorem rmw_jsimNP [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {lock : Bool}
    {p : Std.Rco Int64} {op : w.type → Option w.type} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    {g : E.State} (h : (o.rmw lock s p op k₁).AllEnv E g P₁) :
    J.W (toEv {} (o.rmw lock s p op k₂)) g := by
  cases o with
  | reg x =>
    unfold RegOrMem.rmw at h ⊢
    simp only [MachineData.setReg] at h ⊢
    cases hop : op (s.regs.get x) <;> simp only [hop] at h ⊢ <;> exact hk _ _ _ h
  | mem a =>
    unfold RegOrMem.rmw at h ⊢
    cases lock with
    | true => exact rmwK_jsimNP J hk h
    | false => exact rmwPlain_jsimNP J hk h

/-! ### Per instruction -/

theorem jW_iteNP (c : Prop) [Decidable c] (a b : EvTree MachineState) (g : E.State) :
    J.W (if c then a else b) g ↔ if c then J.W a g else J.W b g := by
  split <;> rfl

theorem allEnv_iteNP (c : Prop) [Decidable c] (a b : Effects) (g : E.State) :
    (if c then a else b).AllEnv E g P₁ ↔ if c then a.AllEnv E g P₁ else b.AllEnv E g P₁ := by
  split <;> rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] RegOrMem.interp Operand.interp RelRegOrMem.interp MachineData.set
  MachineData.load MachineData.store MachineData.storeNT MachineData.rmwK MachineData.rmwPlain RegOrMem.rmw
  AvxRegOrMem.interp AvxOperand.interp MachineData.setAvx MachineData.setAvxLegacy
  MachineData.loadAvx MachineData.storeAvx MachineData.rmw16K MachineData.rmw16Plain

set_option hygiene false in
/-- `X64LiveRun`'s `jsim_search` without the private-memory split. -/
local macro "jsim_searchNP" : tactic =>
  `(tactic| (
    simp only [Operation.interp, Reg.interp, MachineData.setReg, Effects.AllEnv, toEv, toEv_ite,
      jW_iteNP, allEnv_iteNP] at h ⊢ <;>
    repeat' first
      | exact hk _ _ h
      | exact hj _ _ _ h
      | exact h.elim
      | exact J.fault
      | exact J.fence h.1 fun g' hg => hk _ _ (h.2 g' hg)
      | refine operand_jsimNP J (fun v s g h => ?_) h
      | refine regOrMem_jsimNP J (fun v s g h => ?_) h
      | refine relRegOrMem_jsimNP J (fun v s g h => ?_) h
      | refine set_jsimNP J (fun s g h => ?_) h
      | refine load_jsimNP J (fun v s g h => ?_) h
      | refine store_jsimNP J (fun s g h => ?_) h
      | refine storeNT_jsimNP J (fun s g h => ?_) h
      | refine rmwK_jsimNP J (fun v s g h => ?_) h
      | refine rmw_jsimNP J (fun v s g h => ?_) h
      | refine undefined_jsimNP J (fun v h => ?_) h
      | (refine J.choose fun i => ?_; specialize h (i.val == 1))
      | dsimp only at h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [Reg.interp, MachineData.setReg, Effects.AllEnv, toEv, toEv_ite, jW_iteNP,
          allEnv_iteNP] at h ⊢))

set_option maxHeartbeats 1000000 in
theorem operation_jsimNP [Labels] [AddressSize] {w : Width} (op : Operation w) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hj : ∀ pc s g, (j₁ pc s).AllEnv E g P₁ → J.W (toEv {} (j₂ pc s)) g)
    {g : E.State} (h : (Operation.interp op p s k₁ j₁).AllEnv E g P₁) :
    J.W (toEv {} (Operation.interp op p s k₂ j₂)) g := by
  cases op
  case xadd lock dst src => cases dst <;> jsim_searchNP
  case bswap dst => cases w <;> jsim_searchNP
  all_goals jsim_searchNP

theorem avxOperation_jsimNP [Labels] [AddressSize] {w : AvxWidth} (op : AvxOperation w) (hnp : op.NoPieces)
    (p : Std.Rco Int64) {s : MachineData} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    {g : E.State} (h : (AvxOperation.interp op p s k₁).AllEnv E g P₁) :
    J.W (toEv {} (AvxOperation.interp op p s k₂)) g := by
  cases op <;> simp only [AvxOperation.NoPieces] at hnp
  case cmpxchg16b lock dst =>
    subst hnp
    simp only [AvxOperation.interp] at h ⊢
    split <;> rename_i hc <;> simp only [hc, ite_true, ite_false, Bool.false_eq_true] at h ⊢
    · exact rmw16K_jsimNP J (fun v s g h => hk _ _ h) h
    · simp only [toEv]
      exact J.fault
  all_goals first
    | exact hnp.elim
    | (subst hnp
       simp only [AvxOperation.interp] at h ⊢
       first
         | exact avxRegOrMem_jsimNP J (fun v s g h => setAvxLegacy_jsimNP J hk h) h
         | exact avxRegOrMem_jsimNP J (fun v s g h => setAvx_jsimNP J hk h) h)
    | (simp only [AvxOperation.interp, MachineData.setAvxReg] at h ⊢
       exact hk _ _ h)

theorem instr_jsimNP [Labels] (i : Instr) (hnp : (Directive.instr i).NoPieces) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hj : ∀ pc s g, (j₁ pc s).AllEnv E g P₁ → J.W (toEv {} (j₂ pc s)) g)
    {g : E.State} (h : (i.interp s p k₁ j₁).AllEnv E g P₁) :
    J.W (toEv {} (i.interp s p k₂ j₂)) g := by
  cases i with
  | regular asz osz op =>
    simp only [Instr.interp] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact operation_jsimNP J op p hk hj h
  | avx asz osz aop =>
    simp only [Instr.interp] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact avxOperation_jsimNP J aop hnp p hk h

theorem directive_jsimNP [Labels] (dir : Directive) (hnp : dir.NoPieces) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s g, (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hj : ∀ pc s g, (j₁ pc s).AllEnv E g P₁ → J.W (toEv {} (j₂ pc s)) g)
    {g : E.State} (h : (dir.interp s p k₁ j₁).AllEnv E g P₁) :
    J.W (toEv {} (dir.interp s p k₂ j₂)) g := by
  cases dir with
  | instr i => exact instr_jsimNP J i hnp p hk hj h
  | label l => exact hk _ _ h
  | byteArray b => exact h.elim

end JSimNP

/-! ## One instruction -/

/-- **One instruction of piece-free code, any tree judgment, x64, no
layout**: `exec_treeJ_of_instrStepEnv` with `CodeNoPieces e` in place of
`Split`, `X64Fit` and `Le16`. -/
theorem exec_treeJ_of_instrStepEnvNP {E : SharedEnv} (J : TreeJ E State)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hds : st.decls = {}) (hnp : CodeNoPieces e)
    (h : e.instrStepEnv E (st.st, g) R)
    (hR : ∀ m g', R (m, g') → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  obtain ⟨d, sz, rest, hcode, hstep⟩ := h
  have hd : d.NoPieces := hnp d sz (mem_of_codeAt hcode)
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
    · refine directive_jsimNP J' d hd _ ?_ ?_ hstep
      · intro s' g' h
        exact J'.done (hR _ _ h)
      · intro _ _ _ h
        exact h.elim
    · refine directive_jsimNP J' d hd _ ?_ ?_ hstep
      · intro _ _ h
        exact h.elim
      · intro pc s' g' h
        exact J'.done (hR _ _ h)

/-- **One instruction of piece-free code, any live tree judgment, x64, no
layout** (`exec_treeJ_of_instrStepEnvNP` at `J.toTreeJ`; every x64 tree is
live). -/
theorem exec_treeJLive_of_instrStepEnvNP {E : SharedEnv} (J : SLR.EnvG.TreeJLive E State)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hds : st.decls = {}) (hnp : CodeNoPieces e)
    (h : e.instrStepEnv E (st.st, g) R)
    (hR : ∀ m g', R (m, g') → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g := fun tree ht =>
  exec_treeJ_of_instrStepEnvNP J.toTreeJ he hds hnp h hR tree ht (exec_rmwLive st tree ht)

/-- **One instruction of piece-free code with strict sized declarations,
any live tree judgment, x64, no layout**: `exec_treeJLive_of_instrStepEnvNP`
at the `decls = {}` state for the restricted judgment
(`exec_treeJLive_of_underDecls`). -/
theorem exec_treeJLive_of_instrStepEnvNPD {E : SharedEnv} (J : SLR.EnvG.TreeJLive E State)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hsz : st.decls.Sized) (hnp : CodeNoPieces e)
    (h : e.instrStepEnv E (st.st, g) R)
    (hR : ∀ m g', R (m, g') → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g :=
  SLR.EnvG.exec_treeJLive_of_underDecls J hsz
    (exec_treeJLive_of_instrStepEnvNP ((J.comap (State.withDecls st.decls)).underDecls st.decls hsz)
      (st := st.noDecls) he rfl hnp h fun m g' hm => by
        show J.Post (State.withDecls st.decls { st.noDecls with st := m }) g'
        rw [State.withDecls_noDecls_st]; exact hR m g' hm)

/-- **One instruction of piece-free code with strict sized declarations,
any tree judgment** (`exec_treeJLive_of_instrStepEnvNPD` for `TreeJ`). -/
theorem exec_treeJ_of_instrStepEnvNPD {E : SharedEnv} (J : TreeJ E State)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hsz : st.decls.Sized) (hnp : CodeNoPieces e)
    (h : e.instrStepEnv E (st.st, g) R)
    (hR : ∀ m g', R (m, g') → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g :=
  SLR.EnvG.exec_treeJ_of_underDecls J hsz
    (exec_treeJ_of_instrStepEnvNP ((J.comap (State.withDecls st.decls)).underDecls st.decls hsz)
      (st := st.noDecls) he rfl hnp h fun m g' hm => by
        show J.Post (State.withDecls st.decls { st.noDecls with st := m }) g'
        rw [State.withDecls_noDecls_st]; exact hR m g' hm)

end EnvG

end Kraken.Promising.X64
