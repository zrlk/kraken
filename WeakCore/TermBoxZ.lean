import WeakCore.TermCut

/-!
# TermBoxZ: the `SysInvN` box clauses (box L1–L3)

Boxes are frozen ghost entries of `E_g`, created by their owner `B.own` with frontier
`B.fr` its `vWr` at creation (`EFoot`'s box disjunct).  The clauses, used by the
certificate transfer (`TermIni.runAgree_payW`, `RunAgree.pay`):

* (L1) `BoxPV`: a payload reference's view is below its box's frontier;
* (L2) `BoxFrOwn`: a box's frontier is at most its owner's `vWr`;
* (Ln) `BoxFrLe`: a box's frontier is at most the memory size;
* (L3) `PayOwn`: a payload reference to an unpublished cell names a cell of the box's owner;
* `BoxSto`: box labels hold no cell.
-/

namespace TermBoxZ
open CoreLang CoreTerm TermRun TermSound TermCut
open WeakMem (Address Ts AllocLabel)

/-- (box L1) A box payload reference's view is below the box's frontier. -/
def BoxPV (Eg : GEnv) : Prop :=
  ∀ l B, Eg.box l = some B → ∀ w ∈ B.pay, ∀ (a : Address) (g : Nat), w.val = .loc a g → w.view < B.fr

/-- (box L2) A box's frontier is at most its owner's `vWr`. -/
def BoxFrOwn (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ l B, Eg.box l = some B → ∀ th, c.ths[B.own]? = some th → B.fr ≤ th.vs.vWr

/-- (box Ln) Every box's frontier is at most the memory size. -/
def BoxFrLe (Eg : GEnv) (n : Nat) : Prop := ∀ l B, Eg.box l = some B → B.fr ≤ n

/-- (box L3) A box payload reference to an unpublished cell names a cell of the box's owner. -/
def PayOwn (Eg : GEnv) : Prop :=
  ∀ l B, Eg.box l = some B → ∀ w ∈ B.pay, ∀ (a : Address) (g : Nat), w.val = .loc a g →
    ∀ cl, Eg.sto a.label = some cl → Eg.pfr a.label = none → cl.owner = some B.own

/-- Box labels hold no cell. -/
def BoxSto (Eg : GEnv) : Prop := ∀ l B, Eg.box l = some B → Eg.sto l = none

/-- With no boxes, every box clause holds. -/
theorem boxPV_none {Eg : GEnv} (h : ∀ l, Eg.box l = none) : BoxPV Eg :=
  fun l B hB => by rw [h l] at hB; cases hB
theorem boxFrOwn_none {Eg : GEnv} {c : Cfg} (h : ∀ l, Eg.box l = none) : BoxFrOwn Eg c :=
  fun l B hB => by rw [h l] at hB; cases hB
theorem boxFrLe_none {Eg : GEnv} {n : Nat} (h : ∀ l, Eg.box l = none) : BoxFrLe Eg n :=
  fun l B hB => by rw [h l] at hB; cases hB
theorem payOwn_none {Eg : GEnv} (h : ∀ l, Eg.box l = none) : PayOwn Eg :=
  fun l B hB => by rw [h l] at hB; cases hB
theorem boxSto_none {Eg : GEnv} (h : ∀ l, Eg.box l = none) : BoxSto Eg :=
  fun l B hB => by rw [h l] at hB; cases hB

end TermBoxZ

#print axioms TermBoxZ.payOwn_none
