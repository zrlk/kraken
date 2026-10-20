/-
Program-independent address lemmas for a laid-out x64 program
(`Kraken.Promising.X64.isa`), the x64 counterpart of the address part of
`SLR/A64Trees.lean`. The per-program `*Trees.lean` files
(`SLR/X64SpinTrees`, `LiveX64TicketTrees`, `LiveX64Ticket2Trees`,
`LiveSpinX64CmpxTrees`, `LiveSpinX64XchgTrees`) state their `addrOf_step`,
`addrOf_label`, `addrOf_ne_succ` and `addrOf_inj` at their image and prove
them from these.

## Contents

- `layout_getElem`, `addrOf_step`, `addrOf_label`: addresses of positions of a
  laid-out program (one position further is one cell size further; a label
  occupies no bytes).
- `addrOf_ne_succ`: the address past an instruction differs from every
  address at or before it. The per-program files keep their own `isInstr`
  (a pattern-matching definition), so it is a parameter `isI` here, with the
  only fact used about it: labels are not instructions.
- `addrOf_inj_gen`: positions whose canonical representatives (at the same
  address) are increasing and each preceded by an instruction have distinct
  addresses (the x64 twin of `Live.SpinSwpTrees.addrOf_inj_gen`).
-/
import Kraken.Promising.SLR.X64Bridge

namespace Kraken.Promising.SLR.X64Trees

open Kraken Kraken.Promising Kraken.Promising.X64

variable [layout : _root_.Layout]

/-- The cell of a laid-out program at a position. -/
theorem layout_getElem (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]

/-- Stepping one position advances the address by that position's size. -/
theorem addrOf_step {p : Program} {i : Nat} (hi : i < p.length) :
    (layout p).addrOf (i + 1) = (layout p).addrOf i + .ofNat (Kraken.Layout.size Directive i) :=
  Executable.addrOf_succ _ (by rw [layout_getElem, List.getElem?_eq_getElem hi]; rfl)

/-- A label position occupies no bytes: the next position has its address. -/
theorem addrOf_label {p : Program} [hv : Executable.ValidLayout (layout p)] {i : Nat} {l : Label}
    (hp : p[i]? = some (Directive.label l)) : (layout p).addrOf (i + 1) = (layout p).addrOf i := by
  have hi : i < p.length := by
    by_cases h : i < p.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hp; cases hp
  have hz : Kraken.Layout.size Directive i = 0 :=
    hv.label_size i l _ (by rw [layout_getElem, hp]; rfl)
  rw [addrOf_step hi, hz]
  simp

/-- The address past an instruction (`isI`, which is `false` on labels)
differs from every address at or before it. -/
theorem addrOf_ne_succ (P : Program) [Executable.ValidLayout (layout P)] (isI : Directive → Bool)
    (hisI : ∀ l, isI (.label l) = false) {k n : Nat} (hk : k ≤ n) (h : P[n]?.map isI = some true) :
    (layout P).addrOf k ≠ (layout P).addrOf (n + 1) := by
  cases hp : P[n]? with
  | none => rw [hp] at h; cases h
  | some d =>
    rw [hp] at h
    refine Executable.addrOf_ne_of_valid _ (by omega) ?_ ?_
    · rw [Nat.add_sub_cancel, layout_getElem, hp]; rfl
    · intro l z hc
      rw [Nat.add_sub_cancel, layout_getElem, hp] at hc
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      simp [hisI] at h

/-- **Distinct addresses from a canonical representative**: positions `ps`
whose representatives (`canon`, at the same address) are increasing and each
preceded by an instruction have distinct addresses. -/
theorem addrOf_inj_gen (P : Program) [Executable.ValidLayout (layout P)] (isI : Directive → Bool)
    (hisI : ∀ l, isI (.label l) = false) (ps : List Nat) (canon : Nat → Nat)
    (hcan : ∀ i ∈ ps, (layout P).addrOf (canon i) = (layout P).addrOf i)
    (hc : ∀ i ∈ ps, ∀ j ∈ ps, i < j → canon i < canon j ∧ 1 ≤ canon j ∧ P[canon j - 1]?.map isI = some true)
    {i j : Nat} (hi : i ∈ ps) (hj : j ∈ ps) (h : (layout P).addrOf i = (layout P).addrOf j) : i = j := by
  have key : ∀ i j, i ∈ ps → j ∈ ps → i < j → (layout P).addrOf i ≠ (layout P).addrOf j := by
    intro i j hi hj hlt
    rw [← hcan i hi, ← hcan j hj]
    obtain ⟨h1, h2, h3⟩ := hc i hi j hj hlt
    have := addrOf_ne_succ P isI hisI (k := canon i) (n := canon j - 1) (by omega) h3
    rwa [Nat.sub_add_cancel h2] at this
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (key i j hi hj hlt)
  · exact heq
  · exact absurd h.symm (key j i hj hi hgt)

/-- **Read the cell at position `i` of the laid-out image `P`** through
`exec_eq_of_codeAt` and unfold it (the per-program `cell` macros of the x64
`Live*Trees` files). `h : At st i`; `us` unfold `P` to its directive list;
`ts` are extra simp lemmas (the program's label addresses and the cell's
operands). -/
macro "x64cell" h:ident i:num P:term:max "[" us:Lean.Parser.Tactic.simpLemma,* "]"
    "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := $P) (i := $i)
    (d := ($P)[$i]) (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : ($P)[$i] = d at hc
  simp only [$us,*, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  rw [exec_eq_of_codeAt ($h).exe ($h).decls ($h).ne hc]
  simp only [Directive.interp, Instr.interp, Operation.interp]
  simp [toEv, EvTree.map, EvTree.access_empty, Operand.interp, RegOrMem.interp, MachineData.set,
    MachineData.load, MachineData.store, MachineData.rmwK, RegOrMem.rmw, AddrExpr.interp,
    MachineData.setReg, RelRegOrMem.interp, ConstExpr.interp, BitVec.toAddressSize, $ts,*]))

end Kraken.Promising.SLR.X64Trees
