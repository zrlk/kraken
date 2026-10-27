import Spike.Lib.Src.NJLB

/-!
**A ghost memory for a value's slices** (ISA-neutral). `NJB`'s labels `L`,
memory `sm` and bound `B` are ghosts: no field relates them to the source's
memory (the facts on the real memory are the memory side's). So words with
their layout's slices at any `L`, `sm` (`SliceL (SlP L sm)`, as `RetL`'s
`EnvSl` gives a returned value) have them at a ghost memory that also meets
`MemB`: `sm`'s messages at labels below the words' locatives' bound
(`locBound`), each holding `0`, and `L` cut at that bound.

- `locBound`: one past every locative label among the words;
- `SliceL.inWords`: a slice's label is a locative of the words;
- `sliceL_ghost`: `SliceL` at some ghost meeting `MemB`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (LitV)

/-- **One past every locative label among the words.** -/
def locBound : List TermRun.Word → Nat
  | [] => 0
  | w :: ws => match w.val with
    | .loc a _ => max (a.label + 1) (locBound ws)
    | _ => locBound ws

theorem lt_locBound : ∀ {ws : List TermRun.Word} {w : TermRun.Word}, w ∈ ws → ∀ {a : WeakMem.Address} {t : Nat},
    w.val = .loc a t → a.label < locBound ws
  | w' :: ws, w, hw, a, t, hv => by
    rcases List.mem_cons.1 hw with rfl | hw
    · show a.label < (match w.val with | .loc a _ => max (a.label + 1) (locBound ws) | _ => locBound ws)
      rw [hv]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · have := lt_locBound hw hv
      show a.label < (match w'.val with | .loc a _ => max (a.label + 1) (locBound ws) | _ => locBound ws)
      split
      · exact Nat.lt_of_lt_of_le this (Nat.le_max_right _ _)
      · exact this

/-- **A slice's label is a locative of the words.** -/
theorem SliceL.inWords {P : WeakMem.AllocLabel → Nat → Prop} :
    ∀ {V : LitV} {ws : List TermRun.Word}, SliceL P V ws →
      SliceL (fun l m => P l m ∧ ∃ w ∈ ws, w.val = .loc ⟨l, 0⟩ 0) V ws
  | .nil, _, _ | .leaf _, _, _ | .loc, _, _ => trivial
  | .node l r, ws, ⟨h0, hl, hr⟩ => by
    refine ⟨fun he => ?_, (SliceL.inWords hl).mono ?_, (SliceL.inWords hr).mono ?_⟩
    · obtain ⟨l', m, h1, h2, h3⟩ := h0 he
      obtain ⟨w, hw, hwv⟩ := Option.map_eq_some_iff.1 h1
      exact ⟨l', m, h1, h2, h3, w, List.mem_of_getElem? hw, hwv⟩
    · rintro l' m ⟨h, w, hw, hv⟩; exact ⟨h, w, List.mem_of_mem_take hw, hv⟩
    · rintro l' m ⟨h, w, hw, hv⟩; exact ⟨h, w, List.mem_of_mem_drop hw, hv⟩

/-- **The ghost memory**: `sm`'s messages at labels below `B`, each
holding `0`. -/
def ghostZ (sm : WeakMem.Memory) (B : Nat) : WeakMem.Memory :=
  (sm.filter fun m => decide (m.loc.label < B)).map fun m => ⟨m.loc, .num 0, m.view⟩

theorem mem_ghostZ {sm : WeakMem.Memory} {B : Nat} {m : WeakMem.Msg} (h : m ∈ ghostZ sm B) :
    m.loc.label < B ∧ m.val = .num 0 := by
  obtain ⟨m0, hm0, rfl⟩ := Array.mem_map.1 h
  exact ⟨of_decide_eq_true (Array.mem_filter.1 hm0).2, rfl⟩

theorem HasCell.ghostZ {sm : WeakMem.Memory} {sa : WeakMem.Address} (h : HasCell sm sa) {B : Nat}
    (hB : sa.label < B) : HasCell (Spike.Lib.LowerNode.ghostZ sm B) sa := by
  obtain ⟨k, m, hk, rfl⟩ := h
  have hm : (⟨m.loc, .num 0, m.view⟩ : WeakMem.Msg) ∈ Spike.Lib.LowerNode.ghostZ sm B :=
    Array.mem_map.2 ⟨m, Array.mem_filter.2 ⟨Array.mem_of_getElem? hk, decide_eq_true hB⟩, rfl⟩
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 hm
  exact ⟨j, _, hj, rfl⟩

/-- **Words with their layout's slices at any labels and memory have them
at a ghost meeting `MemB`** (`L` cut at `locBound ws`, `ghostZ`). -/
theorem sliceL_ghost {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {V : LitV} {ws : List TermRun.Word}
    (h : SliceL (SlP L sm) V ws) :
    ∃ (L' : WeakMem.AllocLabel → Prop) (sm' : WeakMem.Memory) (B : Nat), SliceL (SlP L' sm') V ws ∧ MemB L' sm' B := by
  refine ⟨fun l => L l ∧ l < locBound ws, ghostZ sm (locBound ws), locBound ws, (SliceL.inWords h).mono ?_,
    ⟨fun k m hk _ => ⟨0, (mem_ghostZ (Array.mem_of_getElem? hk)).2, by decide⟩,
      fun k m hk => (mem_ghostZ (Array.mem_of_getElem? hk)).1, fun _ hl => hl.2⟩⟩
  rintro l m ⟨⟨hL, hc, hm⟩, w, hw, hv⟩
  have hlt := lt_locBound hw hv
  exact ⟨⟨hL, hlt⟩, fun i hi => (hc i hi).ghostZ hlt, hm⟩

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.sliceL_ghost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.sliceL_ghost
