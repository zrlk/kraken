/-
**The branch-target check from a local invariant of the output** (x86-64;
the twin of `Spike/Lib/LowerA64/G1TgSeg.lean`): `tgOkB`
(`Spike/Lib/LowerX64/UserTgt.lean`) reads the run after the first
occurrence of every user label (`WcL`, none of the write abort's) and asks
that each `jmp` or `jcc` of it go to a label with a nonempty run, none of
the write abort's. It reads the cells' directives only (`cells.map (·.1)`),
and holds once every occurrence of a user label is followed by a non-label
and every `jmp`/`jcc` of the run after it goes to a user label of the
program (`TgInv`): no label uniqueness is needed, since whichever
occurrence is the first, its run is one of those.

The output is a header, one segment per function and a tail; `TgInv`
follows from a condition on each segment (`PartOk`): a segment with no user
label (the header, the runtime's functions, the tail), or a user function's
(`UserPart`): its name then a list in which every label is followed by a
non-label (`labFollowed`), ending with a non-label, every `jmp`/`jcc` going
to a user label of the list.

- `dirTgt`, `dirTgt_of_classify`: a directive's direct jump target, as
  `tgOkB`'s `classify` reads it;
- `TgInv`, `tgOkB_of_tgInv`: the local invariant and the check from it;
- `labFollowed`, `labFollowed_append`, `labFollowed_next`: every label
  followed by a non-label;
- `PartOk`, `UserPart`, `tgInv_of_parts`: the invariant from the segments.
-/
import Spike.Lib.LowerX64.UserTgt

namespace Spike.Lib.LowerX64

open Kraken
open Spike.Lib.X64 (AI classify classify_sound)
open Scc.Cert.Rt.X64 (labelIdx run labelIdx_spec)
open Spike.Lib.X64.AllocG (abLabs)

/-! ## Direct jump targets -/

/-- **The direct jump target of a directive**: a `jmp` or `jcc` to a
label. -/
def dirTgt : Directive → Option Label
  | .instr (.regular _ _ (.jmp (.rel (.sub (.label L) _)))) => some L
  | .instr (.regular _ _ (.jcc _ L)) => some L
  | _ => none

/-- A directive `classify` reads as a `jmp` or `jcc` has that target. -/
theorem dirTgt_of_classify {d : Directive} {L : Label}
    (h : classify d = some (.jmp L) ∨ ∃ cc, classify d = some (.jcc cc L)) : dirTgt d = some L := by
  rcases h with h | ⟨cc, h⟩
  · rw [(classify_sound h).1]; rfl
  · rw [(classify_sound h).1]; rfl

/-- A non-label directive. -/
def nLab (d : Directive) : Bool := !d.isLabel

/-- A directive with a direct jump target is no label. -/
theorem nLab_of_dirTgt {d : Directive} {T : Label} (h : dirTgt d = some T) : nLab d = true := by
  unfold dirTgt at h
  split at h <;> first | rfl | cases h

/-! ## The local invariant -/

/-- **The local invariant at index `i`**: if the `i`th directive is a user
label (`WcL`, none of the write abort's), the next one is no label, and
every direct jump of the directives after it (up to the next label) goes to
a user label of the program. -/
def TgInvAt (prog : List Directive) (i : Nat) : Prop :=
  ∀ L0, prog[i]? = some (.label L0) → WcL L0 → L0 ∉ abLabs →
    (∃ d, prog[i + 1]? = some d ∧ nLab d = true) ∧
    ∀ d ∈ (prog.drop (i + 1)).takeWhile nLab, ∀ T, dirTgt d = some T →
      WcL T ∧ T ∉ abLabs ∧ Directive.label T ∈ prog

/-- **The local invariant** at every index. -/
def TgInv (prog : List Directive) : Prop := ∀ i, TgInvAt prog i

/-- A label of the cells has an index. -/
theorem labelIdx_of_mem : ∀ {cells : List (Directive × Nat)} {l : Label}, Directive.label l ∈ cells.map (·.1) →
    ∃ n, labelIdx cells l = some n
  | [], _, h => by simp at h
  | c :: cs, l, h => by
    unfold labelIdx
    split
    · exact ⟨0, rfl⟩
    · next hne =>
      have hm : Directive.label l ∈ cs.map (·.1) := by
        rcases List.mem_cons.mp h with e | h
        · exact absurd e.symm hne
        · exact h
      obtain ⟨n, hn⟩ := labelIdx_of_mem hm
      exact ⟨n + 1, by rw [hn]; rfl⟩

/-- The directive at an index of the cells. -/
theorem getElem?_map_fst {cells : List (Directive × Nat)} {n : Nat} {d : Directive} {z : Nat}
    (h : cells[n]? = some (d, z)) : (cells.map (·.1))[n]? = some d := by
  rw [List.getElem?_map, h]; rfl

/-- The run's directives are the directives' run. -/
theorem run_map {cells : List (Directive × Nat)} {n : Nat} :
    ((cells.drop (n + 1)).takeWhile (fun c => !c.1.isLabel)).map (·.1) =
      ((cells.map (·.1)).drop (n + 1)).takeWhile nLab := by
  rw [← List.map_drop, List.takeWhile_map]
  rfl

/-- **The run after a user label is nonempty** under the invariant. -/
theorem run_ne_nil_of_tgInv {cells : List (Directive × Nat)} (h : TgInv (cells.map (·.1))) {T : Label}
    (hT : Directive.label T ∈ cells.map (·.1)) (hw : WcL T) (hab : T ∉ abLabs) : run cells T ≠ [] := by
  obtain ⟨m, hm⟩ := labelIdx_of_mem hT
  obtain ⟨⟨z, hz⟩, -⟩ := labelIdx_spec hm
  obtain ⟨d, hd, hi⟩ := (h m T (getElem?_map_fst hz) hw hab).1
  unfold run
  rw [hm]
  intro he
  have he' := congrArg (List.map (·.1)) he
  rw [run_map] at he'
  have h0 : ((cells.map (·.1)).drop (m + 1))[0]? = some d := by rw [List.getElem?_drop]; simpa using hd
  cases hdrop : (cells.map (·.1)).drop (m + 1) with
  | nil => rw [hdrop] at h0; cases h0
  | cons x xs =>
    rw [hdrop] at h0 he'
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    rw [List.takeWhile_cons_of_pos hi] at he'
    cases he'

/-- **The check from the local invariant** of the cells' directives. -/
theorem tgOkB_of_tgInv {cells : List (Directive × Nat)} (h : TgInv (cells.map (·.1))) : tgOkB cells = true := by
  unfold tgOkB
  refine List.all_eq_true.mpr fun c hc => ?_
  obtain ⟨d, z⟩ := c
  cases d with
  | label L0 =>
    show (!(decide (WcL L0) && decide (L0 ∉ abLabs)) || (run cells L0).all fun c' =>
      match classify c'.1 with
      | some (.jmp L) => tgtOkB cells L
      | some (.jcc _ L) => tgtOkB cells L
      | _ => true) = true
    by_cases hq : WcL L0 ∧ L0 ∉ abLabs
    · rw [decide_eq_true hq.1, decide_eq_true hq.2, Bool.and_true, Bool.not_true, Bool.false_or]
      have hd : Directive.label L0 ∈ cells.map (·.1) := List.mem_map.mpr ⟨_, hc, rfl⟩
      obtain ⟨n, hn⟩ := labelIdx_of_mem hd
      obtain ⟨⟨z0, hz0⟩, -⟩ := labelIdx_spec hn
      obtain ⟨-, hblk⟩ := h n L0 (getElem?_map_fst hz0) hq.1 hq.2
      refine List.all_eq_true.mpr fun c hc => ?_
      unfold run at hc
      rw [hn] at hc
      have hc' : c.1 ∈ ((cells.map (·.1)).drop (n + 1)).takeWhile nLab := by
        rw [← run_map]; exact List.mem_map.mpr ⟨c, hc, rfl⟩
      have key : ∀ T, dirTgt c.1 = some T → tgtOkB cells T = true := by
        intro T hT
        obtain ⟨hw, hab, hmem⟩ := hblk c.1 hc' T hT
        obtain ⟨m, hm⟩ := labelIdx_of_mem hmem
        have hne := run_ne_nil_of_tgInv h hmem hw hab
        simp only [tgtOkB, hm, Option.isSome_some, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
          List.isEmpty_eq_false_iff, decide_eq_true_eq]
        exact ⟨hne, hab⟩
      split
      · next L hL => exact key L (dirTgt_of_classify (.inl hL))
      · next cc L hL => exact key L (dirTgt_of_classify (.inr ⟨cc, hL⟩))
      · rfl
    · have : (decide (WcL L0) && decide (L0 ∉ abLabs)) = false := by
        cases h1 : decide (WcL L0) <;> cases h2 : decide (L0 ∉ abLabs) <;> simp_all
      rw [this]; rfl
  | instr _ => rfl
  | byteArray _ => rfl

/-! ## Every label followed by a non-label -/

/-- **Every label of a list is followed in it by a non-label** (the last
directive may be a label). -/
def labFollowed : List Directive → Bool
  | [] => true
  | [_] => true
  | d1 :: d2 :: ds => (nLab d1 || nLab d2) && labFollowed (d2 :: ds)

theorem labFollowed_cons_cons {d1 d2 : Directive} {ds : List Directive} :
    labFollowed (d1 :: d2 :: ds) = ((nLab d1 || nLab d2) && labFollowed (d2 :: ds)) := rfl

/-- A singleton passes. -/
theorem labFollowed_singleton (d : Directive) : labFollowed [d] = true := rfl

/-- **Appending**: if the first list ends with a label, the second starts
with a non-label. -/
theorem labFollowed_append : ∀ {A B : List Directive}, labFollowed A = true → labFollowed B = true →
    (∀ a, A.getLast? = some a → ∀ b, B.head? = some b → (nLab a || nLab b) = true) →
    labFollowed (A ++ B) = true
  | [], B, _, hB, _ => by simpa using hB
  | [a], B, _, hB, hAB => by
    cases B with
    | nil => rfl
    | cons b bs =>
      rw [List.singleton_append, labFollowed_cons_cons, hB, hAB a rfl b rfl]
      rfl
  | a1 :: a2 :: rest, B, hA, hB, hAB => by
    rw [labFollowed_cons_cons, Bool.and_eq_true] at hA
    rw [List.cons_append, List.cons_append, labFollowed_cons_cons, hA.1, Bool.true_and]
    exact labFollowed_append hA.2 hB (fun a ha b hb => hAB a (by rw [List.getLast?_cons_cons]; exact ha) b hb)

/-- **The directive after a label** of a passing list is no label. -/
theorem labFollowed_next : ∀ {D : List Directive}, labFollowed D = true → ∀ {i : Nat} {L : Label},
    D[i]? = some (.label L) → ∀ d, D[i + 1]? = some d → nLab d = true
  | [], _, i, _, h, _, _ => by simp at h
  | [_], _, i, _, h, d, hd => by
    cases i with
    | zero => simp at hd
    | succ i => simp at h
  | d1 :: d2 :: ds, hD, i, L, h, d, hd => by
    rw [labFollowed_cons_cons, Bool.and_eq_true] at hD
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h hd
      subst h
      subst hd
      simpa [nLab, Directive.isLabel] using hD.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at h hd
      exact labFollowed_next hD.2 h d hd

/-- A passing list ending with a non-label has a non-label after each of
its labels. -/
theorem labFollowed_last_of_label {D : List Directive} (hD : labFollowed D = true)
    (hl : ∀ d, D.getLast? = some d → nLab d = true) {i : Nat} {L : Label}
    (h : D[i]? = some (.label L)) : ∃ d, D[i + 1]? = some d ∧ nLab d = true := by
  have hi : i < D.length := (List.getElem?_eq_some_iff.mp h).1
  by_cases hi1 : i + 1 < D.length
  · exact ⟨D[i + 1], List.getElem?_eq_getElem hi1, labFollowed_next hD h _ (List.getElem?_eq_getElem hi1)⟩
  · have he : i = D.length - 1 := by omega
    have := hl (.label L) (by
      rw [List.getLast?_eq_getElem?, ← he]
      exact h)
    cases this

/-! ## The invariant from the segments -/

/-- **A user function's segment**: its name's label (no user label) then
a list in which every label is followed by a non-label, ending with a
non-label, every direct jump of it going to a user label of the list. -/
def UserPart (P : List Directive) : Prop :=
  ∃ name P', P = .label name :: P' ∧ ¬ WcL name ∧ labFollowed P' = true ∧
    (∀ d, P'.getLast? = some d → nLab d = true) ∧
    ∀ d ∈ P', ∀ T, dirTgt d = some T → WcL T ∧ T ∉ abLabs ∧ Directive.label T ∈ P'

/-- **A segment of the output**: with no user label, or a user function's. -/
def PartOk (P : List Directive) : Prop :=
  (∀ L, Directive.label L ∈ P → ¬ WcL L) ∨ UserPart P

/-- The prefix of a list up to its first non-`p` element stays in the list
when what follows is empty or starts with a non-`p` element. -/
theorem mem_takeWhile_append {p : Directive → Bool} {X B : List Directive}
    (hB : ∀ b, B.head? = some b → p b = false) {d : Directive} (hd : d ∈ (X ++ B).takeWhile p) : d ∈ X := by
  induction X with
  | nil =>
    simp only [List.nil_append] at hd
    cases B with
    | nil => simp at hd
    | cons b bs =>
      rw [List.takeWhile_cons_of_neg (by simpa using hB b rfl)] at hd
      simp at hd
  | cons x xs ih =>
    rw [List.cons_append] at hd
    by_cases hx : p x = true
    · rw [List.takeWhile_cons_of_pos hx] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hd)
    · rw [List.takeWhile_cons_of_neg hx] at hd
      simp at hd

/-- **The invariant at the indices of one segment**: the program is
`A ++ P ++ B`, `P` a segment (`PartOk`) and `B` empty or starting with a
label. -/
theorem tgInvAt_part {prog A P B : List Directive} (hprog : prog = A ++ (P ++ B)) (hP : PartOk P)
    (hB : ∀ b, B.head? = some b → nLab b = false) {i : Nat} (hi : i < P.length) :
    TgInvAt prog (A.length + i) := by
  intro L0 hL0 hw hab
  have hPi : P[i]? = some (.label L0) := by
    rw [hprog, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left hi] at hL0
    exact hL0
  rcases hP with hno | ⟨name, P', rfl, hname, hfol, hlast, htg⟩
  · exact absurd hw (hno L0 (List.mem_of_getElem? hPi))
  · cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Directive.label.injEq] at hPi
      subst hPi
      exact absurd hw hname
    | succ i =>
      simp only [List.getElem?_cons_succ] at hPi
      obtain ⟨d, hd, hdi⟩ := labFollowed_last_of_label hfol hlast hPi
      have hi1 : i + 1 < P'.length := (List.getElem?_eq_some_iff.mp hd).1
      have hd' : prog[A.length + (i + 1) + 1]? = some d := by
        rw [hprog, show A.length + (i + 1) + 1 = A.length + (i + 1 + 1) by omega,
          List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
          List.getElem?_append_left (by simp only [List.length_cons]; omega), List.getElem?_cons_succ]
        exact hd
      refine ⟨⟨d, hd', hdi⟩, fun c hc T hT => ?_⟩
      have hc' : c ∈ P'.drop (i + 1) := by
        rw [hprog, show A.length + (i + 1) + 1 = A.length + (i + 1 + 1) by omega,
          List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append,
          Nat.add_sub_cancel_left,
          List.drop_append_of_le_length (by simp only [List.length_cons]; omega), List.drop_succ_cons] at hc
        exact mem_takeWhile_append hB hc
      obtain ⟨hwT, habT, hmemT⟩ := htg c (List.mem_of_mem_drop hc') T hT
      exact ⟨hwT, habT, by rw [hprog]; simp [hmemT]⟩

/-- **The invariant from the segments**: the program is a prefix `A` whose
indices pass, then segments each passing `PartOk` and each starting with a
label (or empty). -/
theorem tgInv_of_parts (prog : List Directive) :
    ∀ (A : List Directive) (parts : List (List Directive)), prog = A ++ parts.flatten →
      (∀ i, i < A.length → TgInvAt prog i) → (∀ P ∈ parts, PartOk P) →
      (∀ P ∈ parts, ∀ d, P.head? = some d → nLab d = false) → TgInv prog
  | A, [], hprog, hA, _, _ => by
    intro i L0 hL0
    have hlen : prog.length = A.length := by rw [hprog]; simp
    exact hA i (hlen ▸ (List.getElem?_eq_some_iff.mp hL0).1) L0 hL0
  | A, P :: parts, hprog, hA, hok, hstart => by
    refine tgInv_of_parts prog (A ++ P) parts (by rw [hprog, List.flatten_cons, List.append_assoc]) ?_
      (fun Q hQ => hok Q (List.mem_cons_of_mem _ hQ)) (fun Q hQ => hstart Q (List.mem_cons_of_mem _ hQ))
    intro i hi
    rw [List.length_append] at hi
    by_cases hiA : i < A.length
    · exact hA i hiA
    · obtain ⟨j, rfl⟩ : ∃ j, i = A.length + j := ⟨i - A.length, by omega⟩
      refine tgInvAt_part (B := parts.flatten) (by rw [hprog, List.flatten_cons])
        (hok P (List.mem_cons_self ..)) ?_ (by omega)
      intro b hb
      obtain ⟨Q, hQ, hbQ⟩ : ∃ Q ∈ parts, Q.head? = some b := by
        clear hprog hA hok hstart hi hiA
        induction parts with
        | nil => simp at hb
        | cons Q qs ih =>
          rw [List.flatten_cons] at hb
          cases Q with
          | nil =>
            obtain ⟨Q', hQ', h⟩ := ih (by simpa using hb)
            exact ⟨Q', List.mem_cons_of_mem _ hQ', h⟩
          | cons q Q' => exact ⟨q :: Q', List.mem_cons_self .., by simpa using hb⟩
      exact hstart Q (List.mem_cons_of_mem _ hQ) b hbQ

/-- **A prefix with no user label passes** at each of its indices. -/
theorem tgInvAt_prefix {prog A : List Directive} (hA : ∀ L, Directive.label L ∈ A → ¬ WcL L)
    {B : List Directive} (hprog : prog = A ++ B) : ∀ i, i < A.length → TgInvAt prog i := by
  intro i hi L0 hL0 hw _
  rw [hprog, List.getElem?_append_left hi] at hL0
  exact absurd hw (hA L0 (List.mem_of_getElem? hL0))

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.tgOkB_of_tgInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.tgOkB_of_tgInv

/-- info: 'Spike.Lib.LowerX64.tgInv_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.tgInv_of_parts
