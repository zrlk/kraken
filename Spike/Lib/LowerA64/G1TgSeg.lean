/-
**The branch-target check from a local invariant of the output** (AArch64):
`tgOkB` (`Spike/Lib/LowerA64/UserTgt.lean`) reads the run after the first
occurrence of every user label (`wcL`, none of the write abort's) and asks
that each direct branch of it go to a label with a nonempty run, none of the
write abort's. It holds once every occurrence of a user label is followed
by an instruction and every direct branch of the instructions after it goes
to a user label of the program (`TgInv`): no label uniqueness is needed,
since whichever occurrence is the first, its run is one of those.

The output of the lowering is a header, one segment per function and a
tail (`Spike/Lib/LowerA64/G1TgEmit.lean`); `TgInv` follows from a condition
on each segment (`PartOk`): a segment with no user label (the header, the
runtime's functions, the tail), or a user function's (`UserPart`): its name
then a list in which every label is followed by an instruction
(`labFollowed`), ending with an instruction, every direct branch going to a
user label of the list.

- `dirTgt`, `dTgt_classify`: a directive's direct branch target, as
  `dTgt (classify ·)` reads it;
- `TgInv`, `tgOkB_of_tgInv`: the local invariant and the check from it;
- `labFollowed`, `labFollowed_append`, `labFollowed_next`: every label
  followed by an instruction;
- `PartOk`, `UserPart`, `tgInv_of_parts`: the invariant from the segments.
-/
import Spike.Lib.LowerA64.UserTgt

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow (classify AI)
open Scc.Cert.Rt.A64 (labelIdx run isIns labelIdx_spec)
open Spike.Lib.A64.AllocG (abLabs)

/-! ## Direct branch targets -/

/-- **The direct branch target of a directive**: a `b`, `b.cond`, `cbz` or
`cbnz` to a label. -/
def dirTgt : Directive → Option Label
  | .instr ⟨.W64, .B (.label L)⟩ => some L
  | .instr ⟨.W64, .B_cond _ (.label L)⟩ => some L
  | .instr ⟨.W64, .CBZ _ (.label L)⟩ => some L
  | .instr ⟨.W64, .CBNZ _ (.label L)⟩ => some L
  | _ => none

/-- `dTgt` of a classified directive is its `dirTgt`. -/
theorem dTgt_classify (d : Directive) : dTgt (classify d) = dirTgt d := by
  unfold dirTgt
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · rename_i h1 h2 h3 h4
    unfold classify
    split
    · rfl
    · rfl
    · exact absurd rfl (h1 _)
    · exact absurd rfl (h2 _ _)
    · exact absurd rfl (h3 _ _)
    · exact absurd rfl (h4 _ _)
    · rfl
    · rfl
    · split <;> rfl
    · rfl

/-- A label is not an instruction. -/
theorem isIns_label (L : Label) : isIns (.label L) = false := rfl

/-- A directive with a direct branch target is an instruction. -/
theorem isIns_of_dirTgt {d : Directive} {T : Label} (h : dirTgt d = some T) : isIns d = true := by
  unfold dirTgt at h
  split at h <;> first | rfl | cases h

/-! ## The local invariant -/

/-- **The local invariant at index `i`**: if the `i`th directive is a user
label (`wcL`, none of the write abort's), the next one is an instruction,
and every direct branch of the instructions after it (up to the next label
or data) goes to a user label of the program. -/
def TgInvAt (prog : List Directive) (i : Nat) : Prop :=
  ∀ L0, prog[i]? = some (.label L0) → wcL L0 = true → L0 ∉ abLabs →
    (∃ d, prog[i + 1]? = some d ∧ isIns d = true) ∧
    ∀ d ∈ (prog.drop (i + 1)).takeWhile isIns, ∀ T, dirTgt d = some T →
      wcL T = true ∧ T ∉ abLabs ∧ Directive.label T ∈ prog

/-- **The local invariant** at every index. -/
def TgInv (prog : List Directive) : Prop := ∀ i, TgInvAt prog i

/-- A label of the program has an index. -/
theorem labelIdx_of_mem : ∀ {prog : List Directive} {l : Label}, Directive.label l ∈ prog →
    ∃ n, labelIdx prog l = some n
  | [], _, h => by simp at h
  | d :: ds, l, h => by
    unfold labelIdx
    split
    · exact ⟨0, rfl⟩
    · next hne =>
      have hm : Directive.label l ∈ ds := by
        rcases List.mem_cons.mp h with rfl | h
        · exact absurd rfl hne
        · exact h
      obtain ⟨n, hn⟩ := labelIdx_of_mem hm
      exact ⟨n + 1, by rw [hn]; rfl⟩

/-- **The run after a user label is nonempty** under the invariant. -/
theorem run_ne_nil_of_tgInv {prog : List Directive} (h : TgInv prog) {T : Label}
    (hT : Directive.label T ∈ prog) (hw : wcL T = true) (hab : T ∉ abLabs) : run prog T ≠ [] := by
  obtain ⟨m, hm⟩ := labelIdx_of_mem hT
  obtain ⟨d, hd, hi⟩ := (h m T (labelIdx_spec hm).1 hw hab).1
  unfold run
  rw [hm]
  show List.takeWhile isIns (prog.drop (m + 1)) ≠ []
  have h0 : (prog.drop (m + 1))[0]? = some d := by rw [List.getElem?_drop]; simpa using hd
  cases hdrop : prog.drop (m + 1) with
  | nil => rw [hdrop] at h0; cases h0
  | cons x xs =>
    rw [hdrop] at h0
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    rw [List.takeWhile_cons_of_pos hi]
    simp

/-- **The check from the local invariant.** -/
theorem tgOkB_of_tgInv {prog : List Directive} (h : TgInv prog) : tgOkB prog = true := by
  unfold tgOkB tgOkQB
  refine List.all_eq_true.mpr fun d hd => ?_
  cases d with
  | label L0 =>
    show (!(wcL L0 && !abLabs.contains L0) || (run prog L0).all fun c => match dTgt (classify c) with
      | some L => tgtOkB prog L
      | none => true) = true
    cases hq : (wcL L0 && !abLabs.contains L0)
    · rfl
    · rw [Bool.not_true, Bool.false_or]
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hq
      obtain ⟨n, hn⟩ := labelIdx_of_mem hd
      obtain ⟨-, hblk⟩ := h n L0 (labelIdx_spec hn).1 hq.1 hq.2
      refine List.all_eq_true.mpr fun c hc => ?_
      unfold run at hc
      rw [hn] at hc
      rw [dTgt_classify]
      split
      · next T hT =>
        obtain ⟨hw, hab, hmem⟩ := hblk c hc T hT
        obtain ⟨m, hm⟩ := labelIdx_of_mem hmem
        have hne := run_ne_nil_of_tgInv h hmem hw hab
        simp only [tgtOkB, hm, Option.isSome_some, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
          List.isEmpty_eq_false_iff, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨hne, hab⟩
      · rfl
  | instr _ => rfl
  | byteArray _ => rfl
  | zeros _ => rfl

/-! ## Every label followed by an instruction -/

/-- **Every label of a list is followed in it by an instruction** (the last
directive may be a label). -/
def labFollowed : List Directive → Bool
  | [] => true
  | [_] => true
  | d1 :: d2 :: ds => (isIns d1 || isIns d2) && labFollowed (d2 :: ds)

theorem labFollowed_cons_cons {d1 d2 : Directive} {ds : List Directive} :
    labFollowed (d1 :: d2 :: ds) = ((isIns d1 || isIns d2) && labFollowed (d2 :: ds)) := rfl

/-- A list of instructions passes. -/
theorem labFollowed_of_all : ∀ {D : List Directive}, D.all isIns = true → labFollowed D = true
  | [], _ => rfl
  | [_], _ => rfl
  | d1 :: d2 :: ds, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [labFollowed_cons_cons, h.1, labFollowed_of_all (by simpa using h.2)]
    rfl

/-- A singleton passes. -/
theorem labFollowed_singleton (d : Directive) : labFollowed [d] = true := rfl

/-- **Appending**: if the first list ends with a label, the second starts
with an instruction. -/
theorem labFollowed_append : ∀ {A B : List Directive}, labFollowed A = true → labFollowed B = true →
    (∀ a, A.getLast? = some a → ∀ b, B.head? = some b → (isIns a || isIns b) = true) →
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

/-- **The directive after a label** of a passing list is an instruction. -/
theorem labFollowed_next : ∀ {D : List Directive}, labFollowed D = true → ∀ {i : Nat} {L : Label},
    D[i]? = some (.label L) → ∀ d, D[i + 1]? = some d → isIns d = true
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
      simpa [isIns] using hD.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at h hd
      exact labFollowed_next hD.2 h d hd

/-- A passing list has no label at an index followed by another index
unless the next is an instruction: so a label at the last index only. -/
theorem labFollowed_last_of_label {D : List Directive} (hD : labFollowed D = true)
    (hl : ∀ d, D.getLast? = some d → isIns d = true) {i : Nat} {L : Label}
    (h : D[i]? = some (.label L)) : ∃ d, D[i + 1]? = some d ∧ isIns d = true := by
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
a list in which every label is followed by an instruction, ending with an
instruction, every direct branch of it going to a user label of the list. -/
def UserPart (P : List Directive) : Prop :=
  ∃ name P', P = .label name :: P' ∧ wcL name = false ∧ labFollowed P' = true ∧
    (∀ d, P'.getLast? = some d → isIns d = true) ∧
    ∀ d ∈ P', ∀ T, dirTgt d = some T → wcL T = true ∧ T ∉ abLabs ∧ Directive.label T ∈ P'

/-- **A segment of the output**: with no user label, or a user function's. -/
def PartOk (P : List Directive) : Prop :=
  (∀ L, Directive.label L ∈ P → wcL L = false) ∨ UserPart P

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
label (or data). -/
theorem tgInvAt_part {prog A P B : List Directive} (hprog : prog = A ++ (P ++ B)) (hP : PartOk P)
    (hB : ∀ b, B.head? = some b → isIns b = false) {i : Nat} (hi : i < P.length) :
    TgInvAt prog (A.length + i) := by
  intro L0 hL0 hw hab
  have hPi : P[i]? = some (.label L0) := by
    rw [hprog, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left hi] at hL0
    exact hL0
  rcases hP with hno | ⟨name, P', rfl, hname, hfol, hlast, htg⟩
  · exact absurd hw (by rw [hno L0 (List.mem_of_getElem? hPi)]; decide)
  · cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Directive.label.injEq] at hPi
      subst hPi
      rw [hname] at hw
      cases hw
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
label (or data, or empty). -/
theorem tgInv_of_parts (prog : List Directive) :
    ∀ (A : List Directive) (parts : List (List Directive)), prog = A ++ parts.flatten →
      (∀ i, i < A.length → TgInvAt prog i) → (∀ P ∈ parts, PartOk P) →
      (∀ P ∈ parts, ∀ d, P.head? = some d → isIns d = false) → TgInv prog
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

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.tgOkB_of_tgInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.tgOkB_of_tgInv

/-- info: 'Spike.Lib.LowerA64.tgInv_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.tgInv_of_parts
