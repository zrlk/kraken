import Scc.Cert.Rt.CodeX64

/-!
# Fixed code at its labels in one pass (x64)

The x64 twin of `Scc/Cert/Rt/RtPassA64.lean`. The runtime's code checks
(`Rt.X64.Abort.abortIn`, `Rt.X64.Print.printIn`, the tails of
`scc_rt_main`) are conjunctions of `blockAtB` and `labelGapB` facts at fixed
labels; each fact with a label not met before searches the code from its
start (`after`, `labelIdx`), comparing strings, so the checks cost the
kernel a pass over the code per distinct label.

`rtIn cells gs` checks the same facts in one pass, as `blocksIn` does: the
groups `gs` (`RGrp`) in program order, each label of the code encoded once
into a number (`key`) and compared with the next group's. A group is a
label, blocks at byte offsets after it (as `blockAtB`), and optionally a
label gap: the run of non-label cells after the label takes exactly `off`
bytes and the label `b` ends it (`labelGapB`). The pass stops after the last
group.

`rtIn_sound` gives every group's facts (`RtAll`, unfolding to the
conjunction of the `blockAtB`/`labelGapB` facts on a concrete table).

Where x64 differs from AArch64: offsets are in bytes, so a block's place is
found by walking the run after its label (`dropBytes`, as `blockAtB`), and
a gap is a byte count, with the gap's cell count the run's length (as
`labelGapB`).
-/

namespace Scc.Cert.Rt.X64

open Kraken Kraken.Promising Kraken.Promising.X64

/-- **A group of fixed code**: blocks at byte offsets after the first
`label l` (`blockAtB cells l off b`), and optionally the label ending the
run after it, `off` bytes on (`labelGapB cells l b off`). -/
structure RGrp where
  l : Label
  bs : List (Nat × List (Directive × Nat))
  gap : Option (Nat × Label) := none

/-- `runRest` for the code generator. -/
def runRestImpl : List (Directive × Nat) → List (Directive × Nat)
  | [] => []
  | c :: cs => if notLab c then runRestImpl cs else c :: cs

/-- The cells after the non-label cells at the head of a list (from its
first label on). -/
@[implemented_by runRestImpl] def runRest (cs : List (Directive × Nat)) : List (Directive × Nat) :=
  List.rec (motive := fun _ => List (Directive × Nat)) [] (fun c cs r => if notLab c then r else c :: cs) cs

theorem cellRun_append_runRest : ∀ cs : List (Directive × Nat), cellRun cs ++ runRest cs = cs
  | [] => rfl
  | c :: cs => by
    have ih := cellRun_append_runRest cs
    simp only [cellRun, runRest] at ih ⊢
    cases h : notLab c <;> simp [ih]

private theorem pred_of_mem_takeWhile {α : Type} {p : α → Bool} : ∀ {l : List α} {x : α},
    x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | a :: l, x, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · assumption
      · exact pred_of_mem_takeWhile h
    · simp at h

theorem notLabel_of_mem_cellRun {cs : List (Directive × Nat)} {c : Directive × Nat} (h : c ∈ cellRun cs) :
    c.1.isLabel = false := by
  rw [cellRun_eq] at h
  simpa using pred_of_mem_takeWhile h

/-- A block's check in the cells `cs` after its label (as `blockAtB`): the
block `ob.2` at `ob.1` bytes into the run. -/
def bOk (cs : List (Directive × Nat)) (ob : Nat × List (Directive × Nat)) : Bool :=
  match dropBytes (cellRun cs) ob.1 with
  | some r => decide (r.take ob.2.length = ob.2)
  | none => false

/-- The gap check at a label of key `km` (the keys of the labels before it
`seen`) followed by `cs`: the run after it takes `off` bytes, then the
`label b`, `b` not met before. -/
def gapOk (seen : List Nat) (km : Nat) (cs : List (Directive × Nat)) : Option (Nat × Label) → Bool
  | none => true
  | some (off, b) =>
    Nat.beq (sizeSum (cellRun cs)) off &&
      match runRest cs with
      | (.label b', _) :: _ => Nat.beq (key b') (key b) && !memR (key b) (km :: seen)
      | _ => false

/-- One step of `rtPass`: at a label, the next group's checks if the keys
agree; done after the last group. -/
def rtStep (c : Directive × Nat) (cs : List (Directive × Nat)) (r : List Nat → List RGrp → Bool)
    (seen : List Nat) (gs : List RGrp) : Bool :=
  match gs with
  | [] => true
  | g :: gs' =>
    match c.1 with
    | .label m =>
      cond (Nat.beq (key m) (key g.l))
        (!memR (key m) seen && g.bs.all (bOk cs) && gapOk seen (key m) cs g.gap && r (key m :: seen) gs')
        (r (key m :: seen) (g :: gs'))
    | _ => r seen (g :: gs')

/-- `rtPass` for the code generator. -/
def rtPassImpl : List (Directive × Nat) → List Nat → List RGrp → Bool
  | [], _, gs => gs.isEmpty
  | c :: cs, seen, gs => rtStep c cs (rtPassImpl cs) seen gs

/-- **One pass over the code** checking the groups in program order, each
at the first label of its name (none before it among `seen`). -/
@[implemented_by rtPassImpl]
def rtPass (cells : List (Directive × Nat)) : List Nat → List RGrp → Bool :=
  List.rec (motive := fun _ => List Nat → List RGrp → Bool)
    (fun _ gs => gs.isEmpty) (fun c cs r => rtStep c cs r) cells

/-- **The groups' code in `cells`**, checked in one pass. -/
def rtIn (cells : List (Directive × Nat)) (gs : List RGrp) : Bool := rtPass cells [] gs

/-- info: [true, false, false, false, true, false] -/
#guard_msgs in
#eval [rtIn [(.label "a", 0), (.label "b", 0), (.label "c", 0)] [⟨"a", [], some (0, "b")⟩, ⟨"c", [], none⟩],
  rtIn [(.label "a", 0), (.label "b", 0)] [⟨"b", [], none⟩, ⟨"a", [], none⟩],
  rtIn [(.label "a", 0), (.label "b", 0), (.label "c", 0)] [⟨"a", [], some (0, "c")⟩],
  rtIn [(.label "b", 0), (.label "a", 0), (.label "b", 0)] [⟨"a", [], some (0, "b")⟩],
  rtIn [(.label "a", 0), (.byteArray .empty, 3), (.byteArray .empty, 5), (.label "b", 0)]
    [⟨"a", [(3, [(.byteArray .empty, 5)])], some (8, "b")⟩],
  rtIn [(.label "a", 0), (.byteArray .empty, 3), (.byteArray .empty, 5), (.label "b", 0)] [⟨"a", [(2, [])], none⟩]]

/-! ## Soundness -/

/-- A group's label gap, as `labelGapB`. -/
def GapAt (cells : List (Directive × Nat)) (a : Label) : Option (Nat × Label) → Prop
  | none => True
  | some (off, b) => labelGapB cells a b off = true

/-- A group's blocks, as `blockAtB`. -/
def BsOk (cells : List (Directive × Nat)) (l : Label) : List (Nat × List (Directive × Nat)) → Prop
  | [] => True
  | ob :: bs => blockAtB cells l ob.1 ob.2 = true ∧ BsOk cells l bs

/-- **Every group's facts**: its blocks (`blockAtB`) and its gap (`labelGapB`). -/
def RtAll (cells : List (Directive × Nat)) : List RGrp → Prop
  | [] => True
  | g :: gs => BsOk cells g.l g.bs ∧ GapAt cells g.l g.gap ∧ RtAll cells gs

theorem RtAll.append {cells : List (Directive × Nat)} : ∀ {xs ys : List RGrp},
    RtAll cells (xs ++ ys) → RtAll cells xs ∧ RtAll cells ys
  | [], _, h => ⟨trivial, h⟩
  | _ :: _, _, ⟨h1, h2, h3⟩ => ⟨⟨h1, h2, (RtAll.append h3).1⟩, (RtAll.append h3).2⟩

theorem labelIdx_append_of {l : Label} : ∀ {xs : List (Directive × Nat)} (ys : List (Directive × Nat)),
    (∀ c ∈ xs, c.1 ≠ .label l) → labelIdx (xs ++ ys) l = (labelIdx ys l).map (· + xs.length)
  | [], ys, _ => by simp
  | c :: xs, ys, h => by
    have hd : c.1 ≠ .label l := h c List.mem_cons_self
    have ih := labelIdx_append_of (xs := xs) ys (fun c' h' => h c' (List.mem_cons_of_mem _ h'))
    simp only [List.cons_append, labelIdx, hd, ↓reduceIte, ih, Option.map_map, List.length_cons]
    congr 1

theorem labelIdx_head {c : Directive × Nat} {l : Label} (hc : c.1 = .label l) (ys : List (Directive × Nat)) :
    labelIdx (c :: ys) l = some 0 := by
  simp [labelIdx, hc]

private theorem after_split {prog pre cs : List (Directive × Nat)} {c : Directive × Nat} {m : Label}
    (hp : prog = pre ++ c :: cs) (hc : c.1 = .label m) (hm : ∀ c' ∈ pre, c'.1 ≠ .label m) :
    after m prog = some cs := by
  rw [hp, after_append _ hm, after_cons]
  simp [isLab, hc]

private theorem bsOk_of {prog pre cs : List (Directive × Nat)} {c : Directive × Nat} {m : Label}
    (hp : prog = pre ++ c :: cs) (hc : c.1 = .label m) (hm : ∀ c' ∈ pre, c'.1 ≠ .label m) :
    ∀ bs : List (Nat × List (Directive × Nat)), bs.all (bOk cs) = true → BsOk prog m bs
  | [], _ => trivial
  | ob :: bs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    refine ⟨?_, bsOk_of hp hc hm bs h.2⟩
    unfold blockAtB
    rw [after_split hp hc hm]
    exact h.1

private theorem gapAt_of {prog pre cs : List (Directive × Nat)} {c : Directive × Nat} {m : Label}
    {seen : List Nat} (hp : prog = pre ++ c :: cs) (hc : c.1 = .label m)
    (hpre : ∀ m', ∀ c' ∈ pre, c'.1 = .label m' → key m' ∈ seen) (hm : ∀ c' ∈ pre, c'.1 ≠ .label m) :
    ∀ gap, gapOk seen (key m) cs gap = true → GapAt prog m gap
  | none, _ => trivial
  | some (off, b), h => by
    simp only [gapOk, Bool.and_eq_true] at h
    obtain ⟨hoff, h⟩ := h
    have hcs := cellRun_append_runRest cs
    split at h
    next b' z rest hrr =>
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨hb, hseen⟩ := h
      have hb' : b' = b := key_inj (Nat.eq_of_beq_eq_true hb)
      subst hb'
      have hcs' : cs = cellRun cs ++ (.label b', z) :: rest := by rw [← hrr]; exact hcs.symm
      have hsplit : prog = (pre ++ c :: cellRun cs) ++ (.label b', z) :: rest := by
        rw [hp]; exact (congrArg (fun t => pre ++ c :: t) hcs').trans (by simp)
      have hnb : ∀ c' ∈ pre ++ c :: cellRun cs, c'.1 ≠ .label b' := by
        intro c' hmem he
        rcases List.mem_append.mp hmem with hmem | hmem
        · have : memR (key b') (key m :: seen) = true :=
            memR_iff.mpr (List.mem_cons_of_mem _ (hpre _ c' hmem he))
          simp [this] at hseen
        · rcases List.mem_cons.mp hmem with e | hmem
          · have : memR (key b') (key m :: seen) = true := by
              rw [e, hc, Directive.label.injEq] at he; rw [he]; exact memR_iff.mpr List.mem_cons_self
            simp [this] at hseen
          · have := notLabel_of_mem_cellRun hmem
            rw [he] at this; cases this
      have hi : labelIdx prog m = some pre.length := by
        rw [hp, labelIdx_append_of _ hm, labelIdx_head hc]; simp
      have hd : List.drop (pre.length + 1) prog = cs := by rw [hp]; simp
      have hrun : run prog m = cellRun cs := by
        simp only [run, hi, hd, cellRun_eq]
      have hj : labelIdx prog b' = some (pre.length + 1 + (cellRun cs).length) := by
        rw [hsplit, labelIdx_append_of _ hnb, labelIdx_head rfl]; simp; omega
      have ht : cs.take (cellRun cs).length = cellRun cs := by
        calc cs.take (cellRun cs).length = (cellRun cs ++ runRest cs).take (cellRun cs).length := by rw [hcs]
          _ = cellRun cs := by simp
      show labelGap prog m b' (run prog m).length off = true
      unfold labelGap
      rw [hi, hj, hrun]
      dsimp only
      rw [hd, ht]
      have hall : (cellRun cs).all (fun c => !c.1.isLabel) = true := by
        simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        exact fun _ h => notLabel_of_mem_cellRun h
      rw [← sizeSum_eq, Nat.eq_of_beq_eq_true hoff, hall]
      simp
    next => cases h

theorem rtPass_sound : ∀ (s pre : List (Directive × Nat)) (seen : List Nat) (gs : List RGrp),
    (∀ m, ∀ c ∈ pre, c.1 = .label m → key m ∈ seen) → rtPass s seen gs = true → RtAll (pre ++ s) gs
  | [], _, _, gs, _, h => by
    cases gs with
    | nil => trivial
    | cons _ _ => cases h
  | c :: cs, pre, seen, gs, hpre, h => by
    have ih := rtPass_sound cs (pre ++ [c])
    have happ : pre ++ [c] ++ cs = pre ++ c :: cs := by simp
    rw [← happ]
    change rtStep c cs (rtPass cs) seen gs = true at h
    unfold rtStep at h
    split at h
    next => trivial
    next g gs' =>
      split at h
      next m hc =>
        have hpre' : ∀ m', ∀ c' ∈ pre ++ [c], c'.1 = .label m' → key m' ∈ key m :: seen := by
          intro m' c' hc' he
          rcases List.mem_append.mp hc' with hc' | hc'
          · exact List.mem_cons_of_mem _ (hpre m' c' hc' he)
          · simp only [List.mem_singleton] at hc'; subst hc'
            rw [hc, Directive.label.injEq] at he; simp [he]
        cases hk : Nat.beq (key m) (key g.l)
        · rw [hk, Bool.cond_false] at h
          exact ih _ _ hpre' h
        · rw [hk, Bool.cond_true] at h
          have hm : m = g.l := key_inj (Nat.beq_eq_true_eq _ _ ▸ hk)
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
          obtain ⟨⟨⟨hs, hbs⟩, hgap⟩, hr⟩ := h
          have hnm : ∀ c' ∈ pre, c'.1 ≠ .label m := fun c' hc' he => by
            have := memR_iff.mpr (hpre _ c' hc' he); simp [this] at hs
          rw [happ]
          refine ⟨hm ▸ bsOk_of rfl hc hnm g.bs hbs, hm ▸ gapAt_of rfl hc hpre hnm g.gap hgap, ?_⟩
          have := ih _ _ hpre' hr
          rwa [happ] at this
      next hnl =>
        refine ih _ _ ?_ h
        intro m' c' hc' he
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact hpre m' c' hc' he
        · simp only [List.mem_singleton] at hc'; subst hc'; exact absurd he (hnl m')

/-- **The groups' facts from the one pass.** -/
theorem rtIn_sound {cells : List (Directive × Nat)} {gs : List RGrp} (h : rtIn cells gs = true) :
    RtAll cells gs :=
  rtPass_sound cells [] [] gs (by simp) h

end Scc.Cert.Rt.X64
