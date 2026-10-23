import Scc.Cert.Rt.CodeA64

/-!
# Fixed code at its labels in one pass

The runtime's code checks (`Rt.A64.Abort.abortIn`, `Rt.A64.Print.printIn`,
`mainIn0`/`mainIn`) are conjunctions of `blockAt` and `labelGap` facts at
fixed labels; each fact with a label not met before searches the program
from its start (`labelIdx`), comparing strings, so the checks cost the
kernel a pass over the program per distinct label.

`rtIn prog gs` checks the same facts in one pass, as `blocksIn` does: the
groups `gs` (`RGrp`) in program order, each label of the program encoded
once into a number (`key`) and compared with the next group's. A group is a
label, blocks at offsets after it (as `Grp`), and optionally a label gap:
the label `b` follows after exactly `n` instructions (`labelGap`). The pass
stops after the last group.

`rtIn_sound` gives every group's facts (`RtAll`, unfolding to the
conjunction of the `blockAt`/`labelGap` facts on a concrete table).
-/

namespace Scc.Cert.Rt.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- **A group of fixed code**: blocks at offsets after the first `label l`
(as `Grp`), and optionally the label after exactly `n` instructions
(`labelGap prog l b n`). -/
structure RGrp where
  l : Label
  bs : List (Nat × List Directive)
  gap : Option (Nat × Label) := none

/-- The gap check at a label of key `km` (the keys of the labels before it
`seen`) followed by `ds`: the next `n` directives are instructions, then the
`label b`, `b` not met before. -/
def gapOk (seen : List Nat) (km : Nat) (ds : List Directive) : Option (Nat × Label) → Bool
  | none => true
  | some (n, b) =>
    (ds.take n).all isIns &&
      match ds.drop n with
      | .label b' :: _ => Nat.beq (key b') (key b) && !memR (key b) (km :: seen)
      | _ => false

/-- One step of `rtPass`: at a label, the next group's checks if the keys
agree; done after the last group. -/
def rtStep (d : Directive) (ds : List Directive) (r : List Nat → List RGrp → Bool)
    (seen : List Nat) (gs : List RGrp) : Bool :=
  match gs with
  | [] => true
  | g :: gs' =>
    match d with
    | .label m =>
      cond (Nat.beq (key m) (key g.l))
        (!memR (key m) seen && g.bs.all (fun kb => decide (slice ds kb = kb.2)) &&
          gapOk seen (key m) ds g.gap && r (key m :: seen) gs')
        (r (key m :: seen) (g :: gs'))
    | _ => r seen (g :: gs')

/-- `rtPass` for the code generator. -/
def rtPassImpl : List Directive → List Nat → List RGrp → Bool
  | [], _, gs => gs.isEmpty
  | d :: ds, seen, gs => rtStep d ds (rtPassImpl ds) seen gs

/-- **One pass over the program** checking the groups in program order,
each at the first label of its name (none before it among `seen`). -/
@[implemented_by rtPassImpl]
def rtPass (prog : List Directive) : List Nat → List RGrp → Bool :=
  List.rec (motive := fun _ => List Nat → List RGrp → Bool)
    (fun _ gs => gs.isEmpty) (fun d ds r => rtStep d ds r) prog

/-- **The groups' code in `prog`**, checked in one pass. -/
def rtIn (prog : List Directive) (gs : List RGrp) : Bool := rtPass prog [] gs

/-- info: [true, false, false, false] -/
#guard_msgs in
#eval [rtIn [.label "a", .label "b", .label "c"] [⟨"a", [], some (0, "b")⟩, ⟨"c", [], none⟩],
  rtIn [.label "a", .label "b"] [⟨"b", [], none⟩, ⟨"a", [], none⟩],
  rtIn [.label "a", .label "b", .label "c"] [⟨"a", [], some (1, "c")⟩],
  rtIn [.label "b", .label "a", .label "b"] [⟨"a", [], some (0, "b")⟩]]

/-! ## Soundness -/

/-- A group's label gap, as `labelGap`. -/
def GapAt (prog : List Directive) (a : Label) : Option (Nat × Label) → Prop
  | none => True
  | some (n, b) => labelGap prog a b n = true

/-- A group's blocks, as `blockAt`. -/
def BsOk (prog : List Directive) (l : Label) : List (Nat × List Directive) → Prop
  | [] => True
  | kb :: bs => blockAt prog l kb.1 kb.2 = true ∧ BsOk prog l bs

/-- **Every group's facts**: its blocks (`blockAt`) and its gap (`labelGap`). -/
def RtAll (prog : List Directive) : List RGrp → Prop
  | [] => True
  | g :: gs => BsOk prog g.l g.bs ∧ GapAt prog g.l g.gap ∧ RtAll prog gs

theorem RtAll.append {prog : List Directive} : ∀ {xs ys : List RGrp},
    RtAll prog (xs ++ ys) → RtAll prog xs ∧ RtAll prog ys
  | [], _, h => ⟨trivial, h⟩
  | _ :: _, _, ⟨h1, h2, h3⟩ => ⟨⟨h1, h2, (RtAll.append h3).1⟩, (RtAll.append h3).2⟩

theorem labelIdx_append {l : Label} : ∀ {xs : List Directive} (ys : List Directive),
    Directive.label l ∉ xs → labelIdx (xs ++ ys) l = (labelIdx ys l).map (· + xs.length)
  | [], ys, _ => by simp
  | d :: xs, ys, h => by
    have hd : d ≠ .label l := fun e => h (e ▸ List.mem_cons_self)
    have ih := labelIdx_append (xs := xs) ys (fun h' => h (List.mem_cons_of_mem _ h'))
    simp only [List.cons_append, labelIdx, hd, ↓reduceIte, ih, Option.map_map, List.length_cons]
    congr 1

theorem labelIdx_head (l : Label) (ys : List Directive) : labelIdx (.label l :: ys) l = some 0 := by
  simp [labelIdx]

private theorem bsOk_of {prog pre ds : List Directive} {m : Label} (hp : prog = pre ++ .label m :: ds)
    (hm : Directive.label m ∉ pre) :
    ∀ bs : List (Nat × List Directive), bs.all (fun kb => decide (slice ds kb = kb.2)) = true → BsOk prog m bs
  | [], _ => trivial
  | kb :: bs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨?_, bsOk_of hp hm bs h.2⟩
    rw [← blockAt'_eq]
    unfold blockAt'
    rw [hp, after_append _ hm]
    simp only [after_cons, isLab, beq_self_eq_true, ↓reduceIte]
    exact decide_eq_true h.1

private theorem gapAt_of {prog pre ds : List Directive} {m : Label} {seen : List Nat}
    (hp : prog = pre ++ .label m :: ds) (hpre : ∀ m', Directive.label m' ∈ pre → key m' ∈ seen)
    (hm : Directive.label m ∉ pre) :
    ∀ gap, gapOk seen (key m) ds gap = true → GapAt prog m gap
  | none, _ => trivial
  | some (n, b), h => by
    simp only [gapOk, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hins, h⟩ := h
    split at h
    next b' rest hdrop =>
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨hb, hseen⟩ := h
      have hb' : b' = b := key_inj (Nat.eq_of_beq_eq_true hb)
      subst hb'
      have hlen : (ds.take n).length = n := by
        have : n < ds.length := by
          rcases Nat.lt_or_ge n ds.length with h | h
          · exact h
          · rw [List.drop_eq_nil_of_le h] at hdrop; cases hdrop
        simp; omega
      have hsplit : prog = (pre ++ .label m :: ds.take n) ++ .label b' :: rest := by
        rw [hp, ← hdrop]; simp
      have hnb : Directive.label b' ∉ pre ++ .label m :: ds.take n := by
        intro hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · have := hpre _ hmem
          have : memR (key b') (key m :: seen) = true := memR_iff.mpr (List.mem_cons_of_mem _ this)
          simp [this] at hseen
        · rcases List.mem_cons.mp hmem with e | hmem
          · have : memR (key b') (key m :: seen) = true := by
              simp only [Directive.label.injEq] at e; rw [e]; exact memR_iff.mpr List.mem_cons_self
            simp [this] at hseen
          · have := hins _ hmem
            simp [isIns] at this
      show labelGap prog m b' n = true
      unfold labelGap
      have hi : labelIdx prog m = some pre.length := by
        rw [hp, labelIdx_append _ hm, labelIdx_head]; simp
      have hj : labelIdx prog b' = some (pre.length + 1 + n) := by
        rw [hsplit, labelIdx_append _ hnb, labelIdx_head]; simp [hlen]; omega
      rw [hi, hj]
      simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true]
      intro d hd
      have : List.drop (pre.length + 1) prog = ds := by
        rw [hp]; simp
      rw [this] at hd
      exact hins d hd
    next => cases h

theorem rtPass_sound : ∀ (s pre : List Directive) (seen : List Nat) (gs : List RGrp),
    (∀ m, Directive.label m ∈ pre → key m ∈ seen) → rtPass s seen gs = true → RtAll (pre ++ s) gs
  | [], _, _, gs, _, h => by
    cases gs with
    | nil => trivial
    | cons _ _ => cases h
  | d :: ds, pre, seen, gs, hpre, h => by
    have ih := rtPass_sound ds (pre ++ [d])
    have happ : pre ++ [d] ++ ds = pre ++ d :: ds := by simp
    rw [← happ]
    change rtStep d ds (rtPass ds) seen gs = true at h
    unfold rtStep at h
    split at h
    next => trivial
    next g gs' =>
      split at h
      next m =>
        have hpre' : ∀ m', Directive.label m' ∈ pre ++ [.label m] → key m' ∈ key m :: seen := by
          intro m' hm'
          rcases List.mem_append.mp hm' with hm' | hm'
          · exact List.mem_cons_of_mem _ (hpre m' hm')
          · simp only [List.mem_singleton, Directive.label.injEq] at hm'; simp [hm']
        cases hk : Nat.beq (key m) (key g.l)
        · rw [hk, Bool.cond_false] at h
          exact ih _ _ hpre' h
        · rw [hk, Bool.cond_true] at h
          have hm : m = g.l := key_inj (Nat.beq_eq_true_eq _ _ ▸ hk)
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
          obtain ⟨⟨⟨hs, hbs⟩, hgap⟩, hr⟩ := h
          have hnm : Directive.label m ∉ pre := fun hl => by
            have := memR_iff.mpr (hpre _ hl); simp [this] at hs
          have hp : pre ++ [Directive.label m] ++ ds = pre ++ .label m :: ds := by simp
          rw [hp]
          refine ⟨hm ▸ bsOk_of rfl hnm g.bs hbs, hm ▸ gapAt_of rfl hpre hnm g.gap hgap, ?_⟩
          have := ih _ _ hpre' hr
          rwa [hp] at this
      next hnl =>
        refine ih _ _ ?_ h
        intro m' hm'
        rcases List.mem_append.mp hm' with hm' | hm'
        · exact hpre m' hm'
        · simp only [List.mem_singleton] at hm'; exact absurd hm'.symm (hnl m')

/-- **The groups' facts from the one pass.** -/
theorem rtIn_sound {prog : List Directive} {gs : List RGrp} (h : rtIn prog gs = true) : RtAll prog gs :=
  rtPass_sound prog [] [] gs (by simp) h

end Scc.Cert.Rt.A64
