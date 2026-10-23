/-
Stage B, S3, typed consequences of the fulfil characterisation (TermCert's
`TermFul` section), which need TermStep's layout lemmas (`AtOff`).

(a) `certified_noPairProm`: no outstanding promise of a certified thread lies
in a `word2` unit of a cell whose (fixed) type is `T`, provided every
single-word write the certifying run can issue at that label lands on a `.one`
unit of a component of `T` (`hT`, the typing-dependent hypothesis).
(b) `certified_promWord`: the word-unit value fact (`hwu` of `promise_acct`),
from the hypothesis that every single-word write at a `.word n P` position of
`T` writes a value satisfying `Good n P` (`hB`).
(S4g) `certified_promQC`, `certified_noPairPromC`, `certified_promWordC`: the
same with `Certified c1 i` available to `hQ`/`hT`/`hB` (as stated before, `hB`
is not provable: a Solo prefix that is not certified may lose typing).  The
typed run that discharges them is in `TermTyped`.
-/
import WeakCore.TermStep
import WeakCore.TermCert

namespace TermGlob
open CoreLang CoreTerm TermRun TermCert TermSound TermFul
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- A single-word unit is never inside a pair unit of the same unit list. -/
theorem oneAt_split : ∀ (pre post : List Acc) {j : Nat}, OneAt (pre ++ .two :: post) j →
    j < nWords pre ∨ nWords pre + 2 ≤ j
  | [], post, j, h => by
      cases h with
      | cons _ h' => right; simp [nWords, Acc.size]
  | u :: pre, post, j, h => by
      cases h with
      | here _ => left; simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega
      | cons _ h' =>
          have ih := oneAt_split pre post h'
          simp only [nWords, List.map_cons, List.sum_cons] at ih ⊢
          omega

/-- **Layout**: a `.one` unit of a component `U` of `T` (at `o`) never covers
either word of a `word2` component of `T`. -/
theorem oneAt_word2 {T U : Ty} {o o2 j : Nat} {us : List Acc} {r : Idx} {P : Proto2}
    (h1 : AtOff T o U) (hus : accs U = some us) (hj : OneAt us j) (h2 : AtOff T o2 (.word2 r P)) :
    o + j ≠ o2 ∧ o + j ≠ o2 + 1 := by
  have hjl := OneAt_lt hj
  have n2 : nWords [Acc.two] = 2 := rfl
  rcases TermStep.AtOff_nest (TermStep.Solid_word2 r P) TermStep.accs_word2 h1 hus h2 with
    h | h | ⟨hle, h⟩
  · rw [n2] at h; omega
  · omega
  · obtain ⟨pre, post, e, hn⟩ := TermStep.AtOff_embed h hus TermStep.accs_word2
    rw [e, List.append_assoc, List.singleton_append] at hj
    have := oneAt_split pre post hj
    omega

/-- **Task 3(a).**  In a certified configuration, no outstanding promise of
thread `i` at label `l` lies in a `word2` unit of `T`, if every single-word write
the certifying run can issue at `l` is a `.one` unit of a component of `T`. -/
theorem certified_noPairProm {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {l : AllocLabel} {T : Ty} (hc : Certified p k arch c i) (hw : PWF c i)
    (hT : ∀ c1 th1 loc val, Solo p k arch i c c1 → c1.ths[i]? = some th1 →
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 loc val → loc.label = l →
      ∃ o U us j, AtOff T o U ∧ accs U = some us ∧ OneAt us j ∧ loc.offset = o + j)
    {t : Ts} {m : Msg} {o2 : Nat} {r : Idx} {P : Proto2} (ht : t ∈ promsOf c i)
    (hm : c.mem[t]? = some m) (hl : m.loc.label = l) (h2 : AtOff T o2 (.word2 r P)) :
    m.loc.offset ≠ o2 ∧ m.loc.offset ≠ o2 + 1 := by
  refine certified_promQ (fun loc _ => loc.label = l → loc.offset ≠ o2 ∧ loc.offset ≠ o2 + 1) hc hw
    (fun c1 th1 loc val hs hth hsw hl' => ?_) ht hm hl
  obtain ⟨o, U, us, j, h1, hus, hj, ho⟩ := hT c1 th1 loc val hs hth hsw hl'
  rw [ho]; exact oneAt_word2 h1 hus hj h2

/-- **Task 3(b).**  The word-unit value fact: an outstanding promise of a
certified thread at a `.word n P` position of `T` (label `l`) carries a value
satisfying `Good n P`, if every single-word write the certifying run can issue
at such a position does. -/
theorem certified_promWord {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {l : AllocLabel} {T : Ty} (Good : Idx → Proto → Val → Prop)
    (hc : Certified p k arch c i) (hw : PWF c i)
    (hB : ∀ c1 th1 loc val, Solo p k arch i c c1 → c1.ths[i]? = some th1 →
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 loc val → loc.label = l →
      ∀ n P, AtOff T loc.offset (.word n P) → Good n P val)
    {t : Ts} {m : Msg} {n : Idx} {P : Proto} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    (hl : m.loc.label = l) (hP : AtOff T m.loc.offset (.word n P)) : Good n P m.val :=
  certified_promQ (fun loc val => loc.label = l → ∀ n P, AtOff T loc.offset (.word n P) → Good n P val)
    hc hw (fun c1 th1 loc val hs hth hsw => hB c1 th1 loc val hs hth hsw) ht hm hl n P hP

/-! ### S3 fix (S4g): the typing hypotheses may use `Certified c1 i` -/

theorem solo_trans {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c1 c2 : Cfg}
    (h1 : Solo p k arch i c c1) (h2 : Solo p k arch i c1 c2) : Solo p k arch i c c2 := by
  induction h1 with
  | refl => exact h2
  | thread hs _ ih => exact .thread hs (ih h2)
  | prom a v w hw _ ih => exact .prom a v w hw (ih h2)
  | ext hs _ ih => exact .ext hs (ih h2)

/-- Every configuration on a run into a certified configuration is certified. -/
theorem certified_back {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c1 : Cfg}
    (h : Solo p k arch i c c1) (hc : Certified p k arch c1 i) : Certified p k arch c i :=
  let ⟨c', hs, hn⟩ := hc
  ⟨c', solo_trans h hs, hn⟩

/-- `certified_fulfil` with the certification of the fulfilling step's target. -/
theorem certified_fulfilC {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {t : Ts}
    (hc : Certified p k arch c i) (hw : PWF c i) (ht : t ∈ promsOf c i) :
    ∃ m, c.mem[t]? = some m ∧ ∃ c1 c2 th1, Solo p k arch i c c1 ∧ c2 ∈ threadSteps p k arch c1 i ∧
      Certified p k arch c2 i ∧ c1.ths[i]? = some th1 ∧ c1.mem[t]? = some m ∧ t ∈ th1.promises ∧
      t ∉ promsOf c2 i ∧ SW (gOf p k arch c1 i) c1.mem c1.pairs th1 m.loc m.val := by
  obtain ⟨c', hs, hn⟩ := hc
  have hn' : t ∉ promsOf c' i := by rw [noPromises_nil hn]; exact List.not_mem_nil
  obtain ⟨m, hm, c1, c2, th1, h1, h2, h3, hth1, hm1, ht1, hn2, hsw, -⟩ := solo_fulfil hs hw t ht hn'
  exact ⟨m, hm, c1, c2, th1, h1, h2, ⟨c', h3, hn⟩, hth1, hm1, ht1, hn2, hsw⟩

/-- **`certified_promQ`, amended**: `hQ` may use `Certified c1 i`. -/
theorem certified_promQC {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    (Q : Address → Val → Prop) (hc : Certified p k arch c i) (hw : PWF c i)
    (hQ : ∀ c1 th1 loc val, Solo p k arch i c c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 →
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 loc val → Q loc val)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) : Q m.loc m.val := by
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, -, -, -, hsw⟩ := certified_fulfilC hc hw ht
  rw [hm] at hm'
  cases hm'
  exact hQ c1 th1 _ _ h1 (certified_back (.thread h2 (.refl _)) hc2) hth1 hsw

/-- **Task 3(a), amended**: `hT` may use `Certified c1 i`. -/
theorem certified_noPairPromC {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {l : AllocLabel} {T : Ty} (hc : Certified p k arch c i) (hw : PWF c i)
    (hT : ∀ c1 th1 loc val, Solo p k arch i c c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 →
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 loc val → loc.label = l →
      ∃ o U us j, AtOff T o U ∧ accs U = some us ∧ OneAt us j ∧ loc.offset = o + j)
    {t : Ts} {m : Msg} {o2 : Nat} {r : Idx} {P : Proto2} (ht : t ∈ promsOf c i)
    (hm : c.mem[t]? = some m) (hl : m.loc.label = l) (h2 : AtOff T o2 (.word2 r P)) :
    m.loc.offset ≠ o2 ∧ m.loc.offset ≠ o2 + 1 := by
  refine certified_promQC (fun loc _ => loc.label = l → loc.offset ≠ o2 ∧ loc.offset ≠ o2 + 1) hc hw
    (fun c1 th1 loc val hs hc1 hth hsw hl' => ?_) ht hm hl
  obtain ⟨o, U, us, j, h1, hus, hj, ho⟩ := hT c1 th1 loc val hs hc1 hth hsw hl'
  rw [ho]; exact oneAt_word2 h1 hus hj h2

/-- **Task 3(b), amended**: `hB` may use `Certified c1 i`. -/
theorem certified_promWordC {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {l : AllocLabel} {T : Ty} (Good : Idx → Proto → Val → Prop)
    (hc : Certified p k arch c i) (hw : PWF c i)
    (hB : ∀ c1 th1 loc val, Solo p k arch i c c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 →
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 loc val → loc.label = l →
      ∀ n P, AtOff T loc.offset (.word n P) → Good n P val)
    {t : Ts} {m : Msg} {n : Idx} {P : Proto} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    (hl : m.loc.label = l) (hP : AtOff T m.loc.offset (.word n P)) : Good n P m.val :=
  certified_promQC (fun loc val => loc.label = l → ∀ n P, AtOff T loc.offset (.word n P) → Good n P val)
    hc hw (fun c1 th1 loc val hs hc1 hth hsw => hB c1 th1 loc val hs hc1 hth hsw) ht hm hl n P hP

#print axioms oneAt_word2
#print axioms certified_noPairProm
#print axioms certified_promWord
#print axioms certified_promQC
#print axioms certified_noPairPromC
#print axioms certified_promWordC

end TermGlob
