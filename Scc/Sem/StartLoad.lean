/-
**The ISA-free half of `Components` at load** (`Scc/Sem/StartA64.lean`,
`Scc/Sem/StartX64.lean`). The two canonical targets load alike: slot 0 runs
the program, the others are dormant (`Kernel.KState.init`), no stack range
is held, and the initial shared memory is the layout's image as 8-byte
words, then `.rodata`. What does not depend on the ISA is here, so that
each ISA file (which cannot import the other) states only its loader's
equations.

- `not_live_start`: nothing is live at the source start;
- `Witness.start`: the witness at load;
- `Kernel.KState.init_runs`: at load only slot 0 runs;
- `wordsList`, `find?_wordsList`, `initVal_wordsList`, `wordAt_wordsList`:
  the initial word at an image address, for initial values that are the
  image as 8-byte words (each ISA's `imageMem` is `wordsList Λ.image` by
  definition).
-/
import Scc.Sem.Start1
import Scc.Sem.SrcStart
import Scc.Sem.Kernel

namespace Scc.Sem

open Kraken Kraken.Promising

/-- **Nothing is live at the source start**: its thread's only variable is
the unit argument, which has no word, and its memory is empty. -/
theorem not_live_start {cap : Nat} {l : WeakMem.AllocLabel} : ¬ Live (SrcStart.start cap) l := by
  intro hl
  induction hl with
  | root hr =>
    obtain ⟨i, th, d, e, xs, x, ty, ws, wd, a, g, hth, he, -, -, hws, hwd, -⟩ := hr
    obtain ⟨-, rfl⟩ := SrcStart.start_ths hth
    match d, he with
    | 0, he =>
      simp only [frameEnvs, List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      simp only [TermRun.lookupE, List.find?_cons, List.find?_nil] at hws
      split at hws <;> simp_all
  | cell _ hm _ _ => simp [SrcStart.start, SrcSem.mainStart] at hm

/-- **The witness at load**: source thread 0 is target slot 0; static labels
where `Λ` puts them, of sizes `lsize`; no message, no word, no mark, no
epoch. -/
def Witness.start (M : ExtMachine) (Λ : Layout) (lsize : WeakMem.AllocLabel → Nat) : Witness M where
  thr i := if i = 0 then some 0 else none
  lbl := Λ.static
  lsize := lsize
  ts _ := none
  env _ _ _ _ := none
  marked _ _ := False
  since _ := 0
  tsFrom _ := 0

/-- At load only slot 0 runs. -/
theorem Kernel.KState.init_runs {n : Nat} {E : Entry} {Λ : Layout} {j : Nat}
    (h : (Kernel.KState.init n E Λ).runs j = true) : j = 0 := by
  unfold Kernel.KState.runs Kernel.KState.init at h
  rcases j with _ | j
  · rfl
  · exfalso
    simp only [Array.getElem?_append, List.size_toArray, List.length_singleton] at h
    simp only [show ¬ (j + 1 < 1) by omega, ↓reduceIte, Array.getElem?_replicate] at h
    split at h <;> simp_all

/-! ## The initial words -/

/-- 8-byte words `(address, value)` as initial shared memory (each ISA's
`wordsMem`). -/
def wordsList (ws : List (Nat × Nat)) : List (Loc × Val) :=
  ws.map fun p => (⟨BitVec.ofNat 64 p.1, 8⟩, BitVec.ofNat 128 p.2)

/-- Looking up a word address among `wordsList ws` is looking it up in `ws`,
when every address fits in 64 bits. -/
theorem find?_wordsList {ws : List (Nat × Nat)} (hlt : ∀ p ∈ ws, p.1 < 2 ^ 64) {a : Nat} (ha : a < 2 ^ 64) :
    (wordsList ws).find? (·.1 == wordLoc a) =
      (ws.find? (·.1 == a)).map fun p => ((⟨BitVec.ofNat 64 p.1, 8⟩ : Loc), BitVec.ofNat 128 p.2) := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    have hp := hlt p (List.mem_cons_self ..)
    have ih := ih fun q hq => hlt q (List.mem_cons_of_mem _ hq)
    simp only [wordsList, List.map_cons, List.find?_cons] at ih ⊢
    have hiff : ((⟨BitVec.ofNat 64 p.1, 8⟩ : Loc) == wordLoc a) = (p.1 == a) := by
      by_cases h : p.1 = a
      · rw [h]; simp [wordLoc]
      · have hne : (⟨BitVec.ofNat 64 p.1, 8⟩ : Loc) ≠ wordLoc a := by
          intro he
          apply h
          have := congrArg (fun l : Loc => l.addr.toNat) he
          simp only [wordLoc, BitVec.toNat_ofNat] at this
          rwa [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt ha] at this
        rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h]
    rw [hiff]
    split <;> simp_all [wordsList]

/-- **The initial value of an image word**: in a target memory whose
initial values are the layout's image (then anything), the word at an
image address reads its image word. -/
theorem initVal_wordsList {Λ : Layout} (hwf : Λ.WF) {rest : List (Loc × Val)} {tm : Memory}
    (hinit : tm.init = wordsList Λ.image ++ rest) {a v : Nat} (hav : (a, v) ∈ Λ.image) :
    (tm.initVal (wordLoc a)).toNat = Scc.Cert.Link.wordOf Λ.image a := by
  have hlt : ∀ p ∈ Λ.image, p.1 < 2 ^ 64 := by
    intro p hp
    have hd := (hwf.image p hp).1
    have hs := hwf.inSpace Λ.data (by simp [Layout.regions])
    simp only [Range.contains] at hd
    simp only [Range.InSpace] at hs
    omega
  have ha : a < 2 ^ 64 := hlt _ hav
  have hsome : (Λ.image.find? (·.1 == a)).isSome := by
    rw [List.find?_isSome]; exact ⟨_, hav, by simp⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
  have hq2 : q.2 < 2 ^ 64 := (hwf.image q (List.mem_of_find?_eq_some hq)).2.2
  unfold Memory.initVal Scc.Cert.Link.wordOf
  rw [hinit, List.find?_append, find?_wordsList hlt ha, hq]
  simp only [Option.map_some, Option.some_or, Option.getD_some, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans hq2 (by decide))

/-- **The target's initial word at an image address** is its image word
(`wordAt` at timestamp 0). With `image_word`, for an 8-aligned item it is
the item's little-endian word. -/
theorem wordAt_wordsList {Λ : Layout} (hwf : Λ.WF) {rest : List (Loc × Val)} {tm : Memory}
    (hinit : tm.init = wordsList Λ.image ++ rest) {a v : Nat} (hav : (a, v) ∈ Λ.image) :
    wordAt tm a 0 = some (Scc.Cert.Link.wordOf Λ.image a) := by
  simp only [wordAt, Memory.read?, ↓reduceIte]
  rw [initVal_wordsList hwf hinit hav]

end Scc.Sem
