import Scc.Cert.LinkX64
import Scc.Sem.Kernel

/-!
# The runtime's data words in the canonical x86-64 link

The x86-64 twin of `Scc/Cert/Rt/RtWordsA64.lean`. The runtime's thread
start (`scc_rt_main`'s setup, the TCB allocation and the stack take) touches
six data words named by symbols of the link: `scc_rt_pinned` (the first
TCB), `scc_rt_pinned_next`, `scc_rt_stacks` (the first stack),
`scc_rt_stack_next`, `scc_rt_stack_lock` and `scc_rt_stack_free_n`. Its
specs take their addresses and side conditions on them as hypotheses. This
file decides them on the link and the code cells (`rtWordsOk`, the placement
check's component A8) and derives them:

- **The labels** (`label_threadAt_of_sym`, generic): a data symbol `(x, a)`
  the canonical loader places (`symsOk`), the only one named `x` and no
  code label of that name, is at `a` in the loaded thread's executable:
  `placeSyms` lays the symbols out in address order, after the code cells,
  with padding up to each; `label_threadAt_of_sym_around` the same for
  symbols on both sides of the code (`symsAround`). `symLab` decides
  the premises for a name; `label_of_rtWordsOk` gives each word's label at
  any layout passing A2 (`loadOk`).
- **The side conditions** (`*_of_wordsOk`): the words (`rtWords`: the
  counters, the first TCB's header and its six fields) lie below `2 ^ 32`,
  8-aligned, clear of the entry stack and of the stack pool, mapped for
  reading and writing at load time (`Kernel.KState.init`) with their bytes
  in `.data` or the pinned region; the pool fits the address space below the
  entry stack; the first stack is 16-aligned and inside the pool; the words
  are pairwise disjoint (`WordSep`; `words_disj_of_wordsOk`), so the TCB's
  are none of the counters (`tcbSep_of_wordsOk`).

Where x86-64 differs from AArch64: the program is a list of sized cells, a
code label's address the sum of the sizes before it (`codeLabel` in place
of `codeOf`).
-/

namespace Scc.Cert.Rt.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.Link.X64

/-! ## Data symbols at their labels -/

section Labels

/-- The step of `placeSyms`' fold. -/
private def symStep (acc : List (Directive × Nat) × Nat) (xa : String × Nat) : List (Directive × Nat) × Nat :=
  (acc.1 ++ [((Directive.byteArray (.mk #[]) : Directive), xa.2 - acc.2), (.label xa.1, 0)], max xa.2 acc.2)

/-- `placeSyms`' fold over symbols in strictly increasing address order, all
above the current address `c` and below `B`: it appends cells whose sizes
take `c` to its new current address, below `B`, each label cell named by
one of the symbols. -/
private theorem symStep_fold : ∀ (L : List (String × Nat)) (cells : List (Directive × Nat)) (c B : Nat),
    (∀ p ∈ L, c < p.2 ∧ p.2 < B) → L.Pairwise (fun a b => a.2 < b.2) → c < B →
    ∃ new, (L.foldl symStep (cells, c)).1 = cells ++ new ∧
      (∀ y ∈ new, ∀ l, y.1 = Directive.label l → ∃ p ∈ L, p.1 = l) ∧
      (new.map (·.2)).sum + c = (L.foldl symStep (cells, c)).2 ∧ (L.foldl symStep (cells, c)).2 < B
  | [], cells, c, _, _, _, hc => ⟨[], by simp, by simp, by simp, hc⟩
  | (x, a) :: L, cells, c, B, hL, hp, _ => by
    have ha := hL (x, a) (List.mem_cons_self ..)
    have hp' := List.pairwise_cons.mp hp
    obtain ⟨new, h1, h2, h3, h4⟩ := symStep_fold L
      (cells ++ [((Directive.byteArray (.mk #[]) : Directive), a - c), (.label x, 0)]) a B
      (fun p hp => ⟨hp'.1 p hp, (hL p (List.mem_cons_of_mem _ hp)).2⟩) hp'.2 ha.2
    have hmax : max a c = a := Nat.max_eq_left (Nat.le_of_lt ha.1)
    refine ⟨[((Directive.byteArray (.mk #[]) : Directive), a - c), (.label x, 0)] ++ new, ?_, ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, symStep, hmax]; rw [h1, List.append_assoc]
    · intro y hy l hl
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with (rfl | rfl) | hy
      · cases hl
      · cases hl; exact ⟨(x, a), List.mem_cons_self .., rfl⟩
      · obtain ⟨p, hp, he⟩ := h2 y hy l hl
        exact ⟨p, List.mem_cons_of_mem _ hp, he⟩
    · simp only [List.foldl_cons, symStep, hmax] at h3 ⊢
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · simpa only [List.foldl_cons, symStep, hmax] using h4

/-- A name `codeLabel` does not resolve labels no cell. -/
theorem ne_label_of_codeLabel {x : String} {lo : Nat} {cells : List (Directive × Nat)}
    (h : codeLabel lo cells x = none) : ∀ c ∈ cells, c.1 ≠ .label x :=
  Link.X64.ne_label_of_codeLabel h

/-- **A data symbol at its label** in the canonical loader's thread: a
symbol `(x, a)` the loader places (`symsOk`), the only symbol named `x`
(`hone`) and no cell the label `x` (`hcode`), labels `a`. -/
theorem label_threadAt_of_sym {E : Entry} {base : Nat} {cells : List (Directive × Nat)}
    {syms : List (String × Nat)} {x : String} {a : Nat} (hsyms : symsOk base cells syms = true)
    (hmem : (x, a) ∈ syms) (hone : ∀ p ∈ syms, p.1 = x → p.2 = a) (hcode : ∀ c ∈ cells, c.1 ≠ .label x) :
    (_root_.Executable.labels (threadAt E base cells syms).exe).label x = Int64.ofNat a := by
  have hold := threadAt_exe_eq_old (E := E) (codeEnd_lt_of_symsOk hsyms) (nodup_of_symsOk hsyms)
  simp only [symsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsyms
  obtain ⟨hab, hnd⟩ := hsyms
  let le : String × Nat → String × Nat → Bool := fun a b => decide (a.2 ≤ b.2)
  have hperm := List.mergeSort_perm syms le
  have hsorted : (syms.mergeSort le).Pairwise (fun a b => le a b) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) syms
  have hnd' : ((syms.mergeSort le).map (·.2)).Nodup := hnd.perm (hperm.map _).symm
  have hlt : (syms.mergeSort le).Pairwise (fun a b => a.2 < b.2) := by
    have := List.Pairwise.and hsorted (List.pairwise_map.mp hnd')
    refine this.imp fun {a b} h => ?_
    simp only [le, decide_eq_true_eq] at h
    omega
  have hin : ∀ p ∈ syms.mergeSort le, codeEnd base cells < p.2 ∧ p.2 < base + 2 ^ 64 := fun p hp => by
    have := hab p (hperm.mem_iff.mp hp)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem (hperm.mem_iff.mpr hmem)
  have hsyms1 : ∀ p ∈ L1, p ∈ syms := fun p hp => hperm.mem_iff.mp (by rw [hL]; simp [hp])
  rw [hL] at hlt hin
  have hlt' := List.pairwise_append.mp hlt
  have hlt2 := List.pairwise_cons.mp hlt'.2.1
  have h1a : ∀ p ∈ L1, p.2 < a := fun p hp => hlt'.2.2 p hp (x, a) (List.mem_cons_self ..)
  have hxa := hin (x, a) (by simp)
  obtain ⟨n1, e1, l1, s1, b1⟩ := symStep_fold L1 [] (codeEnd base cells) a
    (fun p hp => ⟨(hin p (List.mem_append_left _ hp)).1, h1a p hp⟩) hlt'.1 hxa.1
  generalize hc1 : (L1.foldl symStep ([], codeEnd base cells)).2 = c1 at s1 b1
  have hf1 : L1.foldl symStep ([], codeEnd base cells) = (n1, c1) := by
    rw [← hc1, List.nil_append] at *; exact Prod.ext e1 rfl
  let pad : Directive × Nat := ((Directive.byteArray (.mk #[]) : Directive), a - c1)
  obtain ⟨n2, e2, -, -, -⟩ := symStep_fold L2 (n1 ++ [pad, (.label x, 0)]) a (base + 2 ^ 64)
    (fun p hp => ⟨hlt2.1 p hp, (hin p (by simp [hp])).2⟩) hlt2.2 hxa.2
  have hcells : (threadAt E base cells syms).exe.2 = cells ++ (n1 ++ (pad :: (.label x, 0) :: n2)) := by
    rw [hold]
    show cells ++ Scc.Cert.PlaceSyms.placeSymsOld _ _ _ _ = _
    rw [Scc.Cert.PlaceSyms.placeSymsOld]
    show _ ++ ((syms.mergeSort le).foldl symStep ([], codeEnd base cells)).1 = _
    rw [hL, List.foldl_append, hf1, List.foldl_cons]
    have hmax : max a c1 = a := Nat.max_eq_left (Nat.le_of_lt b1)
    simp only [symStep, hmax]
    rw [e2]; simp
  have hl := Kraken.Executable.label_addrOf (threadAt E base cells syms).exe x (cells.length + (n1.length + 1))
    (by rw [hcells, List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp)
    (by
      rw [hcells, List.take_length_add_append, List.take_length_add_append]
      intro dz hdz
      simp only [List.take_succ_cons, List.take_zero, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hdz
      rcases hdz with hdz | hdz | rfl
      · exact hcode dz hdz
      · intro he
        obtain ⟨p, hp, hpx⟩ := l1 dz hdz x he
        exact absurd (hone p (hsyms1 p hp) hpx) (Nat.ne_of_lt (h1a p hp))
      · intro he; cases he)
  rw [hl]
  unfold Kraken.Executable.addrOf Kraken.Executable.sizeBefore
  rw [hcells, List.take_length_add_append, List.take_length_add_append]
  simp only [List.take_succ_cons, List.take_zero, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [show (threadAt E base _ syms).exe.1 = Int64.ofNat base by rw [hold]]
  rw [← Int64.ofNat_add]
  congr 1
  simp only [codeEnd] at s1 b1
  simp only [pad]
  omega

/-- **A data symbol's address, decided**: the address `syms` lists for
`x`, when `x` names no other address and no code label of `cells`. -/
def symLab (base : Nat) (cells : List (Directive × Nat)) (syms : List (String × Nat)) (x : String) : Option Nat :=
  match syms.lookup x with
  | some a => if (codeLabel base cells x).isNone && syms.all (fun p => p.1 != x || p.2 == a) then some a else none
  | none => none

/-- **A data symbol at its label, around the code**: in the canonical
loader's thread with data symbols on both sides of the code (`symsAround`),
a symbol `(x, a)`, the only address of `x` (`hone`), no cell the label `x`
(`hcode`), labels `a`. -/
theorem label_threadAt_of_sym_around {E : Entry} {base : Nat} {cells : List (Directive × Nat)}
    {syms : List (String × Nat)} {x : String} {a : Nat} (hsyms : symsAround base cells syms = true)
    (hmem : (x, a) ∈ syms) (hone : ∀ p ∈ syms, p.1 = x → p.2 = a) (hcode : ∀ c ∈ cells, c.1 ≠ .label x) :
    (_root_.Executable.labels (threadAt E base cells syms).exe).label x = Int64.ofNat a := by
  have hpad : ∀ y, (Directive.byteArray (.mk #[]) : Directive) ≠ .label y := fun _ h => by cases h
  have hlbl : ∀ y z, (Directive.label y : Directive) = .label z → y = z := fun _ _ h => by cases h; rfl
  have hcells := threadAt_exe_cells E base cells syms
  have hBs := (Scc.Cert.PlaceSyms.placeBelow_spec (Directive.byteArray (.mk #[])) Directive.label base syms)
  rcases out_of_symsAround hsyms (x, a) hmem with hlo | hhi
  · -- below the code: among the cells before it
    have hmB : (x, a) ∈ symsBelow base syms := Scc.Cert.PlaceSyms.mem_symsBelow.mpr ⟨hmem, hlo⟩
    obtain ⟨pre, post, he, hpre, hsum⟩ := Scc.Cert.PlaceSyms.placeBelow_label _ _ hpad hlbl hmB
      (fun p hp hpx => hone p (Scc.Cert.PlaceSyms.mem_symsBelow.mp hp).1 hpx)
    rw [he] at hcells
    have hl := Kraken.Executable.label_addrOf (threadAt E base cells syms).exe x pre.length
      (by rw [hcells, List.append_assoc, List.getElem?_append_right (by omega)]; simp)
      (by rw [hcells, List.append_assoc, List.take_left]; exact hpre)
    rw [hl]
    unfold Kraken.Executable.addrOf Kraken.Executable.sizeBefore
    rw [hcells, List.append_assoc, List.take_left]
    show Int64.ofNat (exeStart base syms) + _ = _
    rw [← Int64.ofNat_add]
    congr 1
    omega
  · -- above the code: among the cells after it
    have hmF : (x, a) ∈ symsFrom base syms := Scc.Cert.PlaceSyms.mem_symsFrom.mpr ⟨hmem, by
      simp only [codeEnd] at hhi; omega⟩
    obtain ⟨pre, post, he, hpre, hsum⟩ := Scc.Cert.PlaceSyms.placeSyms_label _ _ hpad hlbl hmF hhi
      (fun p hp hpx => hone p (Scc.Cert.PlaceSyms.mem_symsFrom.mp hp).1 hpx)
    rw [he] at hcells
    generalize hB : placeBelow (Directive.byteArray (.mk #[])) Directive.label base syms = B at hcells hBs
    have hidx : B.length + (cells.length + pre.length) = (B ++ cells ++ pre).length := by
      simp
    replace hcells : (threadAt E base cells syms).exe.2 = (B ++ cells ++ pre) ++ (Directive.label x, 0) :: post := by
      rw [hcells]; simp
    have hl := Kraken.Executable.label_addrOf (threadAt E base cells syms).exe x (B.length + (cells.length + pre.length))
      (by rw [hcells, hidx, List.getElem?_append_right (Nat.le_refl _)]; simp)
      (by
        rw [hcells, hidx, List.take_left]
        intro dz hdz
        simp only [List.mem_append] at hdz
        rcases hdz with (hdz | hdz) | hdz
        · rcases hBs.1 dz hdz with ⟨h, -⟩ | ⟨p, hp, rfl⟩
          · rw [h]; exact hpad x
          · intro hpx
            have := hone p (Scc.Cert.PlaceSyms.mem_symsBelow.mp hp).1 (hlbl _ _ hpx)
            have := (Scc.Cert.PlaceSyms.mem_symsBelow.mp hp).2
            simp only [codeEnd] at hhi
            omega
        · exact hcode dz hdz
        · exact hpre dz hdz)
    rw [hl]
    unfold Kraken.Executable.addrOf Kraken.Executable.sizeBefore
    rw [hcells, hidx, List.take_left]
    simp only [List.map_append, List.sum_append]
    show Int64.ofNat (exeStart base syms) + _ = _
    rw [← Int64.ofNat_add]
    congr 1
    simp only [codeEnd] at hsum
    omega

/-- **A decided data symbol at its label** in the canonical loader's thread,
the data symbols around the code (`symsAround`). -/
theorem label_threadAt_of_symLab {E : Entry} {base : Nat} {cells : List (Directive × Nat)}
    {syms : List (String × Nat)} {x : String} {a : Nat} (hsyms : symsAround base cells syms = true)
    (h : symLab base cells syms x = some a) :
    (_root_.Executable.labels (threadAt E base cells syms).exe).label x = Int64.ofNat a := by
  unfold symLab at h
  split at h
  · next a' hl =>
    split at h
    · next hc =>
      cases h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true, Bool.or_eq_true,
        bne_iff_ne, ne_eq, beq_iff_eq] at hc
      obtain ⟨l1, l2, he, -⟩ := List.lookup_eq_some_iff.mp hl
      refine label_threadAt_of_sym_around hsyms (by rw [he]; simp) (fun p hp hpx => ?_)
        (ne_label_of_codeLabel hc.1)
      rcases hc.2 p hp with h | h
      · exact absurd hpx h
      · exact h
    · cases h
  · cases h

end Labels

/-! ## The runtime's words -/

/-- The names of the runtime's data words: the first TCB, the pinned
counter, the first stack, the stack counter, lock and free count. -/
def rtNames : List String :=
  ["scc_rt_pinned", "scc_rt_pinned_next", "scc_rt_stacks", "scc_rt_stack_next", "scc_rt_stack_lock",
    "scc_rt_stack_free_n"]

/-- The runtime word named `x`'s address in the canonical link (0 if
`symLab` does not decide it). -/
def rtA (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (secs : DataSecs) (x : String) : BitVec 64 :=
  BitVec.ofNat 64 ((symLab Λ.code.lo cells (loadSyms Λ secs.rodata) x).getD 0)

/-- **The words the start of a thread touches**: the counters
`scc_rt_pinned_next`, `scc_rt_stack_next`, `scc_rt_stack_lock`,
`scc_rt_stack_free_n`; the first TCB's header at `scc_rt_pinned`; its six
fields from `scc_rt_pinned + 8`. -/
def rtWords (pinA pnA nextA lockA freeNA : BitVec 64) : List (BitVec 64) :=
  [pnA, nextA, lockA, freeNA, pinA] ++ (List.range 6).map fun i => pinA + BitVec.ofNat 64 (8 * (i + 1))

/-- The word `a` is clear of the range `r` (its 8 bytes outside). -/
def clearB (r : Scc.Sem.Range) (a : BitVec 64) : Bool :=
  decide (a.toNat + 8 ≤ r.lo) || decide (r.lo + r.size ≤ a.toNat)

/-- The side conditions of one word: below `2 ^ 32`, 8-aligned, clear of
the stack pool, each byte in `.data` or the pinned region (so mapped at
load time for writing and reading whatever the entry state,
`words_mappedE_of_wordsOk`). -/
def wordOk (Λ : Scc.Sem.Layout) (a : BitVec 64) : Bool :=
  decide (a.toNat < 2 ^ 32) && decide (a.toNat % 8 = 0) && clearB Λ.stackPool a &&
    (List.range 8).all fun i => decide (Λ.data.contains (a.toNat + i)) || decide (Λ.pinned.contains (a.toNat + i))

/-- Two words' 8 bytes are disjoint. -/
def WordSep (a b : BitVec 64) : Prop := a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat

instance (a b : BitVec 64) : Decidable (WordSep a b) := inferInstanceAs (Decidable (_ ∨ _))

/-- The side conditions of the words, the stack pool and the first stack;
the words pairwise disjoint. -/
def wordsOk (Λ : Scc.Sem.Layout) (pinA pnA stacksA nextA lockA freeNA : BitVec 64) : Bool :=
  (rtWords pinA pnA nextA lockA freeNA).all (wordOk Λ) &&
    decide (Λ.stackPool.lo + Λ.stackPool.size < 2 ^ 64) &&
    decide (stacksA.toNat % 16 = 0) &&
    decide (Λ.stackPool.lo ≤ stacksA.toNat ∧ stacksA.toNat + 16384 ≤ Λ.stackPool.lo + Λ.stackPool.size) &&
    decide ((rtWords pinA pnA nextA lockA freeNA).Pairwise WordSep)

/-- **The runtime's words** (A8): each name of `rtNames` a data symbol of
the link at a decided address (`symLab`), the words at those addresses
passing `wordsOk`. -/
def rtWordsOk (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (secs : DataSecs) : Bool :=
  rtNames.all (fun x => (symLab Λ.code.lo cells (loadSyms Λ secs.rodata) x).isSome) &&
    wordsOk Λ (rtA Λ cells secs "scc_rt_pinned") (rtA Λ cells secs "scc_rt_pinned_next")
      (rtA Λ cells secs "scc_rt_stacks") (rtA Λ cells secs "scc_rt_stack_next")
      (rtA Λ cells secs "scc_rt_stack_lock") (rtA Λ cells secs "scc_rt_stack_free_n")

section Extract

variable {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)} {secs : DataSecs} {offs : List (String × Nat)}

/-- **A runtime word at its label** in the canonical loader's thread. -/
theorem label_of_rtWordsOk (hl : loadOk Λ cells secs offs = true) (h : rtWordsOk Λ cells secs = true)
    {x : String} (hx : x ∈ rtNames) (E : Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)).exe).label x).toBitVec =
      rtA Λ cells secs x := by
  simp only [rtWordsOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h.1 x hx)
  rw [label_threadAt_of_symLab (symsAround_of_loadOk hl) ha, rtA, ha]
  simp

/-- The words' side conditions, the pool's and the first stack's. -/
theorem wordsOk_of_rtWordsOk (h : rtWordsOk Λ cells secs = true) :
    wordsOk Λ (rtA Λ cells secs "scc_rt_pinned") (rtA Λ cells secs "scc_rt_pinned_next")
      (rtA Λ cells secs "scc_rt_stacks") (rtA Λ cells secs "scc_rt_stack_next")
      (rtA Λ cells secs "scc_rt_stack_lock") (rtA Λ cells secs "scc_rt_stack_free_n") = true := by
  simp only [rtWordsOk, Bool.and_eq_true] at h; exact h.2

end Extract

section Words

variable {Λ : Scc.Sem.Layout} {pinA pnA stacksA nextA lockA freeNA : BitVec 64}

theorem clear_of_clearB {r : Scc.Sem.Range} {a : BitVec 64} (h : clearB r a = true) :
    a.toNat + 8 ≤ r.lo ∨ r.lo + r.size ≤ a.toNat := by
  simpa only [clearB, Bool.or_eq_true, decide_eq_true_eq] using h

private theorem wordOk_of (h : wordsOk Λ pinA pnA stacksA nextA lockA freeNA = true) {a : BitVec 64}
    (ha : a ∈ rtWords pinA pnA nextA lockA freeNA) : wordOk Λ a = true := by
  simp only [wordsOk, Bool.and_eq_true, List.all_eq_true] at h; exact h.1.1.1.1 a ha

private theorem wordOk_parts {a : BitVec 64} (h : wordOk Λ a = true) :
    a.toNat < 2 ^ 32 ∧ a.toNat % 8 = 0 ∧ clearB Λ.stackPool a = true ∧
      ∀ i < 8, Λ.data.contains (a.toNat + i) ∨ Λ.pinned.contains (a.toNat + i) := by
  simp only [wordOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true]
    at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A word whose bytes lie in `.data` or the pinned region is mapped at
load time for writing and reading, whatever the entry state and the number
of thread slots. -/
theorem mapped_init_of_bytes {E : Entry} {n : Nat} {w : Bool} {a : BitVec 64}
    (h : ∀ i < 8, Λ.data.contains (a.toNat + i) ∨ Λ.pinned.contains (a.toNat + i)) :
    Kernel.mapped (Kernel.KState.init n E Λ) w ⟨a, 8⟩ = true := by
  simp only [Kernel.mapped, Kernel.mappedRegions, Kernel.KState.init, List.all_eq_true, List.mem_range,
    List.any_eq_true, decide_eq_true_eq]
  intro i hi
  rcases h i hi with hd | hp
  · exact ⟨Λ.data, by simp, hd⟩
  · exact ⟨Λ.pinned, by simp, hp⟩

variable (h : wordsOk Λ pinA pnA stacksA nextA lockA freeNA = true)
include h

/-- The words lie below `2 ^ 32`. -/
theorem words_small_of_wordsOk : ∀ a ∈ rtWords pinA pnA nextA lockA freeNA, a.toNat < 2 ^ 32 :=
  fun _ ha => (wordOk_parts (wordOk_of h ha)).1

/-- The words are 8-aligned. -/
theorem words_al_of_wordsOk : ∀ a ∈ rtWords pinA pnA nextA lockA freeNA, a.toNat % 8 = 0 :=
  fun _ ha => (wordOk_parts (wordOk_of h ha)).2.1

/-- The words are clear of the Linux entry stack (they lie below
`2 ^ 32`). -/
theorem words_entry_of_wordsOk : ∀ a ∈ rtWords pinA pnA nextA lockA freeNA,
    a.toNat + 8 ≤ Entry.linux.stack.lo ∨ Entry.linux.stack.lo + Entry.linux.stack.size ≤ a.toNat := by
  intro a ha
  have := (wordOk_parts (wordOk_of h ha)).1
  have hlo : Entry.linux.stack.lo = 2 ^ 47 - 4096 - 65536 := rfl
  omega

/-- The words are clear of the stack pool. -/
theorem words_pool_of_wordsOk : ∀ a ∈ rtWords pinA pnA nextA lockA freeNA,
    a.toNat + 8 ≤ Λ.stackPool.lo ∨ Λ.stackPool.lo + Λ.stackPool.size ≤ a.toNat :=
  fun _ ha => clear_of_clearB (wordOk_parts (wordOk_of h ha)).2.2.1

/-- The words' bytes lie in `.data` or the pinned region. -/
theorem words_bytes_of_wordsOk : ∀ a ∈ rtWords pinA pnA nextA lockA freeNA,
    ∀ i < 8, Λ.data.contains (a.toNat + i) ∨ Λ.pinned.contains (a.toNat + i) :=
  fun _ ha => (wordOk_parts (wordOk_of h ha)).2.2.2

/-- The words are mapped at load time for writing and reading, whatever the
entry state `E` and the number of thread slots `n`, their bytes in `.data`
or the pinned region. -/
theorem words_mappedE_of_wordsOk (E : Entry) (n : Nat) : ∀ a ∈ rtWords pinA pnA nextA lockA freeNA,
    Kernel.mapped (Kernel.KState.init n E Λ) true ⟨a, 8⟩ = true ∧
      Kernel.mapped (Kernel.KState.init n E Λ) false ⟨a, 8⟩ = true ∧
      ∀ i < 8, Λ.data.contains (a.toNat + i) ∨ Λ.pinned.contains (a.toNat + i) := fun a ha =>
  ⟨mapped_init_of_bytes (words_bytes_of_wordsOk h a ha), mapped_init_of_bytes (words_bytes_of_wordsOk h a ha),
    words_bytes_of_wordsOk h a ha⟩

/-- The words are mapped at load time for writing and reading at the Linux
entry state with one thread slot, their bytes in `.data` or the pinned
region. -/
theorem words_mapped_of_wordsOk : ∀ a ∈ rtWords pinA pnA nextA lockA freeNA,
    Kernel.mapped (Kernel.KState.init 1 Entry.linux Λ) true ⟨a, 8⟩ = true ∧
      Kernel.mapped (Kernel.KState.init 1 Entry.linux Λ) false ⟨a, 8⟩ = true ∧
      ∀ i < 8, Λ.data.contains (a.toNat + i) ∨ Λ.pinned.contains (a.toNat + i) :=
  words_mappedE_of_wordsOk h Entry.linux 1

/-- The stack pool fits the address space. -/
theorem pool_fit_of_wordsOk : Λ.stackPool.lo + Λ.stackPool.size < 2 ^ 64 := by
  simp only [wordsOk, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1.2

/-- The first stack is 16-aligned. -/
theorem stacks_al_of_wordsOk : stacksA.toNat % 16 = 0 := by
  simp only [wordsOk, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.2

/-- The first stack lies in the pool. -/
theorem stacks_sub_of_wordsOk : (⟨stacksA.toNat, 16384⟩ : Scc.Sem.Range).Sub Λ.stackPool := by
  simp only [wordsOk, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2

/-- The words are pairwise disjoint (in `rtWords`' order: the four counters,
the TCB's header, its six fields). -/
theorem words_disj_of_wordsOk : (rtWords pinA pnA nextA lockA freeNA).Pairwise WordSep := by
  simp only [wordsOk, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

/-- **The TCB's words are none of the counters**: the header and its six
fields (`pinA + 8 j`, `j < 7`) differ from `pnA`, `lockA`, `freeNA` and
`nextA`. -/
theorem tcbSep_of_wordsOk : ∀ j < 7, pinA + BitVec.ofNat 64 (8 * j) ∉ [pnA, lockA, freeNA, nextA] := by
  intro j hj hm
  have hd := words_disj_of_wordsOk h
  have e : rtWords pinA pnA nextA lockA freeNA = [pnA, nextA, lockA, freeNA] ++
      (pinA :: (List.range 6).map fun i => pinA + BitVec.ofNat 64 (8 * (i + 1))) := rfl
  rw [e, List.pairwise_append] at hd
  have h2 : pinA + BitVec.ofNat 64 (8 * j) ∈
      pinA :: (List.range 6).map fun i => pinA + BitVec.ofNat 64 (8 * (i + 1)) := by
    rcases j with _ | i
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)
  have h1 : pinA + BitVec.ofNat 64 (8 * j) ∈ [pnA, nextA, lockA, freeNA] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with hm | hm | hm | hm <;> simp [hm]
  have hs := hd.2.2 _ h1 _ h2
  unfold WordSep at hs; omega

end Words

end Scc.Cert.Rt.X64
