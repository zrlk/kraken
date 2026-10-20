/-
Copied from x64's `Kraken/Promising/SeqLinkX64Step.lean`, adapted for AArch64.
AArch64's `ValidLayout` has no `instr_size` field in x64's form (every
instruction is 4 bytes); `ValidLayout.size_pos` supplies the positive size of
a non-label cell instead.

AArch64: from Kraken's instruction-step judgment to the merged link.

The weakest precondition of `Kraken.AArch64.WP.MachineWP` and the procedure
specifications of `Kraken.AArch64.WP.Step` conclude `Eventually e.instrStep P`:
one cell per step, the first one past the labels at the pc (`codeAt`). The
merged link (`Kraken.Promising.SeqLinkAArch64`) consumes
`Eventually (step1W L e) P`, whose steps are `Executable.step`: every cell laid
out at the pc. On a valid layout the cells at an address are its labels and
one instruction (`directivesAtAddress_of_codeAt`), so an `instrStep` is a
`step1` (`instrStep_step1`, `eventually_step1_of_instrStep`), and with the
access discipline (`eventually_step1W`) a `step1W`.
-/
import Kraken.Promising.SeqLinkAArch64
import Kraken.AArch64.WP.Step
import Kraken.AArch64.WP.InterpSound

open Kraken

namespace Kraken.Promising.AArch64

/-! ## The cells at an address -/

private theorem le_sum_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by simp
  | y :: _, _, .tail _ h => by have := le_sum_of_mem h; simp; omega

private theorem mem_takeWhile {α} {p : α → Bool} : ∀ {l : List α} {a : α}, a ∈ l.takeWhile p → p a = true
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    by_cases hp : p x
    · rw [List.takeWhile_cons_of_pos hp] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact hp
      · exact mem_takeWhile h'
    · rw [List.takeWhile_cons_of_neg hp] at h
      simp at h

private theorem dropWhile_eq_cons {α} {p : α → Bool} :
    ∀ {l : List α} {x : α} {xs : List α}, l.dropWhile p = x :: xs → p x = false
  | [], _, _, h => by simp at h
  | y :: ys, x, xs, h => by
    rw [List.dropWhile_cons] at h
    split at h
    · exact dropWhile_eq_cons h
    · rename_i hy
      cases h
      simpa using hy

private theorem add_ofNat_ne_self (pc : Int64) {z : Nat} (h0 : 0 < z) (h1 : z < 2 ^ 64) :
    pc + Int64.ofNat z ≠ pc := by
  intro h
  have h2 := congrArg Int64.toBitVec h
  rw [Int64.toBitVec_add, Int64.toBitVec_ofNat'] at h2
  bv_omega

theorem withAddresses_nil (a : Int64) :
    Kraken.Executable.withAddresses (a, ([] : List (Directive × Nat))) = [] := by
  rw [Kraken.Executable.withAddresses]

theorem withAddresses_cons (a : Int64) (c : Directive × Nat) (ds : List (Directive × Nat)) :
    Kraken.Executable.withAddresses (a, c :: ds) =
      (a, c) :: Kraken.Executable.withAddresses (a + .ofNat c.2, ds) := by
  rw [Kraken.Executable.withAddresses]

/-- Dropping a prefix of the cells with addresses leaves the cells with
addresses of a suffix. -/
theorem dropWhile_withAddresses (p : Int64 × Directive × Nat → Bool) :
    ∀ (ds : List (Directive × Nat)) (a : Int64), ∃ a' ds',
      (Kraken.Executable.withAddresses (a, ds)).dropWhile p = Kraken.Executable.withAddresses (a', ds') ∧
        ds' <:+ ds := by
  intro ds
  induction ds with
  | nil =>
    intro a
    refine ⟨a, [], ?_, List.suffix_refl _⟩
    rw [withAddresses_nil]
    rfl
  | cons c ds ih =>
    intro a
    rw [withAddresses_cons, List.dropWhile_cons]
    split
    · obtain ⟨a', ds', h1, h2⟩ := ih (a + .ofNat c.2)
      exact ⟨a', ds', h1, h2.trans (List.suffix_cons c ds)⟩
    · exact ⟨a, c :: ds, (withAddresses_cons a c ds).symm, List.suffix_refl _⟩

/-- Cells of size zero at `pc` all sit at `pc`. -/
theorem withAddresses_zeros (pc : Int64) :
    ∀ (ls X : List (Directive × Nat)), (∀ c ∈ ls, c.2 = 0) →
      Kraken.Executable.withAddresses (pc, ls ++ X) =
        ls.map (fun c => (pc, c)) ++ Kraken.Executable.withAddresses (pc, X) := by
  intro ls
  induction ls with
  | nil => intro X _; rfl
  | cons c ls ih =>
    intro X hls
    rw [List.cons_append, withAddresses_cons, hls c List.mem_cons_self, Int64.add_ofNat_zero,
      ih X (fun c hc => hls c (List.mem_cons_of_mem _ hc))]
    rfl

/-- On a valid layout, the cells at an address are its labels and the one
instruction `codeAt` finds behind them. -/
theorem directivesAtAddress_of_codeAt {e : Kraken.Executable Directive} [hv : Kraken.Executable.ValidLayout e]
    {pc : Int64} {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (h : e.codeAt pc = (d, z) :: rest) :
    ∃ ls, e.directivesAtAddress pc = ls ++ [(d, z)] ∧ ∀ c ∈ ls, c.1.isLabel = true ∧ c.2 = 0 := by
  obtain ⟨start, ds⟩ := e
  obtain ⟨a', ds', hW, hsuf⟩ := dropWhile_withAddresses (fun x => decide (x.1 ≠ pc)) ds start
  have hfrom : Kraken.Executable.directivesFromAddress (start, ds) pc = ds' := by
    unfold Kraken.Executable.directivesFromAddress
    rw [hW, Kraken.Executable.withAddresses_map_snd]
  unfold Kraken.Executable.codeAt at h
  rw [hfrom] at h
  have hsplit : ds' = ds'.takeWhile (fun c => c.1.isLabel) ++ (d, z) :: rest := by
    conv => lhs; rw [← List.takeWhile_append_dropWhile (p := fun c => c.1.isLabel) (l := ds')]
    rw [h]
  have hmem : ∀ c ∈ ds', ∃ i, ds[i]? = some c := fun c hc => List.mem_iff_getElem?.mp (hsuf.subset hc)
  -- the labels in front occupy no bytes
  have hlab : ∀ c ∈ ds'.takeWhile (fun c => c.1.isLabel), c.1.isLabel = true ∧ c.2 = 0 := by
    intro c hc
    have hl : c.1.isLabel = true := mem_takeWhile (p := fun c : Directive × Nat => c.1.isLabel) hc
    refine ⟨hl, ?_⟩
    obtain ⟨i, hi⟩ := hmem c ((List.takeWhile_prefix _).subset hc)
    obtain ⟨d', z'⟩ := c
    cases d' with
    | label l => exact hv.label_size i l z' hi
    | instr _ => simp [Directive.isLabel] at hl
    | byteArray _ => simp [Directive.isLabel] at hl
  generalize ds'.takeWhile (fun c => c.1.isLabel) = ls at hsplit hlab
  -- the instruction occupies at least one byte and less than the address space
  have hdz : pc + Int64.ofNat z ≠ pc := by
    obtain ⟨i, hi⟩ := hmem (d, z) (by rw [hsplit]; simp)
    have hnl : ∀ l, d ≠ Directive.label l := by
      intro l hd
      have := dropWhile_eq_cons h
      simp [hd, Directive.isLabel] at this
    have h0 := @Kraken.Executable.ValidLayout.size_pos (start, ds) hv i d z hi hnl
    have h1 : z ≤ (ds.map (·.2)).sum :=
      le_sum_of_mem (List.mem_map.mpr ⟨(d, z), List.mem_of_getElem? hi, rfl⟩)
    exact add_ofNat_ne_self pc h0 (Nat.lt_of_le_of_lt h1 hv.no_wrap)
  -- the cells from the pc start at the pc
  have ha' : a' = pc := by
    rw [hsplit] at hW
    cases ls with
    | nil =>
      rw [List.nil_append, withAddresses_cons] at hW
      simpa using dropWhile_eq_cons hW
    | cons c ls =>
      rw [List.cons_append, withAddresses_cons] at hW
      simpa using dropWhile_eq_cons hW
  refine ⟨ls, ?_, hlab⟩
  unfold Kraken.Executable.directivesAtAddress
  dsimp only
  rw [hW, ha', hsplit, withAddresses_zeros pc ls _ (fun c hc => (hlab c hc).2), withAddresses_cons,
    List.takeWhile_append_of_pos (fun a ha => by obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha; simp),
    List.takeWhile_cons_of_pos (by simp)]
  have htail : (Kraken.Executable.withAddresses (pc + Int64.ofNat (d, z).2, rest)).takeWhile
      (fun x => decide (x.1 = pc)) = [] := by
    cases rest with
    | nil => rw [withAddresses_nil]; rfl
    | cons c rest => rw [withAddresses_cons, List.takeWhile_cons_of_neg (by simpa using hdz)]
  rw [htail]
  simp [Function.comp_def]


/-! ## An instruction step is a step -/

/-- On a valid layout, one instruction step of the ambient code is a step of
Kraken's single-step judgment. -/
theorem instrStep_step1 [_root_.Layout] {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    {st : MachineState} {post : MachineState → Prop} (h : e.instrStep st post) : step1 e st post := by
  obtain ⟨d, z, rest, hcode, hstep⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  letI := _root_.Executable.labels e
  show (Directives.interp (e.directivesAtAddress st.2) st.1 st.2 (fun pc s => .done (s, pc))).All post
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]
  unfold Kraken.Executable.stepAt at hstep
  -- name the address behind the cell, so the transport unifies syntactically
  generalize st.2 + Int64.ofNat z = pc' at hstep ⊢
  exact Directive.interp_sound (next := fun s' => post (s', pc')) (jmp := post) (fun _ h => h) (fun _ h => h)
    hstep

/-- An instruction chain is a chain of Kraken's single steps. -/
theorem eventually_step1_of_instrStep [_root_.Layout] {e : Kraken.Executable Directive}
    [Kraken.Executable.ValidLayout e] {P : MachineState → Prop} {st : MachineState}
    (h : Eventually e.instrStep P st) : Eventually (step1 e) P st := by
  induction h with
  | done st hP => exact .done st hP
  | step st mid hT _ ih => exact .step st mid (instrStep_step1 hT) ih

/-- An instruction chain whose steps respect the layout `L`, by an invariant
(as in `eventually_step1W`), is a chain of the merged judgment's steps. -/
theorem eventually_step1W_of_instrStep [_root_.Layout] {L : SharedLayout} {e : Kraken.Executable Directive}
    [Kraken.Executable.ValidLayout e] {Inv P : MachineState → Prop}
    (hpres : ∀ s R, Inv s → step1 e s R → step1 e s (fun s' => R s' ∧ Inv s'))
    (hacc : ∀ s, Inv s → (Executable.step e s .done).AllW L (fun _ => True))
    {s₀ : MachineState} (h : Eventually e.instrStep P s₀) (h0 : Inv s₀) : Eventually (step1W L e) P s₀ :=
  eventually_step1W hpres hacc (eventually_step1_of_instrStep h) h0

end Kraken.Promising.AArch64
