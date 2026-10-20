/-
Copied from x64's `Kraken/MachineWP.lean` at commit `86cde85`, adapted for
AArch64: the sections "The bridge to the segment judgment" and "Deriving the
ambient facts" (`CodeWF`, `Executable.bridge`, `codeWF_of_valid`, the walk of a
laid-out program, `directivesFromAddress_end`) and the read-back
`Program.instrStep_of_triple(_exits)`/`Program.run_of_triple`. The proofs are
x64's; AArch64's `ValidLayout` (every instruction 4 bytes, no alignment no-op)
supplies the same facts, so x64's `Program.label_aligned_of_align` has no
counterpart.

A triple's meaning is `Eventually e.instrStep`: one instruction per step. The
baseline judgment is `Eventually (straightlineStep e)`: one segment burst per
step. `Executable.bridge` refines the second by the first, for any executable
that is wellformed code (`CodeWF`); a laid-out program is
(`codeWF_of_valid`). `Program.run_of_triple` reads a triple on a whole
laid-out program back as the baseline judgment from its start address.
-/
import Kraken.AArch64.WP.InterpSound

open Kraken
open Std.WP
open Lean.Order

/-! ## The bridge to the segment judgment

`instrStep` runs one instruction; kraken's `straightlineStep` runs a whole
segment, from the pc until a jump or the end of the text. An instruction
chain therefore refines a segment chain, and the two agree when the
postcondition can hold only where the text has run out. -/

/-- What the bridge needs of the ambient code: a label occupies no bytes, and
behind an instruction cell the segment map continues with the cells behind
it. -/
structure Kraken.Executable.CodeWF (e : Kraken.Executable Directive) : Prop where
  label_size : ∀ c ∈ e.2, c.1.isLabel = true → c.2 = 0
  advance : ∀ pc d z rest, e.codeAt pc = (d, z) :: rest →
    e.directivesFromAddress (pc + .ofNat z) = rest

private theorem mem_takeWhile {α} {p : α → Bool} {l : List α} {a : α}
    (h : a ∈ l.takeWhile p) : p a = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hp : p x
    · rw [List.takeWhile_cons, if_pos hp] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact hp
      · exact ih h'
    · rw [List.takeWhile_cons, if_neg hp] at h
      simp at h

/-- One segment burst, as a step of the omni-judgment. -/
private theorem step_burst [_root_.Layout] {e : Kraken.Executable Directive} {post : @Post MachineState}
    {st : MachineState}
    (h : (Executable.straightline e st .done).All
      (fun m => Eventually (straightlineStep e) post m)) :
    Eventually (straightlineStep e) post st := by
  refine step_cps _ _ _ ?_
  unfold straightlineStep at h ⊢
  exact h

/-- One segment, cut at its first instruction: the instruction runs, and a
fall-through continues with the segment behind it. -/
theorem Kraken.Executable.straightline_cons {e : Kraken.Executable Directive} (hwf : e.CodeWF)
    {pc : Int64} {s : MachineData} {d : Directive} {z : Nat}
    {rest : List (Directive × Nat)} (hcode : e.codeAt pc = (d, z) :: rest) :
    Executable.straightline e (s, pc) .done
      = @Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
          (fun s' => Executable.straightline e (s', pc + .ofNat z) .done)
          (fun pc' s' => .done (s', pc')) := by
  letI := (_root_.Executable.labels e)
  have hsplit : e.directivesFromAddress pc
      = (e.directivesFromAddress pc).takeWhile (fun c => c.1.isLabel) ++ (d, z) :: rest := by
    conv => lhs; rw [← List.takeWhile_append_dropWhile (p := fun c => c.1.isLabel)
      (l := e.directivesFromAddress pc)]
    rw [show (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel)
      = (d, z) :: rest from hcode]
  have hsub : ∀ c ∈ e.directivesFromAddress pc, c ∈ e.2 := by
    intro c hc
    unfold Kraken.Executable.directivesFromAddress at hc
    have hmem : c ∈ e.withAddresses.map (·.2) :=
      List.map_subset _ (List.dropWhile_subset _) hc
    rwa [show e.withAddresses.map (·.2) = e.2 from Executable.withAddresses_map_snd e.2 e.1]
      at hmem
  have hls : ∀ c ∈ (e.directivesFromAddress pc).takeWhile (fun c => c.1.isLabel),
      c.1.isLabel = true ∧ c.2 = 0 := by
    intro c hc
    have hlab : c.1.isLabel = true :=
      mem_takeWhile (p := fun c : Directive × Nat => c.1.isLabel) hc
    have hmem : c ∈ e.directivesFromAddress pc :=
      (List.takeWhile_sublist _).subset hc
    exact ⟨hlab, hwf.label_size c (hsub c hmem) hlab⟩
  show @Directives.interp (_root_.Executable.labels e) (e.directivesFromAddress pc) s pc
    (fun pc' s' => .done (s', pc')) = _
  rw [hsplit, Directives.interp_label_prefix _ _ _ _ _ hls]
  simp only [Directives.interp]
  congr 1
  funext s'
  show Directives.interp rest s' (pc + .ofNat z) _ = _
  rw [← hwf.advance pc d z rest hcode]
  rfl

/-- An instruction chain is a segment chain, when the postcondition can hold
only where the text has run out. -/
theorem Kraken.Executable.bridge [_root_.Layout] {e : Kraken.Executable Directive} (hwf : e.CodeWF)
    {post : @Post MachineState}
    (hbnd : ∀ st, post st → e.directivesFromAddress st.2 = []) :
    ∀ st, Eventually e.instrStep post st → Eventually (straightlineStep e) post st := by
  have key : ∀ st, Eventually e.instrStep post st →
      (Executable.straightline e st .done).All
        (fun m => Eventually (straightlineStep e) post m) := by
    intro st h
    induction h with
    | done st hp =>
      show (@Directives.interp (_root_.Executable.labels e) (e.directivesFromAddress st.2) st.1 st.2 _).All _
      rw [hbnd st hp]
      simp only [Directives.interp, Effects.All]
      exact Eventually.done _ hp
    | step st mid_p htrans _ ih =>
      obtain ⟨d, z, rest, hcode, hstep⟩ := htrans
      rw [Executable.straightline_cons hwf hcode]
      letI := (_root_.Executable.labels e)
      -- name the address behind the cell, so the transport unifies syntactically
      -- instead of reducing 64-bit arithmetic under a metavariable
      unfold Executable.stepAt at hstep
      generalize hnext : st.2 + (Int64.ofNat z) = pc' at hstep ⊢
      exact Directive.interp_sound (next := fun s' => mid_p (s', pc')) (jmp := mid_p)
        (fun s' hmid => ih (s', pc') hmid)
        (fun st' hmid => step_burst (ih st' hmid))
        hstep
  intro st h
  exact step_burst (key st h)

section Derive

/-! ## Deriving the ambient facts

A laid-out program satisfies `CodeWF`: `ValidLayout` gives a label cell zero
size and an instruction cell positive size (four bytes on AArch64), so the
address behind an instruction determines the position behind it. -/

private theorem dropWhile_eq_drop {α} (p : α → Bool) (l : List α) :
    ∃ j, l.dropWhile p = l.drop j ∧ ∀ i a, i < j → l[i]? = some a → p a = true := by
  induction l with
  | nil => exact ⟨0, rfl, by intro i a hi h; simp at h⟩
  | cons x xs ih =>
    obtain ⟨j, hj, hp⟩ := ih
    by_cases hx : p x
    · refine ⟨j + 1, ?_, ?_⟩
      · rw [List.dropWhile_cons, if_pos hx, List.drop_succ_cons]
        exact hj
      · intro i a hi hg
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
          exact hg ▸ hx
        | succ n =>
          simp only [List.getElem?_cons_succ] at hg
          exact hp n a (by omega) hg
    · refine ⟨0, ?_, by intro i a hi; omega⟩
      rw [List.dropWhile_cons, if_neg hx, List.drop_zero]

private theorem addrOf_succ_of_none (e : Kraken.Executable Directive) {n : Nat} (h : e.2[n]? = none) :
    e.addrOf (n + 1) = e.addrOf n := by
  have hle : e.2.length ≤ n := by
    by_cases hlt : n < e.2.length
    · rw [List.getElem?_eq_getElem hlt] at h; cases h
    · omega
  unfold Executable.addrOf Executable.sizeBefore
  rw [List.take_of_length_le (by omega), List.take_of_length_le hle]

/-- A run of label cells occupies no bytes, so the address does not move. -/
private theorem addrOf_add_of_labels (e : Kraken.Executable Directive) [Executable.ValidLayout e] {k : Nat} :
    ∀ (j : Nat), (∀ i a, i < j → e.2[k + i]? = some a → a.1.isLabel = true) →
      e.addrOf (k + j) = e.addrOf k := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have hstep : e.addrOf (k + n + 1) = e.addrOf (k + n) := by
      cases hc : e.2[k + n]? with
      | none => exact addrOf_succ_of_none e hc
      | some c =>
        have hlab := h n c (by omega) hc
        obtain ⟨d, z⟩ := c
        cases d with
        | label l =>
          have hz : z = 0 := Executable.ValidLayout.label_size (k + n) l z hc
          rw [Executable.addrOf_succ e hc, hz]
          simp
        | instr i => simp [Directive.isLabel] at hlab
        | byteArray a => simp [Directive.isLabel] at hlab
    rw [show k + (n + 1) = k + n + 1 from rfl, hstep]
    exact ih (fun i a hi hg => h i a (by omega) hg)

/-- A laid-out program is wellformed code. -/
theorem Kraken.Executable.codeWF_of_valid (e : Kraken.Executable Directive) [hv : Executable.ValidLayout e] :
    e.CodeWF where
  label_size := by
    intro c hc hlab
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
    obtain ⟨d, z⟩ := c
    cases d with
    | label l => exact hv.label_size i l z hi
    | instr i' => simp [Directive.isLabel] at hlab
    | byteArray a => simp [Directive.isLabel] at hlab
  advance := by
    intro pc d z rest hcode
    have hne : e.directivesFromAddress pc ≠ [] := by
      intro hnil
      rw [Executable.codeAt, hnil] at hcode
      simp at hcode
    obtain ⟨k, hklen, hkaddr, hkdrop⟩ := Executable.exists_pos_of_directivesFromAddress e hne
    obtain ⟨j, hj, hjp⟩ := dropWhile_eq_drop (fun c : Directive × Nat => c.1.isLabel)
      (e.directivesFromAddress pc)
    have hcodeDrop : e.2.drop (k + j) = (d, z) :: rest := by
      rw [← List.drop_drop, ← hkdrop, ← hj]
      exact hcode
    have hcell : e.2[k + j]? = some (d, z) := by
      have h0 : (e.2.drop (k + j))[0]? = some (d, z) := by rw [hcodeDrop]; rfl
      rw [List.getElem?_drop] at h0
      simpa using h0
    have hdlab : d.isLabel = false := by
      have := List.head?_dropWhile_not (p := fun c : Directive × Nat => c.1.isLabel)
        (l := e.directivesFromAddress pc)
      rw [show (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel) = (d, z) :: rest
        from hcode] at this
      simpa using this
    have haddr : e.addrOf (k + j) = pc := by
      rw [addrOf_add_of_labels e j ?_, hkaddr]
      intro i a hi hg
      refine hjp i a hi ?_
      rw [hkdrop, List.getElem?_drop]
      exact hg
    have hsucc : e.addrOf (k + j + 1) = pc + .ofNat z := by
      rw [Executable.addrOf_succ e hcell, haddr]
    have hfresh : ∀ i, i < k + j + 1 → e.addrOf i ≠ e.addrOf (k + j + 1) := by
      intro i hi
      refine Executable.addrOf_ne_of_valid e hi ?_ ?_
      · rw [show k + j + 1 - 1 = k + j from rfl, hcell]
        rfl
      · intro l zz hzz
        rw [show k + j + 1 - 1 = k + j from rfl, hcell] at hzz
        simp only [Option.some.injEq, Prod.mk.injEq] at hzz
        rw [hzz.1] at hdlab
        simp [Directive.isLabel] at hdlab
    have hlen : k + j + 1 ≤ e.2.length := by
      have : (e.2.drop (k + j)).length = e.2.length - (k + j) := List.length_drop
      rw [hcodeDrop] at this
      simp only [List.length_cons] at this
      omega
    have hdfa := Executable.directivesFromAddress_addrOf e (k + j + 1) hlen hfresh
    rw [hsucc] at hdfa
    rw [hdfa]
    have : e.2.drop (k + j + 1) = rest := by
      rw [show k + j + 1 = (k + j) + 1 from rfl, ← List.drop_drop, hcodeDrop]
      rfl
    exact this

/-- Unfold a placement at a cell that is not a label. -/
theorem Kraken.Executable.sits_cons_of_not_label {e : Kraken.Executable Directive} {pc : Int64} {d : Directive}
    {q : Program} (hd : d.isLabel = false) :
    e.sits pc (d :: q) = ∃ z rest, e.codeAt pc = (d, z) :: rest ∧ e.sits (pc + .ofNat z) q := by
  cases d with
  | label l => simp [Directive.isLabel] at hd
  | instr i => rfl
  | byteArray a => rfl

/-- Unfold the fall-through address past a cell that is not a label. -/
theorem Kraken.Executable.after_cons_of_not_label {e : Kraken.Executable Directive} {pc : Int64} {d : Directive}
    {q : Program} {z : Nat} {rest : List (Directive × Nat)} (hd : d.isLabel = false)
    (hcode : e.codeAt pc = (d, z) :: rest) :
    e.after pc (d :: q) = e.after (pc + .ofNat z) q := by
  cases d with
  | label l => simp [Directive.isLabel] at hd
  | instr i => simp only [Executable.after, hcode]
  | byteArray a => simp only [Executable.after, hcode]

/-! ### Walking a laid-out program

A laid-out program places the directive at position `i` at the address
`Executable.addrOf i`, so a fragment of the text sits at the address of its
first position (`Executable.walk_addrOf`), and a label's address is the
address of its cell (`Program.label_addrOf_drop`). The whole text sits at one
address only (`Executable.entry_of_sits`): a placement consumes one cell per
non-label directive, and the text has no cell to spare. -/

private theorem countP_frag [_root_.Layout] (f : Directive → Bool) :
    ∀ (n : Nat) (q : Program), (Layout.frag n q).countP (fun c => f c.1) = q.countP f := by
  intro n q
  induction q generalizing n with
  | nil => rfl
  | cons d q ih => rw [Layout.frag_cons, List.countP_cons, List.countP_cons, ih]

/-- The cell of a laid-out program at a position. -/
private theorem layout_getElem [layout : _root_.Layout] (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]

/-- A label occupies no bytes. -/
private theorem size_label [layout : _root_.Layout] {p : Program}
    [hv : Executable.ValidLayout (layout p)] {i : Nat} {l : Label}
    (hp : p[i]? = some (Directive.label l)) : Kraken.Layout.size Directive i = 0 :=
  hv.label_size i l _ (by rw [layout_getElem, hp]; rfl)

/-- Stepping one position advances the address by that position's size. -/
private theorem addrOf_step [layout : _root_.Layout] {p : Program} {i : Nat} {d : Directive}
    (hp : p[i]? = some d) :
    (layout p).addrOf (i + 1) = (layout p).addrOf i + .ofNat (Kraken.Layout.size Directive i) :=
  Executable.addrOf_succ _ (by rw [layout_getElem, hp]; rfl)

/-- The cells at the address of a position that holds an instruction: the text
from that position on. -/
theorem Kraken.Executable.codeAt_addrOf [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {i : Nat} {d : Directive}
    (hd : d.isLabel = false) (hp : p[i]? = some d) :
    (layout p).codeAt ((layout p).addrOf i)
      = (d, Kraken.Layout.size Directive i) :: Layout.frag (i + 1) (p.drop (i + 1)) := by
  have hi : i < p.length := by
    by_cases h : i < p.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hp; cases hp
  have hlen : i ≤ (layout p).2.length := by
    rw [Layout.apply_snd, Layout.frag_length]; omega
  obtain ⟨j, hji, hdfa, hlab⟩ := Executable.exists_cut (layout p) hlen
  have hlent : ((p.drop j).take (i - j)).length = i - j := by
    rw [List.length_take, List.length_drop]; omega
  have hdrop : (layout p).2.drop j
      = Layout.frag j ((p.drop j).take (i - j)) ++ Layout.frag i (p.drop i) := by
    rw [Layout.apply_snd, Layout.frag_drop, Nat.zero_add]
    conv => lhs; rw [← List.take_append_drop (i - j) (p.drop j)]
    rw [Layout.frag_append, hlent, List.drop_drop, show j + (i - j) = i from by omega]
  have hslice : ∀ dz ∈ Layout.frag j ((p.drop j).take (i - j)),
      (fun c : Directive × Nat => c.1.isLabel) dz = true := by
    intro dz hdz
    show dz.1.isLabel = true
    obtain ⟨m, hm, heq⟩ := List.getElem_of_mem (Layout.frag_mem hdz)
    rw [hlent] at hm
    have hpm : p[j + m]? = some dz.1 := by
      rw [← List.getElem?_drop, ← List.getElem?_take_of_lt hm,
        List.getElem?_eq_getElem (by rw [hlent]; omega), heq]
    obtain ⟨l', z, hlz⟩ := hlab (j + m) (Nat.le_add_right j m) (by omega)
    rw [layout_getElem, hpm] at hlz
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hlz
    rw [hlz.1]
    rfl
  have hget : p[i] = d := by
    have h := List.getElem?_eq_getElem hi
    rw [hp] at h
    exact (Option.some.inj h).symm
  have hhead : p.drop i = d :: p.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hget]
  rw [Executable.codeAt, hdfa, hdrop, List.dropWhile_append_of_pos hslice, hhead,
    Layout.frag_cons, List.dropWhile_cons, if_neg (by simpa using hd)]

/-- Walking a fragment of a laid-out program: it sits at the address of its
first position, and the walk ends at the address of the position behind it. -/
theorem Kraken.Executable.walk_addrOf [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] :
    ∀ (body rest : Program) (i : Nat), p.drop i = body ++ rest →
      (layout p).sits ((layout p).addrOf i) body
        ∧ (layout p).after ((layout p).addrOf i) body
            = (layout p).addrOf (i + body.length) := by
  intro body
  induction body with
  | nil => intro rest i _; exact ⟨trivial, by simp [Executable.after]⟩
  | cons d body ih =>
    intro rest i hdrop
    have hp : p[i]? = some d := by
      have h0 : (p.drop i)[0]? = some d := by rw [hdrop]; rfl
      rw [List.getElem?_drop] at h0
      simpa using h0
    have hdrop' : p.drop (i + 1) = body ++ rest := by
      rw [← List.drop_drop, hdrop]
      rfl
    obtain ⟨hsits, hafter⟩ := ih rest (i + 1) hdrop'
    by_cases hd : d.isLabel
    · obtain ⟨l, rfl⟩ : ∃ l, d = Directive.label l := by
        cases d with
        | label l => exact ⟨l, rfl⟩
        | instr i' => simp [Directive.isLabel] at hd
        | byteArray a => simp [Directive.isLabel] at hd
      have hstep : (layout p).addrOf (i + 1) = (layout p).addrOf i := by
        rw [addrOf_step hp, size_label hp]
        simp
      rw [hstep] at hsits hafter
      refine ⟨hsits, ?_⟩
      rw [show (layout p).after ((layout p).addrOf i) (Directive.label l :: body)
        = (layout p).after ((layout p).addrOf i) body from rfl, hafter]
      congr 1
      simp only [List.length_cons]
      omega
    · have hdf : d.isLabel = false := by simpa using hd
      have hcode := Executable.codeAt_addrOf hdf hp
      rw [addrOf_step hp] at hsits hafter
      refine ⟨?_, ?_⟩
      · rw [Executable.sits_cons_of_not_label hdf]
        exact ⟨_, _, hcode, hsits⟩
      · rw [Executable.after_cons_of_not_label hdf hcode, hafter]
        congr 1
        simp only [List.length_cons]
        omega

/-- A placement consumes one cell per non-label directive: the segment at the
placement's start is the segment behind it, with those cells in front. -/
private theorem consume {e : Kraken.Executable Directive} (hwf : e.CodeWF) :
    ∀ (q : Program) (pc : Int64), e.sits pc q →
      ∃ pre, e.directivesFromAddress pc = pre ++ e.directivesFromAddress (e.after pc q)
        ∧ pre.countP (fun c => !c.1.isLabel) = q.countP (fun d => !d.isLabel) := by
  intro q
  induction q with
  | nil => intro pc _; exact ⟨[], by simp [Executable.after], by simp⟩
  | cons d q ih =>
    intro pc hsits
    by_cases hd : d.isLabel
    · obtain ⟨l, rfl⟩ : ∃ l, d = Directive.label l := by
        cases d with
        | label l => exact ⟨l, rfl⟩
        | instr i => simp [Directive.isLabel] at hd
        | byteArray a => simp [Directive.isLabel] at hd
      obtain ⟨pre, hpre, hcnt⟩ := ih pc hsits
      exact ⟨pre, hpre, by simpa [List.countP_cons, Directive.isLabel] using hcnt⟩
    · have hdf : d.isLabel = false := by simpa using hd
      rw [Executable.sits_cons_of_not_label hdf] at hsits
      obtain ⟨z, rest, hcode, hsits'⟩ := hsits
      obtain ⟨pre, hpre, hcnt⟩ := ih (pc + (Int64.ofNat z : Int64)) hsits'
      refine ⟨(e.directivesFromAddress pc).takeWhile (fun c => c.1.isLabel) ++ (d, z) :: pre,
        ?_, ?_⟩
      · rw [Executable.after_cons_of_not_label hdf hcode, List.append_assoc,
          List.cons_append, ← hpre, hwf.advance pc d z rest hcode]
        conv => lhs; rw [← List.takeWhile_append_dropWhile
          (p := fun c : Directive × Nat => c.1.isLabel) (l := e.directivesFromAddress pc)]
        rw [show (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel)
          = (d, z) :: rest from hcode]
      · have hzero : ((e.directivesFromAddress pc).takeWhile
            (fun c => c.1.isLabel)).countP (fun c => !c.1.isLabel) = 0 :=
          List.countP_eq_zero.mpr (fun c hc => by
            simp [mem_takeWhile (p := fun c : Directive × Nat => c.1.isLabel) hc])
        rw [List.countP_append, hzero, List.countP_cons, List.countP_cons, hcnt, hdf]
        simp

/-- The one address a laid-out program sits at: its start. Every non-label
directive consumes a cell, and the text has exactly as many. -/
theorem Kraken.Executable.entry_of_sits [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] (hne : 0 < p.countP (fun d => !d.isLabel))
    {pc : Int64} (h : (layout p).sits pc p) : pc = (layout p).addrOf 0 := by
  obtain ⟨pre, hpre, hcnt⟩ := consume (Executable.codeWF_of_valid (layout p)) p pc h
  have htext : ((layout p).2).countP (fun c => !c.1.isLabel)
      = p.countP (fun d => !d.isLabel) := by
    rw [Layout.apply_snd]
    exact countP_frag (fun d => !d.isLabel) 0 p
  have hnil : (layout p).directivesFromAddress pc ≠ [] := by
    intro hz
    rw [hz] at hpre
    have : pre = [] := (List.append_eq_nil_iff.mp hpre.symm).1
    rw [this] at hcnt
    simp at hcnt
    omega
  obtain ⟨k, -, hk, hdrop⟩ :=
    Executable.exists_pos_of_directivesFromAddress (layout p) hnil
  have hsplit : ((layout p).2).countP (fun c => !c.1.isLabel)
      = (((layout p).2).take k).countP (fun c => !c.1.isLabel)
        + (((layout p).2).drop k).countP (fun c => !c.1.isLabel) := by
    conv => lhs; rw [← List.take_append_drop k ((layout p).2)]
    rw [List.countP_append]
  rw [← hdrop, hpre, List.countP_append, hcnt, htext] at hsplit
  have htake : (((layout p).2).take k).countP (fun c => !c.1.isLabel) = 0 := by omega
  have hlabels : ∀ i a, i < k → ((layout p).2)[0 + i]? = some a → a.1.isLabel = true := by
    intro i a hi hget
    rw [Nat.zero_add] at hget
    have hmem : a ∈ ((layout p).2).take k :=
      List.mem_iff_getElem?.mpr ⟨i, by rw [List.getElem?_take_of_lt hi]; exact hget⟩
    simpa using List.countP_eq_zero.mp htake a hmem
  rw [← hk]
  have := addrOf_add_of_labels (layout p) (k := 0) k hlabels
  rw [Nat.zero_add] at this
  exact this

/-- The address of a label, from the position its scope suffix starts at. -/
theorem Program.label_addrOf_drop [layout : _root_.Layout] {p : Program}
    [hv : Executable.ValidLayout (layout p)] (hnd : (Program.labels p).Nodup)
    {l : Label} {i : Nat} (hdrop : p.drop i = Program.fromLabel p l)
    (hne : Program.fromLabel p l ≠ []) :
    (_root_.Executable.labels (layout p)).label l = (layout p).addrOf i := by
  obtain ⟨t, rest, hsplit, hfl, hfresh, hlen⟩ := Program.fromLabel_split hnd hne
  have hplen : p.length = t.length + (Program.fromLabel p l).length := by
    have h := congrArg List.length hsplit
    rw [hfl]
    simpa using h
  have hdlen : p.length - i = (Program.fromLabel p l).length := by
    have h := congrArg List.length hdrop
    rwa [List.length_drop] at h
  have hile : i ≤ p.length := by
    by_cases h : i ≤ p.length
    · exact h
    · rw [List.drop_eq_nil_of_le (by omega)] at hdrop
      exact absurd hdrop.symm hne
  have hit : i = t.length := by omega
  have hcell : p[i]? = some (Directive.label l) := by
    have h0 : (p.drop i)[0]? = some (Directive.label l) := by rw [hdrop, hfl]; rfl
    rw [List.getElem?_drop] at h0
    simpa using h0
  have hlay : (layout p).2[i]? = some (Directive.label l, Kraken.Layout.size Directive i) := by
    rw [layout_getElem, hcell]; rfl
  refine Executable.label_addrOf (layout p) l i ?_ ?_
  · rw [hlay, hv.label_size i l _ hlay]
  · have hpt : p.take i = t := by
      rw [hit, hsplit]
      exact List.take_left' rfl
    have htake : ((layout p).2).take i = Layout.frag 0 (p.take i) := by
      rw [Layout.apply_snd]
      conv => lhs; rw [← List.take_append_drop i p, Layout.frag_append]
      exact List.take_left' (by rw [Layout.frag_length, List.length_take]; omega)
    intro dz hdz heq
    rw [htake, hpt] at hdz
    exact hfresh (Program.mem_labels_of_cell (heq ▸ Layout.frag_mem hdz))

/-- Behind a laid-out program whose last cell is an instruction the text runs
out. -/
theorem Kraken.Executable.directivesFromAddress_end [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive}
    (hlast : p[p.length - 1]? = some dlast) (hd : dlast.isLabel = false) :
    (layout p).directivesFromAddress ((layout p).addrOf p.length) = [] := by
  have hlen : (layout p).2.length = p.length := by
    rw [Layout.apply_snd, Layout.frag_length]
  have hcell : (layout p).2[p.length - 1]? = some (dlast, Kraken.Layout.size Directive (p.length - 1)) := by
    rw [layout_getElem, hlast]; rfl
  have hfresh : ∀ k, k < p.length → (layout p).addrOf k ≠ (layout p).addrOf p.length := by
    intro k hk
    refine Executable.addrOf_ne_of_valid (layout p) hk (by rw [hcell]; rfl) ?_
    intro l z hz
    rw [hcell] at hz
    simp only [Option.some.injEq, Prod.mk.injEq] at hz
    rw [hz.1] at hd
    simp [Directive.isLabel] at hd
  rw [Executable.directivesFromAddress_addrOf (layout p) p.length (by omega) hfresh]
  exact List.drop_eq_nil_of_le (by omega)

/-- The empty exit channel holds nowhere. -/
theorem Kraken.Executable.bot_elim {a : Int64} {s : MachineData} {C : Prop}
    (h : (⊥ : Int64 → MachineData → Prop) a s) : C :=
  ((Lean.Order.bot_le (α := Int64 → MachineData → Prop) (fun _ _ => False)) a s h).elim

open MachineWP in
/-- A triple with exits on a laid-out program, read at the machine as the
instruction-step judgment: from the start address the machine reaches the end
of the text with the postcondition, or stops at an address satisfying the exit
channel `E`. -/
theorem Program.instrStep_of_triple_exits [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (ht : ⦃ P ⦄ p ⦃ Q; E ⦄) (hs : P s)
    (henv : cenv = layout p := by rfl) :
    Eventually (layout p).instrStep
      (fun st => (st.2 = (layout p).addrOf p.length ∧ Q () st.1) ∨ E st.2 st.1)
      (s, Kraken.Layout.start Directive) := by
  have h : (layout p).wp p (Q ()) E s := henv ▸ ht.le_wp s hs
  obtain ⟨hsits, hafter⟩ := Executable.walk_addrOf (p := p) p [] 0 (by simp)
  rw [Nat.zero_add] at hafter
  have hev := h ((layout p).addrOf 0) hsits
  rwa [hafter, Executable.addrOf_zero, Layout.apply_fst] at hev

open MachineWP in
/-- A triple on a laid-out program, read at the machine as the
instruction-step judgment: from the start address the machine reaches the end
of the text with the triple's postcondition. -/
theorem Program.instrStep_of_triple [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {s : MachineData}
    (ht : ⦃ P ⦄ p ⦃ Q ⦄) (hs : P s)
    (henv : cenv = layout p := by rfl) :
    Eventually (layout p).instrStep
      (fun st => st.2 = (layout p).addrOf p.length ∧ Q () st.1)
      (s, Kraken.Layout.start Directive) :=
  eventually_weaken _ _ _ _ (fun _ hst => hst.elim id Executable.bot_elim)
    (Program.instrStep_of_triple_exits ht hs henv)

open MachineWP in
/-- A triple on a laid-out program, read at the machine as the baseline
judgment: from the start address the segment judgment reaches the triple's
postcondition. -/
theorem Program.run_of_triple [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {s : MachineData} {dlast : Directive}
    (ht : ⦃ P ⦄ p ⦃ Q ⦄) (hs : P s)
    (henv : cenv = layout p := by rfl)
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    Eventually (straightlineStep (layout p)) (fun st => Q () st.1) (s, Kraken.Layout.start Directive) := by
  have hbnd : ∀ st : MachineState, (st.2 = (layout p).addrOf p.length ∧ Q () st.1) →
      (layout p).directivesFromAddress st.2 = [] := by
    rintro ⟨s', a⟩ ⟨rfl, -⟩
    exact Executable.directivesFromAddress_end hlast hd
  exact eventually_weaken _ _ _ _ (fun _ hst => hst.2)
    (Executable.bridge (Executable.codeWF_of_valid (layout p)) hbnd _
      (Program.instrStep_of_triple ht hs henv))

end Derive
