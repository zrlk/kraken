/-
Copied from x64's `Kraken/Promising/SeqLinkX64Prog.lean`, adapted for AArch64,
including the environment twin `Program.instrStepEnv_of_tripleEnv` for the
triples of `Kraken.AArch64.EnvWP`.

AArch64: from a `vcgen` triple on a laid-out program to the premises of the
merged link.

`merged_link_halt` (`Kraken.Promising.SeqLinkAArch64`) consumes an
`Eventually (step1W L e) P` judgment whose `P` holds only at the end address
`endPc`, and `hstop`: a step at `endPc` changes nothing. A triple
`⦃ P ⦄ p ⦃ Q ⦄` on the laid-out program `layout p` gives both:

- `Program.instrStep_of_triple` (`Kraken.AArch64.WP.Bridge`): the triple is an
  `Eventually (layout p).instrStep` judgment from the start address to the end
  address `(layout p).addrOf p.length`, with `Q`.
- `eventually_step1W_of_instrStep` (`Kraken.Promising.SeqLinkAArch64Step`):
  with the access discipline as an invariant (`hpres`, `hacc`, `h0`), that is
  a `step1W` judgment.
- `step1W_stop_of_end`: behind the text of a program whose last cell is not a
  label nothing is laid out (`Executable.directivesFromAddress_end`), so
  `Executable.step` there is `.done` at the state it started from
  (`step_of_directivesFromAddress_nil`): every step stutters.

`merged_premises_of_triple` puts the three together.
-/
import Kraken.Promising.SeqLinkAArch64Step
import Kraken.AArch64.WP.Bridge
import Kraken.AArch64.EnvWP

open Kraken
open Std.WP

namespace Kraken.Promising.AArch64

/-! ## Behind the text -/

/-- Where nothing is laid out from an address, nothing is laid out at it. -/
theorem directivesAtAddress_of_directivesFromAddress_nil {e : Kraken.Executable Directive} {a : Int64}
    (h : e.directivesFromAddress a = []) : e.directivesAtAddress a = [] := by
  unfold Kraken.Executable.directivesFromAddress at h
  unfold Kraken.Executable.directivesAtAddress
  rw [List.map_eq_nil_iff.mp h]
  rfl

/-- Where nothing is laid out from the pc, a step returns the state it started
from. -/
theorem step_of_directivesFromAddress_nil {e : _root_.Executable} {y : MachineState}
    (h : Kraken.Executable.directivesFromAddress e y.2 = []) (ret : MachineState → Effects) :
    Executable.step e y ret = ret y := by
  unfold Executable.step
  rw [directivesAtAddress_of_directivesFromAddress_nil h]
  rfl

/-- Where nothing is laid out from the pc, there is no instruction step. -/
theorem not_instrStep_of_directivesFromAddress_nil {e : Kraken.Executable Directive} {y : MachineState}
    {R : MachineState → Prop} (h : Kraken.Executable.directivesFromAddress e y.2 = []) : ¬ e.instrStep y R := by
  rintro ⟨d, z, rest, hcode, -⟩
  unfold Kraken.Executable.codeAt at hcode
  rw [h] at hcode
  cases hcode

/-- Where nothing is laid out from the pc, a merged step stutters. -/
theorem step1W_stop_of_directivesFromAddress_nil {L : SharedLayout} {e : _root_.Executable}
    {y : MachineState} {R : MachineState → Prop} (h : Kraken.Executable.directivesFromAddress e y.2 = [])
    (hs : step1W L e y R) : R y := by
  unfold step1W at hs
  rw [step_of_directivesFromAddress_nil h] at hs
  exact hs

/-- Where nothing is laid out from the pc, a single step stutters. -/
theorem step1_stop_of_directivesFromAddress_nil [_root_.Layout] {e : _root_.Executable}
    {y : MachineState} {R : MachineState → Prop} (h : Kraken.Executable.directivesFromAddress e y.2 = [])
    (hs : step1 e y R) : R y := by
  unfold step1 at hs
  rw [step_of_directivesFromAddress_nil h] at hs
  exact hs

/-- `hstop` of `merged_link_halt` at the end address of a laid-out program
whose last cell is not a label: every merged step there stutters. -/
theorem step1W_stop_of_end [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive} (L : SharedLayout)
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    ∀ y R, y.2 = (layout p).addrOf p.length → step1W L (layout p) y R → R y := by
  intro y R hy hs
  refine step1W_stop_of_directivesFromAddress_nil ?_ hs
  rw [hy]
  exact Executable.directivesFromAddress_end hlast hd

/-- At the end address of a laid-out program whose last cell is not a label,
a single step stutters. -/
theorem step1_stop_of_end [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive}
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    ∀ y R, y.2 = (layout p).addrOf p.length → step1 (layout p) y R → R y := by
  intro y R hy hs
  refine step1_stop_of_directivesFromAddress_nil ?_ hs
  rw [hy]
  exact Executable.directivesFromAddress_end hlast hd

/-- At the end address of a laid-out program whose last cell is not a label
there is no instruction step. -/
theorem not_instrStep_of_end [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive}
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    ∀ y R, y.2 = (layout p).addrOf p.length → ¬ (layout p).instrStep y R := by
  intro y R hy
  refine not_instrStep_of_directivesFromAddress_nil ?_
  rw [hy]
  exact Executable.directivesFromAddress_end hlast hd

/-! ## Behind the text, past trailing labels

A program may end in labels (`... done:`): they sit at the end address, so the
text laid out from there is not empty but holds labels only. A step there
still stutters and no instruction runs. Here the last instruction is the cell
`p.length - 1 - k`, followed by `k` labels; with `k := 0` this is the
situation of `step1W_stop_of_end`. -/

/-- Behind the last instruction of a laid-out program, followed by `k` labels
only, every cell laid out from the end address is a label of size `0`. -/
theorem directivesFromAddress_end_labels [layout : _root_.Layout] {p : Program}
    [hv : Executable.ValidLayout (layout p)] {dlast : Directive} (k : Nat)
    (hlast : p[p.length - 1 - k]? = some dlast) (hd : dlast.isLabel = false)
    (hls : (p.drop (p.length - k)).all Directive.isLabel = true) :
    ∀ c ∈ (layout p).directivesFromAddress ((layout p).addrOf p.length),
      c.1.isLabel = true ∧ c.2 = 0 := by
  have hcell : ∀ i, (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
    intro i
    rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]
  have hlen : (layout p).2.length = p.length := by
    rw [Layout.apply_snd, Layout.frag_length]
  have hlab : ∀ i, p.length - k ≤ i → ∀ d, p[i]? = some d → d.isLabel = true := by
    intro i hi d h
    have hmem : d ∈ p.drop (p.length - k) := by
      rw [List.mem_iff_getElem?]
      refine ⟨i - (p.length - k), ?_⟩
      rw [List.getElem?_drop, show p.length - k + (i - (p.length - k)) = i by omega]
      exact h
    exact List.all_eq_true.mp hls d hmem
  have hk : k < p.length := by
    refine Nat.lt_of_not_le fun hk => ?_
    have := hlab (p.length - 1 - k) (by omega) dlast hlast
    rw [hd] at this
    cases this
  have hlsize : ∀ i, p.length - k ≤ i → ∀ c, (layout p).2[i]? = some c → c.1.isLabel = true ∧ c.2 = 0 := by
    intro i hi c hc
    obtain ⟨d, z⟩ := c
    have hc' := hc
    rw [hcell] at hc'
    cases hpi : p[i]? with
    | none => rw [hpi] at hc'; cases hc'
    | some d' =>
      rw [hpi] at hc'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc'
      obtain ⟨rfl, rfl⟩ := hc'
      have hl := hlab i hi _ hpi
      refine ⟨hl, ?_⟩
      cases d' with
      | label l => exact hv.label_size i l _ hc
      | instr _ => simp [Directive.isLabel] at hl
      | byteArray _ => simp [Directive.isLabel] at hl
  have hj : ∀ m, m ≤ k → (layout p).addrOf (p.length - k) = (layout p).addrOf (p.length - k + m) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      obtain ⟨⟨d, z⟩, hc⟩ : ∃ c, (layout p).2[p.length - k + m]? = some c :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hz := (hlsize _ (by omega) _ hc).2
      simp only at hz
      rw [ih (by omega), ← Nat.add_assoc, Executable.addrOf_succ (layout p) hc, hz]
      simp
  have hjend := hj k (Nat.le_refl k)
  rw [show p.length - k + k = p.length by omega] at hjend
  have hprev : (layout p).2[p.length - k - 1]? = some (dlast, Kraken.Layout.size Directive (p.length - 1 - k)) := by
    rw [hcell, show p.length - k - 1 = p.length - 1 - k by omega, hlast]
    rfl
  have hseg := Executable.directivesFromAddress_addrOf_first (layout p) (p.length - k) p.length
    (by omega) (by omega) hjend (by
      intro k' hk'
      rw [← hjend]
      refine Executable.addrOf_ne_of_valid (layout p) hk' (by rw [hprev]; rfl) ?_
      intro l z hz
      rw [hprev] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at hz
      rw [hz.1] at hd
      simp [Directive.isLabel] at hd)
  intro c hc
  rw [hseg] at hc
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
  rw [List.getElem?_drop] at hi
  exact hlsize _ (by omega) c hi

/-- Where only labels are laid out from the pc, a step returns the state it
started from. -/
theorem step_of_directivesFromAddress_labels {e : _root_.Executable} {y : MachineState}
    (h : ∀ c ∈ Kraken.Executable.directivesFromAddress e y.2, c.1.isLabel = true ∧ c.2 = 0)
    (ret : MachineState → Effects) :
    Executable.step e y ret = ret y := by
  have hat : ∀ c ∈ Kraken.Executable.directivesAtAddress e y.2, c.1.isLabel = true ∧ c.2 = 0 := by
    intro c hc
    refine h c ?_
    unfold Kraken.Executable.directivesAtAddress at hc
    unfold Kraken.Executable.directivesFromAddress
    exact List.map_subset _ (List.takeWhile_sublist _).subset hc
  unfold Executable.step
  letI := _root_.Executable.labels e
  show Directives.interp (Kraken.Executable.directivesAtAddress e y.2) y.1 y.2 (fun pc s => ret (s, pc)) = ret y
  rw [← List.append_nil (Kraken.Executable.directivesAtAddress e y.2),
    Directives.interp_label_prefix _ _ _ _ _ hat]
  rfl

/-- Where only labels are laid out from the pc, there is no cell to run. -/
theorem codeAt_of_directivesFromAddress_labels {e : Kraken.Executable Directive} {a : Int64}
    (h : ∀ c ∈ e.directivesFromAddress a, c.1.isLabel = true ∧ c.2 = 0) : e.codeAt a = [] := by
  unfold Kraken.Executable.codeAt
  generalize e.directivesFromAddress a = l at h ⊢
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.dropWhile_cons, ite_eq_left (by simp [(h c List.mem_cons_self).1])]
    exact ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')

/-- `hstop` of `merged_link_halt` at the end address of a laid-out program
whose last instruction is followed by `k` labels (`... done:`): every merged
step there stutters. `step1W_stop_of_end` is the case `k = 0`. -/
theorem step1W_stop_of_end_labels [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive} (L : SharedLayout) (k : Nat)
    (hlast : p[p.length - 1 - k]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl)
    (hls : (p.drop (p.length - k)).all Directive.isLabel = true := by rfl) :
    ∀ y R, y.2 = (layout p).addrOf p.length → step1W L (layout p) y R → R y := by
  intro y R hy hs
  unfold step1W at hs
  rw [step_of_directivesFromAddress_labels (by rw [hy]; exact directivesFromAddress_end_labels k hlast hd hls)] at hs
  exact hs

/-- At the end address of a laid-out program whose last instruction is
followed by `k` labels there is no instruction step. -/
theorem not_instrStep_of_end_labels [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive} (k : Nat)
    (hlast : p[p.length - 1 - k]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl)
    (hls : (p.drop (p.length - k)).all Directive.isLabel = true := by rfl) :
    ∀ y R, y.2 = (layout p).addrOf p.length → ¬ (layout p).instrStep y R := by
  rintro y R hy ⟨d, z, rest, hcode, -⟩
  rw [hy, codeAt_of_directivesFromAddress_labels (directivesFromAddress_end_labels k hlast hd hls)] at hcode
  cases hcode

/-! ## The premises of the merged link -/

open MachineWP in
/-- A triple on a laid-out program gives the `hP`, `hstop` and `hev` premises
of `merged_link_halt` at `endPc := (layout p).addrOf p.length`, from the start
address, given the access discipline as an invariant `Inv` (as in
`eventually_step1W`): `P` is the triple's postcondition at `endPc`. -/
theorem merged_premises_of_triple [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {L : SharedLayout} {Inv : MachineState → Prop}
    {P : MachineData → Prop} {Q : Unit → MachineData → Prop} {s : MachineData} {dlast : Directive}
    (ht : ⦃ P ⦄ p ⦃ Q ⦄) (hs : P s)
    (hpres : ∀ s R, Inv s → step1 (layout p) s R → step1 (layout p) s (fun s' => R s' ∧ Inv s'))
    (hacc : ∀ s, Inv s → (Executable.step (layout p) s .done).AllW L (fun _ => True))
    (h0 : Inv (s, Kraken.Layout.start Directive))
    (henv : cenv = layout p := by rfl)
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    (∀ y : MachineState, (y.2 = (layout p).addrOf p.length ∧ Q () y.1) → y.2 = (layout p).addrOf p.length) ∧
      (∀ y R, y.2 = (layout p).addrOf p.length → step1W L (layout p) y R → R y) ∧
      Eventually (step1W L (layout p)) (fun y => y.2 = (layout p).addrOf p.length ∧ Q () y.1)
        (s, Kraken.Layout.start Directive) :=
  ⟨fun _ hy => hy.1, step1W_stop_of_end L hlast hd,
    eventually_step1W_of_instrStep hpres hacc (Program.instrStep_of_triple ht hs henv) h0⟩

end Kraken.Promising.AArch64

/-! ## The environment twin -/

/-- A triple with the environment on a laid-out program, read at the machine:
from the start address the machine, its environment state threaded through,
reaches the end of the text with `Q`, or stops at an address satisfying `E`.
The twin of `Program.instrStep_of_triple_exits`. -/
theorem Program.instrStepEnv_of_tripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {env : SharedEnv} {P : MachineData → env.State → Prop}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (ht : MachineWP.TripleEnv env P p Q E) (hs : P s g)
    (henv : cenv = layout p := by rfl) :
    Eventually ((layout p).instrStepEnv env)
      (fun x => (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2)
      ((s, Kraken.Layout.start Directive), g) := by
  have h : (layout p).wpEnv env p Q E s g := henv ▸ ht s g hs
  obtain ⟨hsits, hafter⟩ := Executable.walk_addrOf (p := p) p [] 0 (by simp)
  rw [Nat.zero_add] at hafter
  have hev := h ((layout p).addrOf 0) hsits
  rwa [hafter, Executable.addrOf_zero, Layout.apply_fst] at hev
