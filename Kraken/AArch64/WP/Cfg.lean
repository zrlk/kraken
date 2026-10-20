/-
Copied from x64's `Kraken/MachineWP.lean` at commit `87e2e12`, adapted for
AArch64: the sections "Linking fragments" (`Program.Cont`, `Program.link_at`,
`Program.link`), "The control-flow rule" (`Program.PlacedIn`/`Placed`,
`Program.placed_of_layout`, `Table.ofLabels`, `MachineWP.cfg`) and "The
control-flow rule for a procedure" (`cfg_reach(_at)`, `ProcSpec.of_cfg(_at,
_post)`, `ProcSpecK.of_cfg(_exists)`, `cfg_blocks_exists`). The statements and
proofs are x64's verbatim: they are typed by the root-level names the two
interpreters share. They live here rather than in `MachineWP.lean` because
`placed_of_layout` walks a laid-out program with `Kraken.AArch64.WP.Bridge`'s
`Executable.walk_addrOf`, `entry_of_sits` and `Program.label_addrOf_drop`,
and `Bridge` imports `MachineWP`. `TripleAt` is in `MachineWP.lean`; the
splitting tactic `cfg_cases` is in `Kraken.AArch64.WP.Blocks`.
-/
import Kraken.AArch64.WP.Bridge

open Kraken
open Std.WP
open Lean.Order

/-! ## Walking a laid-out program, by position

Three facts of `Bridge`'s walk that are private there, restated for
`placed_of_layout`. -/

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

/-! ## Linking fragments

`Program.link` ties finitely or infinitely many separately verified
fragments into one run. Each index `i` names a placed fragment: its text
`frag i` and the address `entry i` where it starts. The address behind it is
derived, `cenv.after`. `T i` is the invariant at that entry, and
`r` orders index-state pairs. A fragment's obligation is a Triple, so `vcgen`
proves it; `link` supplies the well-founded induction that a back edge
needs. -/

/-- Where a step out of fragment `i`, entered in state `s₀`, may land: the
global postcondition at the address it stopped at, or another fragment's
entry, with that fragment's invariant and a smaller measure. -/
def Program.Cont {ι : Type} (post : @Post MachineState) (entry : ι → Int64)
    (T : ι → MachineData → Prop) (r : ι × MachineData → ι × MachineData → Prop)
    (i : ι) (s₀ : MachineData) (a : Int64) (s : MachineData) : Prop :=
  post (s, a) ∨ ∃ j, entry j = a ∧ T j s ∧ r (j, s) (i, s₀)

open MachineWP in
/-- `Program.link` with each fragment's obligation at its entry address, so
that a fragment may read the pc. -/
theorem Program.link_at [CodeEnv] {ι : Type} {post : @Post MachineState}
    (frag : ι → Program) (entry : ι → Int64) (T : ι → MachineData → Prop)
    (r : ι × MachineData → ι × MachineData → Prop) (hwf : WellFounded r)
    (hplace : ∀ i, cenv.sits (entry i) (frag i))
    (hfrag : ∀ i s₀,
      TripleAt (entry i) (fun s => T i s ∧ s = s₀) (frag i)
        (fun _ s => Program.Cont post entry T r i s₀ (cenv.after (entry i) (frag i)) s)
        (fun a s => Program.Cont post entry T r i s₀ a s)) :
    ∀ i s, T i s → Eventually cenv.instrStep post (s, entry i) := by
  suffices h : ∀ is : ι × MachineData, T is.1 is.2 →
      Eventually cenv.instrStep post (is.2, entry is.1) by
    intro i s hT
    exact h (i, s) hT
  intro is
  induction is using hwf.induction with
  | _ is ih =>
    intro hT
    have hev := hfrag is.1 is.2 is.2 ⟨hT, rfl⟩ (hplace is.1)
    refine eventually_trans _ _ _ _ hev ?_
    rintro ⟨s', a⟩ (⟨ha, hc⟩ | hc)
    · subst ha
      rcases hc with hp | ⟨j, hj, hTj, hr⟩
      · exact Eventually.done _ hp
      · rw [← hj]
        exact ih (j, s') hr hTj
    · rcases hc with hp | ⟨j, hj, hTj, hr⟩
      · exact Eventually.done _ hp
      · dsimp only at hj
        rw [← hj]
        exact ih (j, s') hr hTj

open MachineWP in
theorem Program.link [CodeEnv] {ι : Type} {post : @Post MachineState}
    (frag : ι → Program) (entry : ι → Int64) (T : ι → MachineData → Prop)
    (r : ι × MachineData → ι × MachineData → Prop) (hwf : WellFounded r)
    (hplace : ∀ i, cenv.sits (entry i) (frag i))
    (hfrag : ∀ i s₀,
      ⦃ fun s => T i s ∧ s = s₀ ⦄
        frag i
      ⦃ fun _ s => Program.Cont post entry T r i s₀
          (cenv.after (entry i) (frag i)) s;
        fun a s => Program.Cont post entry T r i s₀ a s ⦄) :
    ∀ i s, T i s → Eventually cenv.instrStep post (s, entry i) :=
  Program.link_at frag entry T r hwf hplace (fun i s₀ => TripleAt.of_triple (hfrag i s₀))

/-! ## The control-flow rule

`Program.cfg` instantiates `link` at the blocks of a labeled program: the
index is the label, the entry is the label's address, the fragment is the
block body, and the order is the lex order of variant and block position.
`Program.Placed` collects the placement facts that connect the program's
syntax to the ambient addresses. -/

/-- Where the blocks of a fragment sit in the ambient code: every block at its
label's address, falling through to the address of the label behind it. This
much holds of one procedure inside a larger image, so it is what a procedure's
proof assumes (`Program.PlacedIn.of_placed` derives it from the image's
`Placed`). -/
structure Program.PlacedIn [CodeEnv] (p : Program) : Prop where
  /-- A block's body sits at its label's address. -/
  block : ∀ l blk, Program.blockAt p l = some blk →
    cenv.sits ((_root_.Executable.labels cenv).label l) blk.body
  /-- A block that falls into another ends at that block's address. -/
  next : ∀ l blk l', Program.blockAt p l = some blk → blk.next = some l' →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = (_root_.Executable.labels cenv).label l'

/-- Where a label's block sits in the ambient code, for the whole text. -/
structure Program.Placed [CodeEnv] (p : Program) (l₀ : Label) : Prop
    extends Program.PlacedIn p where
  /-- Every placement of the text starts at the entry label's address. -/
  entry : ∀ pc, cenv.sits pc p → (_root_.Executable.labels cenv).label l₀ = pc
  /-- The last block ends where the text ends. -/
  last : ∀ l blk, Program.blockAt p l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = cenv.after ((_root_.Executable.labels cenv).label l₀) p

/-- The placement facts of a laid-out program: every block sits at its label's
address, and falls through to the address of the label behind it. -/
theorem Program.placed_of_layout [layout : _root_.Layout] {p p' : Program}
    [Executable.ValidLayout (layout p)] {l₀ : Label} (hwf : Program.WF p)
    (hp : p = Directive.label l₀ :: p')
    (hne : p.any (fun d => !d.isLabel) = true) :
    @Program.Placed ⟨layout p⟩ p l₀ := by
  have hnd := hwf.nodup
  -- the entry label names the start of the text
  have hfl₀ : Program.fromLabel p l₀ = p := by
    have hlab : Program.labels p = l₀ :: Program.labels p' := by rw [hp]; rfl
    have hp' : Program.fromLabel p' l₀ = [] := by
      by_cases h : Program.fromLabel p' l₀ = []
      · exact h
      · exact absurd (Program.mem_labels_of_cell (Program.fromLabel_mem h))
          (by rw [hlab] at hnd; exact (List.nodup_cons.mp hnd).1)
    rw [hp, Program.fromLabel_cons, if_pos ⟨hp', rfl⟩]
  have hne₀ : Program.fromLabel p l₀ ≠ [] := by
    rw [hfl₀, hp]
    exact List.cons_ne_nil _ _
  have hentry : (_root_.Executable.labels (layout p)).label l₀ = (layout p).addrOf 0 :=
    Program.label_addrOf_drop hnd (l := l₀) (i := 0) (by rw [List.drop_zero, hfl₀]) hne₀
  have hwhole : (layout p).after ((layout p).addrOf 0) p
      = (layout p).addrOf p.length := by
    have h := (Executable.walk_addrOf (p := p) p [] 0 (by simp)).2
    rwa [Nat.zero_add] at h
  -- every block, at the position of its label cell
  have hpos : ∀ l blk, Program.blockAt p l = some blk →
      ∃ pos i, pos < p.length
        ∧ blk.next = ((Program.view p).2[i + 1]?).map (·.1)
        ∧ p.drop (pos + 1)
            = blk.body ++ ((Program.view p).2.drop (i + 1)).flatMap Program.blockCells
        ∧ (_root_.Executable.labels (layout p)).label l = (layout p).addrOf pos
        ∧ (layout p).sits ((layout p).addrOf pos) blk.body
        ∧ (layout p).after ((layout p).addrOf pos) blk.body
            = (layout p).addrOf (pos + 1 + blk.body.length) := by
    intro l blk hb
    obtain ⟨-, i, hi, hnext⟩ := Program.blockAtAux_spec hb
    have hne' : Program.fromLabel p l ≠ [] :=
      Program.fromLabel_ne_nil_of_mem (Program.blockAt_mem_labels hb)
    obtain ⟨t, rest, hsplit, hfl, -, -⟩ := Program.fromLabel_split hnd hne'
    have hdropt : p.drop t.length = Program.fromLabel p l := by
      conv => lhs; rw [hsplit]
      rw [List.drop_left, hfl]
    have hdrop : p.drop t.length
        = Directive.label l
          :: (blk.body ++ ((Program.view p).2.drop (i + 1)).flatMap Program.blockCells) := by
      rw [hdropt, Program.fromLabel_view hnd hi, Program.drop_flatMap_cons hi]
    have hlabel : (_root_.Executable.labels (layout p)).label l = (layout p).addrOf t.length :=
      Program.label_addrOf_drop hnd hdropt hne'
    have hcell : p[t.length]? = some (Directive.label l) := by
      have h0 : (p.drop t.length)[0]? = some (Directive.label l) := by rw [hdrop]; rfl
      rw [List.getElem?_drop] at h0
      simpa using h0
    have hlt : t.length < p.length := by
      by_cases h : t.length < p.length
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hcell; cases hcell
    have hstep : (layout p).addrOf (t.length + 1) = (layout p).addrOf t.length := by
      rw [addrOf_step hcell, size_label hcell]
      simp
    have hbody : p.drop (t.length + 1)
        = blk.body ++ ((Program.view p).2.drop (i + 1)).flatMap Program.blockCells := by
      rw [← List.drop_drop, hdrop]
      rfl
    obtain ⟨hsits, hafter⟩ := Executable.walk_addrOf blk.body _ (t.length + 1) hbody
    rw [hstep] at hsits hafter
    exact ⟨t.length, i, hlt, hnext, hbody, hlabel, hsits, hafter⟩
  refine @Program.Placed.mk ⟨layout p⟩ p l₀ (@Program.PlacedIn.mk ⟨layout p⟩ p ?block ?next)
    ?entry ?last
  case entry =>
    intro pc hplace
    rw [hentry]
    exact (Executable.entry_of_sits (List.countP_pos_iff.mpr (List.any_eq_true.mp hne))
      hplace).symm
  case block =>
    intro l blk hb
    obtain ⟨pos, i, -, -, -, hlabel, hsits, -⟩ := hpos l blk hb
    rw [hlabel]
    exact hsits
  case next =>
    intro l blk l' hb hn
    obtain ⟨pos, i, -, hnext, hbody, hlabel, -, hafter⟩ := hpos l blk hb
    show (layout p).after ((_root_.Executable.labels (layout p)).label l) blk.body = (_root_.Executable.labels (layout p)).label l'
    rw [hn] at hnext
    obtain ⟨⟨l₁, b₁⟩, hi'⟩ : ∃ lb, (Program.view p).2[i + 1]? = some lb := by
      cases h : (Program.view p).2[i + 1]? with
      | none => rw [h] at hnext; cases hnext
      | some lb => exact ⟨lb, rfl⟩
    rw [hi'] at hnext
    simp only [Option.map_some, Option.some.injEq] at hnext
    subst hnext
    have htail : p.drop (pos + 1 + blk.body.length) = Program.fromLabel p l' := by
      rw [← List.drop_drop, hbody, List.drop_left, Program.fromLabel_view hnd hi']
    have hne' : Program.fromLabel p l' ≠ [] := by
      rw [Program.fromLabel_view hnd hi', Program.drop_flatMap_cons hi']
      exact List.cons_ne_nil _ _
    rw [hlabel, hafter, Program.label_addrOf_drop hnd htail hne']
  case last =>
    intro l blk hb hn
    obtain ⟨pos, i, hlt, hnext, hbody, hlabel, -, hafter⟩ := hpos l blk hb
    show (layout p).after ((_root_.Executable.labels (layout p)).label l) blk.body
      = (layout p).after ((_root_.Executable.labels (layout p)).label l₀) p
    rw [hn] at hnext
    have hnone : (Program.view p).2[i + 1]? = none := by
      cases h : (Program.view p).2[i + 1]? with
      | none => rfl
      | some lb => rw [h] at hnext; cases hnext
    have hdropnil : (Program.view p).2.drop (i + 1) = [] :=
      List.drop_eq_nil_of_le (by
        by_cases hle : (Program.view p).2.length ≤ i + 1
        · exact hle
        · rw [List.getElem?_eq_getElem (by omega)] at hnone; cases hnone)
    rw [hdropnil] at hbody
    simp only [List.flatMap_nil, List.append_nil] at hbody
    have hlenb : pos + 1 + blk.body.length = p.length := by
      have h := congrArg List.length hbody
      rw [List.length_drop] at h
      omega
    rw [hlabel, hafter, hlenb, ← hwhole, hentry]

/-- The blocks of `p` are among those of `q`: same bodies, and the same
successor wherever `p` has one. Decidable, so `by decide` closes it for
closed texts; it holds when `p` is a run of whole blocks of `q`. -/
def Program.subBlocksOf (p q : Program) : Bool :=
  (Program.view p).2.all fun lb =>
    match Program.blockAt p lb.1, Program.blockAt q lb.1 with
    | some blk, some blk' =>
      decide (blk'.body = blk.body) && (blk.next.isNone || decide (blk'.next = blk.next))
    | _, _ => false

/-- A fragment whose blocks are among a placed text's is placed. -/
theorem Program.PlacedIn.of_placed [CodeEnv] {p q : Program} {m₀ : Label}
    (hq : Program.Placed q m₀) (h : Program.subBlocksOf p q = true) : Program.PlacedIn p := by
  have key : ∀ l blk, Program.blockAt p l = some blk →
      ∃ blk', Program.blockAt q l = some blk' ∧ blk'.body = blk.body
        ∧ (blk.next.isNone = true ∨ blk'.next = blk.next) := by
    intro l blk hb
    have hmem : l ∈ (Program.view p).2.map (·.1) := by
      rw [← Program.labels_view]
      exact Program.blockAt_mem_labels hb
    obtain ⟨lb, hlb, rfl⟩ := List.mem_map.mp hmem
    have hall := List.all_eq_true.mp h lb hlb
    simp only [hb] at hall
    cases hb' : Program.blockAt q lb.1 with
    | none => rw [hb'] at hall; cases hall
    | some blk' =>
      rw [hb'] at hall
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hall
      exact ⟨blk', rfl, hall.1, hall.2⟩
  refine ⟨?_, ?_⟩
  · intro l blk hb
    obtain ⟨blk', hb', hbody, -⟩ := key l blk hb
    rw [← hbody]
    exact hq.block l blk' hb'
  · intro l blk l' hb hn
    obtain ⟨blk', hb', hbody, hnext⟩ := key l blk hb
    rw [hn] at hnext
    simp only [Option.isNone_some, Bool.false_eq_true, false_or] at hnext
    rw [← hbody]
    exact hq.next l blk' l' hb' hnext

/-- A label-keyed table, read at an address. -/
def Table.ofLabels [CodeEnv] (tl : Label → MachineData → Prop) :
    Int64 → MachineData → Prop :=
  fun a s => ∃ l, (_root_.Executable.labels cenv).label l = a ∧ tl l s

@[grind ←] theorem Table.ofLabels_at [CodeEnv] {tl : Label → MachineData → Prop}
    {l : Label} {s : MachineData} (h : tl l s) :
    Table.ofLabels tl ((_root_.Executable.labels cenv).label l) s := ⟨l, rfl, h⟩

/-- The block a block falls into: it is mapped, and it sits one position
later in the text. -/
theorem Program.blockAt_next {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk)
    {l' : Label} (hn : blk.next = some l') :
    (Program.blockAt p l').isSome ∧ Program.blockIdx p l' = Program.blockIdx p l + 1 := by
  obtain ⟨-, i, hi, hnext⟩ := Program.blockAtAux_spec h
  rw [hn] at hnext
  have hndv : ((Program.view p).2.map (·.1)).Nodup := by rwa [← Program.labels_view]
  cases hj : (Program.view p).2[i + 1]? with
  | none => rw [hj] at hnext; cases hnext
  | some lb =>
    obtain ⟨l₁, b₁⟩ := lb
    rw [hj] at hnext
    simp only [Option.map_some, Option.some.injEq] at hnext
    subst hnext
    refine ⟨?_, ?_⟩
    · show (Program.blockAtAux (Program.view p).2 l').isSome = true
      rw [Program.blockAtAux_of_getElem hndv hj]
      rfl
    · rw [Program.blockIdx_eq hnd hj, Program.blockIdx_eq hnd hi]

/-- A mapped label sits inside the block list. -/
theorem Program.blockIdx_lt {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk) :
    Program.blockIdx p l < (Program.view p).2.length := by
  obtain ⟨-, i, hi, -⟩ := Program.blockAtAux_spec h
  rw [Program.blockIdx_eq hnd hi]
  by_cases hlt : i < (Program.view p).2.length
  · exact hlt
  · rw [List.getElem?_eq_none (by omega)] at hi
    cases hi

/-- The block index never exceeds the number of blocks. -/
theorem Program.blockIdx_le (p : Program) (l : Label) :
    Program.blockIdx p l ≤ (Program.view p).2.length := by
  have h := List.idxOf_le_length (a := l) (l := Program.labels p)
  have hlen : (Program.labels p).length = (Program.view p).2.length := by
    rw [Program.labels_view, List.length_map]
  rw [hlen] at h
  exact h

/-- The lex order of the control-flow rule, encoded in one number: the
variant dominates, and the block position breaks ties. -/
private def Program.cfgMeasure (p : Program) (var : Label → MachineData → Nat)
    (x : Label × MachineData) : Nat :=
  var x.1 x.2 * ((Program.view p).2.length + 1)
    + ((Program.view p).2.length - Program.blockIdx p x.1)

/-- The control-flow rule: one spec table `T`, one variant `var`, one triple
per block of the map `Program.blockAt`. Each block is entered with its table
entry and the variant snapshotted; it falls into the next block with the
entry there and the variant not increased, and a jump exit lands on a mapped
table entry along `Program.EdgeLt`. -/
theorem MachineWP.cfg [CodeEnv] {p p' : Program} {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => Q);
        Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T l' s
          ∧ Program.EdgeLt p var l n l' s) ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.Placed p l₀ := by
      first
        | assumption
        | exact Program.placed_of_layout (by decide) (by rfl) (by decide))
    (hP : P = T l₀ := by rfl) :
    ⦃ P ⦄ p ⦃ Q ⦄ := by
  subst hP
  have hnd := hwf.nodup
  refine Triple.intro fun s hT => ?_
  intro pc hplace
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length :=
    Program.blockIdx_le p
  have key := Program.link (post := fun st => st.2 = cenv.after pc p ∧ Q () st.1)
    (frag := fun l => (Program.blockAt p l).elim [] (·.body))
    (entry := fun l => (_root_.Executable.labels cenv).label l)
    (T := fun l s => (Program.blockAt p l).isSome ∧ T l s)
    (r := fun x y => Program.cfgMeasure p var x < Program.cfgMeasure p var y)
    (measure (Program.cfgMeasure p var)).wf ?_ ?_
  · have h0 : (Program.blockAt p l₀).isSome := by
      rw [hp]
      show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
      simp [Program.view, Program.blockAtAux]
    have hrun := key l₀ s ⟨h0, hT⟩
    rw [hpl.entry pc hplace] at hrun
    exact eventually_weaken _ _ _ _ (fun st hst => Or.inl hst) hrun
  · intro l
    cases hb : Program.blockAt p l with
    | none => exact trivial
    | some blk => simpa using hpl.block l blk hb
  · intro l s₀
    cases hb : Program.blockAt p l with
    | none =>
      exact Triple.intro fun s hpre => absurd hpre.1.1 (by simp [hb])
    | some blk =>
      simp only [Option.elim]
      refine Triple.intro fun s hpre => ?_
      obtain ⟨⟨-, hTl⟩, rfl⟩ := hpre
      have hidx : Program.blockIdx p l < (Program.view p).2.length :=
        Program.blockIdx_lt hnd hb
      refine Executable.wp_mono ?_ ?_ ((hblocks l blk hb (var l s)).le_wp s ⟨hTl, rfl⟩)
      · intro s' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hTl', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hb hnx
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hTl'⟩, ?_⟩
          have hmul : var l' s' * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hvar
          simp only [Program.cfgMeasure]
          omega
        | none =>
          rw [hnx] at hq
          have hend : cenv.after ((_root_.Executable.labels cenv).label l) blk.body = cenv.after pc p := by
            rw [hpl.last l blk hb hnx, hpl.entry pc hplace]
          exact Or.inl ⟨hend.symm ▸ rfl, hq⟩
      · rintro a s' ⟨l', hlab, hsome', hTl', hedge⟩
        refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
        have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
        simp only [Program.cfgMeasure]
        rcases hedge with hlt | ⟨heq, hij⟩
        · have hmul : (var l' s' + 1) * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hlt
          have hsucc : (var l' s' + 1) * ((Program.view p).2.length + 1)
              = var l' s' * ((Program.view p).2.length + 1)
                + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
          omega
        · rw [heq]
          omega

/-! ## The control-flow rule for a procedure

`cfg` concludes a triple on the whole text, which needs the text to be the
whole placement (`Placed.entry`) and closes the exit channel. A procedure is
a fragment of a larger image that leaves through `ret` (or a tail jump), so
its rule, `cfg_reach`, takes `PlacedIn`, keeps the exit channel `E` open, and
concludes that the run from the entry label reaches `E`. `ProcSpec.of_cfg`
and `ProcSpecK.of_cfg` dress this as a procedure specification: the table
and the exits may mention the logical variable, the return address and the
entry state, and the exits are those the convention allows — by default a
return, `a = ra` with the postcondition; a tail call `jmp f` adds an exit at
`f`'s label discharged by `f`'s `ProcSpec` at the same `ra` (`hexit`). -/

/-- `cfg_reach` with each block's obligation a `TripleAt` its label's address,
so that a block may read the pc. `cfg` for a fragment with an open exit channel: entered at `l₀` with its
table entry, the run reaches `E`. The last block must not fall off the end. -/
theorem MachineWP.cfg_reach_at [CodeEnv] {p p' : Program} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (E : Int64 → MachineData → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      MachineWP.TripleAt ((_root_.Executable.labels cenv).label l)
        (fun s => T l s ∧ var l s = n) blk.body
        (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => fun _ _ => False)
        (fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ E a s))
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s, T l₀ s →
      Eventually cenv.instrStep (fun st => E st.2 st.1) (s, (_root_.Executable.labels cenv).label l₀) := by
  have hnd := hwf.nodup
  intro s hT
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length :=
    Program.blockIdx_le p
  have key := Program.link_at (post := fun st => E st.2 st.1)
    (frag := fun l => (Program.blockAt p l).elim [] (·.body))
    (entry := fun l => (_root_.Executable.labels cenv).label l)
    (T := fun l s => (Program.blockAt p l).isSome ∧ T l s)
    (r := fun x y => Program.cfgMeasure p var x < Program.cfgMeasure p var y)
    (measure (Program.cfgMeasure p var)).wf ?_ ?_
  · have h0 : (Program.blockAt p l₀).isSome := by
      rw [hp]
      show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
      simp [Program.view, Program.blockAtAux]
    exact key l₀ s ⟨h0, hT⟩
  · intro l
    cases hb : Program.blockAt p l with
    | none => exact trivial
    | some blk => simpa using hpl.block l blk hb
  · intro l s
    cases hb : Program.blockAt p l with
    | none =>
      exact fun _ hpre _ => absurd hpre.1.1 (by simp)
    | some blk =>
      simp only [Option.elim]
      have hidx : Program.blockIdx p l < (Program.view p).2.length :=
        Program.blockIdx_lt hnd hb
      refine MachineWP.TripleAt.pre ?_
        (MachineWP.TripleAt.mono ?_ ?_ (hblocks l blk hb (var l s)))
      · rintro s' ⟨⟨-, hTl⟩, rfl⟩
        exact ⟨hTl, rfl⟩
      · intro s' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hTl', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hb hnx
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hTl'⟩, ?_⟩
          have hmul : var l' s' * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hvar
          simp only [Program.cfgMeasure]
          omega
        | none =>
          rw [hnx] at hq
          exact hq.elim
      · rintro a s' (⟨l', hlab, hsome', hTl', hedge⟩ | hE)
        · refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
          have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
          simp only [Program.cfgMeasure]
          rcases hedge with hlt | ⟨heq, hij⟩
          · have hmul : (var l' s' + 1) * ((Program.view p).2.length + 1)
                ≤ var l s * ((Program.view p).2.length + 1) :=
              Nat.mul_le_mul_right _ hlt
            have hsucc : (var l' s' + 1) * ((Program.view p).2.length + 1)
                = var l' s' * ((Program.view p).2.length + 1)
                  + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
            omega
          · rw [heq]
            omega
        · exact Or.inl hE

/-- `cfg` for a fragment with an open exit channel: entered at `l₀` with its
table entry, the run reaches `E`. The last block must not fall off the end. -/
theorem MachineWP.cfg_reach [CodeEnv] {p p' : Program} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (E : Int64 → MachineData → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ E a s ⦄)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s, T l₀ s →
      Eventually cenv.instrStep (fun st => E st.2 st.1) (s, (_root_.Executable.labels cenv).label l₀) :=
  MachineWP.cfg_reach_at T var E
    (fun l blk hb n => MachineWP.TripleAt.of_triple (hblocks l blk hb n)) hp hwf hpl

open MachineWP in
/-- A procedure's spec from its blocks. `T x ra t₀ l` is the table entry at
label `l` for the logical variable `x`, the address `ra` to reach, and the
entry state `t₀`; `Exit` the exits the blocks may take besides jumps inside
the procedure, by default the return `a = ra ∧ Post x ra t₀ s`; `hexit` that
every exit reaches `ra` with `Post`, automatic for the default. The blocks
are discharged with `intro x ra t₀` and `cfg_cases`. -/
theorem Kraken.Executable.ProcSpec.of_cfg [CodeEnv] {p p' : Program} {l₀ : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (Exit : α → Int64 → MachineData → Int64 → MachineData → Prop :=
      fun x ra t₀ a s => a = ra ∧ Post x ra t₀ s)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit x ra t₀ a s ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hexit : ∀ x ra t₀ a s, Exit x ra t₀ a s →
      Eventually cenv.instrStep (fun st => st.2 = ra ∧ Post x ra t₀ st.1) (s, a) := by
      rintro x ra t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, h⟩)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label l₀) Pre Post := by
  intro x ra t ht
  have h := MachineWP.cfg_reach (T x ra t) var (Exit x ra t) (hblocks x ra t) hp hwf hpl t
    (hpre x ra t ht)
  exact eventually_trans _ _ _ _ h (fun st hst => hexit x ra t st.2 st.1 hst)

open MachineWP in
/-- `ProcSpec.of_cfg` with each block's obligation a `TripleAt` its label's
address, so that a block may read the pc (`lea_rip_disp_at`). A procedure's spec from its blocks. `T x ra t₀ l` is the table entry at
label `l` for the logical variable `x`, the address `ra` to reach, and the
entry state `t₀`; `Exit` the exits the blocks may take besides jumps inside
the procedure, by default the return `a = ra ∧ Post x ra t₀ s`; `hexit` that
every exit reaches `ra` with `Post`, automatic for the default. The blocks
are discharged with `intro x ra t₀` and `cfg_cases`. -/
theorem Kraken.Executable.ProcSpec.of_cfg_at [CodeEnv] {p p' : Program} {l₀ : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (Exit : α → Int64 → MachineData → Int64 → MachineData → Prop :=
      fun x ra t₀ a s => a = ra ∧ Post x ra t₀ s)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      TripleAt ((_root_.Executable.labels cenv).label l)
        (fun s => T x ra t₀ l s ∧ var l s = n) blk.body
        (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False)
        (fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit x ra t₀ a s))
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hexit : ∀ x ra t₀ a s, Exit x ra t₀ a s →
      Eventually cenv.instrStep (fun st => st.2 = ra ∧ Post x ra t₀ st.1) (s, a) := by
      rintro x ra t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, h⟩)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label l₀) Pre Post := by
  intro x ra t ht
  have h := MachineWP.cfg_reach_at (T x ra t) var (Exit x ra t) (hblocks x ra t) hp hwf hpl t
    (hpre x ra t ht)
  exact eventually_trans _ _ _ _ h (fun st hst => hexit x ra t st.2 st.1 hst)

open MachineWP in
/-- `ProcSpec.of_cfg` with the blocks returning through `Post'`, a form of
the postcondition in the terms the exit block leaves (a frame as the cells
the code used, say), and `hpost` recovering the specification's `Post` from
it: the exit counterpart of `hpre`. -/
theorem Kraken.Executable.ProcSpec.of_cfg_post [CodeEnv] {p p' : Program} {l₀ : Label}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : α → Int64 → MachineData → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ (a = ra ∧ Post' x ra t₀ s) ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hpost : ∀ x ra t₀ s, Post' x ra t₀ s → Post x ra t₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label l₀) Pre Post :=
  Kraken.Executable.ProcSpec.of_cfg T var (fun x ra t₀ a s => a = ra ∧ Post' x ra t₀ s) hblocks
    hpre (by rintro x ra t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, hpost x a t₀ s h⟩)
    hp hwf hpl

open MachineWP in
/-- `ProcSpec.of_cfg` for the continuation form: the table and the exits
mention the continuation `K` instead of a logical variable; the default exit
is the return into `K`. -/
theorem Kraken.Executable.ProcSpecK.of_cfg [CodeEnv] {p p' : Program} {l₀ : Label}
    {Spec : Int64 → (MachineData → Prop) → MachineData → Prop}
    (T : Int64 → (MachineData → Prop) → MachineData → Label → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (Exit : Int64 → (MachineData → Prop) → MachineData → Int64 → MachineData → Prop :=
      fun ra K _ a s => a = ra ∧ K s)
    (hblocks : ∀ (ra : Int64) (K : MachineData → Prop) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T ra K t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T ra K t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T ra K t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit ra K t₀ a s ⦄)
    (hpre : ∀ ra K t, Spec ra K t → T ra K t l₀ t)
    (hexit : ∀ ra K t₀ a s, Exit ra K t₀ a s →
      Eventually cenv.instrStep (fun st => st.2 = ra ∧ K st.1) (s, a) := by
      rintro ra K t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, h⟩)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpecK ((_root_.Executable.labels cenv).label l₀) Spec := by
  intro ra K t ht
  have h := MachineWP.cfg_reach (T ra K t) var (Exit ra K t) (hblocks ra K t) hp hwf hpl t
    (hpre ra K t ht)
  exact eventually_trans _ _ _ _ h (fun st hst => hexit ra K t st.2 st.1 hst)

open MachineWP in
/-- The block obligations of a table with an existential in front, `∃ x, W x ∧
T x l s`, from the obligations at each witness `x` (with `W x` in hand): the
blocks are proved as if `x` were a logical variable, and the exits of the
witness's table are mapped into the common exit `Exit'`. This is how a
`ProcSpecK` whose `Spec` quantifies the caller's data existentially is
established from blocks stated in that data (`ProcSpecK.of_cfg` with the
table `fun ra K t₀ l s => ∃ x, W ra K t₀ x ∧ T ra t₀ x l s`). -/
theorem MachineWP.cfg_blocks_exists [CodeEnv] {β : Type} {p : Program}
    (T : β → Label → MachineData → Prop) (W : β → Prop) (var : Label → MachineData → Nat)
    (Exit : β → Int64 → MachineData → Prop) (Exit' : Int64 → MachineData → Prop)
    (hblocks : ∀ x, W x → ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit x a s ⦄)
    (hexit : ∀ x, W x → ∀ a s, Exit x a s → Exit' a s) :
    ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => (∃ x, W x ∧ T x l s) ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => (∃ x, W x ∧ T x l' s) ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome
          ∧ (∃ x, W x ∧ T x l' s) ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit' a s ⦄ := by
  intro l blk hblk n
  refine Triple.intro fun s ⟨⟨x, hw, ht⟩, hv⟩ => ?_
  have h := (hblocks x hw l blk hblk n).le_wp s ⟨ht, hv⟩
  rw [MachineWP.wp_eq] at h ⊢
  refine Executable.wp_mono ?_ ?_ h
  · intro s' hq
    revert hq
    cases blk.next with
    | some l' => exact fun hq => ⟨⟨x, hw, hq.1⟩, hq.2⟩
    | none => exact fun hq => hq
  · rintro a s' (⟨l', hl, hsome, ht', he⟩ | hex)
    · exact Or.inl ⟨l', hl, hsome, ⟨x, hw, ht'⟩, he⟩
    · exact Or.inr (hexit x hw a s' hex)

open MachineWP in
/-- `ProcSpec.of_cfg_post` for a `ProcSpecK` whose `Spec` quantifies the
caller's data existentially: `Spec ra K t` gives a witness `x` with `W ra K t
x` (the data's side conditions, and the continuation's: `∀ s', Post' x ra t s'
→ K s'`) and the entry `T x ra t l₀ t`. The table and the exit are stated in
`x` as a logical variable, so the block obligations are the ones of the ghost
style, verbatim, with `W` in hand (a recursive procedure's bound lives there). -/
theorem Kraken.Executable.ProcSpecK.of_cfg_exists [CodeEnv] {p p' : Program} {l₀ : Label}
    {β : Type} {Spec : Int64 → (MachineData → Prop) → MachineData → Prop}
    (T : β → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : β → Int64 → MachineData → MachineData → Prop)
    (W : Int64 → (MachineData → Prop) → MachineData → β → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : β) (ra : Int64) (K : MachineData → Prop) (t₀ : MachineData),
      W ra K t₀ x → ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ (a = ra ∧ Post' x ra t₀ s) ⦄)
    (hpre : ∀ ra K t, Spec ra K t → ∃ x, W ra K t x ∧ T x ra t l₀ t)
    (hpost : ∀ ra K t₀ x, W ra K t₀ x → ∀ s, Post' x ra t₀ s → K s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpecK ((_root_.Executable.labels cenv).label l₀) Spec :=
  Kraken.Executable.ProcSpecK.of_cfg
    (fun ra K t₀ l s => ∃ x, W ra K t₀ x ∧ T x ra t₀ l s) var
    (fun ra K _ a s => a = ra ∧ K s)
    (fun ra K t₀ => MachineWP.cfg_blocks_exists (fun x l s => T x ra t₀ l s) (W ra K t₀) var
      (fun x a s => a = ra ∧ Post' x ra t₀ s) (fun a s => a = ra ∧ K s)
      (fun x hw => hblocks x ra K t₀ hw)
      (fun x hw a s h => ⟨h.1, hpost ra K t₀ x hw s h.2⟩))
    hpre (by rintro ra K t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, h⟩) hp hwf hpl

