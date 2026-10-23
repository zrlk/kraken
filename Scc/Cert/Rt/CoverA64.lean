import Scc.Cert.Rt.OffsA64

/-!
# Every instruction of the program in the block table

`blocksIn` (`Scc/Cert/Rt/CodeA64.lean`) checks the rows of a block table
that exist; an empty table passes it. The generic proof needs a row, or a
single instruction it takes on its own, for every instruction it runs, so
A3 also checks **coverage**, `coverOk prog gs`:

* every instruction follows a label or an instruction (`led`): it is in
  the run of instructions after a label;
* in one pass over the program like `slices` (`cover`), at the first
  occurrence of each label, in program order, the next group of the table
  if it is that label's, and then its rows and its single instructions
  (`OGrp.ev`) **tile** the label's run (`Tiles`, checked by `tile`): in
  address order, from its start to its end, without gaps or overlaps, each
  row nonempty;
* at any other label (no group, or a repeated name) an empty run;
* every single instruction is one the block lemmas do not cover
  (`classify d = none`), or a stack switch `add sp, Xn, #0` (`evOk`): a
  covered instruction left out of the rows fails;
* no group left at the end.

`coverOk_sound` gives each group's tiling of its label's run, every
nonempty run's label a group and its first occurrence, and every
instruction in a run; `inRow_of_coverOk` puts every instruction of the
program in a row or a single instruction of the group of its run.

The check is linear: each label is encoded once (`key`), and `tile` visits
each instruction of a run once, counting down the instructions left in the
current row. -/

namespace Scc.Cert.Rt.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64.Flow

/-! ## Single instructions -/

/-- A stack switch, `add sp, Xn, #0`. -/
def isSwitch : Directive → Bool
  | .instr ⟨.W64, .ADD_e (.low .SP .W64) (.low (.reg _) .W64) (.imm ⟨.int64 n, .S0⟩)⟩ => n == 0
  | _ => false

/-- **An instruction a group may leave out of its rows**: one the block
lemmas do not cover, or a stack switch. -/
def evOk (d : Directive) : Bool :=
  match classify d with
  | none => true
  | some _ => isSwitch d

/-! ## Tilings -/

/-- **The rows `bs` and the single instructions `ev` tile the run `r`**
starting at index `n`: in order, either the next row starts at `n`, is
nonempty and within `r`, or the next single instruction is at `n` and
allowed (`evOk`); nothing is left at the end. -/
inductive Tiles : List OBlk → List Nat → Nat → List Directive → Prop
  | nil {n : Nat} : Tiles [] [] n []
  | row {b : OBlk} {bs : List OBlk} {ev : List Nat} {n : Nat} {r : List Directive} :
      b.k = n → b.blk ≠ [] → b.blk.length ≤ r.length →
      Tiles bs ev (n + b.blk.length) (r.drop b.blk.length) → Tiles (b :: bs) ev n r
  | ev {bs : List OBlk} {ev : List Nat} {n : Nat} {d : Directive} {r : List Directive} :
      evOk d = true → Tiles bs ev (n + 1) r → Tiles bs (n :: ev) n (d :: r)

/-- **Every instruction of a tiled run** is in a row, or a single
instruction, allowed. -/
theorem Tiles.cover {bs : List OBlk} {ev : List Nat} {n : Nat} {r : List Directive} (h : Tiles bs ev n r) :
    ∀ i (d : Directive), r[i]? = some d →
      (∃ b ∈ bs, b.k ≤ n + i ∧ n + i < b.k + b.blk.length) ∨ (n + i ∈ ev ∧ evOk d = true) := by
  induction h with
  | nil => intro i d hd; simp at hd
  | @row b bs ev n r hk hne hlen _ ih =>
    intro i d hd
    by_cases hb : i < b.blk.length
    · exact .inl ⟨b, List.mem_cons_self, by omega, by omega⟩
    · have hd' : (r.drop b.blk.length)[i - b.blk.length]? = some d := by
        rw [List.getElem?_drop, show b.blk.length + (i - b.blk.length) = i by omega, hd]
      have := ih (i - b.blk.length) d hd'
      rw [show n + b.blk.length + (i - b.blk.length) = n + i by omega] at this
      rcases this with ⟨b', hb', h1, h2⟩ | he
      · exact .inl ⟨b', List.mem_cons_of_mem _ hb', h1, h2⟩
      · exact .inr he
  | @ev bs ev n d₀ r hd₀ _ ih =>
    intro i d hd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      exact .inr ⟨by simp, hd₀⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hd
      have := ih i d hd
      rw [show n + 1 + i = n + (i + 1) by omega] at this
      rcases this with hb | ⟨he, hok⟩
      · exact .inl hb
      · exact .inr ⟨List.mem_cons_of_mem _ he, hok⟩

/-! ## The tiling check -/

/-- One step of `tile` at the instruction `d` of index `n`, `c`
instructions of the current row left: the row's next one; else the next
row if it starts here; else the next single instruction if it is here and
allowed. -/
def tileStep (d : Directive) (r : List OBlk → List Nat → Nat → Nat → Bool)
    (bs : List OBlk) (ev : List Nat) (n c : Nat) : Bool :=
  cond (Nat.beq c 0)
    (match bs with
     | b :: bs' =>
       cond (Nat.beq b.k n)
         (cond (Nat.beq b.blk.length 0) false (r bs' ev (n + 1) (b.blk.length - 1)))
         (match ev with
          | e :: ev' => Nat.beq e n && evOk d && r bs ev' (n + 1) 0
          | [] => false)
     | [] =>
       match ev with
       | e :: ev' => Nat.beq e n && evOk d && r bs ev' (n + 1) 0
       | [] => false)
    (r bs ev (n + 1) (c - 1))

/-- The end of `tile`: no row, no single instruction, nothing left of a
row. -/
def tileEnd (bs : List OBlk) (ev : List Nat) (c : Nat) : Bool :=
  match bs, ev with
  | [], [] => Nat.beq c 0
  | _, _ => false

/-- `tile` for the code generator. -/
def tileImpl : List Directive → List OBlk → List Nat → Nat → Nat → Bool
  | [], bs, ev, _, c => tileEnd bs ev c
  | d :: ds, bs, ev, n, c => tileStep d (tileImpl ds) bs ev n c

/-- **The tiling of a run, checked**: `tile r bs ev n 0` walks the run `r`
from index `n`. -/
@[implemented_by tileImpl]
def tile (r : List Directive) : List OBlk → List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List OBlk → List Nat → Nat → Nat → Bool)
    (fun bs ev _ c => tileEnd bs ev c) (fun d _ r => tileStep d r) r

theorem tile_sound : ∀ (r : List Directive) (bs : List OBlk) (ev : List Nat) (n c : Nat),
    tile r bs ev n c = true → c ≤ r.length ∧ Tiles bs ev (n + c) (r.drop c)
  | [], bs, ev, n, c, h => by
    change tileEnd bs ev c = true at h
    unfold tileEnd at h
    split at h
    · have : c = 0 := Nat.eq_of_beq_eq_true h
      subst this; exact ⟨Nat.le_refl _, .nil⟩
    · cases h
  | d :: ds, bs, ev, n, c, h => by
    change tileStep d (tile ds) bs ev n c = true at h
    unfold tileStep at h
    cases hc : Nat.beq c 0
    · rw [hc, Bool.cond_false] at h
      have hc' : c ≠ 0 := fun h0 => by simp [h0] at hc
      obtain ⟨h1, h2⟩ := tile_sound ds bs ev (n + 1) (c - 1) h
      refine ⟨by simp only [List.length_cons]; omega, ?_⟩
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [List.drop_succ_cons, show n + (c' + 1) = n + 1 + c' by omega]
      simpa using h2
    · rw [hc, Bool.cond_true] at h
      have hc0 : c = 0 := Nat.eq_of_beq_eq_true hc
      subst hc0
      refine ⟨Nat.zero_le _, ?_⟩
      simp only [Nat.add_zero, List.drop_zero]
      -- the single-instruction case, shared by both branches
      have hev : ∀ (bs : List OBlk) (ev : List Nat),
          (match ev with
           | e :: ev' => Nat.beq e n && evOk d && tile ds bs ev' (n + 1) 0
           | [] => false) = true → Tiles bs ev n (d :: ds) := by
        intro bs ev h
        split at h
        · rename_i e ev'
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨he, hok⟩, ht⟩ := h
          have he : e = n := Nat.eq_of_beq_eq_true he
          subst he
          have := (tile_sound ds bs ev' (e + 1) 0 ht).2
          simp only [Nat.add_zero, List.drop_zero] at this
          exact .ev hok this
        · cases h
      split at h
      · rename_i b bs'
        cases hk : Nat.beq b.k n
        · rw [hk, Bool.cond_false] at h; exact hev _ _ h
        · rw [hk, Bool.cond_true] at h
          cases hl : Nat.beq b.blk.length 0
          · rw [hl, Bool.cond_false] at h
            have hl' : b.blk.length ≠ 0 := fun h0 => by simp [h0] at hl
            obtain ⟨h1, h2⟩ := tile_sound ds bs' ev (n + 1) (b.blk.length - 1) h
            refine .row (Nat.eq_of_beq_eq_true hk) (fun h0 => hl' (by simp [h0])) (by simp; omega) ?_
            obtain ⟨m, hm⟩ : ∃ m, b.blk.length = m + 1 := ⟨b.blk.length - 1, by omega⟩
            rw [hm] at h2 ⊢
            rw [List.drop_succ_cons, show n + (m + 1) = n + 1 + m by omega]
            simpa using h2
          · rw [hl, Bool.cond_true] at h; cases h
      · exact hev _ _ h

/-! ## Every instruction after a label -/

/-- One step of `led`: an instruction must follow a label or an instruction
(`p`). -/
def ledStep (d : Directive) (r : Bool → Bool) (p : Bool) : Bool :=
  match d with
  | .instr _ => p && r true
  | .label _ => r true
  | _ => r false

/-- `led` for the code generator. -/
def ledImpl : List Directive → Bool → Bool
  | [], _ => true
  | d :: ds, p => ledStep d (ledImpl ds) p

/-- **Every instruction follows a label or an instruction**, the first one
if `p`. -/
@[implemented_by ledImpl]
def led (prog : List Directive) : Bool → Bool :=
  List.rec (motive := fun _ => Bool → Bool) (fun _ => true) (fun d _ r => ledStep d r) prog

theorem led_sound : ∀ (prog : List Directive) (p : Bool), led prog p = true →
    ∀ i x, prog[i]? = some (.instr x) →
      (∃ a m s, prog = a ++ .label m :: s ∧ a.length < i ∧ i - (a.length + 1) < (insRun s).length) ∨
      (p = true ∧ i < (insRun prog).length)
  | [], _, _, i, x, hi => by simp at hi
  | d :: ds, p, h, i, x, hi => by
    change ledStep d (led ds) p = true at h
    have hrun : ∀ y ds, insRun (.instr y :: ds) = .instr y :: insRun ds := fun _ _ => rfl
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [ledStep, Bool.and_eq_true] at h
      exact .inr ⟨h.1, by rw [hrun]; simp⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have shift : ∀ q, led ds q = true →
          (∃ a m s, ds = a ++ .label m :: s ∧ a.length < i ∧ i - (a.length + 1) < (insRun s).length) ∨
            (q = true ∧ i < (insRun ds).length) →
          (∃ a m s, ds = a ++ .label m :: s ∧ a.length < i ∧ i - (a.length + 1) < (insRun s).length) →
          ∃ a m s, d :: ds = a ++ .label m :: s ∧ a.length < i + 1 ∧
            i + 1 - (a.length + 1) < (insRun s).length := by
        intro _ _ _ ⟨a, m, s, hs, h1, h2⟩
        exact ⟨d :: a, m, s, by simp [hs], by simp; omega, by simp; omega⟩
      unfold ledStep at h
      split at h
      · rename_i y
        simp only [Bool.and_eq_true] at h
        rcases led_sound ds true h.2 i x hi with hl | ⟨_, hr⟩
        · exact .inl (shift true h.2 (.inl hl) hl)
        · exact .inr ⟨h.1, by rw [hrun]; simp; omega⟩
      · rename_i m
        rcases led_sound ds true h i x hi with hl | ⟨_, hr⟩
        · exact .inl (shift true h (.inl hl) hl)
        · exact .inl ⟨[], m, ds, rfl, by simp, by simpa using hr⟩
      · rcases led_sound ds false h i x hi with hl | ⟨hf, _⟩
        · exact .inl (shift false h (.inl hl) hl)
        · cases hf

/-! ## One pass -/

/-- No instruction at the head of a list. -/
def noIns : List Directive → Bool
  | d :: _ => !isIns d
  | [] => true

theorem insRun_of_noIns {ds : List Directive} (h : noIns ds = true) : insRun ds = [] := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    simp only [noIns, Bool.not_eq_true'] at h
    show (if isIns d then _ else []) = []
    rw [h]; rfl

/-- One step of `cover`: at a label, the next group's tiling of its run if
the keys agree (and the label is not repeated), else an empty run. -/
def coverStep (d : Directive) (ds : List Directive) (r : List Nat → List OGrp → Bool)
    (seen : List Nat) (gs : List OGrp) : Bool :=
  match d with
  | .label m =>
    match gs with
    | [] => noIns ds && r (key m :: seen) []
    | g :: gs' =>
      cond (Nat.beq (key m) (key g.l))
        (cond (memR (key g.l) seen) false (tile (insRun ds) g.bs g.ev 0 0 && r (key m :: seen) gs'))
        (noIns ds && r (key m :: seen) (g :: gs'))
  | _ => r seen gs

/-- The end of `cover`: no group left. -/
def coverEnd : List OGrp → Bool
  | [] => true
  | _ => false

/-- `cover` for the code generator. -/
def coverImpl : List Directive → List Nat → List OGrp → Bool
  | [], _, gs => coverEnd gs
  | d :: ds, seen, gs => coverStep d ds (coverImpl ds) seen gs

/-- **One pass over the program**: each group's tiling of its label's run,
the groups in program order at the first labels of their names (none before
among `seen`), every other run empty. -/
@[implemented_by coverImpl]
def cover (prog : List Directive) : List Nat → List OGrp → Bool :=
  List.rec (motive := fun _ => List Nat → List OGrp → Bool) (fun _ gs => coverEnd gs)
    (fun d ds r => coverStep d ds r) prog

/-- **Every instruction of the program in the block table**: in a label's
run, and each run tiled by its label's group (`coverOk_sound`). -/
def coverOk (prog : List Directive) (gs : List OGrp) : Bool :=
  led prog false && cover prog [] gs

theorem cover_sound : ∀ (s pre : List Directive) (seen : List Nat) (gs : List OGrp),
    (∀ m, Directive.label m ∈ pre → key m ∈ seen) → cover s seen gs = true →
    (∀ g ∈ gs, ∃ t, after g.l (pre ++ s) = some t ∧ Tiles g.bs g.ev 0 (insRun t)) ∧
    (∀ a m s', s = a ++ .label m :: s' → insRun s' ≠ [] → Directive.label m ∉ pre ++ a ∧ ∃ g ∈ gs, g.l = m)
  | [], _, _, gs, _, h => by
    change coverEnd gs = true at h
    cases gs with
    | nil => exact ⟨by simp, fun a _ _ hs => by cases a <;> cases hs⟩
    | cons => cases h
  | d :: ds, pre, seen, gs, hpre, h => by
    have happ : pre ++ [d] ++ ds = pre ++ d :: ds := by simp
    change coverStep d ds (cover ds) seen gs = true at h
    -- the second part, from the tail's
    have tl : ∀ (gs' : List OGrp),
        (∀ a m s', ds = a ++ .label m :: s' → insRun s' ≠ [] →
          Directive.label m ∉ pre ++ [d] ++ a ∧ ∃ g ∈ gs', g.l = m) →
        ∀ a m s', a ≠ [] → d :: ds = a ++ .label m :: s' → insRun s' ≠ [] →
          Directive.label m ∉ pre ++ a ∧ ∃ g ∈ gs', g.l = m := by
      intro gs' ih a m s' ha hs hne
      cases a with
      | nil => exact absurd rfl ha
      | cons d' a =>
        simp only [List.cons_append, List.cons.injEq] at hs
        obtain ⟨rfl, hs⟩ := hs
        obtain ⟨h1, g, hg, hgl⟩ := ih a m s' hs hne
        exact ⟨by simpa using h1, g, hg, hgl⟩
    unfold coverStep at h
    split at h
    next m =>
      have hpre' : ∀ m', Directive.label m' ∈ pre ++ [.label m] → key m' ∈ key m :: seen := by
        intro m' hm'
        rcases List.mem_append.mp hm' with hm' | hm'
        · exact List.mem_cons_of_mem _ (hpre m' hm')
        · simp only [List.mem_singleton, Directive.label.injEq] at hm'; simp [hm']
      -- a label with no group here: an empty run, the rest from the tail
      have skip : ∀ gs', noIns ds && cover ds (key m :: seen) gs' = true →
          (∀ g ∈ gs', ∃ t, after g.l (pre ++ .label m :: ds) = some t ∧ Tiles g.bs g.ev 0 (insRun t)) ∧
          (∀ a m' s', Directive.label m :: ds = a ++ .label m' :: s' → insRun s' ≠ [] →
            Directive.label m' ∉ pre ++ a ∧ ∃ g ∈ gs', g.l = m') := by
        intro gs' h
        simp only [Bool.and_eq_true] at h
        obtain ⟨ih1, ih2⟩ := cover_sound ds (pre ++ [.label m]) _ gs' hpre' h.2
        refine ⟨fun g hg => ?_, fun a m' s' hs hne => ?_⟩
        · rw [← happ]; exact ih1 g hg
        · cases a with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, Directive.label.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact absurd (insRun_of_noIns h.1) hne
          | cons => exact tl gs' ih2 _ m' s' (by simp) hs hne
      split at h
      next => exact skip [] h
      next g₀ gs' =>
        cases hk : Nat.beq (key m) (key g₀.l)
        · rw [hk, Bool.cond_false] at h
          exact skip _ h
        · rw [hk, Bool.cond_true] at h
          have hm : m = g₀.l := key_inj (Nat.beq_eq_true_eq _ _ ▸ hk)
          cases hs : memR (key g₀.l) seen
          · rw [hs, Bool.cond_false, Bool.and_eq_true] at h
            obtain ⟨ht, hr⟩ := h
            have hnot : Directive.label m ∉ pre := by
              intro hl
              have := memR_iff.mpr (hpre _ hl)
              rw [← hm] at hs; simp [this] at hs
            obtain ⟨ih1, ih2⟩ := cover_sound ds (pre ++ [.label m]) _ gs' hpre' hr
            refine ⟨fun g hg => ?_, fun a m' s' hs' hne => ?_⟩
            · rcases List.mem_cons.mp hg with rfl | hg
              · refine ⟨ds, ?_, by simpa using (tile_sound _ _ _ 0 0 ht).2⟩
                rw [← hm, after_append _ hnot]
                simp [after_cons, isLab]
              · rw [← happ]; exact ih1 g hg
            · cases a with
              | nil =>
                simp only [List.nil_append, List.cons.injEq, Directive.label.injEq] at hs'
                obtain ⟨rfl, rfl⟩ := hs'
                exact ⟨by simpa using hnot, g₀, List.mem_cons_self, hm.symm⟩
              | cons =>
                obtain ⟨h1, g, hg, hgl⟩ := tl gs' ih2 _ m' s' (by simp) hs' hne
                exact ⟨h1, g, List.mem_cons_of_mem _ hg, hgl⟩
          · rw [hs, Bool.cond_true] at h; cases h
    next hnl =>
      have hpre' : ∀ m', Directive.label m' ∈ pre ++ [d] → key m' ∈ seen := by
        intro m' hm'
        rcases List.mem_append.mp hm' with hm' | hm'
        · exact hpre m' hm'
        · simp only [List.mem_singleton] at hm'; exact absurd hm'.symm (hnl m')
      obtain ⟨ih1, ih2⟩ := cover_sound ds (pre ++ [d]) seen gs hpre' h
      refine ⟨fun g hg => ?_, fun a m s' hs hne => ?_⟩
      · rw [← happ]; exact ih1 g hg
      · cases a with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hs
          exact absurd hs.1 (hnl m)
        | cons => exact tl gs ih2 _ m s' (by simp) hs hne

/-- **What `coverOk` checks**: each group's rows and single instructions
tile the run after the first label of its name; every label with a
nonempty run is the first of its name and has a group; every instruction
is in the run after a label. -/
theorem coverOk_sound {prog : List Directive} {gs : List OGrp} (h : coverOk prog gs = true) :
    (∀ g ∈ gs, ∃ t, after g.l prog = some t ∧ Tiles g.bs g.ev 0 (insRun t)) ∧
    (∀ a m s, prog = a ++ .label m :: s → insRun s ≠ [] → Directive.label m ∉ a ∧ ∃ g ∈ gs, g.l = m) ∧
    (∀ i x, prog[i]? = some (.instr x) →
      ∃ a m s, prog = a ++ .label m :: s ∧ a.length < i ∧ i - (a.length + 1) < (insRun s).length) := by
  simp only [coverOk, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := cover_sound prog [] [] gs (by simp) h.2
  refine ⟨fun g hg => by simpa using h1 g hg, fun a m s hs hne => by simpa using h2 a m s hs hne,
    fun i x hi => ?_⟩
  rcases led_sound prog false h.1 i x hi with hl | ⟨hf, _⟩
  · exact hl
  · cases hf

/-- **Every instruction of a covered program in the table**: the
instruction at index `i` is the `j`-th of the run after the first label of
some group's name, and in one of the group's rows or its single
instructions (then allowed, `evOk`). -/
theorem inRow_of_coverOk {prog : List Directive} {gs : List OGrp} (h : coverOk prog gs = true)
    {i : Nat} {x : Instr} (hi : prog[i]? = some (.instr x)) :
    ∃ g ∈ gs, ∃ t j, after g.l prog = some t ∧ (insRun t)[j]? = some (.instr x) ∧
      ((∃ b ∈ g.bs, b.k ≤ j ∧ j < b.k + b.blk.length) ∨ (j ∈ g.ev ∧ evOk (.instr x) = true)) := by
  obtain ⟨hg, hl, hr⟩ := coverOk_sound h
  obtain ⟨a, m, s, hs, hai, hj⟩ := hr i x hi
  have hne : insRun s ≠ [] := by intro h0; rw [h0] at hj; simp at hj
  obtain ⟨hna, g, hgm, hgl⟩ := hl a m s hs hne
  obtain ⟨t, ht, htile⟩ := hg g hgm
  have hts : t = s := by
    have : after m prog = some s := by rw [hs, after_append _ hna]; simp [after_cons, isLab]
    rw [hgl] at ht; rw [ht] at this; exact Option.some.inj this
  subst hts
  have hpi : prog[i]? = t[i - (a.length + 1)]? := by
    rw [hs, List.getElem?_append_right (by omega), show i - a.length = i - (a.length + 1) + 1 by omega]
    rfl
  have hj' : (insRun t)[i - (a.length + 1)]? = some (.instr x) := by
    obtain ⟨u, hu⟩ : insRun t <+: t := insRun_eq t ▸ List.takeWhile_prefix _
    have : t[i - (a.length + 1)]? = (insRun t)[i - (a.length + 1)]? := by
      have := List.getElem?_append_left (l₂ := u) hj
      rw [hu] at this; exact this
    rw [← this, ← hpi, hi]
  refine ⟨g, hgm, t, i - (a.length + 1), ht, hj', ?_⟩
  simpa using htile.cover _ _ hj'

/-- info: [true, false, false, false, true, false, false, true, false] -/
#guard_msgs in
#eval
  let mov : Directive := .instr ⟨.W64, .MOVZ (.low (.reg .X0) .W64) (.int64 1) .LSL0⟩
  let sw : Directive := .instr ⟨.W64, .ADD_e (.low .SP .W64) (.low (.reg .X9) .W64) (.imm ⟨.int64 0, .S0⟩)⟩
  let svc : Directive := .instr ⟨.W64, .SVC 0⟩
  let r (k : Nat) (b : List Directive) : OBlk := ⟨k, 0, 0, ⟨0, []⟩, b⟩
  let p : List Directive := [.label "f", mov, sw, mov, .label "g"]
  -- a block, a stack switch on its own, a block
  [coverOk p [⟨"f", [r 0 [mov], r 2 [mov]], [1]⟩],
   -- a gap, an overlap, an empty table, a covered instruction on its own
   coverOk p [⟨"f", [r 0 [mov], r 2 [mov]], []⟩],
   coverOk p [⟨"f", [r 0 [mov, sw], r 1 [sw, mov]], []⟩],
   coverOk p [],
   coverOk p [⟨"f", [r 0 [mov, sw, mov]], []⟩],
   coverOk p [⟨"f", [r 1 [sw, mov]], [0]⟩],
   -- an instruction before the first label
   coverOk (mov :: p) [⟨"f", [r 0 [mov, sw, mov]], []⟩],
   -- an instruction the block lemmas do not cover, on its own
   coverOk [.label "f", svc] [⟨"f", [], [0]⟩],
   -- a group after its label's run, out of order
   coverOk [.label "g", .label "f", svc] [⟨"f", [], [0]⟩, ⟨"g", [], []⟩]]

end Scc.Cert.Rt.A64
