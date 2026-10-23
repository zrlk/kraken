import Scc.Cert.Rt.OffsX64

/-!
# Every cell of the program in the block table (x64)

The x64 twin of `Scc/Cert/Rt/CoverA64.lean`, over code cells with their
sizes. `blocksIn` (`Scc/Cert/Rt/CodeX64.lean`) checks the rows of a block
table that exist; an empty table passes it. The generic proof needs a row,
or a single instruction it takes on its own, for every instruction it runs,
so A3 also checks **coverage**, `coverOk cells gs`:

* the first cell is a label (`led`): every other cell is a label or in the
  run of non-label cells after one (`cellRun`);
* in one pass over the cells like `slices` (`cover`), at the first
  occurrence of each label, in program order, the next group of the table
  if it is that label's, and then its rows and its single instructions
  (`OGrp.ev`) **tile** the label's run (`Tiles`, checked by `tile`): in
  run order, from its start to its end, without gaps or overlaps, each
  row nonempty;
* at any other label (no group, or a repeated name) a run of single
  instructions (`runEv`);
* every single instruction is one the block lemmas do not cover
  (`classify d = none`), a load or store through a base other than `%rsp`
  and `%rbp`, or a stack switch `mov %r, %rsp` (`evOk`);
* no group left at the end.

`coverOk_sound` gives each group's tiling of its label's run, every run's
label the first of its name with a group or the run single instructions,
and every non-label cell in a run; `inRow_of_coverOk` puts every non-label
cell of the program in a row or a single instruction of the group of its
run, or makes it a single instruction itself.

Where x64 differs from AArch64:

* a label with no group may have a nonempty run, of single instructions
  (AArch64: an empty run). scc's x64 runtime has such runs, a `ud2` alone
  after a label no branch of a block reaches (`.Lscc_rt_alloc.x4`);
  `inRow_of_coverOk` has the disjunct `evOk c.1 = true` for them;
* the single instructions include loads and stores through a base that is
  not a frame register (`movq %rax, 0(%rcx)`), which `classify` takes as
  covered, and the stack switch is `mov %r, %rsp` (`mov %rax, %rsp`,
  `movq %rbp, %rsp`);
* cells are only labels and instructions in scc's output, so `led` checks
  the first cell only (AArch64: every instruction after a label or an
  instruction).

The check is linear: each label is encoded once (`key`), and `tile` visits
each cell of a run once, counting down the cells left in the current row. -/

namespace Scc.Cert.Rt.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Spike.Lib Spike.Lib.X64

/-! ## Single instructions -/

/-- A stack switch, `mov %r, %rsp` (64-bit). -/
def isSwitch : Directive → Bool
  | .instr (.regular .W64 .W64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low _ .W64))))) => true
  | _ => false

/-- A frame register, `%rsp` or `%rbp`. -/
def isFrame : Reg64 → Bool
  | .rsp | .rbp => true
  | _ => false

/-- **An instruction a group may leave out of its rows**: one the block
lemmas do not cover, a load or store through a base that is not a frame
register, or a stack switch. -/
def evOk (d : Directive) : Bool :=
  match classify d with
  | none => true
  | some (.ld _ b _) => !isFrame b
  | some (.st b _ _) => !isFrame b
  | some _ => isSwitch d

/-! ## Tilings -/

/-- **The rows `bs` and the single instructions `ev` tile the run `r`**
starting at index `n`: in order, either the next row starts at `n`, is
nonempty and within `r`, or the next single instruction is at `n` and
allowed (`evOk`); nothing is left at the end. -/
inductive Tiles : List OBlk → List Nat → Nat → List (Directive × Nat) → Prop
  | nil {n : Nat} : Tiles [] [] n []
  | row {b : OBlk} {bs : List OBlk} {ev : List Nat} {n : Nat} {r : List (Directive × Nat)} :
      b.k = n → b.blk ≠ [] → b.blk.length ≤ r.length →
      Tiles bs ev (n + b.blk.length) (r.drop b.blk.length) → Tiles (b :: bs) ev n r
  | ev {bs : List OBlk} {ev : List Nat} {n : Nat} {c : Directive × Nat} {r : List (Directive × Nat)} :
      evOk c.1 = true → Tiles bs ev (n + 1) r → Tiles bs (n :: ev) n (c :: r)

/-- **Every cell of a tiled run** is in a row, or a single instruction,
allowed. -/
theorem Tiles.cover {bs : List OBlk} {ev : List Nat} {n : Nat} {r : List (Directive × Nat)}
    (h : Tiles bs ev n r) :
    ∀ i (c : Directive × Nat), r[i]? = some c →
      (∃ b ∈ bs, b.k ≤ n + i ∧ n + i < b.k + b.blk.length) ∨ (n + i ∈ ev ∧ evOk c.1 = true) := by
  induction h with
  | nil => intro i c hc; simp at hc
  | @row b bs ev n r hk hne hlen _ ih =>
    intro i c hc
    by_cases hb : i < b.blk.length
    · exact .inl ⟨b, List.mem_cons_self, by omega, by omega⟩
    · have hc' : (r.drop b.blk.length)[i - b.blk.length]? = some c := by
        rw [List.getElem?_drop, show b.blk.length + (i - b.blk.length) = i by omega, hc]
      have := ih (i - b.blk.length) c hc'
      rw [show n + b.blk.length + (i - b.blk.length) = n + i by omega] at this
      rcases this with ⟨b', hb', h1, h2⟩ | he
      · exact .inl ⟨b', List.mem_cons_of_mem _ hb', h1, h2⟩
      · exact .inr he
  | @ev bs ev n c₀ r hc₀ _ ih =>
    intro i c hc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact .inr ⟨by simp, hc₀⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc
      have := ih i c hc
      rw [show n + 1 + i = n + (i + 1) by omega] at this
      rcases this with hb | ⟨he, hok⟩
      · exact .inl hb
      · exact .inr ⟨List.mem_cons_of_mem _ he, hok⟩

/-! ## The tiling check -/

/-- One step of `tile` at the cell `d` of index `n`, `c` cells of the
current row left: the row's next one; else the next row if it starts here;
else the next single instruction if it is here and allowed. -/
def tileStep (d : Directive × Nat) (r : List OBlk → List Nat → Nat → Nat → Bool)
    (bs : List OBlk) (ev : List Nat) (n c : Nat) : Bool :=
  cond (Nat.beq c 0)
    (match bs with
     | b :: bs' =>
       cond (Nat.beq b.k n)
         (cond (Nat.beq b.blk.length 0) false (r bs' ev (n + 1) (b.blk.length - 1)))
         (match ev with
          | e :: ev' => Nat.beq e n && evOk d.1 && r bs ev' (n + 1) 0
          | [] => false)
     | [] =>
       match ev with
       | e :: ev' => Nat.beq e n && evOk d.1 && r bs ev' (n + 1) 0
       | [] => false)
    (r bs ev (n + 1) (c - 1))

/-- The end of `tile`: no row, no single instruction, nothing left of a
row. -/
def tileEnd (bs : List OBlk) (ev : List Nat) (c : Nat) : Bool :=
  match bs, ev with
  | [], [] => Nat.beq c 0
  | _, _ => false

/-- `tile` for the code generator. -/
def tileImpl : List (Directive × Nat) → List OBlk → List Nat → Nat → Nat → Bool
  | [], bs, ev, _, c => tileEnd bs ev c
  | d :: ds, bs, ev, n, c => tileStep d (tileImpl ds) bs ev n c

/-- **The tiling of a run, checked**: `tile r bs ev n 0` walks the run `r`
from index `n`. -/
@[implemented_by tileImpl]
def tile (r : List (Directive × Nat)) : List OBlk → List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List OBlk → List Nat → Nat → Nat → Bool)
    (fun bs ev _ c => tileEnd bs ev c) (fun d _ r => tileStep d r) r

theorem tile_sound : ∀ (r : List (Directive × Nat)) (bs : List OBlk) (ev : List Nat) (n c : Nat),
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
           | e :: ev' => Nat.beq e n && evOk d.1 && tile ds bs ev' (n + 1) 0
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

/-! ## Every cell after a label -/

theorem cellRun_cons (c : Directive × Nat) (cs : List (Directive × Nat)) :
    cellRun (c :: cs) = if notLab c then c :: cellRun cs else [] := rfl

/-- **The first cell is a label** (or there is none). -/
def led : List (Directive × Nat) → Bool
  | c :: _ => !notLab c
  | [] => true

theorem cellRun_of_led {cells : List (Directive × Nat)} (h : led cells = true) : cellRun cells = [] := by
  cases cells with
  | nil => rfl
  | cons c cs =>
    simp only [led, Bool.not_eq_true'] at h
    rw [cellRun_cons, h]; rfl

/-- **Every non-label cell** is in the run after a label, or in the run at
the head. -/
theorem inRun : ∀ (cells : List (Directive × Nat)) (i : Nat) (c : Directive × Nat),
    cells[i]? = some c → notLab c = true →
      (∃ a m z s, cells = a ++ (.label m, z) :: s ∧ a.length < i ∧ i - (a.length + 1) < (cellRun s).length) ∨
      i < (cellRun cells).length
  | [], _, _, hi, _ => by simp at hi
  | d :: ds, 0, c, hi, hc => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact .inr (by rw [cellRun_cons, hc]; simp)
  | d :: ds, i + 1, c, hi, hc => by
    simp only [List.getElem?_cons_succ] at hi
    rcases inRun ds i c hi hc with ⟨a, m, z, s, hs, h1, h2⟩ | hr
    · exact .inl ⟨d :: a, m, z, s, by simp [hs], by simp; omega, by simp; omega⟩
    · cases hd : notLab d
      · obtain ⟨d, z⟩ := d
        cases d <;> simp only [notLab, reduceCtorEq] at hd
        rename_i m
        exact .inl ⟨[], m, z, ds, rfl, by simp, by simpa using hr⟩
      · exact .inr (by rw [cellRun_cons, hd]; simp; omega)

/-! ## One pass -/

/-- `runEv` for the code generator. -/
def runEvImpl : List (Directive × Nat) → Bool
  | [] => true
  | c :: cs => if notLab c then evOk c.1 && runEvImpl cs else true

/-- **The run at the head is single instructions**, each allowed. -/
@[implemented_by runEvImpl]
def runEv (cs : List (Directive × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ r => if notLab c then evOk c.1 && r else true) cs

theorem runEv_sound : ∀ {cs : List (Directive × Nat)}, runEv cs = true → ∀ c ∈ cellRun cs, evOk c.1 = true
  | [], _, _, hc => by simp [cellRun] at hc
  | c :: cs, h, c', hc' => by
    change (if notLab c then evOk c.1 && runEv cs else true) = true at h
    rw [cellRun_cons] at hc'
    cases hn : notLab c
    · rw [hn] at hc'; simp at hc'
    · rw [hn] at h hc'
      simp only [↓reduceIte, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact h.1
      · exact runEv_sound h.2 c' hc'

/-- One step of `cover`: at a label, the next group's tiling of its run if
the keys agree (and the label is not repeated), else a run of single
instructions. -/
def coverStep (c : Directive × Nat) (cs : List (Directive × Nat)) (r : List Nat → List OGrp → Bool)
    (seen : List Nat) (gs : List OGrp) : Bool :=
  match c.1 with
  | .label m =>
    match gs with
    | [] => runEv cs && r (key m :: seen) []
    | g :: gs' =>
      cond (Nat.beq (key m) (key g.l))
        (cond (memR (key g.l) seen) false (tile (cellRun cs) g.bs g.ev 0 0 && r (key m :: seen) gs'))
        (runEv cs && r (key m :: seen) (g :: gs'))
  | _ => r seen gs

/-- The end of `cover`: no group left. -/
def coverEnd : List OGrp → Bool
  | [] => true
  | _ => false

/-- `cover` for the code generator. -/
def coverImpl : List (Directive × Nat) → List Nat → List OGrp → Bool
  | [], _, gs => coverEnd gs
  | c :: cs, seen, gs => coverStep c cs (coverImpl cs) seen gs

/-- **One pass over the cells**: each group's tiling of its label's run,
the groups in program order at the first labels of their names (none before
among `seen`), every other run single instructions. -/
@[implemented_by coverImpl]
def cover (cells : List (Directive × Nat)) : List Nat → List OGrp → Bool :=
  List.rec (motive := fun _ => List Nat → List OGrp → Bool) (fun _ gs => coverEnd gs)
    (fun c cs r => coverStep c cs r) cells

/-- **Every cell of the program in the block table**: in a label's run,
and each run tiled by its label's group or single instructions
(`coverOk_sound`). -/
def coverOk (cells : List (Directive × Nat)) (gs : List OGrp) : Bool :=
  led cells && cover cells [] gs

theorem cover_sound : ∀ (s pre : List (Directive × Nat)) (seen : List Nat) (gs : List OGrp),
    (∀ m, ∀ c ∈ pre, c.1 = .label m → key m ∈ seen) → cover s seen gs = true →
    (∀ g ∈ gs, ∃ t, after g.l (pre ++ s) = some t ∧ Tiles g.bs g.ev 0 (cellRun t)) ∧
    (∀ a m z s', s = a ++ (.label m, z) :: s' →
      ((∀ c ∈ pre ++ a, c.1 ≠ .label m) ∧ ∃ g ∈ gs, g.l = m) ∨ ∀ c ∈ cellRun s', evOk c.1 = true)
  | [], _, _, gs, _, h => by
    change coverEnd gs = true at h
    cases gs with
    | nil => exact ⟨by simp, fun a _ _ _ hs => by cases a <;> cases hs⟩
    | cons => cases h
  | c :: cs, pre, seen, gs, hpre, h => by
    have happ : pre ++ [c] ++ cs = pre ++ c :: cs := by simp
    change coverStep c cs (cover cs) seen gs = true at h
    -- the second part, from the tail's
    have tl : ∀ (gs' : List OGrp),
        (∀ a m z s', cs = a ++ (.label m, z) :: s' →
          ((∀ c' ∈ pre ++ [c] ++ a, c'.1 ≠ .label m) ∧ ∃ g ∈ gs', g.l = m) ∨
            ∀ c' ∈ cellRun s', evOk c'.1 = true) →
        ∀ a m z s', a ≠ [] → c :: cs = a ++ (.label m, z) :: s' →
          ((∀ c' ∈ pre ++ a, c'.1 ≠ .label m) ∧ ∃ g ∈ gs', g.l = m) ∨
            ∀ c' ∈ cellRun s', evOk c'.1 = true := by
      intro gs' ih a m z s' ha hs
      cases a with
      | nil => exact absurd rfl ha
      | cons c'' a =>
        simp only [List.cons_append, List.cons.injEq] at hs
        obtain ⟨rfl, hs⟩ := hs
        rcases ih a m z s' hs with ⟨h1, g, hg, hgl⟩ | he
        · exact .inl ⟨by simpa using h1, g, hg, hgl⟩
        · exact .inr he
    unfold coverStep at h
    split at h
    next m hc =>
      have hpre' : ∀ m', ∀ c' ∈ pre ++ [c], c'.1 = .label m' → key m' ∈ key m :: seen := by
        intro m' c' hc' he
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact List.mem_cons_of_mem _ (hpre m' c' hc' he)
        · simp only [List.mem_singleton] at hc'; subst hc'
          rw [hc, Directive.label.injEq] at he; simp [he]
      -- a label with no group here: a run of single instructions, the rest from the tail
      have skip : ∀ gs', runEv cs && cover cs (key m :: seen) gs' = true →
          (∀ g ∈ gs', ∃ t, after g.l (pre ++ c :: cs) = some t ∧ Tiles g.bs g.ev 0 (cellRun t)) ∧
          (∀ a m' z s', c :: cs = a ++ (.label m', z) :: s' →
            ((∀ c' ∈ pre ++ a, c'.1 ≠ .label m') ∧ ∃ g ∈ gs', g.l = m') ∨
              ∀ c' ∈ cellRun s', evOk c'.1 = true) := by
        intro gs' h
        simp only [Bool.and_eq_true] at h
        obtain ⟨ih1, ih2⟩ := cover_sound cs (pre ++ [c]) _ gs' hpre' h.2
        refine ⟨fun g hg => ?_, fun a m' z s' hs => ?_⟩
        · rw [← happ]; exact ih1 g hg
        · cases a with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact .inr (runEv_sound h.1)
          | cons => exact tl gs' ih2 _ m' z s' (by simp) hs
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
            have hnot : ∀ c' ∈ pre, c'.1 ≠ .label m := by
              intro c' hc' he
              have := memR_iff.mpr (hpre _ c' hc' he)
              rw [hm, hs] at this; cases this
            obtain ⟨ih1, ih2⟩ := cover_sound cs (pre ++ [c]) _ gs' hpre' hr
            refine ⟨fun g hg => ?_, fun a m' z s' hs' => ?_⟩
            · rcases List.mem_cons.mp hg with rfl | hg
              · refine ⟨cs, ?_, by simpa using (tile_sound _ _ _ 0 0 ht).2⟩
                rw [← hm, after_append _ hnot]
                simp [after_cons, isLab, hc]
              · rw [← happ]; exact ih1 g hg
            · cases a with
              | nil =>
                simp only [List.nil_append, List.cons.injEq] at hs'
                obtain ⟨rfl, rfl⟩ := hs'
                simp only [Directive.label.injEq] at hc
                subst hc
                exact .inl ⟨by simpa using hnot, g₀, List.mem_cons_self, hm.symm⟩
              | cons =>
                rcases tl gs' ih2 _ m' z s' (by simp) hs' with ⟨h1, g, hg, hgl⟩ | he
                · exact .inl ⟨h1, g, List.mem_cons_of_mem _ hg, hgl⟩
                · exact .inr he
          · rw [hs, Bool.cond_true] at h; cases h
    next hnl =>
      have hpre' : ∀ m', ∀ c' ∈ pre ++ [c], c'.1 = .label m' → key m' ∈ seen := by
        intro m' c' hc' he
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact hpre m' c' hc' he
        · simp only [List.mem_singleton] at hc'; subst hc'; exact absurd he (hnl m')
      obtain ⟨ih1, ih2⟩ := cover_sound cs (pre ++ [c]) seen gs hpre' h
      refine ⟨fun g hg => ?_, fun a m z s' hs => ?_⟩
      · rw [← happ]; exact ih1 g hg
      · cases a with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hs
          exact absurd (by rw [hs.1]) (hnl m)
        | cons => exact tl gs ih2 _ m z s' (by simp) hs

/-- **What `coverOk` checks**: each group's rows and single instructions
tile the run after the first label of its name; every label's run is the
first of its name with a group, or single instructions; every non-label
cell is in the run after a label. -/
theorem coverOk_sound {cells : List (Directive × Nat)} {gs : List OGrp} (h : coverOk cells gs = true) :
    (∀ g ∈ gs, ∃ t, after g.l cells = some t ∧ Tiles g.bs g.ev 0 (cellRun t)) ∧
    (∀ a m z s, cells = a ++ (.label m, z) :: s →
      ((∀ c ∈ a, c.1 ≠ .label m) ∧ ∃ g ∈ gs, g.l = m) ∨ ∀ c ∈ cellRun s, evOk c.1 = true) ∧
    (∀ i c, cells[i]? = some c → notLab c = true →
      ∃ a m z s, cells = a ++ (.label m, z) :: s ∧ a.length < i ∧ i - (a.length + 1) < (cellRun s).length) := by
  simp only [coverOk, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := cover_sound cells [] [] gs (by simp) h.2
  refine ⟨fun g hg => by simpa using h1 g hg, fun a m z s hs => by simpa using h2 a m z s hs,
    fun i c hi hc => ?_⟩
  rcases inRun cells i c hi hc with hl | hr
  · exact hl
  · rw [cellRun_of_led h.1] at hr; simp at hr

/-- **Every non-label cell of a covered program in the table**: the cell
at index `i` is the `j`-th of the run after the first label of some group's
name, and in one of the group's rows or its single instructions (then
allowed, `evOk`); or it is in the run of a label without a group, a single
instruction, allowed. -/
theorem inRow_of_coverOk {cells : List (Directive × Nat)} {gs : List OGrp} (h : coverOk cells gs = true)
    {i : Nat} {c : Directive × Nat} (hi : cells[i]? = some c) (hc : notLab c = true) :
    (∃ g ∈ gs, ∃ t j, after g.l cells = some t ∧ (cellRun t)[j]? = some c ∧
      ((∃ b ∈ g.bs, b.k ≤ j ∧ j < b.k + b.blk.length) ∨ (j ∈ g.ev ∧ evOk c.1 = true))) ∨
    evOk c.1 = true := by
  obtain ⟨hg, hl, hr⟩ := coverOk_sound h
  obtain ⟨a, m, z, s, hs, hai, hj⟩ := hr i c hi hc
  have hpi : cells[i]? = s[i - (a.length + 1)]? := by
    rw [hs, List.getElem?_append_right (by omega), show i - a.length = i - (a.length + 1) + 1 by omega]
    rfl
  have hj' : (cellRun s)[i - (a.length + 1)]? = some c := by
    obtain ⟨u, hu⟩ : cellRun s <+: s := cellRun_eq s ▸ List.takeWhile_prefix _
    have : s[i - (a.length + 1)]? = (cellRun s)[i - (a.length + 1)]? := by
      have := List.getElem?_append_left (l₂ := u) hj
      rw [hu] at this; exact this
    rw [← this, ← hpi, hi]
  rcases hl a m z s hs with ⟨hna, g, hgm, hgl⟩ | hev
  · obtain ⟨t, ht, htile⟩ := hg g hgm
    have hts : t = s := by
      have : after m cells = some s := by rw [hs, after_append _ hna]; simp [after_cons, isLab]
      rw [hgl] at ht; rw [ht] at this; exact Option.some.inj this
    subst hts
    exact .inl ⟨g, hgm, t, i - (a.length + 1), ht, hj', by simpa using htile.cover _ _ hj'⟩
  · exact .inr (hev c (List.mem_of_getElem? hj'))

/-- info: [true, false, false, false, true, false, false, true, false, true, false] -/
#guard_msgs in
#eval
  let mov : Directive × Nat := (op64 (.mov (.reg (.low .rax .W64)) (.imm (.int64 1))), 7)
  let sw : Directive × Nat := (op64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64)))), 3)
  let ud2 : Directive × Nat := (op64 .ud2, 2)
  let lab (l : Label) : Directive × Nat := (.label l, 0)
  let r (k off : Nat) (b : List (Directive × Nat)) : OBlk := ⟨k, off, 0, 0, ⟨0, []⟩, b⟩
  let p : List (Directive × Nat) := [lab "f", mov, sw, mov, lab "g"]
  -- a block, a stack switch on its own, a block
  [coverOk p [⟨"f", [r 0 0 [mov], r 2 10 [mov]], [1]⟩],
   -- a gap, an overlap, an empty table, a covered instruction on its own
   coverOk p [⟨"f", [r 0 0 [mov], r 2 10 [mov]], []⟩],
   coverOk p [⟨"f", [r 0 0 [mov, sw], r 1 7 [sw, mov]], []⟩],
   coverOk p [],
   coverOk p [⟨"f", [r 0 0 [mov, sw, mov]], []⟩],
   coverOk p [⟨"f", [r 1 7 [sw, mov]], [0]⟩],
   -- a cell before the first label
   coverOk (mov :: p) [⟨"f", [r 0 0 [mov, sw, mov]], []⟩],
   -- an instruction the block lemmas do not cover, on its own
   coverOk [lab "f", ud2] [⟨"f", [], [0]⟩],
   -- a group after its label's run, out of order
   coverOk [lab "g", lab "f", ud2] [⟨"f", [], [0]⟩, ⟨"g", [], []⟩],
   -- a label without a group: its run single instructions, allowed or not
   coverOk [lab "f", ud2, lab "g", mov] [⟨"g", [r 0 0 [mov]], []⟩],
   coverOk [lab "f", mov, lab "g", mov] [⟨"g", [r 0 0 [mov]], []⟩]]

end Scc.Cert.Rt.X64
