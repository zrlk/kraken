import WeakCore.TermOverCrDefs

/-! # TermPoolDefs: the pool credits of the `SysInvN` clause `pool` (Variant S)

`crPl cr pl` is the credit family the cover clause (`TermOverCr.OverCrG`) and the pool's
balance bounds use: the promise credits `cr` plus the pool credits `pl`.  A pool credit sits at
a holder that still has a foreign footprint message of its label at or below it (`PoolTag`);
once none is left (the label-wide window holds) it is converted into `cr` (F1).
-/

namespace TermPool
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The credits plus the pool credits. -/
def crPl (cr pl : Nat → Ts → Res) : Nat → Ts → Res := fun i t => cr i t + pl i t

/-- (pool, piece-lowest) `t` is at or below every promise of `P` inside the piece of type `S` at
word `b` of label `l`. -/
def PieceLow (mem : Memory) (P : List Ts) (l : AllocLabel) (b : Nat) (S : Ty) (t : Ts) : Prop :=
  ∀ usS, accs S = some usS → ∀ t' m', t' ∈ P → mem[t']? = some m' → m'.loc.label = l → b ≤ m'.loc.offset →
    m'.loc.offset < b + nWords usS → t ≤ t'

/-- `PieceLow` frame: memory keeps its prefix, and every new promise is an old one or lies at or above the
old memory size, above `t`. -/
theorem pieceLow_frame {mem mem' : Memory} {P P' : List Ts} {l : AllocLabel} {b : Nat} {S : Ty} {t : Ts}
    (hpre : ∀ t, t < mem.size → mem'[t]? = mem[t]?) (hP : ∀ t', t' ∈ P → t' < mem.size)
    (hsub : ∀ t', t' ∈ P' → t' ∈ P ∨ mem.size ≤ t') (ht : t < mem.size)
    (h : PieceLow mem P l b S t) : PieceLow mem' P' l b S t := by
  intro usS hus t' m' h1 h2 h3 h4 h5
  rcases hsub t' h1 with h1 | h1
  · rw [hpre t' (hP t' h1)] at h2
    exact h usS hus t' m' h1 h2 h3 h4 h5
  · exact Nat.le_of_lt (Nat.lt_of_lt_of_le ht h1)

/-- (b) at a foreign step: the promises are unchanged. -/
theorem pieceLow_foreign {mem mem' : Memory} {P : List Ts} {l : AllocLabel} {b : Nat} {S : Ty} {t : Ts}
    (hpre : ∀ t, t < mem.size → mem'[t]? = mem[t]?) (hP : ∀ t', t' ∈ P → t' < mem.size) (ht : t < mem.size)
    (h : PieceLow mem P l b S t) : PieceLow mem' P l b S t :=
  pieceLow_frame hpre hP (fun _ h1 => Or.inl h1) ht h

/-- (b) at an own step: the promises shrink. -/
theorem pieceLow_own {mem mem' : Memory} {P P' : List Ts} {l : AllocLabel} {b : Nat} {S : Ty} {t : Ts}
    (hpre : ∀ t, t < mem.size → mem'[t]? = mem[t]?) (hP : ∀ t', t' ∈ P → t' < mem.size)
    (hsub : P'.Sublist P) (ht : t < mem.size)
    (h : PieceLow mem P l b S t) : PieceLow mem' P' l b S t :=
  pieceLow_frame hpre hP (fun _ h1 => Or.inl (hsub.subset h1)) ht h

/-- (b) at a promise step: the new promise lies at the old memory size. -/
theorem pieceLow_prom {mem mem' : Memory} {P : List Ts} {l : AllocLabel} {b : Nat} {S : Ty} {t : Ts}
    (hpre : ∀ t, t < mem.size → mem'[t]? = mem[t]?) (hP : ∀ t', t' ∈ P → t' < mem.size) (ht : t < mem.size)
    (h : PieceLow mem P l b S t) : PieceLow mem' (P ++ [mem.size]) l b S t :=
  pieceLow_frame hpre hP (fun t' h1 => by
    rcases List.mem_append.1 h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Nat.le_of_eq (List.mem_singleton.1 h1).symm)) ht h

/-- (unit form; shared with hWbR route (i) COVER) **Pool cover at overtaken
first writes of predicted units**: at every own frontier, non-`pubd` cell of `j`, every unit that is
predicted (`PredU`), not visible, whose lowest own promise `tw` is its first write and overtaken, is
covered by a pool item (credit bound at `pl j`) in the predicted-unit form (`CrItemQ`: the pinned word
may be the first write's own word). -/
def PoolCovU (Eg : GEnv) (c : Cfg) (pl : Nat → Ts → Res) : Prop :=
  ∀ j thj (S : AllocLabel → Prop), c.ths[j]? = some thj → ∀ l cl, (Cut Eg j S).sto l = some cl →
    cl.owner = some j → Eg.pfr l ≠ none → ¬ Eg.pubd l →
    ∀ o tw, PredU (Cut Eg j S) ⟨l, o⟩ → ¬ VisU (Cut Eg j S) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw → FirstW c.mem ⟨l, o⟩ tw →
      TermPlant.OverT (Cut Eg j S) (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      ∃ x usS i, TermOverCr.CrItemQ (Cut Eg j S) (stOf c.mem c.pairs thj) (pl j) l cl x ∧
        accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true

/-- (list form) **Pool cover, list form**: at every own
frontier, non-`pubd` cell of `j`, one list `Gs` of pool items (`CrItemQ` at `pl j`) whose values sum, per
holder, to at most the holder's pool credit, covering every predicted, non-visible unit whose lowest own
promise `tw` is its first write and overtaken (several items may share a holder: creations at different
units of one piece deposit at the same piece-lowest promise). -/
def PoolCovUL (Eg : GEnv) (c : Cfg) (pl : Nat → Ts → Res) : Prop :=
  ∀ j thj (S : AllocLabel → Prop), c.ths[j]? = some thj → ∀ l cl, (Cut Eg j S).sto l = some cl →
    cl.owner = some j → Eg.pfr l ≠ none → ¬ Eg.pubd l →
    ∃ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)),
      (∀ t, Res.sum ((Gs.filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1)) ≤ pl j t) ∧
      (∀ x ∈ Gs, TermOverCr.CrItemQ (Cut Eg j S) (stOf c.mem c.pairs thj) (pl j) l cl x) ∧
      ∀ o tw, PredU (Cut Eg j S) ⟨l, o⟩ → ¬ VisU (Cut Eg j S) ⟨l, o⟩ →
        TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw → FirstW c.mem ⟨l, o⟩ tw →
        TermPlant.OverT (Cut Eg j S) (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
        ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
          x.2.2.2.2.2 i = true

/-- (PoolTag) **A nonzero pool credit** of thread `j` at `t`: `t` is an outstanding promise of `j`,
key-free, with a footprint message of its label at or below it (at every cut of `j`) or else
(F-Pool) a mask-free credit item at holder `t` at a frontier label (it pins and covers
nothing, so it never needs conversion), and a plain credit item (`CrItem`, pinned by `PredAt`) at
holder `t` funded by the pool credit, at a cell of `j`, with `t` lowest among `j`'s promises in the
item's piece (`PieceLow`). -/
def PoolTag (Eg : GEnv) (c : Cfg) (pl : Nat → Ts → Res) : Prop :=
  (∀ j thj t, c.ths[j]? = some thj → pl j t ≠ .zero → t ∈ thj.promises ∧ TermPlant.CrKeys (pl j t) ∧
    ∃ m, c.mem[t]? = some m ∧
      ((∀ S : AllocLabel → Prop, ∃ f mf, f ∈ FpAt (Cut Eg j S) ⟨m.loc.label, 0⟩ ∧ c.mem[f]? = some mf ∧
          mf.loc.label = m.loc.label ∧ f ≤ t) ∨
        ∀ S : AllocLabel → Prop, (Cut Eg j S).pfr m.loc.label ≠ none ∧
          ∃ cl x, (Cut Eg j S).sto m.loc.label = some cl ∧ cl.owner = some j ∧ x.1 = t ∧
            (∀ i, x.2.2.2.2.2 i = false) ∧
            TermPiece.CrItem (Cut Eg j S) (stOf c.mem c.pairs thj) (pl j) m.loc.label cl x) ∧
      ∀ S : AllocLabel → Prop, ∃ cl x, (Cut Eg j S).sto m.loc.label = some cl ∧ cl.owner = some j ∧ x.1 = t ∧
        TermPiece.CrItem (Cut Eg j S) (stOf c.mem c.pairs thj) (pl j) m.loc.label cl x ∧
        PieceLow c.mem thj.promises m.loc.label x.2.1 x.2.2.1 t) ∧
  PoolCovUL Eg c pl

/-- The list form gives the unit form. -/
theorem poolCovU_of_L {Eg : GEnv} {c : Cfg} {pl : Nat → Ts → Res} (h : PoolCovUL Eg c pl) :
    PoolCovU Eg c pl := by
  intro j thj S hj l cl hl ho hp hnp o tw h1 h2 h3 h4 h5
  obtain ⟨Gs, -, hit, hcov⟩ := h j thj S hj l cl hl ho hp hnp
  obtain ⟨x, hx, usS, i, a1, a2, a3, a4⟩ := hcov o tw h1 h2 h3 h4 h5
  exact ⟨x, usS, i, hit x hx, a1, a2, a3, a4⟩

/-- With no outstanding promises the unit cover is vacuous. -/
theorem poolCovU_nil {Eg : GEnv} {c : Cfg} {pl : Nat → Ts → Res}
    (h : ∀ (j : Nat) (thj : TTh), c.ths[j]? = some thj → thj.promises = []) : PoolCovU Eg c pl := by
  intro j thj S hj l cl _ _ _ _ o tw _ _ hlo
  obtain ⟨hin, -⟩ := hlo
  have e : (stOf c.mem c.pairs thj).promises = [] := h j thj hj
  rw [e] at hin
  cases hin

/-- With no outstanding promises the list cover is vacuous (`Gs := []`). -/
theorem poolCovUL_nil {Eg : GEnv} {c : Cfg} {pl : Nat → Ts → Res}
    (h : ∀ (j : Nat) (thj : TTh), c.ths[j]? = some thj → thj.promises = []) : PoolCovUL Eg c pl := by
  intro j thj S hj l cl _ _ _ _
  refine ⟨[], fun t => Res.zero_le _, fun _ hx => absurd hx (List.not_mem_nil), ?_⟩
  intro o tw _ _ hlo
  obtain ⟨hin, -⟩ := hlo
  have e : (stOf c.mem c.pairs thj).promises = [] := h j thj hj
  rw [e] at hin
  cases hin

/-- No pool credits (the cover needs no outstanding promises). -/
theorem poolTag_zero (Eg : GEnv) (c : Cfg)
    (h : ∀ (j : Nat) (thj : TTh), c.ths[j]? = some thj → thj.promises = []) :
    PoolTag Eg c (fun _ _ => .zero) :=
  ⟨fun _ _ _ _ h => absurd rfl h, poolCovUL_nil h⟩

theorem crPl_zero (cr : Nat → Ts → Res) : crPl cr (fun _ _ => .zero) = cr := by
  funext i t
  simp only [crPl, Res.add_zero]

/-- With no own promises nothing is overtaken (copy of `TermOverCr.overCr_noProm`). -/
theorem overCr_noPromP {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    (h : s.promises = []) : TermOverCr.OverCrE E s cr l c := by
  refine ⟨[], ⟨List.nodup_nil, fun x hx => absurd hx (List.not_mem_nil (a := x)), fun o tw _ _ hl _ _ => ?_,
    fun x hx => absurd hx (List.not_mem_nil (a := x)),
    fun t m ht => by rw [h] at ht; exact absurd ht (List.not_mem_nil (a := t))⟩,
    fun x hx => absurd hx (List.not_mem_nil (a := x))⟩
  have h1 := hl.1
  rw [h] at h1
  exact absurd h1 (List.not_mem_nil (a := tw))

/-- (init) The system cover clause at a promise-free configuration (copy of
`TermOverCr.overCrG_noProm`, hypothesis unfolded). -/
theorem overCrG_noPromP {Eg : GEnv} {c : Cfg} {cr : Nat → Ts → Res}
    (h : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.promises = []) : TermOverCr.OverCrG Eg c cr :=
  fun i th _ hth _ _ _ _ _ => overCr_noPromP (h i th hth)

end TermPool
