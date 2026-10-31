import WeakCore.TermStep
import WeakCore.TermLiveProps

namespace TermLiveHeld
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Typing inversions on protocol words -/

/-- `v` lies in a held (non-holding) clause of `P`. -/
def HeldV (P : Proto) (v : WeakMem.Val) : Prop :=
  ∃ (c : Nat) (cl : Clause) (k : Nat), P.clauses[c]? = some cl ∧ cl.holds = false ∧
    v = .num (cl.scale * k + cl.off)

/-- Every `store` on a protocol word (`Give`, `Keep`, `Hand`) consumes a region
token `tok r' (P, i)` with `r' = r` (the word's region). -/
theorem store_word_tok {p : Prog} {cx c' : Cx} {x : String} {rel : Bool} {a v : At}
    {tok : Option At} {t : Ty} {r : Idx} {P : Proto} (h : OpT p cx x (.store rel a v tok) c')
    (ht : cx.peek a = .ok t) (hw : wordOf t = some (r, P)) :
    ∃ tk r' i c₁, tok = some tk ∧ cx.use tk = .ok (.tok r' (some (P, i)), c₁) ∧ EqI c₁ r r' := by
  revert ht hw
  cases h
  all_goals (
    have hpk := ‹Cx.peek _ _ = _›
    have hwo := ‹wordOf _ = _›
    intro ht hw
    rw [ht] at hpk
    cases hpk
    rw [hw] at hwo
    cases hwo)
  all_goals exact ⟨_, _, _, _, rfl, ‹_›, ‹_›⟩

/-- A typed `cas` on a protocol word compares against a value in a state
`(c, k)` of `P` and writes one in a state `(c', k')`; the source clause holds
(`casShare`, `casTake`) or `P` is an epoch counter (`casEpoch`). -/
theorem cas_word_inv {p : Prog} {cx : Cx} {acq rel : Bool} {w e v : At} {t : String}
    {ok fail : Expr} {tw : Ty} {r : Idx} {P : Proto}
    (h : Typed p cx (.cas acq rel w e v t ok fail))
    (ht : cx.peek w = .ok tw) (hw : wordOf tw = some (r, P)) :
    ∃ i j c k c' k', IntIdx cx e i ∧ IntIdx cx v j ∧ InState cx P i c k ∧ InState cx P j c' k' ∧
      ((∃ cl, P.clauses[c]? = some cl ∧ cl.holds = true ∧ P.ghost = false) ∨ P.epoch = true) := by
  revert ht hw
  cases h
  all_goals (
    have hpk := ‹Cx.peek _ w = _›
    have hwo := ‹wordOf _ = _›
    intro ht hw
    rw [ht] at hpk
    cases hpk
    rw [hw] at hwo
    cases hwo)
  · exact ⟨_, _, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, Or.inl ⟨_, ‹_›, ‹_›, ‹_›⟩⟩
  · exact ⟨_, _, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, Or.inl ⟨_, ‹_›, ‹_›, ‹_›⟩⟩
  · exact ⟨_, _, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, Or.inr ‹_›⟩

/-- A typed `fetch` on a protocol word is `fetchShare` (`fetchOK`) or
`fetchEpoch` (an epoch counter). -/
theorem fetch_word_inv {p : Prog} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {tw : Ty} {r : Idx} {P : Proto} (h : OpT p cx x (.fetch o acq rel a v) c')
    (ht : cx.peek a = .ok tw) (hw : wordOf tw = some (r, P)) :
    (∃ d, fetchOK P d = true) ∨ P.epoch = true := by
  revert ht hw
  cases h
  all_goals (
    have hpk := ‹Cx.peek _ _ = _›
    have hwo := ‹wordOf _ = _›
    intro ht hw
    rw [ht] at hpk
    cases hpk
    rw [hw] at hwo
    cases hwo)
  · exact Or.inr ‹_›
  · exact Or.inl ⟨_, ‹_›⟩

/-! ## The token is in the frame -/

theorem one_le_of_VRR_tok {ρ : Nat → Nat} {η : TEnv} {r' : Idx} {o : Option (Proto × Idx)} {S : Shp}
    {ws : List Word} {R Rr Rf : Res} (hv : VRR ρ η (.tok r' o) S ws R) (hle : R + Rr ≤ Rf) :
    1 ≤ Rf (.rg (ev ρ r')) := by
  simp only [VRR] at hv
  subst hv
  have := (Res.le_def.1 hle) (.rg (ev ρ r'))
  simp only [Res.add_apply, Res.one, ite_true] at this
  omega

/-- **Using a token hands over `rg`**: a frame that uses an atom of type
`tok r' o` holds `rg (ev ρ r')` in its bound `Rf`; the context after the use
is satisfied at `ρ`. -/
theorem tok_frame {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx c₁ : Cx} {env : Env} {tk : At} {r' : Idx} {o : Option (Proto × Idx)} {Rf : Res}
    (hi : FInvR ρ η σs K cx env Rf) (hcr : CohR η) (hu : cx.use tk = .ok (.tok r' o, c₁)) :
    1 ≤ Rf (.rg (ev ρ r')) ∧ Sat c₁.facts ρ := by
  obtain ⟨rt, ws, R, Rr, -, -, -, hv, hi1, hle⟩ := useR hu hi hcr
  exact ⟨one_le_of_VRR_tok hv hle, hi1.1.1⟩

/-! ## Where a step appends -/

/-- `t` is a message the step appended: absent before, present after. -/
def NewAt (mem mem' : Memory) (t : Ts) (m : Msg) : Prop := mem[t]? = none ∧ mem'[t]? = some m

theorem size_le_of_none {mem : Memory} {t : Ts} (h : mem[t]? = none) : mem.size ≤ t := by
  rcases Nat.lt_or_ge t mem.size with hl | hl
  · simp [hl] at h
  · exact hl

/-- A `cas` appends at most at its word's address, the new value, over the
value it read (= the expected value): the predecessor of the appended message
at the address has the expected value. -/
theorem tstep_cas_new {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {acq rel : Bool} {w e v : At} {x : String} {ok fail : Expr}
    (hterm : th.term = .cas acq rel w e v x ok fail)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) :
    ∃ tw pw te ew tv nw, evalAt th.env w = some (tw, [pw]) ∧ evalAt th.env e = some (te, [ew]) ∧
      evalAt th.env v = some (tv, [nw]) ∧ addrOf pw = some m.loc ∧ m.val = nw.val ∧
      ∃ wd, PredAt r.1 m.loc t wd ∧ wd.val = ew.val := by
  obtain ⟨h0, h1⟩ := hn
  simp only [tstep, hterm] at hr
  split at hr
  · rename_i tw pw te ew tv nw hw he hv
    split at hr
    · rename_i b hb
      rw [List.mem_map] at hr
      obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
      obtain ⟨t0, m0, hm0, hl0, -, hcase⟩ := stepRmw_mem hin
      rcases hcase with ⟨-, rfl, -⟩ | ⟨hs, ⟨mv, rfl, -, hadj⟩ | ⟨tw', pm, -, rfl, -⟩⟩
      · simp only at h1; rw [h0] at h1; cases h1
      · simp only at h1
        have hsz := size_le_of_none h0
        rw [Array.getElem?_push] at h1
        split at h1
        · rename_i hts
          subst hts
          cases h1
          have hv0 : m0.val = ew.val := by
            simpa [WeakMem.rmwSucceeds, WeakMem.RmwKind.succeeds] using hs
          obtain ⟨hlt, hbt⟩ := rmwAdjacent_spec hadj
          refine ⟨tw, pw, te, ew, tv, nw, hw, he, hv, hb, ?_, mw m0, ?_, hv0⟩
          · simp [WeakMem.RmwKind.apply, mth, rmwNewVal_dataE]
          · refine ⟨t0, m0, hlt, ?_, hl0, rfl, fun t' m' h1' h2' h3' => ?_⟩
            · simp only [Array.getElem?_push, Nat.ne_of_lt hlt, ite_false]; exact hm0
            · simp only [Array.getElem?_push, Nat.ne_of_lt h2', ite_false] at h3'
              exact hbt t' m' h1' h2' h3'
        · rw [h0] at h1; cases h1
      · simp only at h1; rw [h0] at h1; cases h1
    · simp at hr
  · simp at hr

/-- A `store` appends only inside its target's units: at `offs A j` for a
unit start `j` of the stored type's access list (or the second word of a
two-word unit). -/
theorem tstep_store_new {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) :
    ∃ rt pw A μ u us j, evalAt th.env a = some (rt, [pw]) ∧ addrOf pw = some A ∧
      cellOf rt = some (μ, u) ∧ accs u = some us ∧ m.loc = offs A j ∧
      (OneAt us j ∨ TwoAt us j ∨ ∃ jj, j = jj + 1 ∧ TwoAt us jj) := by
  obtain ⟨h0, h1⟩ := hn
  simp only [tstep, hterm, evalOp] at hr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hin, rfl⟩ := hr
  split at hin
  · rename_i rt pw tv ws hea hev
    split at hin
    · rename_i μ u b hc hb
      split at hin
      · rename_i us hus
        rw [List.mem_map] at hin
        obtain ⟨s'', hs'', he⟩ := hin
        injection he with e1 e2
        subst e1
        obtain ⟨-, -, hrole⟩ := storeUnits_roles us ws 0 (stOf mem pairs th) s'' hs''
        obtain ⟨j, hloc, hj⟩ := hrole t m (size_le_of_none h0) h1
        refine ⟨rt, pw, b, μ, u, us, j, hea, hb, hc, hus, by simpa using hloc, ?_⟩
        rcases hj with h | ⟨h, -⟩ | ⟨jj, q, m0, rfl, h, -⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨jj, rfl, h⟩)
      · simp at hin
    · simp at hin
  · simp at hin

/-- A `fetch` appends at most at its word's address. -/
theorem tstep_fetch_new {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) :
    ∃ rt pw, evalAt th.env a = some (rt, [pw]) ∧ addrOf pw = some m.loc := by
  obtain ⟨h0, h1⟩ := hn
  simp only [tstep, hterm, evalOp] at hr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hin, rfl⟩ := hr
  split at hin
  · rename_i rt pw tv nw hea hev
    split at hin
    · rename_i b hb
      rw [List.mem_map] at hin
      obtain ⟨⟨mem', th'⟩, hst, he⟩ := hin
      injection he with e1 e2
      subst e1
      simp only at h1
      obtain ⟨t0, m0, hm0, hl0, -, hcase⟩ := stepRmw_mem hst
      rcases hcase with ⟨-, rfl, -⟩ | ⟨-, ⟨mv, rfl, -, -⟩ | ⟨tw', pm, -, rfl, -⟩⟩
      · simp_all
      · simp only [stOf] at h0 h1
        rw [Array.getElem?_push] at h1
        split at h1
        · cases h1; exact ⟨rt, pw, hea, hb⟩
        · rw [h0] at h1; cases h1
      · simp_all
    · simp at hin
  · simp at hin

/-! ## The word at the operand's address -/

/-- (pair gate) A reference to a non-ghost word of region `r` points at a word unit of region `ev ρ r` in its cell
(the first half of `word_link`). -/
theorem word_cell {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {r : Idx} {P : Proto} {rt : Ty} {pw : Word} {A : Address}
    (hv : VarsOK ρ η σs cx.vars env) (hpk : cx.peek a = .ok t) (hwd : wordOf t = some (r, P))
    (hg : P.ghost = false) (hea : evalAt env a = some (rt, [pw])) (hA : addrOf pw = some A) :
    ∃ c, η.sto A.label = some c ∧ AtOff c.ty A.offset (.word (.lit (ev ρ r)) P) := by
  obtain ⟨μ, hteq⟩ := wordOf_cases hwd
  have hcell : cellOf t = some (μ, .word r P) := by rcases hteq with rfl | rfl <;> simp [cellOf]
  obtain ⟨rt', ws, hea', hvr, -⟩ := peek_VR hv hpk
  rw [hea] at hea'
  cases hea'
  obtain ⟨ad, c, hws, hsto, hat, -, -⟩ := cell_target hcell (Fd_noarr (by simp [cl, accs, hg])) hvr
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
  have hA' : A = ad := by
    simp only [addrOf, hws] at hA
    cases hA; rfl
  subst hA'
  exact ⟨c, hsto, by simpa only [cl, clI_zero] using hat⟩

/-- A reference to a non-ghost word of region `r` and protocol `P` points at a
`WordAt` of region `ev ρ r` and protocol `P`: any `WordAt` at that address is
this one. -/
theorem word_link {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {r : Idx} {P : Proto} {rt : Ty} {pw : Word} {A : Address} {n : Nat} {Pb : Proto}
    (hv : VarsOK ρ η σs cx.vars env) (hpk : cx.peek a = .ok t) (hwd : wordOf t = some (r, P))
    (hg : P.ghost = false) (hea : evalAt env a = some (rt, [pw])) (hA : addrOf pw = some A)
    (hw : WordAt (CE η) A n Pb) : n = ev ρ r ∧ Pb = P := by
  obtain ⟨c, hsto, hat'⟩ := word_cell hv hpk hwd hg hea hA
  obtain ⟨c', hc', hatb, hgb⟩ := hw
  change η.sto A.label = some c' at hc'
  rw [hsto] at hc'
  cases hc'
  obtain ⟨h1, h2⟩ := AtOff_word_uniq hg hgb hat' hatb
  cases h1
  exact ⟨rfl, h2.symm⟩

/-! ## Protocols without held states -/

/-- No clause of `P` is held. -/
def NoHeld (P : Proto) : Prop := ∀ (c : Nat) (cl : Clause), P.clauses[c]? = some cl → cl.holds = true

theorem NoHeld.not_heldV {P : Proto} (h : NoHeld P) (v : WeakMem.Val) : ¬ HeldV P v := by
  rintro ⟨c, cl, k, hc, hh, -⟩
  rw [h c cl hc] at hh
  cases hh

/-- An epoch counter (`pwf`, `epochOK`) is non-ghost and has no held state. -/
theorem epoch_facts {P : Proto} (hpwf : pwf P = true) (hep : P.epoch = true) :
    P.ghost = false ∧ NoHeld P := by
  simp only [pwf, Bool.and_eq_true] at hpwf
  obtain ⟨⟨_, hE⟩, _⟩ := hpwf
  simp only [hep, Bool.not_true, Bool.false_or] at hE
  simp only [epochOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hE
  obtain ⟨⟨⟨⟨⟨⟨hcl, -⟩, -⟩, -⟩, -⟩, hgh⟩, -⟩ := hE
  refine ⟨hgh, fun c cl hc => ?_⟩
  rw [hcl] at hc
  cases c with
  | zero => simp at hc; rw [← hc]
  | succ c => simp at hc

/-- A `fetchOK` protocol is non-ghost and has no held state. -/
theorem fetchOK_facts {P : Proto} {d : Nat} (h : fetchOK P d = true) : P.ghost = false ∧ NoHeld P := by
  simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hg, -⟩, -⟩, -⟩, hall⟩ := h
  refine ⟨hg, fun c cl hc => ?_⟩
  have := hall (c, cl) (by simpa using TermLiveProps.enumFrom_mem P.clauses 0 c cl hc)
  exact this.1

/-- **B-compatibility.**  A robust protocol (`pwf`) has no held state, so no
value at a robust word is held: no step enters or leaves a held state there. -/
theorem robust_noHeld {P : Proto} (hpwf : pwf P = true) (hrob : P.robust = true) : NoHeld P :=
  fun _ _ hc => TermLiveProps.robust_holds hpwf hrob hc

theorem robust_held_static {P : Proto} (hpwf : pwf P = true) (hrob : P.robust = true) (v : WeakMem.Val) :
    ¬ HeldV P v :=
  (robust_noHeld hpwf hrob).not_heldV v

/-- Under `pwf`, a holding value is not a held one (clauses are disjoint). -/
theorem holds_not_heldV {P : Proto} (hpwf : pwf P = true) {v : WeakMem.Val} (h : WordHolds P [v]) :
    ¬ HeldV P v := by
  rintro ⟨c, cl, k, hc, hh, rfl⟩
  have := (WordHolds_clause hpwf h.1 hc k).1 h
  rw [this] at hh
  cases hh

/-! ## C1 per operation -/

/-- (pair gate) Where a word `store` appends: at the word's own unit `A`, and the word is non-ghost (a ghost word's
store appends nothing).  Factored out of `store_word_step`. -/
theorem store_word_loc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {e : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok tw) (hwd : wordOf tw = some (r0, P0))
    (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) :
    ∃ rt pw A, evalAt th.env a = some (rt, [pw]) ∧ addrOf pw = some A ∧ P0.ghost = false ∧ m.loc = A := by
  obtain ⟨rt, pw, A, μr, ru, us, j, hea, hA, hcr, hus, hloc, hj⟩ := tstep_store_new hterm hr hn
  have hi0 := hi.1
  obtain ⟨μ, hteq⟩ := wordOf_cases hwd
  have hcell : cellOf tw = some (μ, .word r0 P0) := by rcases hteq with rfl | rfl <;> simp [cellOf]
  have ho : cx.opaqueOK (.word r0 P0) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hlr := pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk hcell ho hea hcr
  rw [hus] at hlr
  cases hg : P0.ghost
  · have hus1 : us = [.one] := by simpa [cl, accs, hg] using hlr
    subst hus1
    have hj0 : j = 0 := by
      rcases hj with ⟨i, hi', rfl⟩ | ⟨i, hi', -⟩ | ⟨jj, -, i, hi', -⟩
      · cases i with
        | zero => rfl
        | succ i => simp at hi'
      · cases i <;> simp at hi'
      · cases i <;> simp at hi'
    subst hj0
    exact ⟨rt, pw, A, hea, hA, rfl, by rw [hloc]; exact TermLiveProps.offs_zero A⟩
  · have hus0 : us = [] := by simpa [cl, accs, hg] using hlr
    subst hus0
    exfalso
    rcases hj with ⟨i, hi', -⟩ | ⟨i, hi', -⟩ | ⟨jj, -, i, hi', -⟩ <;> simp at hi'

/-- **Word store.**  A store on a protocol word that appends at a `WordAt` of
region `n` was made by a thread whose frame holds `rg n` (the `tok` operand). -/
theorem store_word_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {e : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hop : OpT p cx x (.store rel a v tok) c')
    (hpk : cx.peek a = .ok tw) (hwd : wordOf tw = some (r0, P0))
    (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) :
    1 ≤ Rf (.rg n) := by
  obtain ⟨tk, r', i, c₁, rfl, hu, hrr⟩ := store_word_tok hop hpk hwd
  obtain ⟨hle, hsat⟩ := tok_frame hi hE.2.2 hu
  have he : ev ρ r0 = ev ρ r' := hrr ρ hsat
  obtain ⟨rt, pw, A, hea, hA, hg, hmA⟩ := store_word_loc hterm hpk hwd hi hE htv hr hn
  rw [hmA] at hw
  obtain ⟨rfl, -⟩ := word_link hi.1.2.1 hpk hwd hg hea hA hw
  rw [he]
  exact hle


/-- (pair gate) A `cas` on an epoch counter (`cas_word_inv`'s epoch branch): the word is non-ghost and has no held
state.  Factored out of `cas_word_step`. -/
theorem cas_word_epoch {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {acq rel : Bool} {w e v : At} {x : String} {ok fail : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto}
    (hpk : cx.peek w = .ok tw) (hwd : wordOf tw = some (r0, P0))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx (.cas acq rel w e v x ok fail))
    (hep : P0.epoch = true) : P0.ghost = false ∧ NoHeld P0 := by
  rcases hsc tw hpk with ⟨μ, r1, P1, hteq, hμ⟩ | ⟨u, -, hnw⟩
  · have hpwf1 := wordRef_pwf hpk hteq hμ hi hE htv hm
    have hP : P1 = P0 := by
      rcases hteq with rfl | rfl <;> simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hwd <;>
        exact hwd.2
    subst hP
    exact epoch_facts hpwf1 hep
  · rw [hwd] at hnw
    cases hnw

/-- **Word `cas`.**  A `cas` on a protocol word that appends at a `WordAt` of
protocol `P` overwrote a holding value of `P` (it read the expected value,
whose clause holds), or `P` has no held state (an epoch counter). -/
theorem cas_word_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {acq rel : Bool} {w e v : At} {x : String} {ok fail : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto}
    (hterm : th.term = .cas acq rel w e v x ok fail) (hT : Typed p cx (.cas acq rel w e v x ok fail))
    (hpk : cx.peek w = .ok tw) (hwd : wordOf tw = some (r0, P0))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx (.cas acq rel w e v x ok fail))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) :
    (∃ wd, PredAt r.1 m.loc t wd ∧ WordHolds P [wd.val]) ∨ NoHeld P := by
  obtain ⟨i, j, c, k, c', k', hie, -, hst, -, hsrc⟩ := cas_word_inv hT hpk hwd
  obtain ⟨tw', pw, te, ew, tv, nw, hea, hee, -, hA, -, wd, hpred, hwv⟩ := tstep_cas_new hterm hr hn
  have hsat : Sat cx.facts ρ := hi.1
  rcases hsrc with ⟨cl, hcl, hh, hg⟩ | hep
  · obtain ⟨-, rfl⟩ := word_link hi.2.1 hpk hwd hg hea hA hw
    left
    obtain ⟨tv', htvk, hio⟩ := hie
    obtain ⟨rt2, w2, hev2, hwv2, -⟩ := atom_num hi.2.1 htvk hio
    rw [hee] at hev2
    cases hev2
    obtain ⟨cl0, hcl0, hent⟩ := hst
    rw [hcl] at hcl0
    cases hcl0
    exact ⟨wd, hpred, hg, ev ρ i, c, _, ev ρ k, by rw [hwv, hwv2], hcl, hh, hent ρ hsat⟩
  · obtain ⟨hg, hno⟩ := cas_word_epoch hpk hwd hi hE htv hm hsc hep
    obtain ⟨-, rfl⟩ := word_link hi.2.1 hpk hwd hg hea hA hw
    exact Or.inr hno

/-- (pair gate) A fetch on a protocol word: the word is non-ghost and has no held state (`fetchOK`, or an epoch
counter).  Factored out of `fetch_word_step`. -/
theorem fetch_word_facts {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto}
    (hop : OpT p cx x (.fetch o acq rel a v) c')
    (hpk : cx.peek a = .ok tw) (hwd : wordOf tw = some (r0, P0))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx (.let_ x (.fetch o acq rel a v) e)) :
    P0.ghost = false ∧ NoHeld P0 := by
  rcases fetch_word_inv hop hpk hwd with ⟨d, hd⟩ | hep
  · exact fetchOK_facts hd
  · obtain ⟨μ, u, hteq, hμ⟩ := hsc tw hpk
    obtain ⟨μ', hteq'⟩ := wordOf_cases hwd
    have hμ' : μ' = .own ∨ μ' = .pub := by
      rcases hteq' with rfl | rfl <;> rcases hteq with h | h <;> cases h <;> exact hμ
    exact epoch_facts (wordRef_pwf hpk hteq' hμ' hi hE htv hm) hep

/-- **Word `fetch`.**  A fetch on a protocol word appends only at a word whose
protocol has no held state (`fetchOK`, or an epoch counter). -/
theorem fetch_word_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (hop : OpT p cx x (.fetch o acq rel a v) c')
    (hpk : cx.peek a = .ok tw) (hwd : wordOf tw = some (r0, P0))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx (.let_ x (.fetch o acq rel a v) e))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) :
    NoHeld P := by
  obtain ⟨rt, pw, hea, hA⟩ := tstep_fetch_new hterm hr hn
  have hfacts : P0.ghost = false ∧ NoHeld P0 := fetch_word_facts hop hpk hwd hi hE htv hm hsc
  obtain ⟨-, rfl⟩ := word_link hi.2.1 hpk hwd hfacts.1 hea hA hw
  exact hfacts.2


/-! ## C1 -/

/-- The terms whose step may append at a protocol word: a `store`, `fetch`
or `cas` whose address operand is typed as a protocol word. -/
def WordOp (cx : Cx) : Expr → Prop
  | .let_ _ (.store _ a _ _) _ => ∃ t rP, cx.peek a = .ok t ∧ wordOf t = some rP
  | .let_ _ (.fetch _ _ _ a _) _ => ∃ t rP, cx.peek a = .ok t ∧ wordOf t = some rP
  | .cas _ _ w _ _ _ _ _ => ∃ t rP, cx.peek w = .ok t ∧ wordOf t = some rP
  | _ => False

/-! ## W1: the word key `wd n` -/

/-- A word unit is initialised: in a buffer, it lies in an initialised slot. -/
def IniU (η : TEnv) (A : Address) (n : Nat) (P : Proto) : Prop :=
  ∀ c, η.sto A.label = some c → IniAt η.ini c A (.word (.lit n) P)

/-- (pair gate) The core of `wd_held`: memory's held part holds `wd n` when an initialised unit `U` with words
(not an array) sits at `A` in its cell, and every reading of `U` carries `wd n`.  Shared by the word instance
`wd_held` and the pair instance (`TermLiveC2.wd2_held`). -/
theorem wd_held_core {η : TEnv} {s : St} {H : Res} {A : Address} {n : Nat} {U : Ty} {c : Cell}
    (hH : MemHeld (CE η) s H) (hsto : η.sto A.label = some c) (hat : AtOff c.ty A.offset U)
    (hini : IniAt η.ini c A U) (hna : ∀ N e, U ≠ .array (.lit N) e) (hz : ∃ us, accs U = some us ∧ nWords us ≠ 0)
    (hkey : ∀ ρ E ws R, VRR ρ E U (shp U) ws R → Res.one (.wd n) ≤ R) :
    1 ≤ H (.wd n) := by
  obtain ⟨R0, H0, rfl, hent0, -⟩ := MemHeld_focus hH A.label
  obtain ⟨vals0, -, hC0⟩ := hent0.2 c hsto
  obtain ⟨b, oS, S, wS, Rsg, Rrc, -, hbo, hatS, hwS, hbw, hR0, ⟨hvs, -⟩, -⟩ :=
    (own_segR hC0 hat hini hna).resolve_right (fun ⟨_, _, _, _, _, _, _, hz0⟩ => by
      obtain ⟨us, hus, hne⟩ := hz
      exact hne (hz0 us hus))
  have hsl : ((vals0.drop b).take wS).length = wS := by
    simp only [List.length_take, List.length_drop]; omega
  obtain ⟨n1, Rq, Rr2, -, -, hRs, hRq0, -⟩ := VRR_at (CE η).unsee hatS hvs (by rw [hsl]; exact hwS)
  have h := hkey _ _ _ _ hRq0 (.wd n)
  subst hR0 hRs
  simp only [Res.add_apply, Res.one, ite_true] at h ⊢
  omega

/-- **(W1, memory half)** Memory's held part holds the word key of every
initialised non-epoch word unit: the unit's reading is a `VRR .word` value,
which carries `wd n` whether it holds or not. -/
theorem wd_held {η : TEnv} {s : St} {H : Res} {A : Address} {n : Nat} {P : Proto}
    (hH : MemHeld (CE η) s H) (hw : WordAt (CE η) A n P) (hini : IniU η A n P) (hep : P.epoch = false) :
    1 ≤ H (.wd n) := by
  obtain ⟨c, hsto, hat, hg⟩ := hw
  exact wd_held_core hH hsto hat (hini c hsto) (fun N e h => by cases h)
    ⟨_, (by simp [accs, hg] : accs (Ty.word (.lit n) P) = some [.one]), by simp [nWords, Acc.size]⟩
    (fun _ _ _ _ h => by
      have h1 := wdW_le_VRR_word h
      rwa [wdW_nepoch hep] at h1)


/-- **`wholecell_two_carriers`.**  A thread whose frame holds (under `Rf`) a
value of a cell's whole type `T`, at an address whose cell has an initialised
non-epoch word unit of region `n`, makes two carriers of `wd n`: one in the
value (at the unit's offset), one in memory (`wd_held`).  Every whole-cell op
(`storeOwn`/`storeLoc`, `xchg`/`xchgLoc`, `xchgAt(F)`, `bufInit`, a whole-cell
`storePub`) writing over such a unit is in this situation. -/
theorem wholecell_two_carriers {η E' : TEnv} {s : St} {H Rf Rv Rr : Res} {A : Address} {n : Nat}
    {P : Proto} {T : Ty} {ws : List Word} {ρ₀ : Nat → Nat}
    (hH : MemHeld (CE η) s H) (hw : WordAt (CE η) A n P) (hini : IniU η A n P) (hep : P.epoch = false)
    (hT : ∃ c, η.sto A.label = some c ∧ c.ty = T)
    (hv : VRR ρ₀ (CE E') T (shp T) ws Rv) (hwc : wc T = some ws.length) (hle : Rv + Rr ≤ Rf) :
    2 ≤ Rf (.wd n) + H (.wd n) := by
  have hm := wd_held hH hw hini hep
  obtain ⟨c, hsto, hat, -⟩ := hw
  change η.sto A.label = some c at hsto
  obtain ⟨c', hs', rfl⟩ := hT
  rw [hsto] at hs'
  cases hs'
  obtain ⟨n1, Rq, Rr2, -, -, hRv, hRq, -⟩ := VRR_at E' hat hv hwc
  have h := wdW_le_VRR_word hRq (.wd n)
  rw [wdW_nepoch hep] at h
  have h2 := hle (.wd n)
  subst hRv
  simp only [Res.add_apply, Res.one, ite_true] at h h2
  omega

/-- Under the thread's share of W1 (`Rf (wd n) + H (wd n) ≤ 1`), no whole-cell
value of the cell's type sits in the frame. -/
theorem wholecell_excluded {η E' : TEnv} {s : St} {H Rf Rv Rr : Res} {A : Address} {n : Nat}
    {P : Proto} {T : Ty} {ws : List Word} {ρ₀ : Nat → Nat}
    (hwd : Rf (.wd n) + H (.wd n) ≤ 1)
    (hH : MemHeld (CE η) s H) (hw : WordAt (CE η) A n P) (hini : IniU η A n P) (hep : P.epoch = false)
    (hT : ∃ c, η.sto A.label = some c ∧ c.ty = T)
    (hv : VRR ρ₀ (CE E') T (shp T) ws Rv) (hwc : wc T = some ws.length) (hle : Rv + Rr ≤ Rf) : False := by
  have := wholecell_two_carriers hH hw hini hep hT hv hwc hle
  omega

/-- **The per-thread footprint obligation for the remaining ops (W1 form).**
A step of a term that does not address a protocol word as a word appends at a
non-epoch `WordAt` of region `n` only if the thread's frame carries `wd n`
(a whole-cell op: the written value has a word of region `n` at the unit's
offset, `wholecell_two_carriers`).  Type-disjoint ops (`casCell`/`fetchCell`,
`stl`/`stlw`, `stp`/`casp`, allocations at fresh labels) never append at a
`WordAt` at all, so satisfy it vacuously. -/
def NonWordFootT (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (cx : Cx) (E : TEnv) (Rf : Res) : Prop :=
  ¬ WordOp cx th.term → ∀ r ∈ tstep g mem pairs th, ∀ t m, NewAt mem r.1 t m → ∀ n P,
    WordAt E m.loc n P → P.epoch = false → 1 ≤ Rf (.wd n)



/-! ## `NonWordFootT`, per operation -/

theorem nW_one : nWords [Acc.one] = 1 := by simp [nWords, Acc.size]

/-- The messages a `storeUnits` appends lie inside the stored units. -/
theorem storeUnits_new_loc {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {s s' : St} {mem : Memory}
    (hs : s' ∈ storeUnits k arch pw a rel us ws 0 s) (hsm : s.mem = mem) {t : Ts} {m : Msg}
    (hn : NewAt mem s'.mem t m) : ∃ j, j < nWords us ∧ m.loc = offs a j := by
  obtain ⟨-, -, hrole⟩ := storeUnits_roles us ws 0 s s' hs
  subst hsm
  obtain ⟨j, hloc, hj⟩ := hrole t m (size_le_of_none hn.1) hn.2
  refine ⟨j, ?_, by simpa using hloc⟩
  rcases hj with h | ⟨h, -⟩ | ⟨jj, -, -, rfl, h, -⟩
  · have := OneAt_lt h; omega
  · have := TwoAt_lt h; omega
  · have := TwoAt_lt h; omega

/-- **Frame half, whole cell**: a frame value of the cell's type carries the
word key of each of the cell's non-epoch word units. -/
theorem wd_frame_whole {η E' : TEnv} {Rf Rv Rr : Res} {c : Cell} {ws : List Word} {ρ₀ : Nat → Nat}
    {A : Address} {n : Nat} {P : Proto}
    (hsto : η.sto A.label = some c) (hv : VRR ρ₀ (CE E') c.ty (shp c.ty) ws Rv)
    (hwc : wc c.ty = some ws.length) (hle : Rv + Rr ≤ Rf)
    (hw : WordAt (CE η) A n P) (hep : P.epoch = false) : 1 ≤ Rf (.wd n) := by
  obtain ⟨c0, hs0, hat0, -⟩ := hw
  change η.sto A.label = some c0 at hs0
  rw [hsto] at hs0
  cases hs0
  obtain ⟨n1, Rq, Rr2, -, -, hRv, hRq, -⟩ := VRR_at E' hat0 hv hwc
  have h := wdW_le_VRR_word hRq (.wd n)
  rw [wdW_nepoch hep] at h
  have h2 := hle (.wd n)
  subst hRv
  simp only [Res.add_apply, Res.one, ite_true] at h h2
  omega

/-- **Frame half, a component**: a frame value of a component type `U` (at
offset `o` of the cell) carries the word key of each non-epoch word unit
inside `U`. -/
theorem wd_frame_comp {η E' : TEnv} {Rf Rv Rr : Res} {lab : AllocLabel} {c : Cell} {o j : Nat} {U : Ty}
    {ws : List Word} {ρ₀ : Nat → Nat} {A : Address} {n : Nat} {P : Proto}
    (hsto : η.sto lab = some c) (hat : AtOff c.ty o U)
    (hv : VRR ρ₀ (CE E') U (shp U) ws Rv) (hwc : wc U = some ws.length) (hle : Rv + Rr ≤ Rf)
    (hA : A.label = lab) (hoff : A.offset = o + j) (hj : j < ws.length)
    (hw : WordAt (CE η) A n P) (hep : P.epoch = false) : 1 ≤ Rf (.wd n) := by
  obtain ⟨c', hs', hat', hg⟩ := hw
  change η.sto A.label = some c' at hs'
  rw [hA, hsto] at hs'
  cases hs'
  obtain ⟨us, hus, hus'⟩ : ∃ us, accs U = some us ∧ nWords us = ws.length := by
    cases h : accs U with
    | none => simp [wc, h] at hwc
    | some us => exact ⟨us, rfl, by simpa [wc, h] using hwc⟩
  rw [hoff] at hat'
  rcases AtOff_nest (Solid_word _ P) (accs_word hg) hat hus hat' with h | h | ⟨-, h⟩
  · rw [nW_one] at h; omega
  · omega
  · rw [Nat.add_sub_cancel_left] at h
    obtain ⟨n1, Rq, Rr2, -, -, hRv, hRq, -⟩ := VRR_at E' h hv hwc
    have h1 := wdW_le_VRR_word hRq (.wd n)
    rw [wdW_nepoch hep] at h1
    have h2 := hle (.wd n)
    subst hRv
    simp only [Res.add_apply, Res.one, ite_true] at h1 h2
    omega

/-- A leaf component other than a word holds no word unit. -/
theorem solid_no_word {η : TEnv} {lab : AllocLabel} {c : Cell} {o j : Nat} {U : Ty} {us : List Acc}
    {A : Address} {n : Nat} {P : Proto}
    (hsto : η.sto lab = some c) (hat : AtOff c.ty o U) (hS : Solid U) (hne : ∀ r P, U ≠ .word r P)
    (hus : accs U = some us) (hA : A.label = lab) (hoff : A.offset = o + j) (hj : j < nWords us)
    (hw : WordAt (CE η) A n P) : False := by
  obtain ⟨c', hs', hat', hg⟩ := hw
  change η.sto A.label = some c' at hs'
  rw [hA, hsto] at hs'
  cases hs'
  rw [hoff] at hat'
  rcases AtOff_nest (Solid_word _ P) (accs_word hg) hat hus hat' with h | h | ⟨-, h⟩
  · rw [nW_one] at h; omega
  · omega
  · rw [Nat.add_sub_cancel_left] at h
    obtain ⟨-, e⟩ := AtOff_solid hS (fun t h => by cases h) h
    exact hne _ _ e.symm

/-- A deeply word-free component holds no word unit. -/
theorem dwf_no_word {η : TEnv} {lab : AllocLabel} {c : Cell} {o j : Nat} {U : Ty} {us : List Acc}
    {A : Address} {n : Nat} {P : Proto}
    (hsto : η.sto lab = some c) (hat : AtOff c.ty o U) (hdw : dwf U = true)
    (hus : accs U = some us) (hA : A.label = lab) (hoff : A.offset = o + j) (hj : j < nWords us)
    (hw : WordAt (CE η) A n P) : False := by
  obtain ⟨c', hs', hat', hg⟩ := hw
  change η.sto A.label = some c' at hs'
  rw [hA, hsto] at hs'
  cases hs'
  rw [hoff] at hat'
  rcases AtOff_wordFree_disj hg hat hdw hus hat' with h | h <;> omega

/-- An allocation appends only at a label outside Σ: never at a `WordAt`. -/
theorem grows_no_word {η : TEnv} {mem mem' : Memory} {lbl : AllocLabel} (hg : GrowsAt mem mem' lbl)
    (hnone : η.sto lbl = none) {t : Ts} {m : Msg} (hn : NewAt mem mem' t m) {n : Nat} {P : Proto}
    (hw : WordAt (CE η) m.loc n P) : False := by
  have hl := hg.2.2 t m (size_le_of_none hn.1) hn.2
  obtain ⟨c, hs, -, -⟩ := hw
  change η.sto m.loc.label = some c at hs
  rw [hl, hnone] at hs
  cases hs

theorem keep_no_new {mem mem' : Memory} (h : mem' = mem) {t : Ts} {m : Msg} (hn : NewAt mem mem' t m) : False := by
  subst h
  have h2 := hn.2
  rw [hn.1] at h2
  cases h2
/-! ### Word-key units (pair gate) -/

/-- (pair gate) `A` is one of the two units of a protocol pair of region `n` in its cell. -/
def PairUnit (E : TEnv) (A : Address) (n : Nat) : Prop :=
  ∃ c o P, E.sto A.label = some c ∧ AtOff c.ty o (.word2 (.lit n) P) ∧ o ≤ A.offset ∧ A.offset < o + 2

/-- (pair gate) A unit whose readings carry the word key `wd n`: a non-epoch word unit, or a pair unit. -/
def WdAt (E : TEnv) (A : Address) (n : Nat) : Prop :=
  (∃ P, WordAt E A n P ∧ P.epoch = false) ∨ PairUnit E A n

/-- (pair gate) A word unit or a pair unit (of region `n`). -/
def WUnit (E : TEnv) (A : Address) (n : Nat) : Prop :=
  (∃ P, WordAt E A n P) ∨ PairUnit E A n

theorem WdAt.unit {E : TEnv} {A : Address} {n : Nat} (h : WdAt E A n) : WUnit E A n := by
  rcases h with ⟨P, hw, -⟩ | h
  · exact Or.inl ⟨P, hw⟩
  · exact Or.inr h

/-- (pair gate) `wd_frame_whole` for every word-key unit. -/
theorem wd_frame_wholeG {η E' : TEnv} {Rf Rv Rr : Res} {c : Cell} {ws : List Word} {ρ₀ : Nat → Nat}
    {A : Address} {n : Nat}
    (hsto : η.sto A.label = some c) (hv : VRR ρ₀ (CE E') c.ty (shp c.ty) ws Rv)
    (hwc : wc c.ty = some ws.length) (hle : Rv + Rr ≤ Rf)
    (hw : WdAt (CE η) A n) : 1 ≤ Rf (.wd n) := by
  rcases hw with ⟨P, hw, hep⟩ | ⟨c0, o2, P, hs0, hat0, -, -⟩
  · exact wd_frame_whole hsto hv hwc hle hw hep
  · change η.sto A.label = some c0 at hs0
    rw [hsto] at hs0
    cases hs0
    obtain ⟨n1, Rq, Rr2, -, -, hRv, hRq, -⟩ := VRR_at E' hat0 hv hwc
    have h := wd_le_VRR_word2 hRq (.wd n)
    have h2 := hle (.wd n)
    subst hRv
    simp only [Res.add_apply, Res.one, ite_true] at h h2
    omega

/-- (pair gate) `wd_frame_comp` for every word-key unit. -/
theorem wd_frame_compG {η E' : TEnv} {Rf Rv Rr : Res} {lab : AllocLabel} {c : Cell} {o j : Nat} {U : Ty}
    {ws : List Word} {ρ₀ : Nat → Nat} {A : Address} {n : Nat}
    (hsto : η.sto lab = some c) (hat : AtOff c.ty o U)
    (hv : VRR ρ₀ (CE E') U (shp U) ws Rv) (hwc : wc U = some ws.length) (hle : Rv + Rr ≤ Rf)
    (hA : A.label = lab) (hoff : A.offset = o + j) (hj : j < ws.length)
    (hw : WdAt (CE η) A n) : 1 ≤ Rf (.wd n) := by
  rcases hw with ⟨P, hw, hep⟩ | ⟨c', o2, P, hs', hat', ho1, ho2⟩
  · exact wd_frame_comp hsto hat hv hwc hle hA hoff hj hw hep
  · change η.sto A.label = some c' at hs'
    rw [hA, hsto] at hs'
    cases hs'
    obtain ⟨us, hus, hus'⟩ : ∃ us, accs U = some us ∧ nWords us = ws.length := by
      cases h : accs U with
      | none => simp [wc, h] at hwc
      | some us => exact ⟨us, rfl, by simpa [wc, h] using hwc⟩
    have h2w : nWords [Acc.two] = 2 := by simp [nWords, Acc.size]
    have k1 : o2 ≤ o + j := by rw [← hoff]; exact ho1
    have k2 : o + j < o2 + 2 := by rw [← hoff]; exact ho2
    rcases AtOff_nest (Solid_word2 _ P) accs_word2 hat hus hat' with h | h | ⟨-, h⟩
    · omega
    · omega
    · obtain ⟨n1, Rq, Rr2, -, -, hRv, hRq, -⟩ := VRR_at E' h hv hwc
      have h1 := wd_le_VRR_word2 hRq (.wd n)
      have h2 := hle (.wd n)
      subst hRv
      simp only [Res.add_apply, Res.one, ite_true] at h1 h2
      omega

/-- (pair gate) `solid_no_word` for word and pair units (a solid leaf other than a word or a pair). -/
theorem solid_no_wordG {η : TEnv} {lab : AllocLabel} {c : Cell} {o j : Nat} {U : Ty} {us : List Acc}
    {A : Address} {n : Nat}
    (hsto : η.sto lab = some c) (hat : AtOff c.ty o U) (hS : Solid U) (hne : ∀ r P, U ≠ .word r P)
    (hne2 : ∀ r P, U ≠ .word2 r P)
    (hus : accs U = some us) (hA : A.label = lab) (hoff : A.offset = o + j) (hj : j < nWords us)
    (hw : WUnit (CE η) A n) : False := by
  rcases hw with ⟨P, hw⟩ | ⟨c', o2, P, hs', hat', ho1, ho2⟩
  · exact solid_no_word hsto hat hS hne hus hA hoff hj hw
  · change η.sto A.label = some c' at hs'
    rw [hA, hsto] at hs'
    cases hs'
    have h2w : nWords [Acc.two] = 2 := by simp [nWords, Acc.size]
    have k1 : o2 ≤ o + j := by rw [← hoff]; exact ho1
    have k2 : o + j < o2 + 2 := by rw [← hoff]; exact ho2
    rcases AtOff_nest (Solid_word2 _ P) accs_word2 hat hus hat' with h | h | ⟨-, h⟩
    · omega
    · omega
    · obtain ⟨-, e⟩ := AtOff_solid hS (fun t h => by cases h) h
      exact hne2 _ _ e.symm

/-- (pair gate) `dwf_no_word` for word and pair units. -/
theorem dwf_no_wordG {η : TEnv} {lab : AllocLabel} {c : Cell} {o j : Nat} {U : Ty} {us : List Acc}
    {A : Address} {n : Nat}
    (hsto : η.sto lab = some c) (hat : AtOff c.ty o U) (hdw : dwf U = true)
    (hus : accs U = some us) (hA : A.label = lab) (hoff : A.offset = o + j) (hj : j < nWords us)
    (hw : WUnit (CE η) A n) : False := by
  rcases hw with ⟨P, hw⟩ | ⟨c', o2, P, hs', hat', ho1, ho2⟩
  · exact dwf_no_word hsto hat hdw hus hA hoff hj hw
  · change η.sto A.label = some c' at hs'
    rw [hA, hsto] at hs'
    cases hs'
    have k1 : o2 ≤ o + j := by rw [← hoff]; exact ho1
    have k2 : o + j < o2 + 2 := by rw [← hoff]; exact ho2
    rcases AtOff_wordFree_disj2 hat hdw hus hat' with h | h <;> omega

/-- (pair gate) `grows_no_word` for word and pair units. -/
theorem grows_no_wordG {η : TEnv} {mem mem' : Memory} {lbl : AllocLabel} (hg : GrowsAt mem mem' lbl)
    (hnone : η.sto lbl = none) {t : Ts} {m : Msg} (hn : NewAt mem mem' t m) {n : Nat}
    (hw : WUnit (CE η) m.loc n) : False := by
  rcases hw with ⟨P, hw⟩ | ⟨c, -, -, hs, -⟩
  · exact grows_no_word hg hnone hn hw
  · have hl := hg.2.2 t m (size_le_of_none hn.1) hn.2
    change η.sto m.loc.label = some c at hs
    rw [hl, hnone] at hs
    cases hs

/-- (pair gate) `storeOwn_wd_frame` for every word-key unit (`WdAt`: a non-epoch word unit or either unit of a protocol
pair); `storeOwn_wd_frame` is its word instance. -/
theorem storeOwn_wd_frameG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WdAt (CE η) m.loc n) :
    1 ≤ Rf (.wd n) := by
  have hterm0 := hterm
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t0, u', tv, c₁, hp, hc, hu, hsub⟩ : ∃ t0 u' tv c₁, cx.peek a = .ok t0 ∧
      cellOf t0 = some (.own, u') ∧ cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u' :=
    ⟨_, _, _, _, hp, hc, hu, hsub⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨-, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  have hvR : VRR (fun _ => 0) (CE (CE η)) c.ty (shp c.ty) wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRR ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_sub hsat hsub _ _ _ hvrv
    have hvc : VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_close hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    rw [(Fd_lay hcty).1]
    exact (Fd_VRR η hcty).2 hvc
  obtain ⟨rt', pw', A, μr, ru', us', j, hea', hA, -, -, hloc, -⟩ := tstep_store_new hterm0 hr hn
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨-, rfl⟩ := hea'
  have hlab : m.loc.label = lab := by
    simp only [addrOf, hpw, Option.some.injEq] at hA
    subst hA
    rw [hloc]
    rfl
  exact wd_frame_wholeG (by rw [hlab]; exact hsto) hvR (by rw [hus', hlen]) hle hw

/-- **`NonWordFootT` at `storeOwn`** (frame half of `wholecell_two_carriers`):
an own whole-cell store that appends at a non-epoch `WordAt` of region `n` is
made by a thread whose frame carries `wd n` — the stored value has a word of
region `n` at the unit's offset. -/
theorem storeOwn_wd_frame {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) :=
  storeOwn_wd_frameG hterm hpk hnw hT hi hE htv hr hn (Or.inl ⟨P, hw, hep⟩)


/-- (pair gate) `storeLoc_wd_frame` for every word-key unit (`WdAt`: a non-epoch word unit or either unit of a protocol
pair); `storeLoc_wd_frame` is its word instance. -/
theorem storeLoc_wd_frameG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WdAt (CE η) m.loc n) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t0, u', tv, c₁, hp, hc, hu, hsub⟩ : ∃ t0 u' tv c₁, cx.peek a = .ok t0 ∧
      cellOf t0 = some (.own, u') ∧ cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u' :=
    ⟨_, _, _, _, hp, hc, hu, hsub⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locView hi0 hpk htv ho hwcu
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key, List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  obtain ⟨jj, hjj, hloc⟩ := storeUnits_new_loc hs' rfl hn
  exact wd_frame_compG hsto hat hvalR.1 (by rw [hwU, hlen]) hle (by rw [hloc]; rfl) (by rw [hloc]; rfl)
    (by rw [hlen]; exact hjj) hw

/-- **`NonWordFootT` at `storeLoc`** (an own locative): the stored value has
a word of region `n` at the unit's offset within the component. -/
theorem storeLoc_wd_frame {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) :=
  storeLoc_wd_frameG hterm hpk hnw hT hi hE htv hr hn (Or.inl ⟨P, hw, hep⟩)


/-- (pair gate) `storePub_wd_frame` for every word-key unit (`WdAt`: a non-epoch word unit or either unit of a protocol
pair); `storePub_wd_frame` is its word instance. -/
theorem storePub_wd_frameG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WdAt (CE η) m.loc n) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t0, u', tv, c₁, hp, hc, hu, hsub⟩ : ∃ t0 u' tv c₁, cx.peek a = .ok t0 ∧
      cellOf t0 = some (.pub, u') ∧ cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u' :=
    ⟨_, _, _, _, hp, hc, hu, hsub⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_view hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hlr : accs ru = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    cases h : accs ru with
    | none => rw [h] at hlr; exact absurd hlr.symm hacc
    | some us => exact ⟨us, rfl⟩
  have husc : accs c.ty = some us := by rw [← hlr, hus]
  have hus' : wc c.ty = some (nWords us) := by simp [wc, husc]
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hvR : VRR (fun _ => 0) (CE (CE η)) c.ty (shp c.ty) wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRR ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_sub hsat hsub _ _ _ hvrv
    have hvc : VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_close hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    rw [(Fd_lay hcty).1]
    exact (Fd_VRR η hcty).2 hvc
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key, List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  obtain ⟨jj, -, hloc⟩ := storeUnits_new_loc hs' rfl hn
  have hl : m.loc.label = lab := by rw [hloc]; rfl
  exact wd_frame_wholeG (by rw [hl]; exact hsto) hvR (by rw [hus', hlen]) hle hw

/-- **`NonWordFootT` at `storePub`** (a pub pointer, whole cell). -/
theorem storePub_wd_frame {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) :=
  storePub_wd_frameG hterm hpk hnw hT hi hE htv hr hn (Or.inl ⟨P, hw, hep⟩)


/-- (pair gate) `storePubLoc_wd_frame` for every word-key unit (`WdAt`: a non-epoch word unit or either unit of a protocol
pair); `storePubLoc_wd_frame` is its word instance. -/
theorem storePubLoc_wd_frameG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WdAt (CE η) m.loc n) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t0, u', tv, c₁, hp, hc, hu, hsub⟩ : ∃ t0 u' tv c₁, cx.peek a = .ok t0 ∧
      cellOf t0 = some (.pub, u') ∧ cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u' :=
    ⟨_, _, _, _, hp, hc, hu, hsub⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_target (rfl : cellOf (.loc .pub u) = some (.pub, u)) (Fd_noarr fun h => hwcu (by simp [wc, h])) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .pub ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact hsigu
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key, List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  obtain ⟨jj, hjj, hloc⟩ := storeUnits_new_loc hs' rfl hn
  exact wd_frame_compG hsto hat hvalR.1 (by rw [hwU, hlen]) hle (by rw [hloc]; rfl) (by rw [hloc]; rfl)
    (by rw [hlen]; exact hjj) hw

/-- **`NonWordFootT` at `storePub` through a pub locative.** -/
theorem storePubLoc_wd_frame {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) :=
  storePubLoc_wd_frameG hterm hpk hnw hT hi hE htv hr hn (Or.inl ⟨P, hw, hep⟩)



/-- The messages an exchange (`loadUnits` then `storeUnits`) appends lie
inside the stored units. -/
theorem xchg_new_loc {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address}
    {us : List Acc} {ws : List Word} {s : St} {mem : Memory}
    (hsm : s.mem = mem) {r : St × Ty × List Word} {T : List Word → Ty}
    (hr : r ∈ (loadUnits arch pw a false us 0 s).flatMap fun (s1, old) =>
        (storeUnits k arch pw a false us ws 0 s1).map fun s2 => (s2, T old, old))
    {t : Ts} {m : Msg} (hn : NewAt mem r.1.mem t m) : ∃ j, j < nWords us ∧ m.loc = offs a j := by
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, rfl⟩ := h2
  have hs1 : s1.mem = mem := by rw [← hsm]; exact (loadUnits_frame _ _ _ _ h1).1
  exact storeUnits_new_loc hs2 hs1 hn

/-- (pair gate) `xchgOwn_wd_frame` for every word-key unit (`WdAt`: a non-epoch word unit or either unit of a protocol
pair); `xchgOwn_wd_frame` is its word instance. -/
theorem xchgOwn_wd_frameG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e)
    (hpk : cx.peek a = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WdAt (CE η) m.loc n) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t0, u', o, tv, c₁, hp, hx, hu, hsub⟩ : ∃ t0 u' o tv c₁, cx.peek a = .ok t0 ∧
      XchgCell cx t0 u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) :=
    ⟨_, _, _, _, _, hp, hx, hu, hsub⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨-, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  have hvR : VRR (fun _ => 0) (CE (CE η)) c.ty (shp c.ty) wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRR ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_sub hsat hsub _ _ _ hvrv
    have hvc : VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_close hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    rw [(Fd_lay hcty).1]
    exact (Fd_VRR η hcty).2 hvc
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key, List.mem_map] at hr
  obtain ⟨r1, hr1, rfl⟩ := hr
  obtain ⟨jj, -, hloc⟩ := xchg_new_loc (T := fun _ => ru) rfl hr1 hn
  have hl : m.loc.label = lab := by rw [hloc]; rfl
  exact wd_frame_wholeG (by rw [hl]; exact hsto) hvR (by rw [hus', hlen]) hle hw

/-- **`NonWordFootT` at `xchg` on an own pointer** (whole cell). -/
theorem xchgOwn_wd_frame {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e)
    (hpk : cx.peek a = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) :=
  xchgOwn_wd_frameG hterm hpk hT hi hE htv hr hn (Or.inl ⟨P, hw, hep⟩)


/-- (pair gate) `xchgLoc_wd_frame` for every word-key unit (`WdAt`: a non-epoch word unit or either unit of a protocol
pair); `xchgLoc_wd_frame` is its word instance. -/
theorem xchgLoc_wd_frameG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e)
    (hpk : cx.peek a = .ok (.loc .own u))
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WdAt (CE η) m.loc n) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t0, u', o, tv, c₁, hp, hx, hu, hsub⟩ : ∃ t0 u' o tv c₁, cx.peek a = .ok t0 ∧
      XchgCell cx t0 u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) :=
    ⟨_, _, _, _, _, hp, hx, hu, hsub⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locView hi0 hpk htv ho hwcu
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ad false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ad false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key, List.mem_map] at hr
  obtain ⟨r1, hr1, rfl⟩ := hr
  obtain ⟨jj, hjj, hloc⟩ := xchg_new_loc (T := fun _ => ru) rfl hr1 hn
  exact wd_frame_compG hsto hat hvalR.1 (by rw [hwU, hlen]) hle (by rw [hloc]; rfl) (by rw [hloc]; rfl)
    (by rw [hlen]; exact hjj) hw

/-- **`NonWordFootT` at `xchg` on an own locative** (a component). -/
theorem xchgLoc_wd_frame {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e)
    (hpk : cx.peek a = .ok (.loc .own u))
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) :=
  xchgLoc_wd_frameG hterm hpk hT hi hE htv hr hn (Or.inl ⟨P, hw, hep⟩)


/-- (pair gate) `xchgAt_wd_frame` for every word-key unit (`WdAt`: a non-epoch word unit or either unit of a protocol
pair); `xchgAt_wd_frame` is its word instance. -/
theorem xchgAt_wd_frameG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAt b i v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WdAt (CE η) m.loc n) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu hsub hb =>
  obtain ⟨t0, u, n0, k, j, tv, c₁, hp, hbuf, hint, hlt, hltk, hu, hsub⟩ : ∃ t0 u n0 k j tv c₁,
      cx.peek b = .ok t0 ∧ bufOf t0 = some (.own, n0, u, k) ∧ IntIdx cx i j ∧ LtI cx j n0 ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hint, hlt, hltk, hu, hsub⟩
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, hini, hsku, hsig, htb, -⟩ :=
    slot_view hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 s1).map fun s2 => (s2, ur, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus]
  rw [key, List.mem_map] at hr
  obtain ⟨r1, hr1, rfl⟩ := hr
  obtain ⟨jj, hjj, hloc⟩ := xchg_new_loc (T := fun _ => ur) rfl hr1 hn
  exact wd_frame_compG hsto hat hvalR.1 (by rw [hwU, hlen]) hle (by rw [hloc]; rfl) (by rw [hloc]; rfl)
    (by rw [hlen]; exact hjj) hw

/-- **`NonWordFootT` at `xchgAt`** (a slot of an own buffer). -/
theorem xchgAt_wd_frame {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAt b i v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) :=
  xchgAt_wd_frameG hterm hT hi hE htv hr hn (Or.inl ⟨P, hw, hep⟩)


/-- (pair gate) `xchgAtF_wd_frame` for every word-key unit (`WdAt`: a non-epoch word unit or either unit of a protocol
pair); `xchgAtF_wd_frame` is its word instance. -/
theorem xchgAtF_wd_frameG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b i v : At} {q : List Nat} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAtF b i q v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WdAt (CE η) m.loc n) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | xchgAtF hp hbuf hct hop _ hint hlt hltk hu hsub hb =>
  obtain ⟨t0, u, c, n0, k, j, tv, c₁, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub⟩ : ∃ t0 u c n0 k j tv c₁,
      cx.peek b = .ok t0 ∧ bufOf t0 = some (.own, n0, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧
      IntIdx cx i j ∧ LtI cx j n0 ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv c :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub⟩
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK c = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, -, hsku, hsig, htbu, -⟩ :=
    slot_view hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct htbu
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  obtain ⟨cs, hcs⟩ : ∃ cs, accs cR = some cs := by
    have hwcc : wc (cl ρ η.wit 0 0 c) ≠ none := by
      rw [← wc_of_sig (sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1))]
      exact (Lay_canon hsub hlv).2.2.2.1
    have : wc cR ≠ none := by rw [wc_of_sig hsgc]; exact hwcc
    cases h : accs cR with
    | none => simp [wc, h] at this
    | some cs => exact ⟨cs, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsgc hcs
  have hwU : wc (cl ρ η.wit 0 0 c) = some (nWords cs) := by rw [← wc_of_sig hsgc]; simp [wc, hcs]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us + o)) false cs wsv 0 s1).map fun s2 => (s2, cR, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus, hco, hcs]
  rw [key, List.mem_map] at hr
  obtain ⟨r1, hr1, rfl⟩ := hr
  obtain ⟨jj, hjj, hloc⟩ := xchg_new_loc (T := fun _ => cR) rfl hr1 hn
  exact wd_frame_compG hsto hat' hvalR.1 (by rw [hwU, hlen]) hle (by rw [hloc]; rfl) (by rw [hloc]; rfl)
    (by rw [hlen]; exact hjj) hw

/-- **`NonWordFootT` at `xchgAtF`** (a field of a slot of an own buffer). -/
theorem xchgAtF_wd_frame {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b i v : At} {q : List Nat} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAtF b i q v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) :=
  xchgAtF_wd_frameG hterm hT hi hE htv hr hn (Or.inl ⟨P, hw, hep⟩)



/-- (pair gate) `bufInit_wd_frame` for every word-key unit (`WdAt`: a non-epoch word unit or either unit of a protocol
pair); `bufInit_wd_frame` is its word instance. -/
theorem bufInit_wd_frameG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit b i v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WdAt (CE η) m.loc n) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | bufInit hu hbuf hint heq hlt hu2 hsub hb =>
  obtain ⟨t0, tv, u, n0, k, j, c₁, c₂, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩ : ∃ t0 tv u n0 k j c₁ c₂,
      cx.use b = .ok (t0, c₁) ∧ bufOf t0 = some (.own, n0, u, k) ∧ IntIdx c₁ i j ∧ EqI c₁ j k ∧
      LtI c₁ k n0 ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u ∧
      c₂.bind x (.refine (.loc .own (.array n0 u)) (.ini (.add k (.lit 1)))) = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩
  have ht : t0 = .refine (.loc .own (.array n0 u)) (.ini k) := by
    unfold bufOf at hbuf; split at hbuf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
      obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
    · simp at hbuf
  subst ht
  have htu := use_TvOK hu htv
  obtain ⟨rb, wsb, Rb, Rr1, hea, hvb, hlb, -, hi1, hle1⟩ := useR hu hi hE.2.2
  obtain ⟨rv, wsv, Rv, Rr2, hev, hvv, hlv, hvrv, hi2, hle2⟩ := useR hu2 hi1 hE.2.2
  have hJK : ev ρ j = ev ρ k := heq ρ hi1.1.1
  have hKN : ev ρ k < ev ρ n0 := hlt ρ hi1.1.1
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VR hi1.1.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intS hti hvi)
  simp only [VR] at hvb
  obtain ⟨hv, -⟩ := hvb
  rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, -, -⟩
  · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
    simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
    omega
  obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
  obtain ⟨w, rfl, hwv⟩ := map_singleton hws
  have hat := hat0
  simp only [cl, clI_zero] at hat
  have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
    rw [hlb.2.1]; rfl
  obtain ⟨μr, nr, ur, ψ, rfl, -, hsu⟩ := buf_runtime' hs'
  have htb1 : tb c₁.ke.length u = true := by
    have h := htu.2.1
    rw [← htu.2.2] at h
    simp [tb] at h
    exact h
  have ho : c₁.opaqueOK u = true :=
    sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu2).1)
  have hsig : sig ur = sig (cl ρ η.wit 0 0 u) := by
    have e1 : sig ur = sig (close th.σs u) := sig_of_eskel hsu
    rw [e1]; exact sig_WitL hi1.1.2.2.2.1 ρ ho (lt_of_guardT htb1 hi1.1.2.2.2.2.1)
  obtain ⟨us0, hus0⟩ : ∃ us, accs (cl ρ η.wit 0 0 u) = some us := by
    rcases AtOff_lay hat with h | ⟨n', e', he', h⟩
    · simp [accs] at h
    · simp only [Ty.array.injEq] at he'; rw [he'.2]
      exact Option.ne_none_iff_exists'.1 h
  obtain ⟨us, hus⟩ : ∃ us, accs ur = some us := by
    have : wc ur ≠ none := by rw [wc_of_sig hsig]; simp [wc, hus0]
    cases h : accs ur with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have hwe : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨hval, hlen⟩ :=
    ownStoreVal (cx := c₁) hE.2.1 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 hi2.1.1 hsub ho htb1 hvv hlv hsig hus
  have hvalR := storeValR (cx := c₁) hE.2.1 hE.2.2 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 hi2.1.1 hsub ho htb1
    hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, Ty.refine (Ty.loc μr (Ty.array nr ur))
          (Pred.ini (Idx.lit (ev ρ j + 1))), [w]) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, numOf, hwi, addrOf, hwv, bufElem, hus, List.map_map]; rfl
  rw [key, List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  obtain ⟨jj, hjj, hloc⟩ := storeUnits_new_loc hs' rfl hn
  have hn0 : nWords us0 = nWords us := by
    have h1 : wc (cl ρ η.wit 0 0 u) = some (nWords us0) := by simp [wc, hus0]
    rw [hwe] at h1; exact (Option.some.inj h1).symm
  have hslot := AtOff_trans hat (AtOff.elem (n := ev ρ n0) (j := ev ρ j) hus0 (by omega)
    (AtOff.here (Or.inl (by simp [hus0]))))
  have hle : Rv + Rr2 ≤ Rf := Res.le_def.2 fun q => by
    have h1 := hle1 q
    have h2 := hle2 q
    simp only [Res.add_apply] at h1 h2 ⊢
    omega
  exact wd_frame_compG (j := jj) hsto hslot hvalR.1 (by rw [hwe, hlen]) hle (by rw [hloc]; rfl)
    (by rw [hloc, hn0]; simp only [offs, Nat.add_zero]) (by rw [hlen]; exact hjj) hw

/-- **`NonWordFootT` at `bufInit`** (a slot of an own buffer). -/
theorem bufInit_wd_frame {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit b i v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) :=
  bufInit_wd_frameG hterm hT hi hE htv hr hn (Or.inl ⟨P, hw, hep⟩)


/-- (pair gate) `casCell_no_wordAt` for every word unit or pair unit (`WUnit`); `casCell_no_wordAt` is its word instance. -/
theorem casCell_no_wordAtG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {acq rel : Bool} {w e v : At} {x : String} {ok fail : Expr} {tw u : Ty} {μ : Mode}
    (hterm : th.term = .cas acq rel w e v x ok fail)
    (hpk : cx.peek w = .ok tw) (hcw : cellOf tw = some (μ, u)) (hone : u.rawWords = some 1)
    (haff : affine cx.ke u = false)
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WUnit (CE η) m.loc n) : False := by
  obtain ⟨tw', pw', te, ew, tv, nw, hea', -, -, haddr, -, -⟩ := tstep_cas_new hterm hr hn
  obtain ⟨rt, pw, ad, c, hea, hpw, hsto, hat, -, hdw⟩ :=
    plainTarget hi hE hpk hcw hone haff (tb_cellOf (peek_tb htv hpk) hcw)
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨-, rfl⟩ := hea'
  have hl : m.loc = ad := by simp only [addrOf, hpw, Option.some.injEq] at haddr; exact haddr.symm
  exact dwf_no_wordG (j := 0) hsto hat hdw (accs_cl_one hone) (by simp [hl]) (by simp [hl]) (by simp [nW_one]) hw

/-- **`NonWordFootT` at `casCell`** (type disjointness): a one-word
non-affine cell component is deeply word-free (`plainTarget`), so the RMW
never appends at a `WordAt`. -/
theorem casCell_no_wordAt {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {acq rel : Bool} {w e v : At} {x : String} {ok fail : Expr} {tw u : Ty} {μ : Mode}
    (hterm : th.term = .cas acq rel w e v x ok fail)
    (hpk : cx.peek w = .ok tw) (hcw : cellOf tw = some (μ, u)) (hone : u.rawWords = some 1)
    (haff : affine cx.ke u = false)
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) : False :=
  casCell_no_wordAtG hterm hpk hcw hone haff hi hE htv hr hn (Or.inl ⟨P, hw⟩)


/-- (pair gate) `fetchCell_no_wordAt` for every word unit or pair unit (`WUnit`); `fetchCell_no_wordAt` is its word instance. -/
theorem fetchCell_no_wordAtG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr} {tw : Ty} {μ : Mode}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok tw) (hcw : cellOf tw = some (μ, .int))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WUnit (CE η) m.loc n) : False := by
  obtain ⟨rt', pw', hea', haddr⟩ := tstep_fetch_new hterm hr hn
  have hone : Ty.int.rawWords = some 1 := by first | rfl | simp [Ty.rawWords]
  have haff : affine cx.ke .int = false := by first | rfl | simp [affine]
  obtain ⟨rt, pw, ad, c, hea, hpw, hsto, hat, -, hdw⟩ :=
    plainTarget hi hE hpk hcw hone haff (tb_cellOf (peek_tb htv hpk) hcw)
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨-, rfl⟩ := hea'
  have hl : m.loc = ad := by simp only [addrOf, hpw, Option.some.injEq] at haddr; exact haddr.symm
  exact dwf_no_wordG (j := 0) hsto hat hdw (accs_cl_one hone) (by simp [hl]) (by simp [hl]) (by simp [nW_one]) hw

/-- **`NonWordFootT` at `fetchCell`** (type disjointness): an `Int` cell. -/
theorem fetchCell_no_wordAt {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr} {tw : Ty} {μ : Mode}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok tw) (hcw : cellOf tw = some (μ, .int))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) : False :=
  fetchCell_no_wordAtG hterm hpk hcw hi hE htv hr hn (Or.inl ⟨P, hw⟩)


theorem Solid_lanes (sg : Bool) (w : Wd) : Solid (.lanes sg w) :=
  ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ h => by cases h)⟩

/-- (pair gate) `stl_no_wordAt` for every word unit or pair unit (`WUnit`); `stl_no_wordAt` is its word instance. -/
theorem stl_no_wordAtG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.stl b i v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WUnit (CE η) m.loc n) : False := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | stl hp hbuf hlo hint hlt hltk hpv hfx hb =>
  obtain ⟨t0, u, n0, k, j, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩ : ∃ t0 u n0 k j tv q,
      cx.peek b = .ok t0 ∧ bufOf t0 = some (.own, n0, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n0) ∧ LtI cx j (.smul q.2.lanes k) ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩
  have hi0 := hi.1
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0 hlt hltk
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_num hi0.2.1 hpi hti
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VR hi0.2.1 hpv
  simp only [VR] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ0 : ev ρ j < w.lanes * ev ρ n0 := by simpa [ev] using hlt ρ hi0.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi0.1
  have hJ : ev ρ j / w.lanes < ev ρ n0 :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewN (ev ρ j / w.lanes) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one]
            [cst (.num (setLaneN w y (ev ρ j % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hni, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  cases hno : numOf old with
  | none => simp [hno] at h2
  | some y =>
  rw [hno, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, -, -⟩ := he2
  have hs1 : s1.mem = mem := (loadUnits_frame _ _ _ _ h1).1
  obtain ⟨jj, hjj, hloc⟩ := storeUnits_new_loc hs2 hs1 hn
  have hat' : AtOff c.ty (offs ad (ev ρ j / w.lanes)).offset (.lanes sg w) := by simpa only [cl] using hat
  exact solid_no_wordG hsto hat' (Solid_lanes sg w) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (by simp [accs] : accs (Ty.lanes sg w) = some [.one]) (by rw [hloc]; rfl) (by rw [hloc]; rfl) hjj hw

/-- **`NonWordFootT` at `stl`** (type disjointness): a lane word. -/
theorem stl_no_wordAt {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.stl b i v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) : False :=
  stl_no_wordAtG hterm hT hi htv hr hn (Or.inl ⟨P, hw⟩)


/-- (pair gate) `stlw_no_wordAt` for every word unit or pair unit (`WUnit`); `stlw_no_wordAt` is its word instance. -/
theorem stlw_no_wordAtG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b wi jl v : At} {e : Expr}
    (hterm : th.term = .let_ x (.stlw b wi jl v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WUnit (CE η) m.loc n) : False := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk hpj hij hpv hfx hb =>
  obtain ⟨t0, u, n0, k, jw, tj, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩ :
      ∃ t0 u n0 k jw tj tv q,
      cx.peek b = .ok t0 ∧ bufOf t0 = some (.own, n0, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n0 ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩
  have hi0 := hi.1
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_num hi0.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m0, hej, hwj⟩ := atom_int hi0.2.1 hpj hoj
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VR hi0.2.1 hpv
  simp only [VR] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ := hlt ρ hi0.1
  have hJk := hltk ρ hi0.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewN (ev ρ jw) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m0 := by simp [numOf, hwj]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ jw)) false [.one]
            [cst (.num (setLaneN w y (m0 % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hev, hni, hnj, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  cases hno : numOf old with
  | none => simp [hno] at h2
  | some y =>
  rw [hno, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, -, -⟩ := he2
  have hs1 : s1.mem = mem := (loadUnits_frame _ _ _ _ h1).1
  obtain ⟨jj, hjj, hloc⟩ := storeUnits_new_loc hs2 hs1 hn
  have hat' : AtOff c.ty (offs ad (ev ρ jw)).offset (.lanes sg w) := by simpa only [cl] using hat
  exact solid_no_wordG hsto hat' (Solid_lanes sg w) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (by simp [accs] : accs (Ty.lanes sg w) = some [.one]) (by rw [hloc]; rfl) (by rw [hloc]; rfl) hjj hw

/-- **`NonWordFootT` at `stlw`** (type disjointness): a lane word. -/
theorem stlw_no_wordAt {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {b wi jl v : At} {e : Expr}
    (hterm : th.term = .let_ x (.stlw b wi jl v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (htv : TvOK cx)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) : False :=
  stlw_no_wordAtG hterm hT hi htv hr hn (Or.inl ⟨P, hw⟩)



/-! ### Steps that append only at a fresh label -/

/-- The operations whose step may append at an existing cell. -/
def AppOp : Op → Prop
  | .store .. | .xchg .. | .xchgAt .. | .xchgAtF .. | .bufInit .. | .stl .. | .stlw .. | .fetch ..
  | .stp .. => True
  | _ => False

/-- The terms whose step may append at an existing cell (`AppOp`, `cas`,
`casp`); every other step appends only at the thread's next fresh label. -/
def AppTerm : Expr → Prop
  | .let_ _ op _ => AppOp op
  | .cas .. => True
  | .casp .. => True
  | _ => False

theorem GrowsAt_new {M M' : Memory} {l : AllocLabel} (hg : GrowsAt M M' l) {t : Ts} {m : Msg}
    (hn : NewAt M M' t m) : m.loc.label = l :=
  hg.2.2 t m (size_le_of_none hn.1) hn.2

/-- A boxed projection only loads. -/
theorem projM_frame {g : G} {s : St} {ty : Ty} {ws : List Word} {r : St × Nat × List Word}
    (h : r ∈ projM g s ty ws) : r.1.mem = s.mem ∧ r.1.promises = s.promises ∧ r.1.nalloc = s.nalloc := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        obtain ⟨a1, -, c1, d1⟩ := loadUnits_frame _ _ _ _ h1
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             obtain ⟨a2, -, c2, d2⟩ := loadUnits_frame _ _ _ _ h2
             exact ⟨a2.trans a1, c2.trans c1, d2.trans d1⟩)
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- A boxed injection appends only at the fresh label. -/
theorem injM_new_label {g : G} {s s1 : St} {ty : Ty} {j : Nat} {p : List Word} {r : St × List Word}
    (hf : s1.mem = s.mem ∧ s1.promises = s.promises ∧ s1.nalloc = s.nalloc) (hpl : PromLt s)
    (h : r ∈ injM g s1 ty j p) {t : Ts} {m : Msg} (hn : NewAt s.mem r.1.mem t m) :
    m.loc.label = freshLabel g.lbase g.n g.i s.nalloc := by
  obtain ⟨hm1, hp1, hn1⟩ := hf
  have hpl1 : PromLt s1 := fun t ht => by rw [hm1]; rw [hp1] at ht; exact hpl t ht
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      obtain ⟨hg, -⟩ := alloc_growsP hpl1 _ hs
      rw [← hn1]
      rw [← hm1] at hn
      have hmem : (if g.boxFence then fenceS s' .st else s').mem = s'.mem := by split <;> rfl
      dsimp only at hn
      rw [hmem] at hn
      exact hg.2.2 t m (size_le_of_none hn.1) hn.2
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact (keep_no_new hm1 hn).elim

/-- An operation outside `AppOp` appends only at the fresh label. -/
theorem evalOp_new_label {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (hop : ¬ AppOp op) (hpl : PromLt s) (h : r ∈ evalOp g env σs s op) {t : Ts} {m : Msg}
    (hn : NewAt s.mem r.1.mem t m) : m.loc.label = freshLabel g.lbase g.n g.i s.nalloc := by
  cases op
  case inl τ a =>
    simp only [evalOp] at h
    split at h
    · simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨⟨s1, j, p⟩, h1, ⟨s2, q⟩, h2, rfl⟩ := h
      exact injM_new_label (projM_frame h1) hpl h2 hn
    · simp at h
  case inr τ a =>
    simp only [evalOp] at h
    split at h
    · simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨⟨s1, j, p⟩, h1, ⟨s2, q⟩, h2, rfl⟩ := h
      exact injM_new_label (projM_frame h1) hpl h2 hn
    · simp at h
  case new a _ =>
    simp only [evalOp] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [List.mem_map] at h
         obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
         exact (alloc_growsP hpl _ hs).1.2.2 t m (size_le_of_none hn.1) hn.2)
  case newBuf nn τ =>
    simp only [evalOp] at h
    (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
    (repeat' (first | (split at h) | (dsimp only at h; split at h)))
    all_goals first
      | (simp at h; done)
      | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
         subst h
         dsimp only at hn
         exact GrowsAt_new (allocBuf_grows _ _ _ s).1 hn)
  all_goals first
    | exact absurd trivial hop
    | (exfalso
       simp only [evalOp] at h
       (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
       (repeat' (first | (split at h) | (dsimp only at h; split at h)))
       all_goals first
         | (simp at h; done)
         | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
            subst h; exact keep_no_new rfl hn)
         | (simp only [List.mem_map] at h
            obtain ⟨x, hx, rfl⟩ := h
            exact keep_no_new (loadUnits_frame _ _ _ _ hx).1 hn)
         | (simp only [List.mem_filterMap] at h
            obtain ⟨x, hx, h⟩ := h
            cases hn' : numOf x.2 <;> simp [hn'] at h
            subst h; exact keep_no_new (loadUnits_frame _ _ _ _ hx).1 hn))

/-- **A step of a term outside `AppTerm`** appends only at the thread's next
fresh label. -/
theorem tstep_new_label {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hA : ¬ AppTerm th.term) (hpl : PromLt (stOf mem pairs th))
    (h : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg} (hn : NewAt mem r.1 t m) :
    m.loc.label = freshLabel g.lbase g.n g.i th.nalloc := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact (keep_no_new rfl hn).elim)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h; exact (keep_no_new rfl hn).elim)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h; exact (keep_no_new rfl hn).elim)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       exact evalOp_new_label (fun hh => hA (by rw [‹th.term = _›]; exact hh)) hpl hx hn)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       exact (hA (by rw [‹th.term = _›]; trivial)).elim)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact injM_new_label (projM_frame hx) hpl hy hn)

/-- (pair gate) `fresh_no_word` for every word unit or pair unit (`WUnit`); `fresh_no_word` is its word instance. -/
theorem fresh_no_wordG {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {η : TEnv}
    {r : Memory × List Ts × TTh} (hm : MemInv g (CE η) (stOf mem pairs th))
    (hA : ¬ AppTerm th.term) (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg} (hn : NewAt mem r.1 t m)
    {n : Nat} (hw : WUnit (CE η) m.loc n) : False := by
  have hl := tstep_new_label hA hm.2.2.1 hr hn
  have hnone := (hm.2.2.2.1.1 th.nalloc (Nat.le_refl _)).1
  obtain ⟨c, hs⟩ : ∃ c, η.sto m.loc.label = some c := by
    rcases hw with ⟨P, c, hs, -, -⟩ | ⟨c, -, -, hs, -⟩ <;> exact ⟨c, hs⟩
  change η.sto _ = none at hnone
  rw [hl, hnone] at hs
  cases hs

/-- Outside `AppTerm`, a step never appends at a `WordAt` (the fresh label is
outside Σ, `FreshLP`). -/
theorem fresh_no_word {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {η : TEnv}
    {r : Memory × List Ts × TTh} (hm : MemInv g (CE η) (stOf mem pairs th))
    (hA : ¬ AppTerm th.term) (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg} (hn : NewAt mem r.1 t m)
    {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) : False :=
  fresh_no_wordG hm hA hr hn (Or.inl ⟨P, hw⟩)


/-- **C1, the dichotomy.**  A thread step that appends at an initialised
non-ghost protocol word `m.loc` (region `n`, protocol `P`) either was made by a
thread whose frame holds `rg n`, or overwrote a value in a holding clause (a
`cas`: memory held `rg n`), or `P` has no held state at all.  Non-word ops are
excluded by W1 (`hwd`): their frame would carry a second `wd n`. -/
theorem held_write_dichotomy {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf H : Res}
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hfootT : NonWordFootT g mem pairs th cx (CE η) Rf)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + H (.wd n) ≤ 1) (hini : IniU η m.loc n P) (hpwf : pwf P = true) :
    1 ≤ Rf (.rg n) ∨ (∃ wd, PredAt r.1 m.loc t wd ∧ WordHolds P [wd.val]) ∨ NoHeld P := by
  by_cases hwo : WordOp cx th.term
  · generalize ht : th.term = t0 at hT hsc hwo
    cases t0 with
    | let_ x op e =>
      cases op with
      | store rel a v tok =>
        obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd⟩ := hwo
        cases hT with
        | let_ hop _ => exact Or.inl (store_word_step ht hop hpk hwd hi hE htv hr hn hw)
      | fetch o acq rel a v =>
        obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd⟩ := hwo
        cases hT with
        | let_ hop _ => exact Or.inr (Or.inr (fetch_word_step ht hop hpk hwd hi.1 hE htv hm hsc hr hn hw))
      | _ => exact hwo.elim
    | cas acq rel w e v x ok fail =>
      obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd⟩ := hwo
      exact Or.inr (cas_word_step ht hT hpk hwd hi.1 hE htv hm hsc hr hn hw)
    | _ => exact hwo.elim
  · cases hep : P.epoch
    · exfalso
      have h1 := hfootT hwo r hr t m hn n P hw hep
      have h2 := wd_held hH hw hini hep
      omega
    · exact Or.inr (Or.inr (epoch_facts hpwf hep).2)

/-- **C1, leaving a held state** (`held_write_needs_token`): a thread step that
appends at an initialised word whose predecessor value is in a held clause was
made by a thread whose frame holds the region token `rg n`. -/
theorem held_write_needs_token {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf H : Res}
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hfootT : NonWordFootT g mem pairs th cx (CE η) Rf)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + H (.wd n) ≤ 1) (hini : IniU η m.loc n P)
    (hpwf : pwf P = true) {wd : Word} (hpre : PredAt r.1 m.loc t wd) (hheld : HeldV P wd.val) :
    1 ≤ Rf (.rg n) := by
  rcases held_write_dichotomy hT hi hE htv hm hsc hH hfootT hr hn hw hwd hini hpwf with
    h | ⟨wd', hp', hh'⟩ | hno
  · exact h
  · have := PredAt_uniq hpre hp'
    subst this
    exact absurd hheld (holds_not_heldV hpwf hh')
  · exact absurd hheld (hno.not_heldV _)

/-- **C1, entering a held state**: a thread step that appends a held value at
an initialised word was made by a thread whose frame holds `rg n`, or it is a
`cas` out of a holding value (the token was memory's, `WRes`, and moves to the
frame). -/
theorem held_enter_needs_token {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf H : Res}
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hfootT : NonWordFootT g mem pairs th cx (CE η) Rf)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + H (.wd n) ≤ 1) (hini : IniU η m.loc n P) (hpwf : pwf P = true)
    (hheld : HeldV P m.val) :
    1 ≤ Rf (.rg n) ∨ ∃ wd, PredAt r.1 m.loc t wd ∧ WordHolds P [wd.val] := by
  rcases held_write_dichotomy hT hi hE htv hm hsc hH hfootT hr hn hw hwd hini hpwf with h | h | hno
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hheld (hno.not_heldV _)

/-! ## With token uniqueness -/

/-- Abstract token uniqueness: at most one thread's bound holds `rg n`
(`machine_tokens`' `Σ_i Tot_i (rg n) + H (rg n) ≤ 1` implies it). -/
def TokUniq (Tot : Nat → Res) (n : Nat) : Prop :=
  ∀ i j, 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j

/-- **C2 (abstract)**: under `TokUniq`, if thread `h` holds `rg n`, a step of
thread `j` (bound `Tot j = Rf + Rs`) that appends over a held value at a word of
region `n` is a step of `h`. -/
theorem held_word_changes_only_by_holder {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf Rs : Res}
    {Tot : Nat → Res} {h j : Nat} {n : Nat} {Hm : Res}
    (hu : TokUniq Tot n) (hh : 1 ≤ Tot h (.rg n)) (hTot : Rf + Rs = Tot j)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) Hm) (hfootT : NonWordFootT g mem pairs th cx (CE η) Rf)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + Hm (.wd n) ≤ 1) (hini : IniU η m.loc n P)
    (hpwf : pwf P = true) {wd : Word} (hpre : PredAt r.1 m.loc t wd) (hheld : HeldV P wd.val) :
    j = h := by
  have h1 := held_write_needs_token hT hi hE htv hm hsc hH hfootT hr hn hw hwd hini hpwf hpre hheld
  have h2 : 1 ≤ Tot j (.rg n) := by
    rw [← hTot, Res.add_apply]
    omega
  exact hu j h h2 hh

/-! ## Pairs (Gap 2) -/

/-- `(v0, v1)` lies in a held (non-holding) clause of the pair protocol `P`. -/
def HeldV2 (P : Proto2) (v0 v1 : WeakMem.Val) : Prop :=
  ∃ (c : Nat) (cl : Clause2) (k0 k1 : Nat), P.clauses[c]? = some cl ∧ cl.holds = false ∧
    v0 = .num (cl.s0 * k0 + cl.o0) ∧ v1 = .num (cl.s1 * k1 + cl.o1) ∧ Rel2Holds cl.rel k0 k1

/-- Under `pwf2`, a holding pair value is not a held one. -/
theorem holds_not_heldV2 {P : Proto2} (hp : pwf2 P = true) {v0 v1 : WeakMem.Val}
    (h : Word2Holds P [v0, v1]) : ¬ HeldV2 P v0 v1 := by
  rintro ⟨c, cl, k0, k1, hc, hh, rfl, rfl, hr⟩
  obtain ⟨n0, n1, c2, cl2, k0', k1', hv, hc2, hh2, f0, f1, f2⟩ := h
  simp only [List.cons.injEq, WeakMem.Val.num.injEq, and_true] at hv
  obtain ⟨e0, e1⟩ := hv
  have e := pwf2_disjoint hp hc hc2 e0.symm e1.symm hr f0 f1 f2
  subst e
  rw [hc] at hc2
  cases hc2
  rw [hh] at hh2
  cases hh2

/-- Every `stp` on a protocol pair (`stpGive`, `stpKeep`) consumes a pair
token `tok2 r' P i0 i1` with `r' = r`. -/
theorem stp_word2_tok {p : Prog} {cx c' : Cx} {x : String} {rel : Bool} {a v0 v1 tk : At}
    {t : Ty} {r : Idx} {P : Proto2} (h : OpT p cx x (.stp rel a v0 v1 tk) c')
    (ht : cx.peek a = .ok t) (hw : word2Of t = some (r, P)) :
    ∃ r' i0 i1 c₁, cx.use tk = .ok (.tok2 r' P i0 i1, c₁) ∧ EqI c₁ r r' := by
  revert ht hw
  cases h
  all_goals (
    have hpk := ‹Cx.peek _ _ = _›
    have hwo := ‹word2Of _ = _›
    intro ht hw
    rw [ht] at hpk
    cases hpk
    rw [hw] at hwo
    cases hwo)
  all_goals exact ⟨_, _, _, _, ‹_›, ‹_›⟩

/-- A typed `casp` on a protocol pair compares against a pair in a holding
state (`caspBump`, `caspMove`, `caspTake`; `caspE` is on an epoch pair). -/
theorem casp_word2_inv {p : Prog} {cx : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String}
    {ok fail : Expr} {tw : Ty} {r : Idx} {P : Proto2}
    (h : Typed p cx (.casp acq rel w e0 e1 v0 v1 t ok fail))
    (ht : cx.peek w = .ok tw) (hw : word2Of tw = some (r, P)) :
    ∃ i0 i1 c k0 k1 cl, IntIdx cx e0 i0 ∧ IntIdx cx e1 i1 ∧ InState2 cx P i0 i1 c k0 k1 ∧
      P.clauses[c]? = some cl ∧ cl.holds = true := by
  revert ht hw
  cases h
  all_goals (
    have hpk := ‹Cx.peek _ w = _›
    have hwo := ‹word2Of _ = _›
    intro ht hw
    rw [ht] at hpk
    cases hpk
    rw [hw] at hwo
    cases hwo)
  all_goals exact ⟨_, _, _, _, _, _, ‹IntIdx _ e0 _›, ‹IntIdx _ e1 _›, ‹_›, ‹_›, ‹_›⟩

theorem tok2_frame {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx c₁ : Cx} {env : Env} {tk : At} {r' i0 i1 : Idx} {P : Proto2} {Rf : Res}
    (hi : FInvR ρ η σs K cx env Rf) (hcr : CohR η) (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) :
    1 ≤ Rf (.rg (ev ρ r')) ∧ Sat c₁.facts ρ := by
  obtain ⟨rt, ws, R, Rr, -, -, -, hv, hi1, hle⟩ := useR hu hi hcr
  refine ⟨?_, hi1.1.1⟩
  simp only [VRR] at hv
  subst hv
  have := (Res.le_def.1 hle) (.rg (ev ρ r'))
  simp only [Res.add_apply, Res.one, ite_true] at this
  omega

/-- An `stp` appends only at its pair's two words. -/
theorem tstep_stp_new {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {x : String} {rel : Bool} {a v0 v1 tk : At} {e : Expr}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) :
    ∃ rt pw A, evalAt th.env a = some (rt, [pw]) ∧ addrOf pw = some A ∧ (m.loc = A ∨ m.loc = offs A 1) := by
  obtain ⟨h0, h1⟩ := hn
  simp only [tstep, hterm, evalOp] at hr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hin, rfl⟩ := hr
  split at hin
  · rename_i rt pw tv0 w0 tv1 w1 hea hev0 hev1
    split at hin
    · rename_i rp b hw hb
      rw [List.mem_map] at hin
      obtain ⟨s'', hs'', he⟩ := hin
      injection he with e1 e2
      subst e1
      obtain ⟨-, -, hrole⟩ := storeUnits_roles [.two] (w0 ++ w1) 0 (stOf mem pairs th) s'' hs''
      obtain ⟨j, hloc, hj⟩ := hrole t m (size_le_of_none h0) h1
      refine ⟨rt, pw, b, hea, hb, ?_⟩
      rcases hj with ⟨i, hi', -⟩ | ⟨⟨i, hi', hj⟩, -⟩ | ⟨jj, q, m0, rfl, ⟨i, hi', hjj⟩, -⟩
      · cases i <;> simp at hi'
      · cases i with
        | zero =>
          simp [nWords] at hj
          subst hj
          left
          simpa [TermLiveProps.offs_zero] using hloc
        | succ i => simp at hi'
      · cases i with
        | zero =>
          simp [nWords] at hjj
          subst hjj
          right
          simpa using hloc
        | succ i => simp at hi'
    · simp at hin
  · simp at hin

/-- (pair gate) A `casp` that appends pushes `A` then `A.next` at the end of memory, over the expected pair read
at `A`, `A.next`; the new message is one of the two.  The step facts behind `tstep_casp_new` (and, for pairs,
`tstep_casp_shape`). -/
theorem tstep_casp_push {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {E : TEnv}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {x : String} {ok fail : Expr}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 x ok fail) (hm : MemInv g E (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) :
    ∃ tw pw te0 x0 te1 x1 A t0 t1 m0 m1 u0 u1 mv, evalAt th.env w = some (tw, [pw]) ∧
      evalAt th.env e0 = some (te0, [x0]) ∧ evalAt th.env e1 = some (te1, [x1]) ∧ addrOf pw = some A ∧
      r.1 = (mem.push ⟨A, u0, mv⟩).push ⟨A.next, u1, mv⟩ ∧
      mem[t0]? = some m0 ∧ m0.loc = A ∧ mem[t1]? = some m1 ∧ m1.loc = A.next ∧
      m0.val = x0.val ∧ m1.val = x1.val ∧
      WeakMem.rmwAdjacent mem A t0 mem.size = true ∧ WeakMem.rmwAdjacent mem A.next t1 (mem.size + 1) = true ∧
      ((m = ⟨A, u0, mv⟩ ∧ t = mem.size) ∨ (m = ⟨A.next, u1, mv⟩ ∧ t = mem.size + 1)) := by
  obtain ⟨h0, h1⟩ := hn
  simp only [tstep, hterm] at hr
  split at hr
  · rename_i tw pw te0 x0 te1 x1 tv0 n0 tv1 n1 hw he0 he1 hv0 hv1
    split at hr
    · rename_i b hb
      rw [List.mem_map] at hr
      obtain ⟨⟨mem', pairs', th'⟩, hin, rfl⟩ := hr
      obtain ⟨t0, t1, m0, m1, hm0, hl0, hm1, hl1, -, -, hcase⟩ :=
        stepRmwPair_mem hin (by decide) (MemInv_nopair hm)
      rcases hcase with ⟨-, rfl, -⟩ | ⟨hs0, hs1, mv, rfl, -, hadj0, hadj1⟩
      · simp only at h1; rw [h0] at h1; cases h1
      · refine ⟨tw, pw, te0, x0, te1, x1, b, t0, t1, m0, m1, _, _, mv, hw, he0, he1, hb, rfl, hm0, hl0, hm1, hl1,
          hs0, hs1, hadj0, hadj1, ?_⟩
        simp only at h1
        rw [Array.getElem?_push, Array.size_push] at h1
        split at h1
        · rename_i hts
          cases h1
          exact Or.inr ⟨rfl, hts⟩
        · rw [Array.getElem?_push] at h1
          split at h1
          · rename_i hts
            cases h1
            exact Or.inl ⟨rfl, hts⟩
          · rw [h0] at h1; cases h1
    · simp at hr
  · simp at hr

/-- A `casp` appends at its pair's first word `A` (over the expected pair read
at `A`, `A.next`), and at `A.next`. -/
theorem tstep_casp_new {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {E : TEnv}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {x : String} {ok fail : Expr}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 x ok fail) (hm : MemInv g E (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) :
    ∃ tw pw te0 x0 te1 x1 A, evalAt th.env w = some (tw, [pw]) ∧ evalAt th.env e0 = some (te0, [x0]) ∧
      evalAt th.env e1 = some (te1, [x1]) ∧ addrOf pw = some A ∧
      ((m.loc = A ∧ ∃ wd0 wd1, PredAt r.1 A t wd0 ∧ PredAt r.1 A.next (t + 1) wd1 ∧
          wd0.val = x0.val ∧ wd1.val = x1.val) ∨ m.loc = A.next) := by
  obtain ⟨tw, pw, te0, x0, te1, x1, b, t0, t1, m0, m1, u0, u1, mv, hw, he0, he1, hb, hr1, hm0, hl0, hm1, hl1,
    hs0, hs1, hadj0, hadj1, hnew⟩ := tstep_casp_push hterm hm hr hn
  refine ⟨tw, pw, te0, x0, te1, x1, b, hw, he0, he1, hb, ?_⟩
  rcases hnew with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
  · obtain ⟨hlt0, hbt0⟩ := rmwAdjacent_spec hadj0
    obtain ⟨-, hbt1⟩ := rmwAdjacent_spec hadj1
    have ht1 : t1 < mem.size := lt_of_get hm1
    rw [hr1]
    refine Or.inl ⟨rfl, mw m0, mw m1, ⟨t0, m0, hlt0, ?_, hl0, rfl, ?_⟩,
      ⟨t1, m1, Nat.lt_succ_of_lt ht1, ?_, hl1, rfl, ?_⟩, hs0, hs1⟩
    · simp only [Array.getElem?_push, Array.size_push, Nat.ne_of_lt hlt0,
        Nat.ne_of_lt (Nat.lt_succ_of_lt hlt0), ite_false]
      exact hm0
    · intro t' m' h1' h2' h3'
      simp only [Array.getElem?_push, Array.size_push, Nat.ne_of_lt h2',
        Nat.ne_of_lt (Nat.lt_succ_of_lt h2'), ite_false] at h3'
      exact hbt0 t' m' h1' h2' h3'
    · simp only [Array.getElem?_push, Array.size_push, Nat.ne_of_lt ht1,
        Nat.ne_of_lt (Nat.lt_succ_of_lt ht1), ite_false]
      exact hm1
    · intro t' m' h1' h2' h3'
      rcases Nat.lt_or_ge t' mem.size with hlt | hge
      · simp only [Array.getElem?_push, Array.size_push, Nat.ne_of_lt hlt,
          Nat.ne_of_lt (Nat.lt_succ_of_lt hlt), ite_false] at h3'
        exact hbt1 t' m' h1' (Nat.lt_succ_of_lt hlt) h3'
      · have he : t' = mem.size := Nat.le_antisymm (Nat.le_of_lt_succ h2') hge
        subst he
        simp only [Array.getElem?_push, Array.size_push, Nat.ne_of_lt (Nat.lt_succ_self _),
          ite_false, ite_true, Option.some.injEq] at h3'
        subst h3'
        exact fun h => WeakMem.Address.next_ne b h.symm
  · exact Or.inr rfl


/-- A reference to a pair of region `r` and protocol `P` points at a pair of
region `ev ρ r` and protocol `P` in its cell. -/
theorem word2_link {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {r : Idx} {P : Proto2} {rt : Ty} {pw : Word} {A : Address}
    (hv : VarsOK ρ η σs cx.vars env) (hpk : cx.peek a = .ok t) (hwd : word2Of t = some (r, P))
    (hea : evalAt env a = some (rt, [pw])) (hA : addrOf pw = some A) :
    ∃ c, η.sto A.label = some c ∧ AtOff c.ty A.offset (.word2 (.lit (ev ρ r)) P) := by
  have hcell : ∃ μ, cellOf t = some (μ, .word2 r P) := by
    unfold word2Of at hwd
    split at hwd <;> cases hwd <;> exact ⟨_, rfl⟩
  obtain ⟨μ, hcell⟩ := hcell
  obtain ⟨rt', ws, hea', hvr, -⟩ := peek_VR hv hpk
  rw [hea] at hea'
  cases hea'
  obtain ⟨ad, c, hws, hsto, hat, -, -⟩ := cell_target hcell (Fd_noarr (by simp [cl, accs])) hvr
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
  have hA' : A = ad := by
    simp only [addrOf, hws] at hA
    cases hA; rfl
  subst hA'
  exact ⟨c, hsto, by simpa only [cl, clI_zero] using hat⟩

/-- **Pair `stp`.**  An `stp` on a protocol pair that appends at a pair
`Word2At` of region `n` was made by a thread whose frame holds `rg n`. -/
theorem stp_word2_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v0 v1 tk : At} {e : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto2}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e) (hop : OpT p cx x (.stp rel a v0 v1 tk) c')
    (hpk : cx.peek a = .ok tw) (hwd : word2Of tw = some (r0, P0))
    (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto2} (hw : Word2At (CE η) m.loc n P) :
    1 ≤ Rf (.rg n) := by
  obtain ⟨r', i0, i1, c₁, hu, hrr⟩ := stp_word2_tok hop hpk hwd
  obtain ⟨hle, hsat⟩ := tok2_frame hi hE.2.2 hu
  have he : ev ρ r0 = ev ρ r' := hrr ρ hsat
  obtain ⟨rt, pw, A, hea, hA, hloc⟩ := tstep_stp_new hterm hr hn
  obtain ⟨c, hsto, hat⟩ := word2_link hi.1.2.1 hpk hwd hea hA
  obtain ⟨c', hc', hat'⟩ := hw
  change η.sto m.loc.label = some c' at hc'
  rcases hloc with hl | hl
  · rw [hl] at hc' hat'
    rw [hsto] at hc'
    cases hc'
    obtain ⟨h1, -⟩ := AtOff_word2_uniq hat hat'
    cases h1
    rw [he]
    exact hle
  · rw [hl] at hc' hat'
    simp only [offs] at hc' hat'
    rw [hsto] at hc'
    cases hc'
    exfalso
    rcases AtOff_word2_word2 hat hat' with ⟨h, -⟩ | h | h <;> omega

/-- **Pair `casp`.**  A `casp` on a protocol pair that appends at the first
word of a pair `Word2At` of protocol `P` overwrote a holding pair of `P` (the
expected pair, read at `A`, `A.next`). -/
theorem casp_word2_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {x : String} {ok fail : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto2}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 x ok fail)
    (hT : Typed p cx (.casp acq rel w e0 e1 v0 v1 x ok fail))
    (hpk : cx.peek w = .ok tw) (hwd : word2Of tw = some (r0, P0))
    (hi : FInv ρ η th.σs K cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto2} (hw : Word2At (CE η) m.loc n P) :
    ∃ wd0 wd1, PredAt r.1 m.loc t wd0 ∧ PredAt r.1 m.loc.next (t + 1) wd1 ∧
      Word2Holds P [wd0.val, wd1.val] := by
  obtain ⟨i0, i1, c, k0, k1, cl, hie0, hie1, hst, hcl, hh⟩ := casp_word2_inv hT hpk hwd
  obtain ⟨tw', pw, te0, x0, te1, x1, A, hea, hee0, hee1, hA, hcase⟩ := tstep_casp_new hterm hm hr hn
  have hsat : Sat cx.facts ρ := hi.1
  obtain ⟨c2, hsto, hat⟩ := word2_link hi.2.1 hpk hwd hea hA
  obtain ⟨c', hc', hat'⟩ := hw
  change η.sto m.loc.label = some c' at hc'
  rcases hcase with ⟨hl, wd0, wd1, hp0, hp1, hv0, hv1⟩ | hl
  · rw [hl] at hc' hat' ⊢
    rw [hsto] at hc'
    cases hc'
    obtain ⟨-, rfl⟩ := AtOff_word2_uniq hat hat'
    obtain ⟨tv0, htv0, hio0⟩ := hie0
    obtain ⟨rt0, y0, hev0, hyv0, -⟩ := atom_num hi.2.1 htv0 hio0
    rw [hee0] at hev0
    cases hev0
    obtain ⟨tv1, htv1, hio1⟩ := hie1
    obtain ⟨rt1, y1, hev1, hyv1, -⟩ := atom_num hi.2.1 htv1 hio1
    rw [hee1] at hev1
    cases hev1
    refine ⟨wd0, wd1, hp0, hp1, ?_⟩
    rw [hv0, hv1, hyv0, hyv1]
    exact holds2_of_st hsat hst hcl hh
  · exfalso
    rw [hl] at hc' hat'
    simp only [WeakMem.Address.next] at hc' hat'
    rw [hsto] at hc'
    cases hc'
    rcases AtOff_word2_word2 hat hat' with ⟨h, -⟩ | h | h <;> omega

/-- The terms whose step may append at a protocol pair: an `stp` or `casp`
whose address operand is typed as a pair. -/
def Word2Op (cx : Cx) : Expr → Prop
  | .let_ _ (.stp _ a _ _ _) _ => ∃ t rP, cx.peek a = .ok t ∧ word2Of t = some rP
  | .casp _ _ w _ _ _ _ _ _ _ => ∃ t rP, cx.peek w = .ok t ∧ word2Of t = some rP
  | _ => False

/-- The pair footprint obligation (gap, as `NonWordFoot`): a step of any
other term never appends at the first word of a protocol pair. -/
def NonWord2Foot (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (cx : Cx) (E : TEnv) : Prop :=
  ¬ Word2Op cx th.term → ∀ r ∈ tstep g mem pairs th, ∀ t m, NewAt mem r.1 t m → ∀ n P, ¬ Word2At E m.loc n P

/-- **Pair C1, the dichotomy.**  A thread step that appends at the first word
`m.loc` of a protocol pair (region `n`, protocol `P`) was made by a thread whose
frame holds `rg n` (`stp`), or overwrote a holding pair (`casp`). -/
theorem pair_write_dichotomy {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hfoot : NonWord2Foot g mem pairs th cx (CE η))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto2} (hw : Word2At (CE η) m.loc n P) :
    1 ≤ Rf (.rg n) ∨ ∃ wd0 wd1, PredAt r.1 m.loc t wd0 ∧ PredAt r.1 m.loc.next (t + 1) wd1 ∧
      Word2Holds P [wd0.val, wd1.val] := by
  by_cases hwo : Word2Op cx th.term
  · generalize ht : th.term = t0 at hT hwo
    cases t0 with
    | let_ x op e =>
      cases op with
      | stp rel a v0 v1 tk =>
        obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd⟩ := hwo
        cases hT with
        | let_ hop _ => exact Or.inl (stp_word2_step ht hop hpk hwd hi hE hr hn hw)
      | _ => exact hwo.elim
    | casp acq rel w e0 e1 v0 v1 x ok fail =>
      obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd⟩ := hwo
      exact Or.inr (casp_word2_step ht hT hpk hwd hi.1 hm hr hn hw)
    | _ => exact hwo.elim
  · exact absurd hw (hfoot hwo r hr t m hn n P)

/-- **Pair C1, leaving a held state**: a thread step that appends at the first
word of a pair whose predecessor pair is held was made by a thread whose frame
holds `rg n`. -/
theorem pair_write_needs_token {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hfoot : NonWord2Foot g mem pairs th cx (CE η))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto2} (hw : Word2At (CE η) m.loc n P)
    (hpwf : pwf2 P = true) {wd0 wd1 : Word} (hpre0 : PredAt r.1 m.loc t wd0)
    (hpre1 : PredAt r.1 m.loc.next (t + 1) wd1) (hheld : HeldV2 P wd0.val wd1.val) :
    1 ≤ Rf (.rg n) := by
  rcases pair_write_dichotomy hT hi hE hm hfoot hr hn hw with h | ⟨wd0', wd1', hp0, hp1, hh⟩
  · exact h
  · have e0 := PredAt_uniq hpre0 hp0
    have e1 := PredAt_uniq hpre1 hp1
    subst e0
    subst e1
    exact absurd hheld (holds_not_heldV2 hpwf hh)


/-- **`NonWordFootT` at `stp`** (type disjointness): a pair store appends only
at its pair's two words, never at a non-ghost `WordAt`. -/
theorem stp_no_wordAt {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {x : String} {rel : Bool} {a v0 v1 tk : At} {e : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto2}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok tw) (hwd : word2Of tw = some (r0, P0)) (hi : FInv ρ η th.σs K cx th.env)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) : False := by
  obtain ⟨rt, pw, A, hea, hA, hloc⟩ := tstep_stp_new hterm hr hn
  obtain ⟨c, hsto, hat⟩ := word2_link hi.2.1 hpk hwd hea hA
  obtain ⟨c', hc', hat', hg⟩ := hw
  change η.sto m.loc.label = some c' at hc'
  rcases hloc with hl | hl
  · rw [hl] at hc' hat'
    rw [hsto] at hc'
    cases hc'
    rcases AtOff_word_word2 hg hat' hat with h | h <;> omega
  · rw [hl] at hc' hat'
    simp only [offs] at hc' hat'
    rw [hsto] at hc'
    cases hc'
    rcases AtOff_word_word2 hg hat' hat with h | h <;> omega

/-- **`NonWordFootT` at `casp`** (type disjointness): a pair `casp` appends only
at its pair's two words, never at a non-ghost `WordAt`. -/
theorem casp_no_wordAt {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {x : String} {ok fail : Expr} {tw : Ty} {r0 : Idx} {P0 : Proto2}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 x ok fail)
    (hpk : cx.peek w = .ok tw) (hwd : word2Of tw = some (r0, P0))
    (hi : FInv ρ η th.σs K cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) : False := by
  obtain ⟨tw', pw, te0, x0, te1, x1, A, hea, -, -, hA, hcase⟩ := tstep_casp_new hterm hm hr hn
  obtain ⟨c, hsto, hat⟩ := word2_link hi.2.1 hpk hwd hea hA
  obtain ⟨c', hc', hat', hg⟩ := hw
  change η.sto m.loc.label = some c' at hc'
  rcases hcase with ⟨hl, -⟩ | hl
  · rw [hl] at hc' hat'
    rw [hsto] at hc'
    cases hc'
    rcases AtOff_word_word2 hg hat' hat with h | h <;> omega
  · rw [hl] at hc' hat'
    simp only [WeakMem.Address.next] at hc' hat'
    rw [hsto] at hc'
    cases hc'
    rcases AtOff_word_word2 hg hat' hat with h | h <;> omega


/-- (pair gate) `caspE_no_wordAt` for every word unit or pair unit (`WUnit`); `caspE_no_wordAt` is its word instance. -/
theorem caspE_no_wordAtG {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {x : String} {ok fail : Expr} {tw : Ty} {r0 : Idx} {P0 : ECounter}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 x ok fail)
    (hpk : cx.peek w = .ok tw) (hwd : epairOf tw = some (r0, P0))
    (hi : FInv ρ η th.σs K cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} (hw : WUnit (CE η) m.loc n) : False := by
  obtain ⟨tw', pw, te0, x0, te1, x1, A, hea, -, -, hA, hcase⟩ := tstep_casp_new hterm hm hr hn
  have hcell : ∃ μ, cellOf tw = some (μ, .epair r0 P0) := by
    unfold epairOf at hwd
    split at hwd <;> cases hwd <;> exact ⟨_, rfl⟩
  obtain ⟨μ, hcell⟩ := hcell
  obtain ⟨rt', ws, hea', hvr, -⟩ := peek_VR hi.2.1 hpk
  rw [hea] at hea'
  cases hea'
  obtain ⟨ad, c, hws, hsto, hat, -, -⟩ := cell_target hcell (Fd_noarr (by simp [cl, accs])) hvr
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
  have hA' : A = ad := by
    simp only [addrOf, hws] at hA
    cases hA; rfl
  subst hA'
  simp only [cl, clI_zero] at hat
  have hS : Solid (.epair (.lit (ev ρ r0)) P0) :=
    ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ h => by cases h)⟩
  have hus : accs (.epair (.lit (ev ρ r0)) P0) = some [.two] := by simp [accs]
  rcases hcase with ⟨hl, -⟩ | hl
  · exact solid_no_wordG (j := 0) hsto hat hS (fun _ _ h => by cases h) (fun _ _ h => by cases h) hus (by rw [hl]) (by rw [hl]; rfl)
      (by simp [nWords, Acc.size]) hw
  · exact solid_no_wordG (j := 1) hsto hat hS (fun _ _ h => by cases h) (fun _ _ h => by cases h) hus (by rw [hl]; rfl)
      (by rw [hl]; rfl) (by simp [nWords, Acc.size]) hw

/-- **`NonWordFootT` at `casp` on an epoch pair** (`caspE`; type
disjointness): an epoch pair is a leaf, so its two words hold no `WordAt`. -/
theorem caspE_no_wordAt {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {x : String} {ok fail : Expr} {tw : Ty} {r0 : Idx} {P0 : ECounter}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 x ok fail)
    (hpk : cx.peek w = .ok tw) (hwd : epairOf tw = some (r0, P0))
    (hi : FInv ρ η th.σs K cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P) : False :=
  caspE_no_wordAtG hterm hpk hwd hi hm hr hn (Or.inl ⟨P, hw⟩)


/-! ## Gap 1 at `storeOwn`, closed by W1 -/

/-- **Why a static footprint does not suffice (static part).**  `storeOwn`'s
premises on the cell type hold for an own cell of type `prod (word r P) int`
(head-only `wordFreeIn`), whose offset 0 is a non-ghost protocol word: the
store's unit 0 appends at a `WordAt` with no token in the frame.  Dynamically
the stored value then carries `wd n` (`wholecell_two_carriers`), so W1 rules the
step out at an initialised unit. -/
theorem storeOwn_word_cex (ke : KEnv) (r : Idx) (P : Proto) (hP : P.ghost = false) :
    wordOf (.ptr .own (.prod (.word r P) .int)) = none ∧
    cellOf (.ptr .own (.prod (.word r P) .int)) = some (.own, .prod (.word r P) .int) ∧
    Ty.wordFreeIn ke (.prod (.word r P) .int) = true ∧
    accs (.prod (.word r P) .int) = some [.one, .one] ∧
    AtOff (.prod (.word r P) .int) 0 (.word r P) ∧ dwf (.prod (.word r P) .int) = false := by
  obtain ⟨-, -, h3, h4⟩ := wordFree_counterexample r P hP
  exact ⟨rfl, rfl, rfl, h4, h3, rfl⟩

/-! ## Token uniqueness from the sum form (Gap 4) -/

theorem single_le_sum (f : Nat → Nat) : ∀ {l : List Nat} {i : Nat}, i ∈ l → f i ≤ (l.map f).sum
  | [], _, h => by simp at h
  | a :: l, i, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := single_le_sum f h
      omega

theorem two_le_sum (f : Nat → Nat) : ∀ {l : List Nat}, l.Nodup → ∀ {i j : Nat},
    i ∈ l → j ∈ l → i ≠ j → f i + f j ≤ (l.map f).sum
  | [], _, _, _, hi, _, _ => by simp at hi
  | a :: l, hnd, i, j, hi, hj, hij => by
    simp only [List.map_cons, List.sum_cons]
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hi with hia | hi <;> rcases List.mem_cons.mp hj with hja | hj
    · exact absurd (hia.trans hja.symm) hij
    · have := single_le_sum f hj
      rw [hia]
      omega
    · have := single_le_sum f hi
      rw [hja]
      omega
    · have := two_le_sum f hnd'.2 hi hj hij
      omega

/-- The `machine_tokens` sum form for `N` threads and memory's held part `H`. -/
def TokSum (Tot : Nat → Res) (N : Nat) (H : Res) (n : Nat) : Prop :=
  ((List.range N).map (fun i => Tot i (.rg n))).sum + H (.rg n) ≤ 1

/-- The sum form gives token uniqueness among the `N` threads. -/
theorem tokUniq_of_sum {Tot : Nat → Res} {N : Nat} {H : Res} {n : Nat} (hs : TokSum Tot N H n)
    {i j : Nat} (hiN : i < N) (hjN : j < N)
    (hi : 1 ≤ Tot i (.rg n)) (hj : 1 ≤ Tot j (.rg n)) : i = j := by
  apply Classical.byContradiction
  intro hij
  have := two_le_sum (fun i => Tot i (.rg n)) (List.nodup_range)
    (List.mem_range.mpr hiN) (List.mem_range.mpr hjN) hij
  unfold TokSum at hs
  omega

/-- **C2 (sum form)**: `held_word_changes_only_by_holder` with `TokUniq`
replaced by the `machine_tokens` sum bound over threads `0..N-1`. -/
theorem held_word_changes_only_by_holder_sum {p : Prog} {g : G} {mem : Memory} {pairs : List Ts}
    {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop}
    {Rf Rs : Res} {Tot : Nat → Res} {N : Nat} {Hm : Res} {h j : Nat} {n : Nat}
    (hs : TokSum Tot N Hm n) (hhN : h < N) (hjN : j < N)
    (hh : 1 ≤ Tot h (.rg n)) (hTot : Rf + Rs = Tot j)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) Hm) (hfootT : NonWordFootT g mem pairs th cx (CE η) Rf)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + Hm (.wd n) ≤ 1) (hini : IniU η m.loc n P)
    (hpwf : pwf P = true) {wd : Word} (hpre : PredAt r.1 m.loc t wd) (hheld : HeldV P wd.val) :
    j = h := by
  have h1 := held_write_needs_token hT hi hE htv hm hsc hH hfootT hr hn hw hwd hini hpwf hpre hheld
  have h2 : 1 ≤ Tot j (.rg n) := by
    rw [← hTot, Res.add_apply]
    omega
  exact tokUniq_of_sum hs hjN hhN h2 hh

/-! ## `NonWordFootT` discharged -/

/-- (pair gate) **The word-key footprint**: `nonWordFootT_of`'s case analysis for every word-key unit (`WdAt`), for
a term that addresses neither a word (`WordOp`) nor a pair (`Word2Op`). -/
theorem nonWdFootT_of {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs : Res}
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term) :
    ¬ WordOp cx th.term → ¬ Word2Op cx th.term → ∀ r ∈ tstep g mem pairs th, ∀ t m, NewAt mem r.1 t m →
      ∀ n, WdAt (CE η) m.loc n → 1 ≤ Rf (.wd n) := by
  intro hnw hnw2 r hr t m hn n hw
  by_cases hA : AppTerm th.term
  rotate_left
  · exact (fresh_no_wordG hm hA hr hn hw.unit).elim
  by_cases hR : StepScopeR th.σs cx th.term
  · exact (keep_no_new (frame_keep hR hT hCk hi hE htv hm r hr).1 hn).elim
  have hsc' := hsc.resolve_right hR
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsc' hA hnw hnw2
  cases hT0 with
  | let_ hop _ =>
    cases hop with
    | storeWordGive hpk hw' | storeWordKeep hpk hw' | storeWordHand hpk hw' =>
        exact (hnw (by simp only [WordOp]; exact ⟨_, _, hpk, hw'⟩)).elim
    | storeRgn hpk _ hc | storeCap hpk _ hc => exact absurd hc (hsc' _ hpk _ _)
    | storeOwn hpk hnw' hc =>
        rcases cell_cases hc with rfl | rfl
        · exact storeOwn_wd_frameG ht hpk hnw' hT hi hE htv hr hn hw
        · exact storeLoc_wd_frameG ht hpk hnw' hT hi hE htv hr hn hw
    | storePub hpk hnw' hc =>
        rcases cell_cases hc with rfl | rfl
        · exact storePub_wd_frameG ht hpk hnw' hT hi hE htv hr hn hw
        · exact storePubLoc_wd_frameG ht hpk hnw' hT hi hE htv hr hn hw
    | fetchCell hpk _ hc =>
        rcases hc with hc | ⟨_, hc, _⟩ <;> exact (fetchCell_no_wordAtG ht hpk hc hi.1 hE htv hr hn hw.unit).elim
    | fetchEpoch hpk hw' | fetchShare hpk hw' =>
        exact (hnw (by simp only [WordOp]; exact ⟨_, _, hpk, hw'⟩)).elim
    | xchg hpk hx =>
        cases hx with
        | own _ hc =>
            rcases cell_cases hc with rfl | rfl
            · exact xchgOwn_wd_frameG ht hpk hT hi hE htv hr hn hw
            · exact xchgLoc_wd_frameG ht hpk hT hi hE htv hr hn hw
        | rgn _ hc => exact absurd hc (hsc' _ hpk _ _)
    | xchgAt => exact xchgAt_wd_frameG ht hT hi hE htv hr hn hw
    | xchgAtF => exact xchgAtF_wd_frameG ht hT hi hE htv hr hn hw
    | bufInit => exact bufInit_wd_frameG ht hT hi hE htv hr hn hw
    | stl => exact (stl_no_wordAtG ht hT hi htv hr hn hw.unit).elim
    | stlw => exact (stlw_no_wordAtG ht hT hi htv hr hn hw.unit).elim
    | stpGive hpk hwd | stpKeep hpk hwd =>
        exact (hnw2 (by simp only [Word2Op]; exact ⟨_, _, hpk, hwd⟩)).elim
    | _ => exact (show False from hA).elim
  | casCell hpk _ hc hone haff =>
      rcases hc with hc | ⟨_, hc, _⟩ <;>
        exact (casCell_no_wordAtG ht hpk hc hone haff hi.1 hE htv hr hn hw.unit).elim
  | casShare hpk hw' | casTake hpk hw' | casEpoch hpk hw' =>
      exact (hnw (by simp only [WordOp]; exact ⟨_, _, hpk, hw'⟩)).elim
  | caspMove hpk hwd | caspTake hpk hwd | caspBump hpk hwd =>
      exact (hnw2 (by simp only [Word2Op]; exact ⟨_, _, hpk, hwd⟩)).elim
  | caspE hpk _ hE2 => exact (caspE_no_wordAtG ht hpk hE2 hi.1 hm hr hn hw.unit).elim
  | _ => exact (show False from hA).elim

/-- **`NonWordFootT` holds for every typed, in-scope thread.**  A step outside
`AppTerm` appends only at the fresh label (`fresh_no_word`); a frame-only term
keeps memory (`frame_keep`); the whole-cell and component ops carry `wd n` in
the written value (`*_wd_frame`); `casCell`/`fetchCell`, `stl`/`stlw`,
`stp`/`casp` never append at a `WordAt` (`*_no_wordAt`); region stores and
exchanges are out of scope; the word ops are `WordOp`. -/
theorem nonWordFootT_of {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs : Res}
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term) :
    NonWordFootT g mem pairs th cx (CE η) Rf := by
  intro hnw r hr t m hn n P hw hep
  by_cases h2 : Word2Op cx th.term
  · generalize ht : th.term = t0 at h2
    cases t0 with
    | let_ x op e =>
      cases op with
      | stp rel a v0 v1 tk =>
        obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd⟩ := h2
        exact (stp_no_wordAt ht hpk hwd hi.1 hr hn hw).elim
      | _ => exact h2.elim
    | casp acq rel w e0 e1 v0 v1 x ok fail =>
      obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd⟩ := h2
      exact (casp_no_wordAt ht hpk hwd hi.1 hm hr hn hw).elim
    | _ => exact h2.elim
  · exact nonWdFootT_of hT hCk hi hE htv hm hsc hnw h2 r hr t m hn n (Or.inl ⟨P, hw, hep⟩)


/-! ## C1 without the footprint hypothesis -/

/-- `held_write_dichotomy` with `hfootT` discharged (`nonWordFootT_of`). -/
theorem held_write_dichotomy_noFoot {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rk H : Res}
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rk) cx th.env Rf) (hE : EnvOK p η)
    (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + H (.wd n) ≤ 1) (hini : IniU η m.loc n P) (hpwf : pwf P = true) :
    1 ≤ Rf (.rg n) ∨ (∃ wd, PredAt r.1 m.loc t wd ∧ WordHolds P [wd.val]) ∨ NoHeld P :=
  held_write_dichotomy hT hi hE htv hm hsc hH (nonWordFootT_of hT hCk hi hE htv hm (.inl hsc)) hr hn hw hwd hini hpwf

/-- `held_write_needs_token` with `hfootT` discharged. -/
theorem held_write_needs_token_noFoot {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rk H : Res}
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rk) cx th.env Rf) (hE : EnvOK p η)
    (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + H (.wd n) ≤ 1) (hini : IniU η m.loc n P)
    (hpwf : pwf P = true) {wd : Word} (hpre : PredAt r.1 m.loc t wd) (hheld : HeldV P wd.val) :
    1 ≤ Rf (.rg n) :=
  held_write_needs_token hT hi hE htv hm hsc hH (nonWordFootT_of hT hCk hi hE htv hm (.inl hsc)) hr hn hw hwd
    hini hpwf hpre hheld

/-- `held_enter_needs_token` with `hfootT` discharged. -/
theorem held_enter_needs_token_noFoot {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rk H : Res}
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rk) cx th.env Rf) (hE : EnvOK p η)
    (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {n : Nat} {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + H (.wd n) ≤ 1) (hini : IniU η m.loc n P) (hpwf : pwf P = true)
    (hheld : HeldV P m.val) :
    1 ≤ Rf (.rg n) ∨ ∃ wd, PredAt r.1 m.loc t wd ∧ WordHolds P [wd.val] :=
  held_enter_needs_token hT hi hE htv hm hsc hH (nonWordFootT_of hT hCk hi hE htv hm (.inl hsc)) hr hn hw hwd
    hini hpwf hheld

/-- `held_word_changes_only_by_holder` with `hfootT` discharged. -/
theorem held_word_changes_only_by_holder_noFoot {p : Prog} {g : G} {mem : Memory} {pairs : List Ts}
    {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs Rk : Res}
    {Tot : Nat → Res} {h j : Nat} {n : Nat} {Hm : Res}
    (hu : TokUniq Tot n) (hh : 1 ≤ Tot h (.rg n)) (hTot : Rf + Rs = Tot j)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rk) cx th.env Rf) (hE : EnvOK p η)
    (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) Hm)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + Hm (.wd n) ≤ 1) (hini : IniU η m.loc n P)
    (hpwf : pwf P = true) {wd : Word} (hpre : PredAt r.1 m.loc t wd) (hheld : HeldV P wd.val) :
    j = h :=
  held_word_changes_only_by_holder hu hh hTot hT hi hE htv hm hsc hH
    (nonWordFootT_of hT hCk hi hE htv hm (.inl hsc)) hr hn hw hwd hini hpwf hpre hheld

/-- `held_word_changes_only_by_holder_sum` with `hfootT` discharged. -/
theorem held_word_changes_only_by_holder_sum_noFoot {p : Prog} {g : G} {mem : Memory} {pairs : List Ts}
    {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    {Rf Rs Rk : Res} {Tot : Nat → Res} {N : Nat} {Hm : Res} {h j : Nat} {n : Nat}
    (hs : TokSum Tot N Hm n) (hhN : h < N) (hjN : j < N)
    (hh : 1 ≤ Tot h (.rg n)) (hTot : Rf + Rs = Tot j)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rk) cx th.env Rf) (hE : EnvOK p η)
    (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) Hm)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : NewAt mem r.1 t m) {P : Proto} (hw : WordAt (CE η) m.loc n P)
    (hwd : Rf (.wd n) + Hm (.wd n) ≤ 1) (hini : IniU η m.loc n P)
    (hpwf : pwf P = true) {wd : Word} (hpre : PredAt r.1 m.loc t wd) (hheld : HeldV P wd.val) :
    j = h :=
  held_word_changes_only_by_holder_sum hs hhN hjN hh hTot hT hi hE htv hm hsc hH
    (nonWordFootT_of hT hCk hi hE htv hm (.inl hsc)) hr hn hw hwd hini hpwf hpre hheld

end TermLiveHeld

#print axioms TermLiveHeld.wd_held
#print axioms TermLiveHeld.wholecell_two_carriers
#print axioms TermLiveHeld.wholecell_excluded
#print axioms TermLiveHeld.held_write_dichotomy
#print axioms TermLiveHeld.held_write_needs_token
#print axioms TermLiveHeld.held_enter_needs_token
#print axioms TermLiveHeld.held_word_changes_only_by_holder
#print axioms TermLiveHeld.held_word_changes_only_by_holder_sum
#print axioms TermLiveHeld.pair_write_dichotomy
#print axioms TermLiveHeld.pair_write_needs_token
#print axioms TermLiveHeld.tokUniq_of_sum
#print axioms TermLiveHeld.storeOwn_word_cex
#print axioms TermLiveHeld.storeOwn_wd_frame
#print axioms TermLiveHeld.stp_no_wordAt
#print axioms TermLiveHeld.casp_no_wordAt
#print axioms TermLiveHeld.storeUnits_new_loc
#print axioms TermLiveHeld.wd_frame_whole
#print axioms TermLiveHeld.wd_frame_comp
#print axioms TermLiveHeld.solid_no_word
#print axioms TermLiveHeld.dwf_no_word
#print axioms TermLiveHeld.grows_no_word
#print axioms TermLiveHeld.storeLoc_wd_frame
#print axioms TermLiveHeld.storePub_wd_frame
#print axioms TermLiveHeld.storePubLoc_wd_frame
#print axioms TermLiveHeld.xchgOwn_wd_frame
#print axioms TermLiveHeld.xchgLoc_wd_frame
#print axioms TermLiveHeld.xchgAt_wd_frame
#print axioms TermLiveHeld.xchgAtF_wd_frame
#print axioms TermLiveHeld.bufInit_wd_frame
#print axioms TermLiveHeld.casCell_no_wordAt
#print axioms TermLiveHeld.fetchCell_no_wordAt
#print axioms TermLiveHeld.stl_no_wordAt
#print axioms TermLiveHeld.stlw_no_wordAt
#print axioms TermLiveHeld.caspE_no_wordAt
#print axioms TermLiveHeld.tstep_new_label
#print axioms TermLiveHeld.fresh_no_word
#print axioms TermLiveHeld.nonWordFootT_of
#print axioms TermLiveHeld.held_write_dichotomy_noFoot
#print axioms TermLiveHeld.held_write_needs_token_noFoot
#print axioms TermLiveHeld.held_enter_needs_token_noFoot
#print axioms TermLiveHeld.held_word_changes_only_by_holder_noFoot
#print axioms TermLiveHeld.held_word_changes_only_by_holder_sum_noFoot
#print axioms TermLiveHeld.word_cell
#print axioms TermLiveHeld.store_word_loc
#print axioms TermLiveHeld.fetch_word_facts
#print axioms TermLiveHeld.cas_word_epoch
#print axioms TermLiveHeld.wd_frame_wholeG
#print axioms TermLiveHeld.wd_frame_compG
#print axioms TermLiveHeld.solid_no_wordG
#print axioms TermLiveHeld.dwf_no_wordG
#print axioms TermLiveHeld.grows_no_wordG
#print axioms TermLiveHeld.storeLoc_wd_frameG
#print axioms TermLiveHeld.storePub_wd_frameG
#print axioms TermLiveHeld.storePubLoc_wd_frameG
#print axioms TermLiveHeld.xchgOwn_wd_frameG
#print axioms TermLiveHeld.xchgLoc_wd_frameG
#print axioms TermLiveHeld.xchgAt_wd_frameG
#print axioms TermLiveHeld.xchgAtF_wd_frameG
#print axioms TermLiveHeld.bufInit_wd_frameG
#print axioms TermLiveHeld.storeOwn_wd_frameG
#print axioms TermLiveHeld.casCell_no_wordAtG
#print axioms TermLiveHeld.fetchCell_no_wordAtG
#print axioms TermLiveHeld.stl_no_wordAtG
#print axioms TermLiveHeld.stlw_no_wordAtG
#print axioms TermLiveHeld.caspE_no_wordAtG
#print axioms TermLiveHeld.fresh_no_wordG
#print axioms TermLiveHeld.nonWdFootT_of
#print axioms TermLiveHeld.wd_held_core
#print axioms TermLiveHeld.tstep_casp_push
