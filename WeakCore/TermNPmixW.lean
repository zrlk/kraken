import WeakCore.TermStep

/-!
# TermNPmixW: `storeUnits_NPmix` with the selection's frame (`NewOverSel`), for the `hcovD`

`storeUnits_NPmixS` returns `storeUnits_NPmix`'s conclusion (its own `sel`, `vals`, `WLe`,
`LatestNP`) plus, for every unit `n` the selection keeps old (`sel n = false`), at the unit's
address `A_n = offs a (i + nWords (us.take n))`: no message at `A_n` is newly visible
(`NoNewVis`; equivalently the `NewOverSel`, contrapositive).

`sel` is indexed by unit (as `TermTear.mixU`), and a unit's word offset is
`nWords (us.take n)`, which is `n` when all units are `.one`.  Only a one-word unit that fulfils
a promise and keeps the old witness has `sel n = false`.  Then memory is unchanged and
`LatestNP_subErase`'s `Or.inl` case (`¬ (t0 < t ∧ t ∉ P')`) gives `NoNewVis`.  Units at other
addresses keep `AtSame`, hence `NoNewVis`.

Copies to replace with core exports later:
* `memPromAt_atSame`: COPY (timestamped) of the membership step inside `TermStep.PromAt_atSame`.
* `latestNP_subEraseS`: COPY (timestamped) of `TermStep.LatestNP_subErase`, exporting the case split.
* `stepStore_NPsameS`: COPY (timestamped) of `TermStep.stepStore_NPsameF`/`NPsameP`/`NPsame0`, all three
  readings at once through `PromAt`.
* `storeUnits_NPmixN`: COPY (timestamped) of `TermStep.storeUnits_NPmix`, extended.
-/

namespace TermNPmixW
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `storeUnits_NPmix` with the frame of the old-kept units: a unit `n` with `sel n = false` has
no newly visible message at its address. -/
theorem storeUnits_NPmixN {E : TEnv} {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St) (V : Ts) (old : List Word),
      s' ∈ storeUnits k arch pw a rel us ws i s → V ≤ s.vs.vRelSt → (∀ t, t ∈ s.promises → t < s.mem.size) →
      (∀ t, t ∈ E.fp → t < s.mem.size) → old.length = nWords us →
      (∀ j x, old[j]? = some x → LatestNP s.mem (PromAt E s (offs a (i + j))) (offs a (i + j)) x) →
      ∃ (sel : Nat → Bool) (vals : List Word), WLe (TermTear.mixU us sel (ws.map (bumpW V)) old) vals ∧
        (∀ j x, vals[j]? = some x → LatestNP s'.mem (PromAt E s' (offs a (i + j))) (offs a (i + j)) x) ∧
        ∀ n, n < us.length → sel n = false → us[n]? = some .one ∧
          NoNewVis E s s' (offs a (i + nWords (us.take n))) :=
  fun us ws i s s' V old hs hV hP hF hl hold =>
    let ⟨sel, vals, h1, h2, h3, _⟩ := storeUnits_NPmixNF (E := E) us ws i s s' V old hs hV hP hF hl hold
    ⟨sel, vals, h1, h2, h3⟩

/-- **`storeUnits_NPmixS`** (for the `hcovD`): `storeUnits_NPmix`'s conclusion with its own
`sel`, plus `NewOverSel`.  At unit `n` (address `A_n = offs a (i + nWords (us.take n))`), a
message at `A_n` above a bound `tw` that is newly visible forces `sel n = true`.  Before the store,
every message at `A_n` above `tw` was skipped. -/
theorem storeUnits_NPmixS {E : TEnv} {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St} {V : Ts} {old : List Word}
    (hs : s' ∈ storeUnits k arch pw a rel us ws i s) (hV : V ≤ s.vs.vRelSt)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size) (hF : ∀ t, t ∈ E.fp → t < s.mem.size)
    (hl : old.length = nWords us)
    (hold : ∀ j x, old[j]? = some x → LatestNP s.mem (PromAt E s (offs a (i + j))) (offs a (i + j)) x) :
    ∃ (sel : Nat → Bool) (vals : List Word), WLe (TermTear.mixU us sel (ws.map (bumpW V)) old) vals ∧
      (∀ j x, vals[j]? = some x → LatestNP s'.mem (PromAt E s' (offs a (i + j))) (offs a (i + j)) x) ∧
      ∀ n, n < us.length → ∀ tw : Ts,
        (∀ (t : Ts) (m : Msg), tw < t → s.mem[t]? = some m → m.loc = offs a (i + nWords (us.take n)) →
          t ∈ PromAt E s (offs a (i + nWords (us.take n)))) →
        (∃ (t : Ts) (m : Msg), tw < t ∧ s'.mem[t]? = some m ∧ m.loc = offs a (i + nWords (us.take n)) ∧
          t ∉ PromAt E s' (offs a (i + nWords (us.take n)))) →
        sel n = true := by
  obtain ⟨sel, vals, hW, hL, hS⟩ := storeUnits_NPmixN (E := E) us ws i s s' V old hs hV hP hF hl hold
  refine ⟨sel, vals, hW, hL, fun n hn tw hpre ⟨t, m, hlt, hm, hloc, hnot⟩ => ?_⟩
  cases hsn : sel n with
  | true => rfl
  | false => exact absurd ((hS n hn hsn).2 tw hpre t m hlt hm hloc) hnot

theorem nWords_take_succ_get : ∀ (us : List Acc) (n : Nat) (u : Acc), us[n]? = some u →
    nWords (us.take (n + 1)) = nWords (us.take n) + u.size
  | [], _, _, h => by simp at h
  | v :: us, 0, u, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      simp [nWords]
  | v :: us, n + 1, u, h => by
      have ih := nWords_take_succ_get us n u (by simpa using h)
      rw [List.take_succ_cons, List.take_succ_cons]
      simp only [nWords, List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- **Word-level `NewOverSel`**: a word `j` in a unit `n` the selection keeps old has no newly
visible message at its address (that unit is a one-word unit, so `j` is its word). -/
theorem storeUnits_NPmixW {E : TEnv} {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St} {V : Ts} {old : List Word}
    (hs : s' ∈ storeUnits k arch pw a rel us ws i s) (hV : V ≤ s.vs.vRelSt)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size) (hF : ∀ t, t ∈ E.fp → t < s.mem.size)
    (hl : old.length = nWords us)
    (hold : ∀ j x, old[j]? = some x → LatestNP s.mem (PromAt E s (offs a (i + j))) (offs a (i + j)) x) :
    ∃ (sel : Nat → Bool) (vals : List Word), WLe (TermTear.mixU us sel (ws.map (bumpW V)) old) vals ∧
      (∀ j x, vals[j]? = some x → LatestNP s'.mem (PromAt E s' (offs a (i + j))) (offs a (i + j)) x) ∧
      ∀ n j, InAcc us n j → sel n = false → NoNewVis E s s' (offs a (i + j)) := by
  obtain ⟨sel, vals, hW, hL, hS⟩ := storeUnits_NPmixN (E := E) us ws i s s' V old hs hV hP hF hl hold
  refine ⟨sel, vals, hW, hL, fun n j hI hsn => ?_⟩
  have hn : n < us.length := by
    apply Classical.byContradiction
    intro hn
    have e1 : us.take (n + 1) = us := List.take_of_length_le (by omega)
    have e2 : us.take n = us := List.take_of_length_le (by omega)
    have := hI.2; rw [e1] at this; have := hI.1; rw [e2] at this; omega
  obtain ⟨h1, hN⟩ := hS n hn hsn
  have e := nWords_take_succ_get us n .one h1
  have hj : j = nWords (us.take n) := by
    have := hI.1; have := hI.2; rw [e] at this; simp [Acc.size] at this; omega
  subst hj
  exact hN

/-- Every word of an access list lies in some unit. -/
theorem inAcc_exW : ∀ (us : List Acc) (o : Nat), o < nWords us → ∃ i, InAcc us i o
  | [], o, h => by simp [nWords] at h
  | u :: us, o, h => by
      have hu : nWords (u :: us) = u.size + nWords us := by simp [nWords]
      by_cases ho : o < u.size
      · exact ⟨0, by simp [nWords], by simp [nWords]; omega⟩
      · obtain ⟨i, h1, h2⟩ := inAcc_exW us (o - u.size) (by omega)
        refine ⟨i + 1, ?_, ?_⟩
        · have : nWords ((u :: us).take (i + 1)) = u.size + nWords (us.take i) := by simp [nWords]
          omega
        · have : nWords ((u :: us).take (i + 1 + 1)) = u.size + nWords (us.take (i + 1)) := by simp [nWords]
          omega

/-- (`GdLT`) A word whose unit the selection keeps old (the `decide` form `gd_fund`'s
latest-ness mask takes) has no newly visible message. -/
theorem nnv_sel {E : TEnv} {s s' : St} {us : List Acc} {sel : Nat → Bool} {ad : Address}
    (hNV : ∀ n j, InAcc us n j → sel n = false → NoNewVis E s s' (offs ad (0 + j))) :
    ∀ k, k < nWords us → @decide (∃ i, sel i = true ∧ InAcc us i k) (Classical.propDecidable _) = false →
      NoNewVis E s s' ⟨ad.label, ad.offset + k⟩ := by
  intro k hk hf
  obtain ⟨n0, hI⟩ := inAcc_exW us k hk
  have hno : ¬ ∃ i, sel i = true ∧ InAcc us i k := fun hx => by
    rw [@decide_eq_true _ (Classical.propDecidable _) hx] at hf; cases hf
  have hs : sel n0 = false := by
    cases h : sel n0
    · rfl
    · exact absurd ⟨n0, h, hI⟩ hno
  have := hNV n0 k hI hs
  simpa [offs] using this

-- (PIN option 3; from TermPinFulW)
/-- **(option 3, for `gd_fundX`) One selection, both frames**: `storeUnits_NPmixW`'s
`NoNewVis` at old-kept units, and at every unit fulfilling an own promise at a visible word unit
the selection keeps old (so the complement holds the stored word). -/
theorem storeUnits_NPmixWF {E : TEnv} {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St} {V : Ts} {old : List Word}
    (hs : s' ∈ storeUnits k arch pw a rel us ws i s) (hV : V ≤ s.vs.vRelSt)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size) (hF : ∀ t, t ∈ E.fp → t < s.mem.size)
    (hl : old.length = nWords us)
    (hold : ∀ j x, old[j]? = some x → LatestNP s.mem (PromAt E s (offs a (i + j))) (offs a (i + j)) x) :
    ∃ (sel : Nat → Bool) (vals : List Word), WLe (TermTear.mixU us sel (ws.map (bumpW V)) old) vals ∧
      (∀ j x, vals[j]? = some x → LatestNP s'.mem (PromAt E s' (offs a (i + j))) (offs a (i + j)) x) ∧
      (∀ n j, InAcc us n j → sel n = false → NoNewVis E s s' (offs a (i + j))) ∧
      (∀ t m j n, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc = offs a (i + j) →
        VisU E m.loc → InAcc us n j → sel n = false) ∧
      (∀ t m j, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc = offs a (i + j) →
        VisU E m.loc → (TermTear.mixU us sel old (ws.map (bumpW V)))[j]? = (ws.map (bumpW V))[j]?) := by
  obtain ⟨sel, vals, hW, hL, hS, hC, hB⟩ := storeUnits_NPmixNF (E := E) us ws i s s' V old hs hV hP hF hl hold
  refine ⟨sel, vals, hW, hL, fun n j hI hsn => ?_, hB, hC⟩
  have hn : n < us.length := by
    apply Classical.byContradiction
    intro hn
    have e1 : us.take (n + 1) = us := List.take_of_length_le (by omega)
    have e2 : us.take n = us := List.take_of_length_le (by omega)
    have := hI.2; rw [e1] at this; have := hI.1; rw [e2] at this; omega
  obtain ⟨h1, hN⟩ := hS n hn hsn
  have e := nWords_take_succ_get us n .one h1
  have hj : j = nWords (us.take n) := by
    have := hI.1; have := hI.2; rw [e] at this; simp [Acc.size] at this; omega
  subst hj
  exact hN

#print axioms storeUnits_NPmixWF

end TermNPmixW

#print axioms TermNPmixW.storeUnits_atSame
#print axioms TermNPmixW.stepStore_NPsameS
#print axioms TermNPmixW.storeUnits_NPmixN
#print axioms TermNPmixW.storeUnits_NPmixS
#print axioms TermNPmixW.storeUnits_NPmixW
#print axioms TermNPmixW.nnv_sel
