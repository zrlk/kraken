import WeakCore.TermK2aLd
import WeakCore.TermK2aRet
import WeakCore.TermFulCntR

/-!
# TermK2aMain: assembling `PtrRtsThreadGL` (K-2a)

* `stepOK_of_stepB_nil`: a binding contract proved at the empty store typing (no word is loaded
  from a cell of it) is a full step contract, labels included.
* `memRts_step`: (M), edge form, across an owner step at the old `tmin`.
-/

namespace TermK2aMain

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermPtrRts TermOwnG0Defs TermK2a TermK2aLd
open TermCut (GEnv)
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## 1. Contracts at the empty store typing -/

/-- No word is loaded from a cell of the empty store typing. -/
theorem not_loadW_nil {mem : Memory} {pairs P : List Ts} {w : Word} :
    ¬ LoadW (fun _ => none) mem pairs P w := by
  rintro ⟨u, m, cl, -, -, hcl, -⟩
  cases hcl

/-- **A contract proved at the empty store typing** (every new word old-covered, or naming `N`):
the full step contract at any store typing, the label half from `OldL` and `N`. -/
theorem stepOK_of_stepB_nil {sto : Sto} {s : St} {a : AllocLabel} {N : AllocLabel → Prop} {th th' : TTh}
    (h : StepB (fun _ => none) s.mem s.pairs a N th th') : StepOK sto s a N N th th' := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rcases h b hb with h0 | hn
    · exact .inl h0
    · refine .inr fun w hw => ?_
      obtain ⟨h1, h2⟩ := hn w hw
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact .inl h1
        · exact absurd h1 not_loadW_nil
      · rcases h2 with h2 | h2 | h2
        · exact .inl h2
        · exact absurd h2 not_loadW_nil
        · exact .inr (.inr h2)
  · rcases h b hb with h0 | hn
    · exact .inl h0
    · refine .inr fun w hw l hl => ?_
      rcases (hn w hw).2 with h2 | h2 | h2
      · exact .inr (h2 l hl)
      · exact absurd h2 not_loadW_nil
      · exact .inl (h2 l hl)

/-! ## 2. (M), edge form, across the step -/

/-- **A promise the step fulfils at a plant edge is above `t`** (K-3's argument, at any store
typing over `E.sto`): its value comes from a data word of an environment entry, shallow-pub
(`TermPubOnly.fulSNo`), so counted, and (R) at `t` bounds it below the write's bound. -/
theorem ful_edge_ge {p : Prog} {g : G} {E : TEnv} {sto : Sto} {mem : Memory} {pairs : List Ts} {th : TTh}
    {a : AllocLabel} {t : Ts} {r : Memory × List Ts × TTh} {u : Ts} {m : Msg}
    (hk : g.k.storeDepRts = true) (hsto : ∀ l c, E.sto l = some c → sto l = some c)
    (hT : ThInvE p E th) (hM : MemInv g E (stOf mem pairs th)) (hRts : ThRts t a th)
    (hr : r ∈ tstep g mem pairs th) (hup : u ∈ th.promises) (hn : u ∉ r.2.2.promises)
    (hm : mem[u]? = some m) (hpe : PlantEdge sto m a) : t ≤ u := by
  have hlt := TermStep.MemInv_promLt hM
  have hpp := TermStep.MemInv_nopair hM
  obtain ⟨⟨ca, hca, hno, hrf⟩, a', n, hv, ha'⟩ := hpe
  obtain ⟨-, rem⟩ := TermNoFul.tstep_fulT hlt hpp hr
  obtain ⟨m2, hm2, hw⟩ := rem u hup hn
  have e : m2 = m := Option.some.inj (hm2.symm.trans hm)
  subst e
  have hF := TermPubOnly.fulSNo p
  rcases hw with ⟨y, op, e, hterm, hW | hW⟩ |
      ⟨acq, rel, wa, ee, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, hterm, h1, h2, h3, hb, hval, hrts⟩
  · obtain ⟨pw, b, rel, us, ws, j, w, hU, hj, hwj, hl, hval, hrts⟩ := hW
    have hwv : w.val = .loc a' n := by rw [← hval]; exact hv
    have hnames : Names a w := ⟨a', n, hwv, ha'⟩
    have hwm : w ∈ ws := List.mem_of_getElem? hwj
    obtain ⟨x, rt, hdv, hx⟩ := TermNoFul.unitsOp_var hU hwm hnames
    have hs := hF E sto g mem pairs th x rt ws w m2.loc a hsto hT hM
      ⟨hx, hwm, Or.inl ⟨y, op, e, pw, b, rel, us, j, hterm, hdv, hU, hj, hwj, hl⟩⟩ hnames ⟨ca, hca, hno, hrf⟩
    have hle := hRts.1 x rt ws (TermNoFul.lookupE_mem hx) w (by rw [pubWords_of_sNo hs]; exact hwm) hnames
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt hle (hrts hk a' n hwv))
  · obtain ⟨o, -, -, -, -, -, mr, nw, hval⟩ := hW
    rw [hval] at hv
    exact absurd hv (TermNoFul.fetch_notLoc o mr nw a' n)
  · have hnv : nw.val = .loc a' n := by rw [← hval]; exact hv
    have hnames : Names a nw := ⟨a', n, hnv, ha'⟩
    obtain ⟨x, rfl, hx⟩ := TermNoFul.evalAt_names h3 (List.mem_singleton_self nw) hnames
    have hs := hF E sto g mem pairs th x t3 [nw] nw m2.loc a hsto hT hM
      ⟨hx, List.mem_singleton_self nw, Or.inr ⟨acq, rel, wa, ee, tn, ok, fail, t1, t2, pw, ew, hterm, rfl, h1,
        h2, hb⟩⟩ hnames ⟨ca, hca, hno, hrf⟩
    have hle := hRts.1 x t3 [nw] (TermNoFul.lookupE_mem hx) nw
      (by rw [pubWords_of_sNo hs]; exact List.mem_singleton_self nw) hnames
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt hle (hrts hk a' n hnv))

/-- **`MemRts` across an owner step** at the old `tmin` `t`: an old non-promise message is covered
by `MemRts` before (its cell is in `sto`: a label new to `sto'` holds only promises, `FreshLP`); a
promise the step fulfils is above `t` (`ful_edge_ge`); a new message is above every promise. -/
theorem memRts_step {p : Prog} {g : G} {E E' : TEnv} {sto sto' : Sto} {mem : Memory} {pairs : List Ts}
    {th : TTh} {a : AllocLabel} {t : Ts} {r : Memory × List Ts × TTh}
    (hk : g.k.storeDepRts = true) (h1 : ∀ l c, E.sto l = some c → sto l = some c)
    (h3 : ∀ l c, sto l = some c → sto' l = some c)
    (h4 : ∀ l c, sto' l = some c → sto l = none → E.sto l = none ∧ E'.sto l = some c)
    (hT : ThInvE p E th) (hm : MemInv g E (stOf mem pairs th)) (hr : r ∈ tstep g mem pairs th)
    (hF : Foot g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
    (ht : tminOf sto (stOf mem pairs th) a = some t) (hM : MemRts sto t a mem th.promises)
    (hRts : ThRts t a th) :
    MemRts sto' t a r.1 r.2.2.promises := by
  have hlt : ∀ u ∈ th.promises, u < mem.size := hm.2.2.1
  have htlt : t < mem.size := hlt t (tminOf_spec ht).1
  have hext : MemExt mem r.1 := (tstep_appUp hr).2.1
  intro u m hmu he hnP
  rcases Nat.lt_or_ge u mem.size with hus | hus
  · have hmu0 : mem[u]? = some m := TermFul.memExt_back hext hus hmu
    by_cases hup : u ∈ th.promises
    · exact ful_edge_ge hk (fun l c h => h3 l c (h1 l c h)) hT hm hRts hr hup hnP hmu0 he
    · obtain ⟨⟨ca, hca, hno, hrf⟩, hnm⟩ := he
      have hcl0 : sto m.loc.label = some ca := by
        cases e : sto m.loc.label with
        | some c0 => rw [h3 _ _ e] at hca; rw [hca]
        | none =>
          exfalso
          obtain ⟨hEn, hE'⟩ := h4 _ _ hca e
          rcases hF.1.2.2.1 m.loc.label with h | ⟨⟨j, hj, -, hl⟩, -⟩
          · rw [h, hEn] at hE'; cases hE'
          · exact hup ((hm.2.2.2.1.1 j hj).2.1 u m hmu0 hl)
      exact hM u m hmu0 ⟨⟨ca, hcl0, hno, hrf⟩, hnm⟩ hup
  · exact Nat.le_of_lt (Nat.lt_of_lt_of_le htlt hus)

end TermK2aMain

#print axioms TermK2aMain.stepOK_of_stepB_nil
#print axioms TermK2aMain.ful_edge_ge
#print axioms TermK2aMain.memRts_step
