import WeakCore.TermFulW
import WeakCore.TermFreeQW
import WeakCore.TermStepPred
import WeakCore.TermOwnCP

/-! # TermOwnCR5: zero items at RMW one-unit targets (ownC route (A), R5)

`cas_cls2` / `fetch_cls2`: the RMW targets of `cas` / `fetch` off word units are one-word solid
components that are closed and copyable (`RmwAtomC`).  `freeQW_rmw`: a lowest own promise at such
a unit has a `freeQW` zero item, pinned at a typed word.
-/

namespace TermOwnCR5

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermB5 TermForWU TermFul TermFulW
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A closed, copyable one-word solid component at the address. -/
def RmwAtomC (E : TEnv) (a : Address) : Prop :=
  ∃ c S, E.sto a.label = some c ∧ AtOff c.ty a.offset S ∧ accs S = some [.one] ∧ Solid S ∧
    tb 0 S = true ∧ Ty.affine S = false

theorem tb_int : tb 0 Ty.int = true := by decide
theorem aff_int : Ty.affine Ty.int = false := by decide

/-- A `fetch`'s RMW target: a non-ghost protocol word or an `Int` component. -/
theorem fetch_cls2 {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {b : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some b) :
    WordUnit (CE η) b ∨ RmwAtomC (CE η) b := by
  cases hop with
  | fetchCell hp _ hc =>
      rcases hc with hc0 | ⟨r, hc0, -⟩
      all_goals
        obtain ⟨c, hsto, hat⟩ := int_tgt hi.2.1 hp (cell_cases hc0) hea hb
        exact .inr ⟨c, .int, hsto, hat, rfl, solid_int, tb_int, aff_int⟩
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ := word_mode ht ht' hμ'
      have hg := pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hok.1.1.1.1, hat⟩⟩

#print axioms fetch_cls2

/-- A `cas`'s RMW target: a non-ghost protocol word or a closed copyable one-word component. -/
theorem cas_cls2 {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {b : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some b) :
    WordUnit (CE η) b ∨ RmwAtomC (CE η) b := by
  cases hT with
  | casCell hp _ hc hraw haff =>
      have hraw0 := hraw
      rcases hc with hc0 | ⟨r, hc0, -⟩
      all_goals
        obtain ⟨c, U, hsto, hat, hFd, -⟩ := ptr_targetI hi.2.1 hp (cell_cases hc0) hea hb
        have hV : accs (cl ρ η.wit 0 0 _) = some [.one] := accs_cl_one hraw0
        have hacc : accs U = some [.one] := (Fd_accs hFd).trans hV
        have htb := tb_cellOf (peek_tb htv hp) hc0
        have hVa := AffineCl.affine_cl0 ρ η.wit cx.ke (fun k => (hE.2.1 k).1)
          (fun k _ hk => hi.2.2.2.2.2.2.2.2.1 k hk) _ haff htb
        have hVm := mg_cl (ρ := ρ) (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.2.2.2.2.2.2.1) _ 0 0
          (mg_cellOf (peek_mg htv hp) hc0)
        obtain ⟨S, hS, hsol, hSa, hStb, hSaf⟩ := one_leafM _ _ (Nat.lt_succ_self _)
          (Clo_cl (fun k => (hE.2.1 k).1) ρ _) hVm hV hVa
        have hat2 : AtOff c.ty b.offset S := by
          have := AtOff_trans (AtOff_trans hat (Fd_AtOff hFd (by rw [hacc]; exact Option.some_ne_none _))) hS
          simpa using this
        exact .inr ⟨c, S, hsto, hat2, hSa, hsol, hStb, hSaf⟩
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u, -, hnw⟩
      · have hμ := word_mode ht ht' hμ'
        have hg := pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep
        obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
        exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
      · rw [hw] at hnw; cases hnw

#print axioms cas_cls2

theorem rmwC_one {E : TEnv} {a : Address} (h : RmwAtomC E a) : RmwAtom1 E a := by
  obtain ⟨c, S, hsto, hat, hS, hsol, -, -⟩ := h
  exact ⟨c, S, [.one], hsto, hat, hS, TermForWU.nWords_one, hsol⟩

/-- The one unit of a one-word layout. -/
theorem sing_one : ∀ i o2, InAcc [Acc.one] i 0 → InAcc [Acc.one] i o2 → o2 = 0 := by
  intro i o2 h1 h2
  rcases i with _ | i
  · simp [InAcc, nWords, Acc.size] at h2
    omega
  · simp [InAcc, nWords, Acc.size] at h1

/-- **A zero item at an RMW one-unit target**: the lowest own promise `tw` at `⟨l, o⟩`, a closed
copyable one-word component off word units, pinned at a typed word `w`, has a `freeQW` item. -/
theorem freeQW_rmw {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o : Nat} {tw : Ts} {w : Word}
    (hR : RmwAtomC E ⟨l, o⟩) (hsto : E.sto l = some c) (hl : TermPlant.LowOwn s ⟨l, o⟩ tw)
    (hnw : ¬ WordUnit E ⟨l, o⟩)
    (hpin : ∀ tw', TermPlant.LowOwn s ⟨l, o⟩ tw' → PredAt s.mem ⟨l, o⟩ tw' w)
    (hok : WordOK E c.ty o w) :
    ∃ x, TermFreeQW.FreeQW E s l c tw x := by
  obtain ⟨c', S, hsto', hat, hS, hsol, htb, haf⟩ := hR
  simp only at hsto' hat
  rw [hsto] at hsto'
  cases hsto'
  have hP : TermPiece.Piece c.ty o S := ⟨hat, hsol, by rw [wc_of_accs hS]; simp [nWords, Acc.size]⟩
  refine TermFreeQW.freeQW_exists hsto hl hP hS (Nat.le_refl o) ?_ ?_ htb haf hnw hpin hok
  · simp [nWords, Acc.size]
  · simpa using sing_one

#print axioms freeQW_rmw

/-- **The pin word**: below the lowest own promise `tw` at `a`, with a defined message at
`t0 < tw` there, the predecessor of `tw` is a non-promise defined message (no undef above a defined
one, `hul`), hence typed (`hok`, the `MemOKP` clause). -/
theorem pin_wordOK {E : TEnv} {s : St} {a : Address} {T : Ty} {tw t0 : Ts} {m0 : Msg}
    (hl : TermPlant.LowOwn s a tw) (ht0 : t0 < tw) (hm0 : s.mem[t0]? = some m0) (hl0 : m0.loc = a)
    (hdef : m0.val ≠ .undef)
    (hok : ∀ t m, t ∉ s.promises → s.mem[t]? = some m → m.loc = a → m.val = .undef ∨ WordOK E T a.offset (mw m))
    (hul : ∀ (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → s.mem[t1]? = some m1 → s.mem[t2]? = some m2 →
      m1.loc = a → m2.loc = a → m1.val ≠ .undef → m2.val ≠ .undef) :
    ∃ w, (∀ tw', TermPlant.LowOwn s a tw' → PredAt s.mem a tw' w) ∧ WordOK E T a.offset w := by
  obtain ⟨L, mL, h0L, hLt, hmL, hlL, hnb⟩ :=
    TermStepPred.latest_below s.mem a tw (tw - t0) t0 m0 ht0 (Nat.le_refl _) hm0 hl0
  have hLnp : L ∉ s.promises := fun hp => absurd (hl.2.2 L mL hp hmL hlL) (Nat.not_le.mpr hLt)
  have hLdef : mL.val ≠ .undef := by
    rcases Nat.lt_or_eq_of_le h0L with h | h
    · exact hul t0 L m0 mL h hm0 hmL hl0 hlL hdef
    · subst h
      rw [hm0] at hmL
      cases hmL
      exact hdef
  have hw : WordOK E T a.offset (mw mL) := by
    rcases hok L mL hLnp hmL hlL with h | h
    · exact absurd h hLdef
    · exact h
  refine ⟨mw mL, fun tw' hl' => ?_, hw⟩
  rw [TermPlant.LowOwn_uniq hl' hl]
  exact ⟨L, mL, hLt, hmL, hlL, rfl, hnb⟩

#print axioms pin_wordOK

/-- **Kept items plus the zero items** (`freeWL`): credited kept items (within the credits, held
piece-lowest, every credited non-word promise among their holders) and a cover of every demanded
unit by a kept item or a `freeQW` item give `OverCrE`. -/
theorem overCr_keepZ {E : TEnv} {s : St} {f : Ts → Res} {l : AllocLabel} {c : Cell}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (Gk : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))
    (hit : ∀ x ∈ Gk, TermOverCr.CrItemQ E s f l c x) (hsum : ∀ t, TermOverCrW.sumH Gk t ≤ f t)
    (hwa : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hHL : TermOverCr.HolderLow s l Gk)
    (hcov : ∀ o tw, TermOverCr.CovU E c l o → ¬ VisU E ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw → TermPlant.OverT E s ⟨l, o⟩ tw →
      (∃ x ∈ Gk, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∨ ∃ x, TermFreeQW.FreeQW E s l c tw x)
    (hz : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      f t ≠ .zero → t ∈ Gk.map (·.1)) :
    TermOverCr.OverCrE E s f l c := by
  refine TermOwnCP.overCr_assemble hcpl hni (Gk ++ TermFreeQW.freeWL E s l c) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hit x h
    · exact TermFreeQW.freeWL_item x h
  · intro t
    rw [TermOverCrW.sumH_append, TermOverCrW.sumH_zero TermFreeQW.freeWL_zero t, Res.add_zero]
    exact hsum t
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hwa x h
    · exact TermFreeQW.freeWL_wa x h
  · exact TermOverCr.holderLow_append hHL TermFreeQW.freeWL_holder
  · intro o tw hc hv hlo hg hov
    rcases hcov o tw hc hv hlo hg hov with ⟨x, hx, r⟩ | ⟨x, hx⟩
    · exact ⟨x, List.mem_append_left _ hx, r⟩
    · obtain ⟨x', hx', r⟩ := TermFreeQW.freeWL_cover hx hlo
      exact ⟨x', List.mem_append_right _ hx', r⟩
  · intro t m ht hm hl hw hnz
    rw [List.map_append]
    exact List.mem_append_left _ (hz t m ht hm hl hw hnz)

#print axioms overCr_keepZ

/-! ## The piece-local frame of a credited item -/

section
variable {s s' : St}
  (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
  (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
  (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)

include hpre hP hsub in
/-- `LowOwn` forward at an address whose own promises all survive. -/
theorem lowOwn_fwdP {a : Address} (hk : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc = a → t ∈ s'.promises)
    {tw : Ts} (h : TermPlant.LowOwn s a tw) : TermPlant.LowOwn s' a tw := by
  obtain ⟨h1, ⟨m, hm, hl⟩, h3⟩ := h
  refine ⟨hk tw m h1 hm hl, ⟨m, by rw [hpre tw (hP tw h1)]; exact hm, hl⟩, fun t' m' ht' hm' hl' => ?_⟩
  have ht0 := hsub t' ht'
  exact h3 t' m' ht0 (by rw [← hpre t' (hP t' ht0)]; exact hm') hl'

include hpre hP hsub in
/-- `LowOwn` backward at an address whose own promises all survive. -/
theorem lowOwn_backP {a : Address} (hk : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc = a → t ∈ s'.promises)
    {tw : Ts} (h : TermPlant.LowOwn s' a tw) : TermPlant.LowOwn s a tw := by
  obtain ⟨h1, ⟨m, hm, hl⟩, h3⟩ := h
  have h1' := hsub tw h1
  refine ⟨h1', ⟨m, by rw [← hpre tw (hP tw h1')]; exact hm, hl⟩, fun t' m' ht' hm' hl' => ?_⟩
  exact h3 t' m' (hk t' m' ht' hm' hl') (by rw [hpre t' (hP t' ht')]; exact hm') hl'

theorem inAcc_lt {us : List Acc} {i o : Nat} (h : InAcc us i o) : o < nWords us :=
  Nat.lt_of_lt_of_le h.2 (TermStep.nWords_take_le _ _)

include hpre hP hsub in
/-- **A credited item is kept** along a step keeping the own promises of its piece. -/
theorem crItemQ_frameP {E E' : TEnv} {l : AllocLabel} {cr cr' : Ts → Res} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (hkP : ∀ usS, accs x.2.2.1 = some usS → ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l →
      x.2.1 ≤ m.loc.offset → m.loc.offset < x.2.1 + nWords usS → t ∈ s'.promises)
    (hstoL : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ o tw', TermPlant.LowOwn s' ⟨l, o⟩ tw' → FirstW s'.mem ⟨l, o⟩ tw' → PredU E ⟨l, o⟩ →
      PredU E' ⟨l, o⟩) (hcr : cr x.1 ≤ cr' x.1)
    (h : TermOverCr.CrItemQ E s cr l c x) : TermOverCr.CrItemQ E' s' cr' l c x := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  have hx : x.1 < s.mem.size := hP _ a3.1
  have hkA : ∀ o, x.2.1 ≤ o → o < x.2.1 + nWords usS → ∀ t m, t ∈ s.promises → s.mem[t]? = some m →
      m.loc = ⟨l, o⟩ → t ∈ s'.promises := fun o h1 h2 t m ht hm hl =>
    hkP usS a7 t m ht hm (by rw [hl]) (by rw [hl]; exact h1) (by rw [hl]; exact h2)
  have hkh : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc = mh.loc → t ∈ s'.promises := by
    intro t m ht hm hl
    have e : mh.loc = ⟨l, mh.loc.offset⟩ := by rw [← a2]
    exact hkA mh.loc.offset a8 a9 t m ht hm (hl.trans e)
  refine ⟨mh, usS, by rw [hpre _ hx]; exact a1, a2, lowOwn_fwdP hpre hP hsub hkh a3, ?_, a5, a6, a7, a8, a9, a10,
    hV _ _ _ a11, Res.le_trans a12 hcr, ?_⟩
  · intro hw; apply a4
    have e : E'.sto mh.loc.label = E.sto mh.loc.label := by rw [a2]; exact hstoL
    exact (WordUnit_congr e).1 hw
  · intro i o w tw' hK hIn hw hlo
    have hkU := hkA (x.2.1 + o) (Nat.le_add_right _ _) (Nat.add_lt_add_left (inAcc_lt hIn) _)
    have hlo0 := lowOwn_backP hpre hP hsub hkU hlo
    have htw : tw' < s.mem.size := hP _ hlo0.1
    rcases a13 i o w tw' hK hIn hw hlo0 with hp | ⟨hu, hf, m, hm, hmw⟩
    · exact .inl (TermPlant.PredAt_mono htw hpre hp)
    · have hf' := TermOwnCF.firstW_fwd hpre htw hf
      exact .inr ⟨hPU _ _ hlo hf' hu, hf', m, by rw [hpre _ htw]; exact hm, hmw⟩

end

#print axioms crItemQ_frameP

/-! ## The owner's cover across an RMW fulfilment at a one-unit piece (R5) -/

/-- Inside an item's piece meeting the RMW unit `o`, every word is `o`. -/
theorem piece_at_rmw {E E' : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} {o p : Nat}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} {usS : List Acc}
    (hR : RmwAtomC E' ⟨l, o⟩) (hsto : E'.sto l = some c) (hx : TermOverCr.CrItemQ E s cr l c x)
    (hus : accs x.2.2.1 = some usS) (h1 : x.2.1 ≤ o) (h2 : o < x.2.1 + nWords usS)
    (h3 : x.2.1 ≤ p) (h4 : p < x.2.1 + nWords usS) : p = o := by
  obtain ⟨c', S, hsto', hat, hS, hsol, -, -⟩ := hR
  simp only at hsto' hat
  rw [hsto] at hsto'
  cases hsto'
  obtain ⟨mh, usS', -, -, -, -, a5, a6, -⟩ := hx
  have hP : TermPiece.Piece c.ty x.2.1 x.2.2.1 :=
    ⟨a5, a6, by rw [wc_of_accs hus]; simp only [ne_eq, Option.some.injEq]; omega⟩
  obtain ⟨e1, e2⟩ := piece_one hP hus h1 h2 hat hS TermForWU.nWords_one hsol
  omega

/-- **The owner's cover across a `fetch`/`cas` fulfilment** of its lowest own promise `th0` at a
closed copyable one-word unit `⟨l, o⟩` off word units: the items not held at `th0` are kept
(their pieces avoid `o`), and a `freeQW` zero item covers the new lowest own promise at `o`, pinned
at `th0`'s (defined, hence typed) word. -/
theorem overCr_rmw {E E' : TEnv} {s s' : St} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell} {o : Nat}
    {th0 : Ts} {m0 : Msg}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
    (hkeep : ∀ t, t ∈ s.promises → t ≠ th0 → t ∈ s'.promises)
    (hth0 : th0 ∉ s'.promises) (hlo0 : TermPlant.LowOwn s ⟨l, o⟩ th0)
    (hm0 : s'.mem[th0]? = some m0) (hdef : m0.val ≠ .undef)
    (hR : RmwAtomC E' ⟨l, o⟩) (hsto : E'.sto l = some c) (hnw : ¬ WordUnit E' ⟨l, o⟩)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hstoL : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ o tw', TermPlant.LowOwn s' ⟨l, o⟩ tw' → FirstW s'.mem ⟨l, o⟩ tw' → PredU E ⟨l, o⟩ →
      PredU E' ⟨l, o⟩)
    (hCov : ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o)
    (hVis : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hG : ∀ o' tw, o' ≠ o → TermPlant.LowOwn s ⟨l, o'⟩ tw → TermOverCr.WinG E' s' l o' tw →
      TermOverCr.WinG E s l o' tw)
    (hOT : ∀ o' tw, o' ≠ o → TermPlant.LowOwn s ⟨l, o'⟩ tw → TermPlant.OverT E' s' ⟨l, o'⟩ tw →
      TermPlant.OverT E s ⟨l, o'⟩ tw)
    (hcr : ∀ t, t ∈ s'.promises → cr t ≤ cr' t)
    (hz : ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m → m.loc.label = l → cr' t ≠ .zero → cr t ≠ .zero)
    (hok : ∀ t m, t ∉ s'.promises → s'.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      m.val = .undef ∨ WordOK E' c.ty o (mw m))
    (hul : ∀ (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → s'.mem[t1]? = some m1 → s'.mem[t2]? = some m2 →
      m1.loc = ⟨l, o⟩ → m2.loc = ⟨l, o⟩ → m1.val ≠ .undef → m2.val ≠ .undef)
    (hpreC : TermOverCr.OverCrE E s cr l c) : TermOverCr.OverCrE E' s' cr' l c := by
  obtain ⟨Gs, ⟨h1, h2, h3, h4, h5⟩, hHL⟩ := hpreC
  obtain ⟨mt, hmt, hlt⟩ := hlo0.2.1
  have hm0s : s.mem[th0]? = some m0 := by rw [← hpre th0 (hP th0 hlo0.1)]; exact hm0
  have emt : mt = m0 := Option.some.inj (hmt.symm.trans hm0s)
  have hl0 : m0.loc = ⟨l, o⟩ := emt ▸ hlt
  -- an item held at `th0` has its piece over `o`
  have hhold : ∀ x ∈ Gs, x.1 = th0 → ∀ usS, accs x.2.2.1 = some usS → x.2.1 ≤ o ∧ o < x.2.1 + nWords usS := by
    intro x hx e usS hus
    obtain ⟨mh, usS', a1, -, -, -, -, -, a7, a8, a9, -⟩ := h2 x hx
    rw [hus] at a7
    cases a7
    rw [e, hm0s] at a1
    have emh : m0 = mh := Option.some.inj a1
    subst emh
    rw [hl0] at a8 a9
    exact ⟨a8, a9⟩
  -- an item whose piece meets `o` is held at `th0`
  have hone : ∀ x ∈ Gs, ∀ usS, accs x.2.2.1 = some usS → x.2.1 ≤ o → o < x.2.1 + nWords usS → x.1 = th0 := by
    intro x hx usS hus b1 b2
    obtain ⟨mh, usS', a1, a2, a3, -, -, -, a7, a8, a9, -⟩ := h2 x hx
    rw [hus] at a7
    cases a7
    have hoff : mh.loc.offset = o := piece_at_rmw hR hsto (h2 x hx) hus b1 b2 a8 a9
    have e : mh.loc = ⟨l, o⟩ := by rw [← hoff, ← a2]
    rw [e] at a3
    exact TermPlant.LowOwn_uniq a3 hlo0
  let Gk := Gs.filter (fun x => decide (x.1 ≠ th0))
  have hmemK : ∀ x, x ∈ Gk ↔ x ∈ Gs ∧ x.1 ≠ th0 := fun x => by
    simp only [Gk, List.mem_filter, decide_eq_true_eq]
  -- the own promises of a kept item's piece survive
  have hkP : ∀ x ∈ Gk, ∀ usS, accs x.2.2.1 = some usS → ∀ t m, t ∈ s.promises → s.mem[t]? = some m →
      m.loc.label = l → x.2.1 ≤ m.loc.offset → m.loc.offset < x.2.1 + nWords usS → t ∈ s'.promises := by
    intro x hx usS hus t m ht hm hl b1 b2
    obtain ⟨hxG, hxn⟩ := (hmemK x).1 hx
    by_cases e : t = th0
    · subst e
      have em : m0 = m := Option.some.inj (hm0s.symm.trans hm)
      subst em
      rw [hl0] at b1 b2
      exact absurd (hone x hxG usS hus b1 b2) hxn
    · exact hkeep t ht e
  have hkU : ∀ x ∈ Gk, ∀ usS i o2, accs x.2.2.1 = some usS → InAcc usS i o2 → ∀ t m, t ∈ s.promises →
      s.mem[t]? = some m → m.loc = ⟨l, x.2.1 + o2⟩ → t ∈ s'.promises := by
    intro x hx usS i o2 hus hi t m ht hm hl
    exact hkP x hx usS hus t m ht hm (by rw [hl]) (by rw [hl]; exact Nat.le_add_right _ _)
      (by rw [hl]; exact Nat.add_lt_add_left (inAcc_lt hi) _)
  have hkO : ∀ o', o' ≠ o → ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc = ⟨l, o'⟩ →
      t ∈ s'.promises := by
    intro o' ho t m ht hm hl
    by_cases e : t = th0
    · subst e
      have em : m0 = m := Option.some.inj (hm0s.symm.trans hm)
      subst em
      exact absurd (congrArg Address.offset (hl.symm.trans hl0)) ho
    · exact hkeep t ht e
  refine overCr_keepZ hcpl hni Gk ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact crItemQ_frameP hpre hP hsub (hkP x hx) hstoL hV hPU
      (hcr x.1 (hkeep x.1 (by obtain ⟨_, _, _, _, a3, -⟩ := h2 x ((hmemK x).1 hx).1; exact a3.1)
        ((hmemK x).1 hx).2)) (h2 x ((hmemK x).1 hx).1)
  · refine TermOverCrW.sumH_le_of_nodup (List.Nodup.sublist ((List.filter_sublist (p := fun x : Ts × Nat × Ty × List Word × Res × (Nat → Bool) => decide (x.1 ≠ th0)) (l := Gs)).map _) h1) ?_
    intro x hx
    obtain ⟨hxG, hxn⟩ := (hmemK x).1 hx
    obtain ⟨_, _, _, _, a3, -, -, -, -, -, -, -, -, a12, -⟩ := h2 x hxG
    exact Res.le_trans a12 (hcr x.1 (hkeep x.1 a3.1 hxn))
  · intro x hx usS i o2 hus hk hi
    obtain ⟨t0, ht0⟩ := h4 x ((hmemK x).1 hx).1 usS i o2 hus hk hi
    exact ⟨t0, lowOwn_fwdP hpre hP hsub (hkU x hx usS i o2 hus hi) ht0⟩
  · intro x hx usS hus t m ht hm hl b1 b2
    have ht0 := hsub t ht
    exact hHL x ((hmemK x).1 hx).1 usS hus t m ht0 (by rw [← hpre t (hP t ht0)]; exact hm) hl b1 b2
  · intro o' tw hc hv hlo hg hov
    by_cases ho : o' = o
    · subst ho
      right
      obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := id hlo
      have htw0 := hsub tw htw
      have hmws : s.mem[tw]? = some mw := by rw [← hpre tw (hP tw htw0)]; exact hmw
      have hle : th0 ≤ tw := hlo0.2.2 tw mw htw0 hmws hml
      have hne : th0 ≠ tw := fun e => hth0 (e ▸ htw)
      obtain ⟨w, hpin, hokw⟩ := pin_wordOK hlo (Nat.lt_of_le_of_ne hle hne) hm0 hl0 hdef hok hul
      exact freeQW_rmw hR hsto hlo hnw hpin hokw
    · left
      have hloB := lowOwn_backP hpre hP hsub (hkO o' ho) hlo
      obtain ⟨x, hx, usS, i, b1, b2, b3, b4⟩ :=
        h3 o' tw (hCov o' hc) (hVis o' hv) hloB (hG o' tw ho hloB hg) (hOT o' tw ho hloB hov)
      have hxn : x.1 ≠ th0 := by
        intro e
        obtain ⟨c1, c2⟩ := hhold x hx e usS b1
        have hlt' : o' < x.2.1 + nWords usS := by
          have := inAcc_lt b3
          omega
        exact ho (piece_at_rmw hR hsto (h2 x hx) b1 c1 c2 b2 hlt')
      exact ⟨x, (hmemK x).2 ⟨hx, hxn⟩, usS, i, b1, b2, b3, b4⟩
  · intro t m ht hm hl hw hnz
    have ht0 := hsub t ht
    have hms : s.mem[t]? = some m := by rw [← hpre t (hP t ht0)]; exact hm
    have hw0 : ¬ WordUnit E m.loc := fun hw' => hw (by
      have e : E'.sto m.loc.label = E.sto m.loc.label := by rw [hl]; exact hstoL
      exact (WordUnit_congr e).2 hw')
    obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (h5 t m ht0 hms hl hw0 (hz t m ht hm hl hnz))
    have hxn : x.1 ≠ th0 := fun e => hth0 (e ▸ hx1 ▸ ht)
    exact List.mem_map.2 ⟨x, (hmemK x).2 ⟨hx, hxn⟩, hx1⟩

#print axioms overCr_rmw

end TermOwnCR5
