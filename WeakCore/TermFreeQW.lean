import WeakCore.TermOverCrWb
import WeakCore.TermA4P

/-!
# TermFreeQW: piece-level free items (PubShape lost-fp units)

The typing core of `freeQW`: a typed word at word `o` of a cell gives a resource-free value of any
solid, copyable piece `U` around `o` holding that word at its place.
-/

namespace TermFreeQW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper TermOverCrW
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem wle_set : ∀ {ws : List Word} {i : Nat} {w0 w : Word}, ws[i]? = some w0 → WLe1 w0 w →
    WLe ws (ws.set i w)
  | [], _, _, _, h, _ => by simp at h
  | a :: l, 0, w0, w, h, hle => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨hle, wle_refl l⟩
  | a :: l, i + 1, w0, w, h, hle => by
      simp only [List.getElem?_cons_succ] at h
      exact ⟨WLe1_refl a, wle_set h hle⟩
where
  wle_refl : ∀ (l : List Word), WLe l l
    | [] => trivial
    | a :: l => ⟨WLe1_refl a, wle_refl l⟩

/-- **A typed word fills a resource-free piece value.**  At a solid, copyable piece `U` (at word
`b`) around a typed word `o`, some resource-free value of `U` holds that word at its place. -/
theorem valOfR_zero_fill {E : TEnv} {T : Ty} {o b : Nat} {w : Word} {U : Ty} {us : List Acc}
    (h : WordOK E T o w) (hP : AtOff T b U) (hsol : Solid U) (hU : accs U = some us)
    (hb : b ≤ o) (ho : o < b + nWords us)
    (hcl : tb 0 U = true) (ha : Ty.affine U = false) :
    ∃ ws, ws.length = nWords us ∧ ws[o - b]? = some w ∧ ValOfR E U ws .zero := by
  obtain ⟨bs, S, ws, o', w0, hseg, ⟨⟨hvr, hvd⟩, hsh⟩, hw0, hle, hbo⟩ := h
  have hlt0 : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  obtain ⟨q, hatS, usS, hS, hq⟩ : ∃ q, AtOff S q U ∧ ∃ us0, accs S = some us0 ∧ q + (o - b) = o' := by
    rcases hseg with ⟨rfl, rfl, hT⟩ | ⟨N, us0, j, rfl, hus, hj, rfl⟩
    · obtain ⟨us0, hus0⟩ := Option.ne_none_iff_exists'.1 hT
      exact ⟨b, hP, us0, hus0, by omega⟩
    · rcases AtOff_arr_elem hP rfl with h | ⟨us', j', o'', hus', hj', hbe, hat⟩
      · exact absurd h (hsol.2.1 _ _)
      · rw [hus] at hus'
        cases hus'
        have hlt1 : o' < nWords us0 := hsh us0 hus ▸ hlt0
        have hlt2 : o'' + nWords us ≤ nWords us0 := AtOff_bound hat hus hU
        have e : o' + j * nWords us0 = (o'' + (o - b)) + j' * nWords us0 := by omega
        have e2 := congrArg (· % nWords us0) e
        have hlt3 : o'' + (o - b) < nWords us0 := by omega
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt3] at e2
        exact ⟨o'', hat, us0, hus, e2.symm⟩
  obtain ⟨nn, hwcU, hfit, hvrU, hvdU⟩ :=
    VR_at E.unsee hatS hvr hvd (by simp [wc, hS, hsh usS hS])
  have hnn : nn = nWords us := by
    have h1 : wc U = some (nWords us) := wc_of_accs hU
    rw [h1] at hwcU
    exact (Option.some.inj hwcU).symm
  subst hnn
  have hlen : ((ws.drop q).take (nWords us)).length = nWords us := by
    simp only [List.length_take, List.length_drop]; omega
  have hat0 : ((ws.drop q).take (nWords us))[o - b]? = some w0 := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, hq]
    exact hw0
  refine ⟨((ws.drop q).take (nWords us)).set (o - b) w, by rw [List.length_set]; exact hlen,
    List.getElem?_set_self (by rw [hlen]; omega), ?_⟩
  exact ValOfR_up (wle_set hat0 hle) ⟨VR_VRR_copy_closed hcl ha hvrU, hvdU⟩

#print axioms valOfR_zero_fill

/-- The unit mask of a single unit: the units holding word `o'` of the piece. -/
noncomputable def unitK (us : List Acc) (o' : Nat) (i : Nat) : Bool := by
  classical
  exact decide (InAcc us i o')

theorem unitK_spec {us : List Acc} {o' i : Nat} (h : unitK us o' i = true) : InAcc us i o' := by
  classical
  unfold unitK at h
  exact of_decide_eq_true h

theorem unitK_of {us : List Acc} {o' i : Nat} (h : InAcc us i o') : unitK us o' i = true := by
  classical
  unfold unitK
  exact decide_eq_true h

/-- **The piece-level free item, general pin**: held by the piece-lowest own promise `t0`, a
resource-free value `ws` of the piece `U` at word `b`, masked at the single unit of word `o`, whose word
`w` there meets `CrItemQ`'s pin (either arm) at every lowest own promise of the unit.  `freeQW`'s item
(`crItemQ_freeQW`) is the `PredAt` arm; `TermFgnNew.crItemQ_freeFW` the predicted-unit arm. -/
theorem crItemQ_freeG {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} {b o : Nat}
    {U : Ty} {us : List Acc} {t0 : Ts} {mh : Msg} {w : Word} {ws : List Word}
    (hmh : s.mem[t0]? = some mh) (hml : mh.loc.label = l) (hlo0 : TermPlant.LowOwn s mh.loc t0)
    (hnw0 : ¬ WordUnit E mh.loc) (hb0 : b ≤ mh.loc.offset) (ho0 : mh.loc.offset < b + nWords us)
    (hat : AtOff c.ty b U) (hsol : Solid U) (hU : accs U = some us) (hb : b ≤ o)
    (hsing : ∀ i o2, InAcc us i (o - b) → InAcc us i o2 → o2 = o - b)
    (hpin : ∀ tw, TermPlant.LowOwn s ⟨l, o⟩ tw → PredAt s.mem ⟨l, o⟩ tw w ∨
      (PredU E ⟨l, o⟩ ∧ FirstW s.mem ⟨l, o⟩ tw ∧ ∃ m, s.mem[tw]? = some m ∧ mw m = w))
    (hlen : ws.length = nWords us) (hwo : ws[o - b]? = some w) (hv : ValOfR E U ws .zero) :
    TermOverCr.CrItemQ E s cr l c (t0, b, U, ws, .zero, unitK us (o - b)) := by
  refine ⟨mh, us, hmh, hml, hlo0, hnw0, hat, hsol, hU, hb0, ho0, hlen, hv, Res.zero_le _,
    fun i o2 w2 tw2 hk hio hw2 hl2 => ?_⟩
  have e2 : o2 = o - b := hsing i o2 (unitK_spec hk) hio
  subst e2
  have eo : b + (o - b) = o := by omega
  have hw' : w2 = w := Option.some.inj (hw2.symm.trans hwo)
  subst hw'
  rw [eo] at hl2 ⊢
  exact hpin tw2 hl2

#print axioms crItemQ_freeG

/-- **The piece-level free item** (`freeQW`): held by the piece-lowest own promise `t0`, a
resource-free value `ws` of the solid, copyable piece `U` at word `b`, pinned at the single unit of
word `o` to the word before the unit's lowest own promise (`crItemQ_freeG`, `PredAt` arm). -/
theorem crItemQ_freeQW {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} {b o : Nat}
    {U : Ty} {us : List Acc} {t0 : Ts} {mh : Msg} {w : Word} {ws : List Word}
    (hmh : s.mem[t0]? = some mh) (hml : mh.loc.label = l) (hlo0 : TermPlant.LowOwn s mh.loc t0)
    (hnw0 : ¬ WordUnit E mh.loc) (hb0 : b ≤ mh.loc.offset) (ho0 : mh.loc.offset < b + nWords us)
    (hat : AtOff c.ty b U) (hsol : Solid U) (hU : accs U = some us) (hb : b ≤ o)
    (hsing : ∀ i o2, InAcc us i (o - b) → InAcc us i o2 → o2 = o - b)
    (hpin : ∀ tw, TermPlant.LowOwn s ⟨l, o⟩ tw → PredAt s.mem ⟨l, o⟩ tw w)
    (hlen : ws.length = nWords us) (hwo : ws[o - b]? = some w) (hv : ValOfR E U ws .zero) :
    TermOverCr.CrItemQ E s cr l c (t0, b, U, ws, .zero, unitK us (o - b)) :=
  crItemQ_freeG hmh hml hlo0 hnw0 hb0 ho0 hat hsol hU hb hsing (fun tw hl => .inl (hpin tw hl)) hlen hwo hv

#print axioms crItemQ_freeQW

/-- The `freeQW` item covers word `o`. -/
theorem freeQW_cover {b o : Nat} {us : List Acc} (hb : b ≤ o) (ho : o < b + nWords us) :
    ∃ i, InAcc us i (o - b) ∧ unitK us (o - b) i = true := by
  obtain ⟨i, hi⟩ := TermPlant.inAcc_ex us (o - b) (by omega)
  exact ⟨i, hi, unitK_of hi⟩

/-- The `freeQW` item's masked words have a lowest own promise (`hFwa`). -/
theorem freeQW_wa {s : St} {l : AllocLabel} {b o : Nat} {us : List Acc} {tw : Ts} (hb : b ≤ o)
    (hsing : ∀ i o2, InAcc us i (o - b) → InAcc us i o2 → o2 = o - b)
    (hlo : TermPlant.LowOwn s ⟨l, o⟩ tw) :
    ∀ i o2, unitK us (o - b) i = true → InAcc us i o2 → ∃ t1, TermPlant.LowOwn s ⟨l, b + o2⟩ t1 := by
  intro i o2 hk hio
  have e2 : o2 = o - b := hsing i o2 (unitK_spec hk) hio
  subst e2
  have eo : b + (o - b) = o := by omega
  rw [eo]
  exact ⟨tw, hlo⟩

#print axioms freeQW_wa

/-- **No word unit in a solid piece around a non-word unit.** -/
theorem noWU_piece {E : TEnv} {l : AllocLabel} {c : Cell} {b o x : Nat} {S : Ty} {us : List Acc}
    (hsto : E.sto l = some c) (hP : TermPiece.Piece c.ty b S) (hus : accs S = some us)
    (hb : b ≤ o) (ho : o < b + nWords us) (hbx : b ≤ x) (hox : x < b + nWords us)
    (hnw : ¬ WordUnit E ⟨l, o⟩) : ¬ WordUnit E ⟨l, x⟩ := by
  rintro ⟨c', hc', hW⟩
  rw [hsto] at hc'
  cases hc'
  have hwS : wc S = some (nWords us) := wc_of_accs hus
  rcases hW with ⟨r, P, hg, hat⟩ | ⟨r, P, hat⟩ | ⟨r, P, h1, hat⟩
  · have hu1 : accs (Ty.word r P) = some [Acc.one] := by simp [accs, hg]
    have hPw : TermPiece.Piece c.ty x (.word r P) := ⟨hat, Solid_word r P, by rw [wc_of_accs hu1]; decide⟩
    obtain ⟨e1, e2⟩ := TermPiece.piece_match hP hPw hwS (wc_of_accs hu1) hbx hox (Nat.le_refl x)
      (by show x < x + nWords [Acc.one]; simp [nWords, Acc.size])
    subst e1 e2
    rw [hu1] at hus
    cases hus
    have e : o = b := by simp [nWords, Acc.size] at ho; omega
    subst e
    exact hnw ⟨c, hsto, .inl ⟨r, P, hg, hat⟩⟩
  · have hw2 : wc (Ty.word2 r P) = some 2 := by simp [wc, accs, nWords, Acc.size]
    have hPw : TermPiece.Piece c.ty x (.word2 r P) := ⟨hat, Solid_word2 r P, by rw [hw2]; decide⟩
    obtain ⟨e1, e2⟩ := TermPiece.piece_match hP hPw hwS hw2 hbx hox (Nat.le_refl x) (by omega)
    subst e1 e2
    have hn : nWords us = 2 := Option.some.inj (hwS.symm.trans hw2)
    rcases Nat.lt_or_ge o (b + 1) with h | h
    · have e : o = b := by omega
      subst e
      exact hnw ⟨c, hsto, .inr (.inl ⟨r, P, hat⟩)⟩
    · have e : o = b + 1 := by omega
      subst e
      exact hnw ⟨c, hsto, .inr (.inr ⟨r, P, show 1 ≤ b + 1 by omega,
        show AtOff c.ty (b + 1 - 1) _ by rw [Nat.add_sub_cancel]; exact hat⟩)⟩
  · have hw2 : wc (Ty.word2 r P) = some 2 := by simp [wc, accs, nWords, Acc.size]
    have hPw : TermPiece.Piece c.ty (x - 1) (.word2 r P) := ⟨hat, Solid_word2 r P, by rw [hw2]; decide⟩
    obtain ⟨e1, e2⟩ := TermPiece.piece_match hP hPw hwS hw2 hbx hox (by omega) (by omega)
    subst e2
    have hn : nWords us = 2 := Option.some.inj (hwS.symm.trans hw2)
    rcases Nat.lt_or_ge o (b + 1) with h | h
    · have e : o = b := by omega
      subst e
      exact hnw ⟨c, hsto, .inr (.inl ⟨r, P, show AtOff c.ty o _ by rw [e1]; exact hat⟩)⟩
    · have e : o = b + 1 := by omega
      subst e
      exact hnw ⟨c, hsto, .inr (.inr ⟨r, P, show 1 ≤ b + 1 by omega,
        show AtOff c.ty (b + 1 - 1) _ by rw [Nat.add_sub_cancel, e1]; exact hat⟩)⟩

#print axioms noWU_piece

/-- A `freeQW` item for the own promise `tw` (lowest at its unit `o`): covering `o`, pinned
there, resource-free, held piece-lowest. -/
def FreeQW (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) (tw : Ts)
    (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) : Prop :=
  ∃ o us, TermPlant.LowOwn s ⟨l, o⟩ tw ∧ accs x.2.2.1 = some us ∧ x.2.1 ≤ o ∧ o < x.2.1 + nWords us ∧
    x.2.2.2.2.2 = unitK us (o - x.2.1) ∧ x.2.2.2.2.1 = .zero ∧
    (∀ cr, TermOverCr.CrItemQ E s cr l c x) ∧ TermOverCr.HolderLow s l [x] ∧
    (∀ i o2, InAcc us i (o - x.2.1) → InAcc us i o2 → o2 = o - x.2.1)

open Classical in
noncomputable def freeWIt (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) (tw : Ts) :
    Ts × Nat × Ty × List Word × Res × (Nat → Bool) :=
  if h : ∃ x, FreeQW E s l c tw x then Classical.choose h else (tw, 0, .unit, [], .zero, fun _ => true)

open Classical in
/-- **The piece-level free items**: one per own promise with one. -/
noncomputable def freeWL (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) :
    List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :=
  (s.promises.filter (fun tw => decide (∃ x, FreeQW E s l c tw x))).map (freeWIt E s l c)

theorem freeWIt_spec {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {tw : Ts} (h : ∃ x, FreeQW E s l c tw x) :
    FreeQW E s l c tw (freeWIt E s l c tw) := by
  classical
  unfold freeWIt
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

theorem mem_freeWL {E : TEnv} {s : St} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hx : x ∈ freeWL E s l c) :
    ∃ tw, FreeQW E s l c tw x := by
  classical
  unfold freeWL at hx
  obtain ⟨tw, htw, rfl⟩ := List.mem_map.1 hx
  exact ⟨tw, freeWIt_spec (of_decide_eq_true (List.mem_filter.1 htw).2)⟩

theorem freeWL_item {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} :
    ∀ x ∈ freeWL E s l c, TermOverCr.CrItemQ E s cr l c x := fun x hx => by
  obtain ⟨tw, o, us, -, -, -, -, -, -, hi, -⟩ := mem_freeWL hx
  exact hi cr

theorem freeWL_zero {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} :
    ∀ x ∈ freeWL E s l c, x.2.2.2.2.1 = .zero := fun x hx => by
  obtain ⟨tw, o, us, -, -, -, -, -, hz, -⟩ := mem_freeWL hx
  exact hz

theorem freeWL_holder {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} :
    TermOverCr.HolderLow s l (freeWL E s l c) := fun x hx => by
  obtain ⟨tw, o, us, -, -, -, -, -, -, -, hH, -⟩ := mem_freeWL hx
  exact hH x (List.mem_singleton_self x)

theorem freeWL_wa {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} :
    ∀ x ∈ freeWL E s l c, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0 := by
  intro x hx usS i o2 hus hk hio
  obtain ⟨tw, o, us, hlo, hus', hb, -, hK, -, -, -, hsing⟩ := mem_freeWL hx
  rw [hus] at hus'
  cases hus'
  rw [hK] at hk
  exact freeQW_wa hb hsing hlo i o2 hk hio

/-- **Coverage**: a `freeQW` item for `tw` puts an item of `freeWL` over `tw`'s unit. -/
theorem freeWL_cover {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o : Nat} {tw : Ts}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hx : FreeQW E s l c tw x)
    (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) :
    ∃ x ∈ freeWL E s l c, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
      x.2.2.2.2.2 i = true := by
  classical
  have hex : ∃ x, FreeQW E s l c tw x := ⟨x, hx⟩
  have hmem : freeWIt E s l c tw ∈ freeWL E s l c :=
    List.mem_map.2 ⟨tw, List.mem_filter.2 ⟨hl.1, decide_eq_true hex⟩, rfl⟩
  obtain ⟨o', us, hlo', hus, hb, ho, hK, -⟩ := freeWIt_spec hex
  have eo : o' = o := by
    obtain ⟨m1, hm1, hl1⟩ := hl.2.1
    obtain ⟨m2, hm2, hl2⟩ := hlo'.2.1
    rw [hm1] at hm2
    cases hm2
    have := congrArg Address.offset (hl2.symm.trans hl1)
    exact this
  subst eo
  obtain ⟨i, hi, hk⟩ := freeQW_cover (us := us) hb ho
  exact ⟨_, hmem, us, i, hus, hb, hi, by rw [hK]; exact hk⟩

#print axioms freeWL_cover

/-- **A `freeQW` item exists** at an own promise's unit `o` in a solid, copyable piece `U` (at word
`b`) of a non-word unit, `o` its unit's only word, pinned at a typed word. -/
theorem freeQW_exists {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o b : Nat} {U : Ty}
    {us : List Acc} {tw : Ts} {w : Word}
    (hsto : E.sto l = some c) (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) (hP : TermPiece.Piece c.ty b U)
    (hU : accs U = some us) (hb : b ≤ o) (ho : o < b + nWords us)
    (hsing : ∀ i o2, InAcc us i (o - b) → InAcc us i o2 → o2 = o - b)
    (hcl : tb 0 U = true) (ha : Ty.affine U = false) (hnw : ¬ WordUnit E ⟨l, o⟩)
    (hpin : ∀ tw', TermPlant.LowOwn s ⟨l, o⟩ tw' → PredAt s.mem ⟨l, o⟩ tw' w)
    (hok : WordOK E c.ty o w) :
    ∃ x, FreeQW E s l c tw x := by
  obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := id hl
  obtain ⟨t0, m0, ht0, hm0, hl0, hb0, ho0, -, hmin⟩ := lowest_in_piece (l := l) htw hmw (by rw [hml])
    (by rw [hml]; exact hb) (by rw [hml]; exact ho)
  have hlo0 : TermPlant.LowOwn s m0.loc t0 := ⟨ht0, ⟨m0, hm0, rfl⟩, fun t' m' h1 h2 h3 =>
    hmin t' m' h1 h2 (by rw [h3]; exact hl0) (by rw [h3]; exact hb0) (by rw [h3]; exact ho0)⟩
  have hnw0 : ¬ WordUnit E m0.loc := by
    have e : m0.loc = ⟨l, m0.loc.offset⟩ := by rw [← hl0]
    rw [e]
    exact noWU_piece hsto hP hU hb ho hb0 ho0 hnw
  have hml0 : m0.loc.label = l := hl0
  obtain ⟨ws, hlen, hwo, hv⟩ := valOfR_zero_fill hok hP.1 hP.2.1 hU hb ho hcl ha
  refine ⟨(t0, b, U, ws, .zero, unitK us (o - b)), o, us, hl, hU, hb, ho, rfl, rfl,
    fun cr => crItemQ_freeQW hm0 hml0 hlo0 hnw0 hb0 ho0 hP.1 hP.2.1 hU hb hsing hpin hlen hwo hv, ?_, hsing⟩
  · intro x hx usS hus t m ht hm hlab h1 h2
    rw [List.mem_singleton] at hx
    subst hx
    rw [hU] at hus
    cases hus
    exact hmin t m ht hm hlab h1 h2

#print axioms freeQW_exists

/-- `winG_or_lost`, the lost promise below the bound. -/
theorem winG_or_lost2 {E E' : TEnv} {s s' : St} {l : AllocLabel} {o : Nat} {tw : Ts}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hvs : s'.vs = s.vs) (hfpf : ∀ t, t ∈ E.fp → t ∉ s.promises)
    (hV : Vis E l) (hV' : Vis E' l)
    (h : TermOverCr.WinG E' s' l o tw) :
    TermOverCr.WinG E s l o tw ∨ ∃ t m, s'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ t ≤ tw ∧
      (t ∈ E.fp ∧ t ∉ E'.fp ∧ t ∉ s.promises ∧ s.mem[t]? = some m) := by
  by_cases hk : ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≤ tw →
      t ∈ FpAt E' ⟨l, 0⟩
  · exact .inl (winG_backK hpre hpr hvs hk h)
  · refine .inr ((Classical.em _).elim id fun hn => False.elim <| hk fun t m ht hm hl hle => ?_)
    have e1 : FpAt E ⟨l, 0⟩ = E.fp := by unfold FpAt; simp only [hV, ↓reduceIte]
    have e2 : FpAt E' ⟨l, 0⟩ = E'.fp := by unfold FpAt; simp only [hV', ↓reduceIte]
    rw [e1] at ht
    rw [e2]
    have hlt : t < s.mem.size := (Array.getElem?_eq_some_iff.1 hm).1
    exact (Classical.em _).elim id fun ht' => False.elim <|
      hn ⟨t, m, by rw [hpre t hlt]; exact hm, hl, hle, ht, ht', hfpf t ht, hm⟩

#print axioms winG_or_lost2

/-- `hent_ofCO` with the pre-step window given at the unit. -/
theorem hent_ofCOW {E E' Ek : TEnv} {s s' sk : St} {l : AllocLabel} {c ck : Cell} {lt ot n : Nat}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {L0 : Nat → Bool}
    (hmemk : sk.mem = s.mem)
    (hfoot : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset)
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hleft : ∀ o, ¬ VisU E' ⟨l, o⟩ → ∀ t m, t < s.mem.size → s.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      t ∈ PromAt E s ⟨l, o⟩ →
      t ∉ PromAt E' s' ⟨l, o⟩ → lt = l ∧ ot ≤ o ∧ ot + n > o)
    (hcov : ∀ (c : Cell) (b : Nat) (S : Ty) (vs : List Acc) (t : Ts) (m : Msg), Ek.sto lt = some c →
      c.owner ≠ some Ek.tid → TermPiece.Piece c.ty b S → accs S = some vs → t ∈ Ek.fp → sk.mem[t]? = some m →
      m.loc.label = lt → b ≤ m.loc.offset → b + nWords vs > m.loc.offset → ot ≤ m.loc.offset →
      ot + n > m.loc.offset → L0 (m.loc.offset - ot) = true → ∃ g ∈ Gd, g.l = lt ∧ g.b = b ∧ g.S = S)
    (hstok : Ek.sto l = some ck) (hty : ck.ty = c.ty) (hownk : ck.owner ≠ some Ek.tid)
    (hfp : ∀ t, t ∈ s.promises → t ∈ Ek.fp)
    (hpiece : ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → ∃ b S us, TermPiece.Piece c.ty b S ∧ accs S = some us ∧
      b ≤ o ∧ o < b + nWords us)
    (hsing : ∀ o tw b S us i, TermPlant.LowOwn s ⟨l, o⟩ tw → TermPiece.Piece c.ty b S → accs S = some us →
      b ≤ o → InAcc us i (o - b) → ∀ o', InAcc us i o' → o' = o - b)
    (hL : lt = l → ∀ o tw, ot ≤ o → ot + n > o → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ¬ TermPlant.OverT E s ⟨l, o⟩ tw → ∀ g ∈ Gd, g.l = l → g.b ≤ o → g.L (o - g.b) = true)
    (hL0 : lt = l → ∀ o tw, ot ≤ o → ot + n > o → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ¬ TermPlant.OverT E s ⟨l, o⟩ tw → L0 (o - ot) = true)
    (htg : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E s l o tw →
      ¬ VisU E' ⟨l, o⟩ → ∀ us, accs g.S = some us →
      g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t) :
    ∀ o tw, ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw → TermOverCr.WinG E s l o tw →
      (∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) ∧
        TermOverCr.WinG E s l o tw := by
  intro o tw hv' hl hov hno hw
  exact ⟨hent_ofG (Gw := TermOverCr.WinG E s l) hmemk hfoot hpre hleft hcov hstok hty hownk hfp hpiece hsing hL hL0 htg o tw hv' hl hov hno hw, hw⟩

#print axioms hent_ofCOW

/-- (copy of `valOfR_zero_fill` at `FreeP`) A typed word fills a resource-free `FreeP` piece value. -/
theorem valOfR_zero_fillP {E : TEnv} {T : Ty} {o b : Nat} {w : Word} {U : Ty} {us : List Acc}
    (h : WordOK E T o w) (hP : AtOff T b U) (hsol : Solid U) (hU : accs U = some us)
    (hb : b ≤ o) (ho : o < b + nWords us)
    (hF : TermA4.FreeP U) :
    ∃ ws, ws.length = nWords us ∧ ws[o - b]? = some w ∧ ValOfR E U ws .zero := by
  obtain ⟨bs, S, ws, o', w0, hseg, ⟨⟨hvr, hvd⟩, hsh⟩, hw0, hle, hbo⟩ := h
  have hlt0 : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  obtain ⟨q, hatS, usS, hS, hq⟩ : ∃ q, AtOff S q U ∧ ∃ us0, accs S = some us0 ∧ q + (o - b) = o' := by
    rcases hseg with ⟨rfl, rfl, hT⟩ | ⟨N, us0, j, rfl, hus, hj, rfl⟩
    · obtain ⟨us0, hus0⟩ := Option.ne_none_iff_exists'.1 hT
      exact ⟨b, hP, us0, hus0, by omega⟩
    · rcases AtOff_arr_elem hP rfl with h | ⟨us', j', o'', hus', hj', hbe, hat⟩
      · exact absurd h (hsol.2.1 _ _)
      · rw [hus] at hus'
        cases hus'
        have hlt1 : o' < nWords us0 := hsh us0 hus ▸ hlt0
        have hlt2 : o'' + nWords us ≤ nWords us0 := AtOff_bound hat hus hU
        have e : o' + j * nWords us0 = (o'' + (o - b)) + j' * nWords us0 := by omega
        have e2 := congrArg (· % nWords us0) e
        have hlt3 : o'' + (o - b) < nWords us0 := by omega
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt3] at e2
        exact ⟨o'', hat, us0, hus, e2.symm⟩
  obtain ⟨nn, hwcU, hfit, hvrU, hvdU⟩ :=
    VR_at E.unsee hatS hvr hvd (by simp [wc, hS, hsh usS hS])
  have hnn : nn = nWords us := by
    have h1 : wc U = some (nWords us) := wc_of_accs hU
    rw [h1] at hwcU
    exact (Option.some.inj hwcU).symm
  subst hnn
  have hlen : ((ws.drop q).take (nWords us)).length = nWords us := by
    simp only [List.length_take, List.length_drop]; omega
  have hat0 : ((ws.drop q).take (nWords us))[o - b]? = some w0 := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, hq]
    exact hw0
  refine ⟨((ws.drop q).take (nWords us)).set (o - b) w, by rw [List.length_set]; exact hlen,
    List.getElem?_set_self (by rw [hlen]; omega), ?_⟩
  rcases hF.2 with ha | ⟨hrc, hnor⟩
  · exact ValOfR_up (wle_set hat0 hle) ⟨VR_VRR_copy_closed hF.1 ha hvrU, hvdU⟩
  · exact ValOfR_up (wle_set hat0 hle) ⟨TermA4.VR_VRR_rc_closed hF.1 hrc hnor hvrU, hvdU⟩

#print axioms valOfR_zero_fillP

/-- (copy of `freeQW_exists` at `FreeP`) A `freeQW` item exists at a `FreeP` piece. -/
theorem freeQW_existsP {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o b : Nat} {U : Ty}
    {us : List Acc} {tw : Ts} {w : Word}
    (hsto : E.sto l = some c) (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) (hP : TermPiece.Piece c.ty b U)
    (hU : accs U = some us) (hb : b ≤ o) (ho : o < b + nWords us)
    (hsing : ∀ i o2, InAcc us i (o - b) → InAcc us i o2 → o2 = o - b)
    (hF : TermA4.FreeP U) (hnw : ¬ WordUnit E ⟨l, o⟩)
    (hpin : ∀ tw', TermPlant.LowOwn s ⟨l, o⟩ tw' → PredAt s.mem ⟨l, o⟩ tw' w)
    (hok : WordOK E c.ty o w) :
    ∃ x, FreeQW E s l c tw x := by
  obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := id hl
  obtain ⟨t0, m0, ht0, hm0, hl0, hb0, ho0, -, hmin⟩ := lowest_in_piece (l := l) htw hmw (by rw [hml])
    (by rw [hml]; exact hb) (by rw [hml]; exact ho)
  have hlo0 : TermPlant.LowOwn s m0.loc t0 := ⟨ht0, ⟨m0, hm0, rfl⟩, fun t' m' h1 h2 h3 =>
    hmin t' m' h1 h2 (by rw [h3]; exact hl0) (by rw [h3]; exact hb0) (by rw [h3]; exact ho0)⟩
  have hnw0 : ¬ WordUnit E m0.loc := by
    have e : m0.loc = ⟨l, m0.loc.offset⟩ := by rw [← hl0]
    rw [e]
    exact noWU_piece hsto hP hU hb ho hb0 ho0 hnw
  have hml0 : m0.loc.label = l := hl0
  obtain ⟨ws, hlen, hwo, hv⟩ := valOfR_zero_fillP hok hP.1 hP.2.1 hU hb ho hF
  refine ⟨(t0, b, U, ws, .zero, unitK us (o - b)), o, us, hl, hU, hb, ho, rfl, rfl,
    fun cr => crItemQ_freeQW hm0 hml0 hlo0 hnw0 hb0 ho0 hP.1 hP.2.1 hU hb hsing hpin hlen hwo hv, ?_, hsing⟩
  · intro x hx usS hus t m ht hm hlab h1 h2
    rw [List.mem_singleton] at hx
    subst hx
    rw [hU] at hus
    cases hus
    exact hmin t m ht hm hlab h1 h2

#print axioms freeQW_existsP

/-- (interface for package 4) **The cell's upgraded pre-cover and window transport**: an item list `Gs` of
the owner's pre-step cover (`OverCrL` + `HolderLow` at `cv j`), such that at a unit losing a footprint
promise below its lowest own promise (the `HWbRAt` antecedents) the piece is `TermA4.FreeP` (was: resource-free and
copyable), or the window transports back, or a `Gs` item's `K` bit covers the unit. -/
def HWbRUp (c c' : Cfg) (Eg Eg' : GEnv) (cv : Nat → Ts → Res) (j : Nat) (thj : TTh) (Sj : AllocLabel → Prop)
    (l : AllocLabel) (cl : Cell) : Prop :=
  ∃ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)),
    TermOverCr.OverCrL (Cut Eg j Sj) (stOf c.mem c.pairs thj) (cv j) l cl
      (TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gs ∧
    TermOverCr.HolderLow (stOf c.mem c.pairs thj) l Gs ∧
    ∀ o tw b U us, ¬ VisU (Cut Eg' j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg' j Sj) (stOf c'.mem c'.pairs thj) l o tw →
      (∃ t m, c'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ t ≤ tw ∧ t ∈ (Cut Eg j Sj).fp ∧
        t ∉ (Cut Eg' j Sj).fp ∧ t ∉ thj.promises ∧ c.mem[t]? = some m) →
      TermPiece.Piece cl.ty b U → accs U = some us → b ≤ o → o < b + nWords us →
      TermA4.FreeP U ∨ TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw ∨
      ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (R4 dedup) **The `PubShape` cover at an explicit pre-cover `Gs`**, the units losing a footprint
promise handled by `hlostM` (window back, a `freeWL` item, or a `Gs` item).  `foreign_overCrCfgWVG`,
`foreign_overCrCfgO` and `foreign_overCrCfg` are its corollaries. -/
theorem foreign_overCrCfgM {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    {cv : Nat → Ts → Res}
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    (htgW : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ → ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t)
    {Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hL : TermOverCr.OverCrL (Cut Eg j Sj) (stOf c.mem c.pairs thj) (cv j) l cl
      (TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gs)
    (hHL : TermOverCr.HolderLow (stOf c.mem c.pairs thj) l Gs)
    -- a unit losing a footprint promise: the window transports back, a free item or a `Gs` item covers it
    (hlostM : ∀ o tw t m, TermOverCr.CovU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl l o →
      ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) l o tw →
      TermPlant.OverT (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) ⟨l, o⟩ tw →
      c'.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≤ tw →
      (t ∈ (Cut Eg j Sj).fp ∧ t ∉ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).fp ∧
        t ∉ thj.promises ∧ c.mem[t]? = some m) →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw ∨
      (∃ x ∈ freeWL (Cut Eg j Sj) (stOf c.mem c.pairs thj) l cl, ∃ usS i, accs x.2.2.1 = some usS ∧
        x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true) ∨
      ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  have hgf := gfoot_of X Y Z
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, hini2, hrini2, hpfr2⟩ := own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hj' : c'.ths[j]? = some thj := by rw [X.ho j hji]; exact hj
  have hpreM := tctx_pre X
  have hP' := PromsOK_thread X.inv.proms X.inv.disj X.hth X.e3 X.ho (tctx_sub X)
  -- the idle cut before and after
  have hstoE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l =
      (Cut Eg j Sj).sto l := hc2.trans hpre_c.symm
  have hpfE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l =
      (Cut Eg j Sj).pfr l := hpfr2
  have hiniE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini l =
      (Cut Eg j Sj).ini l := hini2
  have hrcE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).rc l =
      (Cut Eg j Sj).rc l := by
    show min ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l)
        ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').rini l) = min (Eg.ini l) (Eg.rini l)
    rw [hini2, hrini2]
  have hI := (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  -- the stepper's cut at `l`
  have hstok : (Cut Eg i S).sto l = some cl := cutSto_some.2 ⟨hs, Or.inr ⟨f, hf⟩⟩
  have hownk : cl.owner ≠ some (Cut Eg i S).tid := by
    rw [hown]; exact fun h => hji (Option.some.inj h)
  -- the owner's typing facts
  obtain ⟨S0, -, -, hmi, -⟩ := X.inv.thr j thj hj
  have hcpl : Ty.coupledOKIn [] cl.ty = true := MemInv_cplT hmi hpre_c hf
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hpre_c hf).1
  have hT0 : (∃ L, accs cl.ty = some L) ∨ ∃ N e, cl.ty = .array (.lit N) e := by
    rcases hlay with hA | ⟨N, e, he, -⟩
    · exact Or.inl (Option.ne_none_iff_exists'.1 hA)
    · exact Or.inr ⟨N, e, he⟩
  -- the footprint
  have hfoot : ∀ (t : Nat) (m : Msg), c.mem.size ≤ t → c'.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset := fun t m h1 h2 =>
    hTF.2.1 t m h1 (by show r.1[t]? = some m; rw [← X.e1]; exact h2)
  have hfpT := fpT_of X.inv.proms hP' hj hji X.e3 X.ho X.hth hTF.2.2
  -- skip lists at `l`: stepper's view vs the owner's
  have hPi : ∀ q t, t ∈ PromAt (Cut Eg i S) (stOf c.mem c.pairs th) ⟨l, q⟩ ↔
      t ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, q⟩ := fun q t =>
    promAt_congr (E1 := Cut Eg j Sj) (E2 := Cut Eg i S) (s1 := stOf c.mem c.pairs thj)
      (s2 := stOf c.mem c.pairs th) (a := ⟨l, q⟩) (hstok.trans hpre_c.symm) rfl rfl rfl (Vis_pfr hf) (Vis_pfr hf) rfl
      (fun t => (X.inv.proms i th X.hth t).trans (X.inv.proms j thj hj t).symm) t
  have hPi' : ∀ q t, t ∈ PromAt (Cut Eg i S) (stOf r.1 r.2.1 r.2.2) ⟨l, q⟩ ↔
      t ∈ PromAt (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) ⟨l, q⟩ := fun q t =>
    promAt_congr (E1 := Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (E2 := Cut Eg i S)
      (s1 := stOf c'.mem c'.pairs thj) (s2 := stOf r.1 r.2.1 r.2.2)
      (a := ⟨l, q⟩) (hstok.trans hc2.symm) hpfr2.symm hini2.symm
      (by
        show min (Eg.ini l) (Eg.rini l) = min ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l)
          ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').rini l)
        rw [hini2, hrini2])
      (Vis_pfr (show (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f from
        hpfr2.trans hf)) (Vis_pfr hf) (show r.1 = c'.mem from X.e1.symm)
      (fun t => (stepper_set_post X.inv.proms X.inv.disj X.inv.fpfree X.hth X.e3 X.ho t).trans
        (hP' j thj hj' t).symm) t
  -- the entry premise
  have hleft := hleft_of (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj)
    (E' := Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (s' := stOf c'.mem c'.pairs thj)
    rfl hpreM (fun o h hv => h ((VisU_congr (a := ⟨l, o⟩) hstoE rfl hpfE).2 hv))
    (fun o h => (predU_congr (a := ⟨l, o⟩) hstoE hpfE hiniE hrcE).1 h)
    (fun _ => Vis_pfr (show (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f
      from hpfr2.trans hf)) hfpT
  have hent := hent_ofCOW (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj)
    (E' := Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (s' := stOf c'.mem c'.pairs thj)
    (l := l) (lt := lt) (ot := ot) (n := n) (Ek := Cut Eg i S) (sk := stOf c.mem c.pairs th) (ck := cl) (c := cl)
    (tg := tgL l tg) (Gd := Gd) rfl hfoot hpreM hleft hcov hstok rfl hownk
    (fun t ht => mem_cut_fp_of_prom X.inv.proms X.inv.disj hji hj X.hth ht)
    (fun o tw hl => by
      obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hl
      have hw := X.inv.promTy j thj tw m hj htw hm cl (by rw [hml]; exact hs) (by rw [hml]; exact ⟨f, hf⟩)
      rw [hml] at hw
      exact piece_of_wordOK (X.inv.clo l cl hs) (X.inv.cmg l cl hs) hw)
    (fun o tw b S us i0 hl hP hus hb hio => by
      obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hl
      have hno := X.inv.promNoTwo j thj tw m cl hj htw hm (by rw [hml]; exact hs)
      rw [hml] at hno
      exact inAcc_single hP.1 hus hio hT0 (fun q hq => by
        rw [Nat.add_sub_cancel' hb]; exact hno q hq))
    (fun hlt => by
      rw [hlt] at hLT
      exact hL_of hLT rfl (show r.1 = c'.mem from X.e1.symm) hPi hPi')
    (fun hlt => by
      rw [hlt] at hLT0
      exact newOver_L0 hLT0 rfl (show r.1 = c'.mem from X.e1.symm) hPi hPi')
    (fun g hg hgl o tw hl hw hv us hus h1 h2 => by
      obtain ⟨t, ht⟩ := htgW g hg hgl o tw hl hw hv us hus h1 h2
      exact ⟨t, by rw [tgL_of hgl]; exact ht⟩)
  have hpf2' : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f :=
    hpfr2.trans hf
  have hlabC : ∀ t m, c.mem[t]? = some m → m.loc.label = l →
      TermPlant.plantD1 Gd TermPiece.GdE.R (tgL l tg) t = TermPlant.plantD1 Gd TermPiece.GdE.R tg t :=
    fun t m hm hl => by
      have hlt : t < c.mem.size := by
        rcases Nat.lt_or_ge t c.mem.size with h1 | h1
        · exact h1
        · rw [Array.getElem?_eq_none h1] at hm; cases hm
      exact plantD1_tgL hTlab (by rw [hpreM t hlt]; exact hm) hl
  have hcovL := foreign_overCrPZOG (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj)
    (E' := Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (s' := stOf c'.mem c'.pairs thj)
    (cr := cv j) (tg := tgL l tg) (Gd := Gd) (Fz := freeWL (Cut Eg j Sj) (stOf c.mem c.pairs thj) l cl)
    hpreM rfl (fun t ht => X.inv.plt j thj t hj ht) hpre_c hstoE
    (fun S0 ws R0 hv => ValOfR_mono hI.prog rfl hI.sto hI.ini hv hI.pfr hI.box hI.rini)
    (Nat.le_of_eq hrcE) (Nat.le_of_eq hiniE) hpf
    (fun o h hv => h ((VisU_congr (a := ⟨l, o⟩) hstoE rfl hpfE).2 hv))
    (fun o h => (predU_congr (a := ⟨l, o⟩) hstoE hpfE hiniE hrcE).2 h)
    (fun t m ht hm => X.inv.promNU j thj t m hj ht hm)
    (fun o tw hcu hv hl hw hov _ => by
      rcases winG_or_lost2 (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj) (s' := stOf c'.mem c'.pairs thj)
          hpreM rfl rfl (fun t ht => X.inv.fpfree j thj t hj ht) (Vis_pfr hf) (Vis_pfr hpf2') hw with
        hw0 | ⟨t, m, hm1, hloc, hle, hsrc⟩
      · exact .inl hw0
      · exact hlostM o tw t m hcu hv hl hw hov hm1 hloc hle hsrc) hcpl (X.inv.stoNI l cl hs)
    hL hHL hnd
    (fun g hg t ht => by
      obtain ⟨hgl, ht'⟩ := tgL_some ht
      exact hT g hg hgl t ht')
    (fun g hg t ht => by
      obtain ⟨hgl, ht'⟩ := tgL_some ht
      exact hTp g hg hgl t ht')
    (fun g _ t ht => (tgL_some ht).1)
    (fun y hy => by
      rw [dnOf_tgL] at hy
      have hy' := hD y hy
      obtain ⟨mh, _, hmh, hlab, _⟩ := id hy'
      refine crItemQ_mono ?_ hy'
      show _ ≤ _
      rw [hlabC y.1 mh hmh hlab]
      exact Res.le_refl _)
    (fun y hy => by
      rw [dnOf_tgL] at hy
      exact hwaD y hy)
    freeWL_item freeWL_zero freeWL_wa freeWL_holder
    (fun o tw hcu hv hl hw hov hno => by
      rcases winG_or_lost2 (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj) (s' := stOf c'.mem c'.pairs thj)
          hpreM rfl rfl (fun t ht => X.inv.fpfree j thj t hj ht) (Vis_pfr hf) (Vis_pfr hpf2') hw with
        hw0 | ⟨t, m, hm1, hloc, hle, hsrc⟩
      · exact .inl (hent o tw hv hl hov hno hw0)
      · rcases hlostM o tw t m hcu hv hl hw hov hm1 hloc hle hsrc with hw0 | hcv | hgs
        · exact .inl (hent o tw hv hl hov hno hw0)
        · exact .inr (.inl hcv)
        · exact .inr (.inr hgs))
  refine overCrE_congrL (fun t m hm hl => ?_) hcovL
  show cv j t + _ = cv j t + _
  rw [plantD1_tgL hTlab hm hl]

#print axioms foreign_overCrCfgM

/-- (hWbR route (iii)) `foreign_overCrCfgWV` with the cell's pre-cover and window transport taken from
`HWbRUp` (whose `Gs` items' `K` bits may cover a unit losing a footprint promise). -/
theorem foreign_overCrCfgWVG {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    {cv : Nat → Ts → Res}
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    (htgW : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ → ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t)
    -- (`UndefLowG`, at single-word units) no `undef` message above a defined one
    (hUL : ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 → m1.loc = ⟨l, o⟩ →
      m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef)
    -- OPEN (hWbR route (iii), the `hWbRUp_of`): the cell's upgraded pre-cover and window transport
    (hUp : HWbRUp c c' Eg (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') cv j thj Sj l cl) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  obtain ⟨Gs, hL, hHL, hWbR⟩ := hUp
  have hgf := gfoot_of X Y Z
  obtain ⟨hpre_c, hs, -, -, -, hpfr2⟩ := own_agree hgf (X.inv.gfresh X.hth r.2.2.nalloc) hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hP' := PromsOK_thread X.inv.proms X.inv.disj X.hth X.e3 X.ho (tctx_sub X)
  have hstoE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l =
      (Cut Eg j Sj).sto l := hc2.trans hpre_c.symm
  have hpf2' : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f :=
    hpfr2.trans hf
  obtain ⟨S0, -, -, hmi, -⟩ := X.inv.thr j thj hj
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hpre_c hf).1
  have hT0 : (∃ L, accs cl.ty = some L) ∨ ∃ N e, cl.ty = .array (.lit N) e := by
    rcases hlay with hA | ⟨N, e, he, -⟩
    · exact Or.inl (Option.ne_none_iff_exists'.1 hA)
    · exact Or.inr ⟨N, e, he⟩
  refine foreign_overCrCfgM X Y Z hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab hT hTp hD hwaD htgW hL hHL ?_
  -- a unit losing a footprint promise: a piece-level free item (`freeQW`)
  intro o tw t m _ hv hl hwP _ hm1 hloc hle hsrc
  obtain ⟨hf1, hf1', hnp, hm0⟩ := hsrc
  obtain ⟨htw, ⟨mq, hmw, hml⟩, -⟩ := id hl
  obtain ⟨b, U, us, hP, hus, hb, ho⟩ : ∃ b S us, TermPiece.Piece cl.ty b S ∧ accs S = some us ∧
      b ≤ o ∧ o < b + nWords us := by
    have hw := X.inv.promTy j thj tw mq hj htw hmw cl (by rw [hml]; exact hs) (by rw [hml]; exact ⟨f, hf⟩)
    rw [hml] at hw
    exact piece_of_wordOK (X.inv.clo l cl hs) (X.inv.cmg l cl hs) hw
  rcases hWbR o tw b U us hv hl hwP ⟨t, m, hm1, hloc, hle, hf1, hf1', hnp, hm0⟩ hP hus hb ho with
    hF | hw0 | hgs
  · have hsing : ∀ i0 o2, InAcc us i0 (o - b) → InAcc us i0 o2 → o2 = o - b := by
      intro i0 o2 hio h2
      have hno := X.inv.promNoTwo j thj tw mq cl hj htw hmw (by rw [hml]; exact hs)
      rw [hml] at hno
      exact inAcc_single hP.1 hus hio hT0 (fun q hq => by
        rw [Nat.add_sub_cancel' hb]; exact hno q hq) o2 h2
    have hnwo : ¬ WordUnit (Cut Eg j Sj) ⟨l, o⟩ := fun hw =>
      hv ⟨(WordUnit_congr (a := ⟨l, o⟩) hstoE).2 hw, Vis_pfr hpf2'⟩
    have htne : t < tw := Nat.lt_of_le_of_ne hle (fun e => hnp (e ▸ htw))
    have hnu : m.val ≠ .undef := by
      obtain ⟨h1, -⟩ := lostFp_stepper X.inv.proms hP' hj hji X.e3 X.ho X.hth hf1 hf1' hnp
      exact X.inv.promNU i th t m X.hth h1 hm0
    obtain ⟨t1, m1, ht1, hpred, ht1w, hm1', hl1⟩ := predAt_above (tw - t) t m rfl htne hm0 hloc
    have hnu1 : m1.val ≠ .undef := by
      rcases Nat.lt_or_ge t t1 with h | h
      · obtain ⟨i0, hi0⟩ := TermPlant.inAcc_ex us (o - b) (Nat.sub_lt_left_of_lt_add hb ho)
        exact hUL o t t1 m m1 h hm0 hm1' hloc hl1 ⟨b, U, us, i0, hP, hus, hb, hi0, fun o2 h2 => hsing i0 o2 hi0 h2⟩ hnu
      · have e : t1 = t := Nat.le_antisymm h ht1
        subst e
        rw [hm0] at hm1'
        cases hm1'
        exact hnu
    have hnp1 : t1 ∉ thj.promises := fun h =>
      Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ht1w (hl.2.2 t1 m1 h hm1' hl1))
    have hok : WordOK (Cut Eg j Sj) cl.ty o (mw m1) := by
      rcases hmi.1.1 t1 m1 cl hnp1 hm1' (by rw [hl1]; exact hpre_c) with hu | hok
      · exact absurd hu hnu1
      · rw [hl1] at hok
        exact WordOK_cut (X.inv.shty l cl ⟨f, hf⟩ hs) hok
    have hpin : ∀ tw', TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw' →
        PredAt (stOf c.mem c.pairs thj).mem ⟨l, o⟩ tw' (mw m1) := fun tw' h' => by
      rw [TermPlant.LowOwn_uniq h' hl]
      exact hpred
    obtain ⟨x, hx⟩ := freeQW_existsP (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj) hpre_c hl hP hus hb ho
      hsing hF hnwo hpin hok
    exact .inr (.inl (freeWL_cover hx hl))
  · exact .inl hw0
  · exact .inr (.inr hgs)
-- the cover with the targets at `l`

/-- (R4 dedup) `htgW` (at non-visible units) from `htgW1` (off two-word units, at non-word units):
a two-word unit of an entry carries no own promise (`noLowOwn_two`). -/
theorem htgW_of1 {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (htgW1 : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ¬ WordUnit (Cut Eg j Sj) ⟨l, o⟩ → ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
      (AtOff cl.ty g.b g.S → ∀ jj, TwoAt us jj → o ≠ g.b + jj ∧ o ≠ g.b + jj + 1) → ∃ t, tg g = some t) :
    ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ → ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t := by
  obtain ⟨-, hs, -⟩ := own_agree (gfoot_of X Y Z) (X.inv.gfresh X.hth r.2.2.nalloc) hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by
    obtain ⟨-, -, -, -, -, hpfr2⟩ := own_agree (gfoot_of X Y Z) (X.inv.gfresh X.hth r.2.2.nalloc) hji Sj hc2 hown
    rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  obtain ⟨hpre_c, -⟩ := own_agree (gfoot_of X Y Z) (X.inv.gfresh X.hth r.2.2.nalloc) hji Sj hc2 hown
  obtain ⟨S0, -, -, hmi, -⟩ := X.inv.thr j thj hj
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hpre_c hf).1
  intro g hg hgl o tw hl hw hv us hus h1 h2
  have hstoE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = (Cut Eg j Sj).sto l := hc2.trans hpre_c.symm
  have hpfp : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f := (own_agree (gfoot_of X Y Z) (X.inv.gfresh X.hth r.2.2.nalloc) hji Sj hc2 hown).2.2.2.2.2.trans hf
  refine htgW1 g hg hgl o tw hl hw (fun hW => hv ⟨(WordUnit_congr (a := ⟨l, o⟩) hstoE).2 hW, Vis_pfr hpfp⟩) us hus h1 h2 (fun hat jj htw => ⟨fun e => ?_, fun e => ?_⟩)
  · exact (noLowOwn_two X.inv.promNoTwo hj hs hlay hat hus htw tw).1 (by rw [← e]; exact hl)
  · exact (noLowOwn_two X.inv.promNoTwo hj hs hlay hat hus htw tw).2 (by rw [← e]; exact hl)

#print axioms htgW_of1

/-- (hWbR route (iii)) `foreign_overCrCfg1WV` at `HWbRUp`. -/
theorem foreign_overCrCfg1WVG {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    {cv : Nat → Ts → Res}
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    -- OPEN (htgW at one-word units): targets of guarded entries, off the entry's two-word units
    (htgW1 : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ¬ WordUnit (Cut Eg j Sj) ⟨l, o⟩ → ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
      (AtOff cl.ty g.b g.S → ∀ jj, TwoAt us jj → o ≠ g.b + jj ∧ o ≠ g.b + jj + 1) → ∃ t, tg g = some t)
    -- (`UndefLowG`, at single-word units) no `undef` message above a defined one
    (hUL : ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 → m1.loc = ⟨l, o⟩ →
      m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef)
    -- OPEN (hWbR route (iii), the `hWbRUp_of`)
    (hUp : HWbRUp c c' Eg (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') cv j thj Sj l cl) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  exact foreign_overCrCfgWVG X Y Z hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab hT hTp hD hwaD
    (htgW_of1 X Y Z hji hj hc2 hown hpf2 htgW1) hUL hUp


/-- (R4 dedup) **`hWbR` + the pre-step cover give `HWbRUp`**: the owner's cover at `cv` (`hOC`)
supplies `Gs`; a `tb 0 ∧ ¬ affine` piece is `TermA4.FreeP`. -/
theorem hWbRUp_of_hWbR {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    {cv : Nat → Ts → Res} (hOC : TermOverCr.OverCrG Eg c cv)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    (hWbR : ∀ o tw b U us, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) l o tw →
      (∃ t m, c'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ t ≤ tw ∧ t ∈ (Cut Eg j Sj).fp ∧
        t ∉ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).fp ∧ t ∉ thj.promises ∧
        c.mem[t]? = some m) →
      TermPiece.Piece cl.ty b U → accs U = some us → b ≤ o → o < b + nWords us →
      (tb 0 U = true ∧ Ty.affine U = false) ∨ TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    HWbRUp c c' Eg (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') cv j thj Sj l cl := by
  obtain ⟨hpre_c, -, -, -, -, hpfr2⟩ := own_agree (gfoot_of X Y Z) (X.inv.gfresh X.hth r.2.2.nalloc) hji Sj hc2 hown
  obtain ⟨Gs, hL, hHL⟩ := hOC j thj Sj hj l cl hpre_c hown (by rw [← hpfr2]; exact hpf2)
  refine ⟨Gs, hL, hHL, fun o tw b U us hv hl hw hlost hP hus hb ho => ?_⟩
  rcases hWbR o tw b U us hv hl hw hlost hP hus hb ho with ⟨hcl, ha⟩ | hw0
  · exact .inl ⟨hcl, .inl ha⟩
  · exact .inr (.inl hw0)

#print axioms hWbRUp_of_hWbR

/-- **`foreign_overCrCfgO` without `hWbT`**: at a unit overtaken after the step, the
window transports back, or a footprint promise below the unit's lowest own promise was lost; such a
unit is covered by a piece-level free item (`freeQW`, pinned by `UndefLowG` and the owner's
`MemOKP`), unless its piece holds a resource or is affine (`hWbR`, OPEN). -/
theorem foreign_overCrCfgW {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hOC : TermOverCr.OverCrG Eg c cr)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    (htgW : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t)
    -- (`UndefLowG`, at single-word units) no `undef` message above a defined one
    (hUL : ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 → m1.loc = ⟨l, o⟩ →
      m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef)
    -- OPEN (hWbT-R): at a unit losing a footprint promise below its lowest own promise, the piece is
    -- resource-free and copyable, or the window transports back
    (hWbR : ∀ o tw b U us, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) l o tw →
      (∃ t m, c'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ t ≤ tw ∧ t ∈ (Cut Eg j Sj).fp ∧
        t ∉ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).fp ∧ t ∉ thj.promises ∧
        c.mem[t]? = some m) →
      TermPiece.Piece cl.ty b U → accs U = some us → b ≤ o → o < b + nWords us →
      (tb 0 U = true ∧ Ty.affine U = false) ∨ TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  exact foreign_overCrCfgWVG X Y (Z.toC _ _ _ _ _) hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab hT hTp hD hwaD
    (fun g hg hgl o tw hl hw _ => htgW g hg hgl o tw hl hw) hUL (hWbRUp_of_hWbR X Y (Z.toC _ _ _ _ _) hOC hji hj hc2 hown hpf2 hWbR)

#print axioms foreign_overCrCfgW

/-- **`foreign_overCrCfg1O` without `hWbT`**: the `PubShape` branch through `foreign_overCrCfgW`. -/
theorem foreign_overCrCfg1W {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hOC : TermOverCr.OverCrG Eg c cr)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    -- OPEN (htgW at one-word units): targets of guarded entries, off the entry's two-word units
    (htgW1 : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
      (AtOff cl.ty g.b g.S → ∀ jj, TwoAt us jj → o ≠ g.b + jj ∧ o ≠ g.b + jj + 1) → ∃ t, tg g = some t)
    -- (`UndefLowG`, at single-word units) no `undef` message above a defined one
    (hUL : ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 → m1.loc = ⟨l, o⟩ →
      m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef)
    -- OPEN (hWbT-R): at a unit losing a footprint promise below its lowest own promise, the piece is
    -- resource-free and copyable, or the window transports back
    (hWbR : ∀ o tw b U us, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) l o tw →
      (∃ t m, c'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ t ≤ tw ∧ t ∈ (Cut Eg j Sj).fp ∧
        t ∉ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).fp ∧ t ∉ thj.promises ∧
        c.mem[t]? = some m) →
      TermPiece.Piece cl.ty b U → accs U = some us → b ≤ o → o < b + nWords us →
      (tb 0 U = true ∧ Ty.affine U = false) ∨ TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  exact foreign_overCrCfg1WVG X Y (Z.toC _ _ _ _ _) hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab hT hTp hD hwaD
    (fun g hg hgl o tw hl hw _ => htgW1 g hg hgl o tw hl hw) hUL (hWbRUp_of_hWbR X Y (Z.toC _ _ _ _ _) hOC hji hj hc2 hown hpf2 hWbR)

#print axioms foreign_overCrCfg1W

end

end TermFreeQW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`foreign_overCrCfg` with the window transport asked only after overtaking (`hWbT`)**: through
`hent_ofCO` and `foreign_overCrPZO` (no free items).  `hWbT` is reduced to the FFUL residual by
`hWbT_of_keep`. -/
theorem foreign_overCrCfgO {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hOC : TermOverCr.OverCrG Eg c cr)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    (htgW : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t)
    -- OPEN (G2, read-only form): the window conditions transport back at units overtaken after the step
    (hWbT : ∀ o tw, TermOverCr.CovU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl l o →
      ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) l o tw →
      TermPlant.OverT (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  obtain ⟨hpre_c, -, -, -, -, hpfr2⟩ := own_agree (gfoot_of X Y (Z.toC _ _ _ _ _)) (X.inv.gfresh X.hth r.2.2.nalloc) hji Sj hc2 hown
  obtain ⟨Gs, hL, hHL⟩ := hOC j thj Sj hj l cl hpre_c hown (by rw [← hpfr2]; exact hpf2)
  exact TermFreeQW.foreign_overCrCfgM X Y (Z.toC _ _ _ _ _) hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab hT hTp hD hwaD
    (fun g hg hgl o tw hl hw _ => htgW g hg hgl o tw hl hw) hL hHL
    (fun o tw _ _ hcu hv hl hw hov _ _ _ _ => .inl (hWbT o tw hcu hv hl hw hov))

#print axioms foreign_overCrCfgO

/-- **`foreign_overCrCfg1` with `hWbT`**: the `PubShape` branch through `foreign_overCrCfgO`. -/
theorem foreign_overCrCfg1O {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hOC : TermOverCr.OverCrG Eg c cr)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    -- OPEN (htgW at one-word units): targets of guarded entries, off the entry's two-word units
    (htgW1 : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
      (AtOff cl.ty g.b g.S → ∀ jj, TwoAt us jj → o ≠ g.b + jj ∧ o ≠ g.b + jj + 1) → ∃ t, tg g = some t)
    -- OPEN (G2, read-only form): the window conditions transport back at units overtaken after the step
    (hWbT : ∀ o tw, TermOverCr.CovU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl l o →
      ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) l o tw →
      TermPlant.OverT (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  obtain ⟨hpre_c, -, -, -, -, hpfr2⟩ := own_agree (gfoot_of X Y (Z.toC _ _ _ _ _)) (X.inv.gfresh X.hth r.2.2.nalloc) hji Sj hc2 hown
  obtain ⟨Gs, hL, hHL⟩ := hOC j thj Sj hj l cl hpre_c hown (by rw [← hpfr2]; exact hpf2)
  exact TermFreeQW.foreign_overCrCfgM X Y (Z.toC _ _ _ _ _) hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab hT hTp hD hwaD
    (TermFreeQW.htgW_of1 X Y (Z.toC _ _ _ _ _) hji hj hc2 hown hpf2 (fun g hg hgl o tw hl hw _ => htgW1 g hg hgl o tw hl hw))
    hL hHL
    (fun o tw _ _ hcu hv hl hw hov _ _ _ _ => .inl (hWbT o tw hcu hv hl hw hov))

#print axioms foreign_overCrCfg1O

/-- **(Cfg layer) The credited cover of an idle thread's own frontier cell after a store
step** of thread `i` (the `PubShape` branch: the step's footprint `TgtFoot`, drop-list coverage
`GdCovU` and mask export `GdLT`, unfolded, at the stepper's cut `Cut Eg i S`).  Every
environment premise of `foreign_overCrP` is discharged from `SysInvN` (`X.inv`) and the step
(`X`, `Y`, `Z`); what remains is about the plant transfer's targets `tg` (`hT`, `hTp`, `hTlab`,
`hD`, `hwaD`, `htgW`) and the OPEN window transport `hWb`. -/
theorem foreign_overCrCfg {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hOC : TermOverCr.OverCrG Eg c cr)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m R us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      PlantCr (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) m t R ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    (htgW : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t)
    -- OPEN (G2): the window conditions transport back along the step
    (hWb : ∀ o tw, TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) l o tw → TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  exact foreign_overCrCfgO X Y Z hOC hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab (hT_low_of_plantCr (s := stOf c'.mem c'.pairs thj) hc2 hT) hTp
    hD hwaD htgW (fun o tw _ _ _ hw _ => hWb o tw hw)

#print axioms foreign_overCrCfg

/-- **(PubShape branch) `foreign_overCrCfg` with `htgW` asked only off two-word units**: on a
word of a two-word unit of an entry's component there is no own promise (`noLowOwn_two`), so the
remaining OPEN target premise `htgW1` is about one-word units only. -/
theorem foreign_overCrCfg1 {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hOC : TermOverCr.OverCrG Eg c cr)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m R us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      PlantCr (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) m t R ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    -- OPEN (htgW at one-word units): targets of guarded entries, off the entry's two-word units
    (htgW1 : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
      (AtOff cl.ty g.b g.S → ∀ jj, TwoAt us jj → o ≠ g.b + jj ∧ o ≠ g.b + jj + 1) → ∃ t, tg g = some t)
    -- OPEN (G2): the window conditions transport back along the step
    (hWb : ∀ o tw, TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) l o tw → TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  exact foreign_overCrCfg1O X Y Z hOC hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab (hT_low_of_plantCr (s := stOf c'.mem c'.pairs thj) hc2 hT) hTp
    hD hwaD htgW1 (fun o tw _ _ _ hw _ => hWb o tw hw)

#print axioms foreign_overCrCfg1

end

end TermOverCrW
