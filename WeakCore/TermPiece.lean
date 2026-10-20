import WeakCore.TermStep
import WeakCore.TermNPmixW
import WeakCore.TermBlkZ

/-! # (D0) Pieces of a laid-out type

A *piece* of a closed laid-out type `T` is a leaf component that `AtOff` reaches:
`AtOff` descends only pairs, `μ`s (through their unfolding) and buffer slots, so a
piece's head is neither a pair nor a `μ` (`Solid`).  We count only pieces of
positive width (zero-width pieces hold no unit, so they never carry a credit).

* `Piece_disj`: two pieces are equal or word-disjoint;
* `Piece_sub` (Fact C): a piece meeting a write target lies inside it, and is a
  piece of the target;
* `VRR_pieces` (Fact B): `VRR` splits exactly over any finite set of pieces, with a
  remainder (the zero-width pieces and the uncovered pieces);
* `VRR_at_pieces`: the same inside a write target, with the put-back of
  `VRR_at` (the exact store identity);
* `Valid_at`: `Valid` descends to every component. -/

namespace TermPiece
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (D0) A piece of `T` at word `b`: a positive-width leaf component. -/
def Piece (T : Ty) (b : Nat) (S : Ty) : Prop := AtOff T b S ∧ Solid S ∧ wc S ≠ some 0

/-- Shift a piece by `n` words. -/
def sh (n : Nat) (p : Nat × Ty) : Nat × Ty := (n + p.1, p.2)

/-- (D0) `PSet T F`: `F` is a set of pieces of `T`, assembled along `T`'s
structure (so they are disjoint by construction). -/
inductive PSet : Ty → List (Nat × Ty) → Prop
  | nil {t : Ty} : PSet t []
  | here {t : Ty} : Solid t → accs t ≠ none → wc t ≠ some 0 → PSet t [(0, t)]
  | prod {a b : Ty} {A B : List (Nat × Ty)} {us : List Acc} : accs a = some us → accs b ≠ none →
      PSet a A → PSet b B → PSet (.prod a b) (A ++ B.map (sh (nWords us)))
  | mu {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} {F : List (Nat × Ty)} : (∀ k, Clo (W k)) →
      s.unguarded 0 = false → accs (cl ρ W 0 0 (.mu s)) ≠ none →
      PSet (cl ρ W 0 0 (unfold1 (.mu s))) F → PSet (cl ρ W 0 0 (.mu s)) F

/-- `p` and `q` occupy disjoint word ranges. -/
def PDisj (p q : Nat × Ty) : Prop :=
  ∃ n m, wc p.2 = some n ∧ wc q.2 = some m ∧ (p.1 + n ≤ q.1 ∨ q.1 + m ≤ p.1)

theorem accs_prod_some {a b : Ty} (h : accs (.prod a b) ≠ none) :
    ∃ ua ub, accs a = some ua ∧ accs b = some ub := by
  cases ha : accs a with
  | none => simp [accs, ha] at h
  | some ua =>
  cases hb : accs b with
  | none => simp [accs, ha, hb] at h
  | some ub => exact ⟨ua, ub, rfl, rfl⟩

theorem Piece_accs {T S : Ty} {b : Nat} (h : Piece T b S) : ∃ us, accs S = some us := by
  rcases AtOff_lay h.1 with hl | ⟨n, e, rfl, -⟩
  · cases hs : accs S with
    | none => exact absurd hs hl
    | some us => exact ⟨us, rfl⟩
  · exact absurd rfl (h.2.1.2.1 _ _)

theorem Piece_pos {T S : Ty} {b : Nat} (h : Piece T b S) {us : List Acc} (hu : accs S = some us) :
    0 < nWords us := by
  have h3 := h.2.2
  rw [wc_of_accs hu] at h3
  have : nWords us ≠ 0 := fun e => h3 (by rw [e])
  omega

theorem PSet_mem {T : Ty} {F : List (Nat × Ty)} (h : PSet T F) : ∀ p ∈ F, Piece T p.1 p.2 := by
  induction h with
  | nil => intro p hp; simp at hp
  | here hs ha hw =>
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨.here (Or.inl ha), hs, hw⟩
  | prod hus _ _ _ ihA ihB =>
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨h1, h2, h3⟩ := ihA p hp
        exact ⟨.fst h1, h2, h3⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨h1, h2, h3⟩ := ihB q hq
        exact ⟨.snd hus h1, h2, h3⟩
  | mu hW hg _ _ ih =>
      intro p hp
      obtain ⟨h1, h2, h3⟩ := ih p hp
      exact ⟨.mu hW hg h1, h2, h3⟩

theorem PSet_cases {T : Ty} {F : List (Nat × Ty)} (h : PSet T F) :
    F = [] ∨ (Solid T ∧ F = [(0, T)]) ∨
      (∃ a b A B us, T = .prod a b ∧ accs a = some us ∧ PSet a A ∧ PSet b B ∧
        F = A ++ B.map (sh (nWords us))) ∨
      (∃ ρ W s, (∀ k, Clo (W k)) ∧ s.unguarded 0 = false ∧ T = cl ρ W 0 0 (.mu s) ∧
        PSet (cl ρ W 0 0 (unfold1 (.mu s))) F) := by
  cases h with
  | nil => exact Or.inl rfl
  | here hs _ _ => exact Or.inr (Or.inl ⟨hs, rfl⟩)
  | prod hus _ hA hB => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, hus, hA, hB, rfl⟩))
  | mu hW hg _ hF => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, hW, hg, rfl, hF⟩))

/-- Two pieces of one type are equal or word-disjoint. -/
theorem Piece_disj {T S S' : Ty} {b b' : Nat} (h : Piece T b S) (h' : Piece T b' S') {us us' : List Acc}
    (hu : accs S = some us) (hu' : accs S' = some us') :
    (b = b' ∧ S = S') ∨ b + nWords us ≤ b' ∨ b' + nWords us' ≤ b := by
  rcases AtOff_nest h'.2.1 hu' h.1 hu h'.1 with h1 | h1 | ⟨hle, h1⟩
  · exact Or.inr (Or.inr h1)
  · exact Or.inr (Or.inl h1)
  · obtain ⟨e1, e2⟩ := AtOff_solid h.2.1 h'.2.1.2.2 h1
    exact Or.inl ⟨by omega, e2.symm⟩

theorem Piece_PDisj {T : Ty} {p q : Nat × Ty} (h : Piece T p.1 p.2) (h' : Piece T q.1 q.2) (hne : p ≠ q) :
    PDisj p q := by
  obtain ⟨us, hu⟩ := Piece_accs h
  obtain ⟨us', hu'⟩ := Piece_accs h'
  refine ⟨nWords us, nWords us', wc_of_accs hu, wc_of_accs hu', ?_⟩
  rcases Piece_disj h h' hu hu' with ⟨e1, e2⟩ | h1 | h1
  · exact absurd (Prod.ext e1 e2) hne
  · exact Or.inl h1
  · exact Or.inr h1

/-- **Fact C**: a piece meeting a laid-out component `U` lies inside it, and is a
piece of `U`. -/
theorem Piece_sub {T U S : Ty} {o b : Nat} {us vs : List Acc} (hU : AtOff T o U) (hus : accs U = some us)
    (hP : Piece T b S) (hvs : accs S = some vs) (hov : o < b + nWords vs) (hov' : b < o + nWords us) :
    o ≤ b ∧ b + nWords vs ≤ o + nWords us ∧ Piece U (b - o) S := by
  rcases AtOff_nest hP.2.1 hvs hU hus hP.1 with h1 | h1 | ⟨hle, h1⟩
  · omega
  · omega
  · have hb := AtOff_bound h1 hus hvs
    exact ⟨hle, by omega, h1, hP.2.1, hP.2.2⟩

/-- A piece of a component is a piece of the whole. -/
theorem Piece_lift {T U S : Ty} {o b : Nat} (hU : AtOff T o U) (hP : Piece U b S) : Piece T (o + b) S :=
  ⟨AtOff_trans hU hP.1, hP.2.1, hP.2.2⟩

/-- Inserting a disjoint piece into a piece set. -/
theorem PSet_insert {T S : Ty} {b : Nat} (h : AtOff T b S) :
    Solid S → wc S ≠ some 0 → accs T ≠ none → ∀ {F : List (Nat × Ty)}, PSet T F →
      (∀ p ∈ F, PDisj (b, S) p) → ∃ F', PSet T F' ∧ F'.Perm ((b, S) :: F) := by
  induction h with
  | @here t _ =>
      intro hs hw ha F hF hd
      rcases PSet_cases hF with rfl | ⟨_, rfl⟩ | ⟨a, b, A, B, us, e, -⟩ | ⟨ρ, W, s, -, -, e, -⟩
      · exact ⟨[(0, t)], .here hs ha hw, .refl _⟩
      · obtain ⟨n, m, h1, h2, h3⟩ := hd (0, t) (List.mem_singleton.2 rfl)
        rw [h1] at h2; cases h2
        exact absurd (by rw [h1]; congr 1; omega) hw
      · exact absurd e (hs.1 _ _)
      · rw [cl_mu_eq] at e; exact absurd e (hs.2.2 _)
  | @fst a b u o h1 ih =>
      intro hs hw ha F hF hd
      obtain ⟨ua, ub, hua, hub⟩ := accs_prod_some ha
      have hb : accs b ≠ none := by simp [hub]
      rcases PSet_cases hF with rfl | ⟨hs', -⟩ | ⟨a', b', A, B, us, e, hus, hA, hB, rfl⟩ |
          ⟨ρ, W, s, -, -, e, -⟩
      · obtain ⟨A', hA', hp⟩ := ih hs hw (by simp [hua]) .nil (by simp)
        exact ⟨A' ++ ([] : List (Nat × Ty)).map (sh (nWords ua)), .prod hua hb hA' .nil, by simpa using hp⟩
      · exact absurd rfl (hs'.1 a b)
      · cases e
        obtain ⟨A', hA', hp⟩ := ih hs hw (by simp [hus]) hA
          (fun p hp => hd p (List.mem_append_left _ hp))
        exact ⟨A' ++ B.map (sh (nWords us)), .prod hus hb hA' hB, hp.append_right _⟩
      · rw [cl_mu_eq] at e; cases e
  | @snd a b u o us hua h1 ih =>
      intro hs hw ha F hF hd
      obtain ⟨ua, ub, hua', hub⟩ := accs_prod_some ha
      have hb : accs b ≠ none := by simp [hub]
      rcases PSet_cases hF with rfl | ⟨hs', -⟩ | ⟨a', b', A, B, us', e, hus, hA, hB, rfl⟩ |
          ⟨ρ, W, s, -, -, e, -⟩
      · obtain ⟨B', hB', hp⟩ := ih hs hw hb .nil (by simp)
        refine ⟨([] : List (Nat × Ty)) ++ B'.map (sh (nWords us)), .prod hua hb .nil hB', ?_⟩
        rw [List.nil_append]; exact hp.map (sh (nWords us))
      · exact absurd rfl (hs'.1 a b)
      · cases e
        rw [hua] at hus; cases hus
        obtain ⟨B', hB', hp⟩ := ih hs hw hb hB (fun q hq => by
          obtain ⟨n, m, h1, h2, h3⟩ := hd (sh (nWords us) q)
            (List.mem_append_right _ (List.mem_map_of_mem hq))
          exact ⟨n, m, h1, h2, by simp only [sh] at h3; omega⟩)
        exact ⟨A ++ B'.map (sh (nWords us)), .prod hua hb hA hB',
          (List.Perm.append_left A (hp.map (sh (nWords us)))).trans List.perm_middle⟩
      · rw [cl_mu_eq] at e; cases e
  | elem _ _ _ _ =>
      intro _ _ ha
      exact absurd (by simp [accs]) ha
  | @mu ρ W s u o hW hg h1 ih =>
      intro hs hw ha F hF hd
      have ha' : accs (cl ρ W 0 0 (unfold1 (.mu s))) ≠ none := by rw [accs_cl_unfold_eq hW hg]; exact ha
      rcases PSet_cases hF with rfl | ⟨hs', -⟩ | ⟨a', b', A, B, us', e, -⟩ |
          ⟨ρ', W', s', hW', -, e, hF'⟩
      · obtain ⟨F', hF', hp⟩ := ih hs hw ha' .nil (by simp)
        exact ⟨F', .mu hW hg ha hF', hp⟩
      · exact absurd (cl_mu_eq _ _ _) (hs'.2.2 _)
      · rw [cl_mu_eq] at e; cases e
      · have hF2 : PSet (cl ρ W 0 0 (unfold1 (.mu s))) F := by
          rw [cl_unfold1 hW, e, ← cl_unfold1 hW']; exact hF'
        obtain ⟨F', hF', hp⟩ := ih hs hw ha' hF2 hd
        exact ⟨F', .mu hW hg ha hF', hp⟩
  | fold _ _ _ _ _ =>
      intro hs
      exact absurd (cl_mu_eq _ _ _) (hs.2.2 _)

/-- A nodup family of pieces is (up to order) a piece set. -/
theorem PSet_of {T : Ty} (hT : accs T ≠ none) :
    ∀ {L : List (Nat × Ty)}, (∀ p ∈ L, Piece T p.1 p.2) → L.Nodup → ∃ F, PSet T F ∧ F.Perm L
  | [], _, _ => ⟨[], .nil, .refl _⟩
  | p :: L, hL, hnd => by
      obtain ⟨hpL, hnd'⟩ := List.nodup_cons.1 hnd
      obtain ⟨F, hF, hp⟩ := PSet_of hT (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hnd'
      have hP := hL p (List.mem_cons_self ..)
      obtain ⟨F', hF', hp'⟩ := PSet_insert hP.1 hP.2.1 hP.2.2 hT hF (fun q hq => by
        have hqL : q ∈ L := hp.mem_iff.1 hq
        exact Piece_PDisj hP (hL q (List.mem_cons_of_mem _ hqL)) (fun e => hpL (by rw [← e] at hqL; exact hqL)))
      exact ⟨F', hF', hp'.trans (hp.cons p)⟩

theorem sumPerm {α : Type} {f : α → Res} {L₁ L₂ : List α} (h : L₁.Perm L₂) :
    Res.sum (L₁.map f) = Res.sum (L₂.map f) := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.map_cons, Res.sum_cons, ih]
  | swap x y L =>
      simp only [List.map_cons, Res.sum_cons]
      rw [← Res.add_assoc, ← Res.add_assoc, Res.add_comm (f y) (f x)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem perm_lift {α β : Type} {F F' : List α} (hp : F.Perm F') :
    ∀ {G : List (α × β)}, G.map Prod.fst = F → ∃ G' : List (α × β), G'.Perm G ∧ G'.map Prod.fst = F' := by
  induction hp with
  | nil => intro G hG; exact ⟨G, .refl _, hG⟩
  | cons x _ ih =>
      intro G hG
      match G, hG with
      | [], hG => simp at hG
      | g :: G0, hG =>
          simp only [List.map_cons, List.cons.injEq] at hG
          obtain ⟨G1, hp1, he1⟩ := ih hG.2
          exact ⟨g :: G1, hp1.cons g, by simp [he1, hG.1]⟩
  | swap x y L =>
      intro G hG
      match G, hG with
      | [], hG => simp at hG
      | [_], hG => simp at hG
      | g1 :: g2 :: G0, hG =>
          simp only [List.map_cons, List.cons.injEq] at hG
          exact ⟨g2 :: g1 :: G0, .swap g1 g2 G0, by simp [hG.1, hG.2.1, hG.2.2]⟩
  | trans _ _ ih1 ih2 =>
      intro G hG
      obtain ⟨G1, p1, e1⟩ := ih1 hG
      obtain ⟨G2, p2, e2⟩ := ih2 e1
      exact ⟨G2, p2.trans p1, e2⟩

/-- A piece with its resources, read off the words `ws` of the whole. -/
def PcR (ρ₀ : Nat → Nat) (E : TEnv) (ws : List Word) (g : (Nat × Ty) × Res) : Prop :=
  ∃ n, wc g.1.2 = some n ∧ g.1.1 + n ≤ ws.length ∧
    VRR ρ₀ (CE E) g.1.2 (shp g.1.2) ((ws.drop g.1.1).take n) g.2

/-- `VRR` splits over a piece set, with a remainder. -/
theorem VRR_pset (E : TEnv) {ρ₀ : Nat → Nat} {T : Ty} {F : List (Nat × Ty)} (h : PSet T F) :
    ∀ {ws : List Word} {R : Res}, VRR ρ₀ (CE E) T (shp T) ws R → wc T = some ws.length →
      ∃ G : List ((Nat × Ty) × Res), G.map Prod.fst = F ∧ ∃ Rr, R = Res.sum (G.map Prod.snd) + Rr ∧
        ∀ g ∈ G, PcR ρ₀ E ws g := by
  induction h with
  | nil => intro ws R _ _; exact ⟨[], rfl, R, by simp, by simp⟩
  | @here t _ _ _ =>
      intro ws R hv hwc
      refine ⟨[((0, t), R)], rfl, .zero, by simp, fun g hg => ?_⟩
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨ws.length, hwc, by simp, by simpa using hv⟩
  | @prod a b A B us hus hb _ _ ihA ihB =>
      intro ws R hv hwc
      cases hb' : accs b with
      | none => exact absurd hb' hb
      | some ub =>
      have hwa : wc a = some (nWords us) := wc_of_accs hus
      have hwb : wc b = some (nWords ub) := wc_of_accs hb'
      simp only [VRR] at hv
      obtain ⟨ra, rb, e, Ra, Rb, hR, -, hsplit⟩ := hv
      simp only [shp, Shp.prod.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hlen : ws.length = nWords us + nWords ub := by
        simp [wc, accs, hus, hb', nWords_append] at hwc; omega
      obtain ⟨_, hva, hvb⟩ := hsplit _ (by rw [shp_wc]; exact hwa)
      have hla : (ws.take (nWords us)).length = nWords us := by simp; omega
      have hlb : (ws.drop (nWords us)).length = nWords ub := by simp; omega
      obtain ⟨GA, eA, RrA, hRA, hGA⟩ := ihA hva (by rw [hla]; exact hwa)
      obtain ⟨GB, eB, RrB, hRB, hGB⟩ := ihB hvb (by rw [hlb]; exact hwb)
      let f : (Nat × Ty) × Res → (Nat × Ty) × Res := fun g => (sh (nWords us) g.1, g.2)
      have hsn : (GB.map f).map Prod.snd = GB.map Prod.snd := by rw [List.map_map]; rfl
      have hfs : (GB.map f).map Prod.fst = (GB.map Prod.fst).map (sh (nWords us)) := by
        rw [List.map_map, List.map_map]; rfl
      refine ⟨GA ++ GB.map f, by rw [List.map_append, eA, hfs, eB], RrA + RrB, ?_, fun g hg => ?_⟩
      · rw [List.map_append, Res.sum_append, hsn, hR, hRA, hRB]
        exact Res.ext fun k => by simp only [Res.add_apply]; omega
      · rcases List.mem_append.1 hg with hg | hg
        · obtain ⟨n, hwn, hle, hvn⟩ := hGA g hg
          rw [hla] at hle
          refine ⟨n, hwn, by omega, ?_⟩
          rwa [take_drop_take hle] at hvn
        · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
          obtain ⟨n, hwn, hle, hvn⟩ := hGB g0 hg0
          rw [hlb] at hle
          refine ⟨n, hwn, by simp only [f, sh]; omega, ?_⟩
          rw [drop_drop'] at hvn
          exact hvn
  | @mu ρ W s F hW hg _ _ ih =>
      intro ws R hv hwc
      have hsig := sig_cl_unfold (ρ := ρ) (W := W) hg
      have e1 : cl ρ W 0 0 (.mu s) = .mu (cl ρ W 1 0 s) := rfl
      have hshp : shp (cl ρ W 0 0 (unfold1 (.mu s))) = shp (cl ρ W 0 0 (.mu s)) := by
        rw [shp_of_sig hsig, e1]; rfl
      have hv' := (VRR_cl_unfold E hW hg).2 hv
      rw [← hshp] at hv'
      have hwc' : wc (cl ρ W 0 0 (unfold1 (.mu s))) = some ws.length := by
        rw [wc_of_sig hsig, ← hwc, e1]; rfl
      exact ih hv' hwc'

/-- **Fact B** (exactness): a value's resources split over any nodup family of
its pieces, each piece holding a `VRR` share of its own words, with a remainder. -/
theorem VRR_pieces (E : TEnv) {ρ₀ : Nat → Nat} {T : Ty} {L : List (Nat × Ty)} (hT : accs T ≠ none)
    (hL : ∀ p ∈ L, Piece T p.1 p.2) (hnd : L.Nodup) {ws : List Word} {R : Res}
    (hv : VRR ρ₀ (CE E) T (shp T) ws R) (hwc : wc T = some ws.length) :
    ∃ G : List ((Nat × Ty) × Res), G.map Prod.fst = L ∧ ∃ Rr, R = Res.sum (G.map Prod.snd) + Rr ∧
      ∀ g ∈ G, PcR ρ₀ E ws g := by
  obtain ⟨F, hF, hp⟩ := PSet_of hT hL hnd
  obtain ⟨G, eG, Rr, hR, hG⟩ := VRR_pset E hF hv hwc
  obtain ⟨G', hp', eG'⟩ := perm_lift hp eG
  exact ⟨G', eG', Rr, by rw [hR, sumPerm hp'], fun g hg => hG g (hp'.mem_iff.1 hg)⟩

/-- **The exact store identity, by pieces**: at a component `U` (offset `o`) of
a value holding `R`, the pieces `L` of `U` hold `Σ G`, with `R = Σ G + Rx + Rr`;
putting a value holding `Rq'` at `U` gives a value holding `Rq' + Rr`.  So the
new value plus the pieces' old shares is at most the old value plus `Rq'`. -/
theorem VRR_at_pieces (E : TEnv) {ρ₀ : Nat → Nat} {T U : Ty} {o : Nat} (h : AtOff T o U) {us : List Acc}
    (hus : accs U = some us) {L : List (Nat × Ty)} (hL : ∀ p ∈ L, Piece U p.1 p.2) (hnd : L.Nodup)
    {ws : List Word} {R : Res} (hv : VRR ρ₀ (CE E) T (shp T) ws R) (hwc : wc T = some ws.length) :
    ∃ G : List ((Nat × Ty) × Res), G.map Prod.fst = L ∧ ∃ Rx Rr,
      R = Res.sum (G.map Prod.snd) + Rx + Rr ∧ o + nWords us ≤ ws.length ∧
      (∀ g ∈ G, PcR ρ₀ E ((ws.drop o).take (nWords us)) g) ∧
      ∀ q Rq', VRR ρ₀ (CE E) U (shp U) q Rq' → q.length = nWords us →
        VRR ρ₀ (CE E) T (shp T) (ws.take o ++ q ++ ws.drop (o + nWords us)) (Rq' + Rr) := by
  obtain ⟨n, Rq, Rr, hwu, hle, hR, hvq, hput⟩ := VRR_at E h hv hwc
  rw [wc_of_accs hus] at hwu
  obtain rfl : nWords us = n := Option.some.inj hwu
  have hwq : wc U = some ((ws.drop o).take (nWords us)).length := by
    rw [wc_of_accs hus]; simp; omega
  obtain ⟨G, eG, Rx, hRq, hG⟩ := VRR_pieces E (by simp [hus]) hL hnd hvq hwq
  exact ⟨G, eG, Rx, Rr, by rw [hR, hRq], hle, hG, hput⟩

/-- `Valid` descends to every laid-out component. -/
theorem Valid_at {T U : Ty} {o : Nat} (h : AtOff T o U) :
    ∀ {ws : List Word}, accs T ≠ none → Valid T ws → wc T = some ws.length →
      ∀ n, wc U = some n → Valid U ((ws.drop o).take n) := by
  induction h with
  | here _ =>
      intro ws _ hv hwc n hn
      rw [hwc] at hn
      obtain rfl := Option.some.inj hn
      simpa using hv
  | @fst a b u o h1 ih =>
      intro ws ha hv hwc n hn
      obtain ⟨ua, ub, hua, hub⟩ := accs_prod_some ha
      have hwa : wc a = some (nWords ua) := wc_of_accs hua
      have hlen : ws.length = nWords ua + nWords ub := by
        simp [wc, accs, hua, hub, nWords_append] at hwc; omega
      have hla : (ws.take (nWords ua)).length = nWords ua := by simp; omega
      obtain ⟨uu, huu, rfl⟩ := wc_some hn
      have hb := AtOff_bound h1 hua huu
      have := ih (by simp [hua]) ((hv _ hwa).1) (by rw [hla]; exact hwa) _ hn
      rwa [take_drop_take hb] at this
  | @snd a b u o us hua h1 ih =>
      intro ws ha hv hwc n hn
      obtain ⟨ua, ub, hua', hub⟩ := accs_prod_some ha
      rw [hua] at hua'; cases hua'
      have hwa : wc a = some (nWords us) := wc_of_accs hua
      have hwb : wc b = some (nWords ub) := wc_of_accs hub
      have hlen : ws.length = nWords us + nWords ub := by
        simp [wc, accs, hua, hub, nWords_append] at hwc; omega
      have hlb : (ws.drop (nWords us)).length = nWords ub := by simp; omega
      have := ih (by simp [hub]) ((hv _ hwa).2) (by rw [hlb]; exact hwb) _ hn
      rwa [drop_drop'] at this
  | elem _ _ _ _ =>
      intro ws ha
      exact absurd (by simp [accs]) ha
  | @mu ρ W s u o hW hg h1 ih =>
      intro ws ha hv hwc n hn
      have hsig := sig_cl_unfold (ρ := ρ) (W := W) hg
      have hv' : Valid (cl ρ W 0 0 (unfold1 (.mu s))) ws :=
        Valid_of_sig hsig.symm (show Valid (cl ρ W 1 0 s) ws from hv)
      have ha' : accs (cl ρ W 0 0 (unfold1 (.mu s))) ≠ none := by rw [accs_cl_unfold_eq hW hg]; exact ha
      have hwc' : wc (cl ρ W 0 0 (unfold1 (.mu s))) = some ws.length := by
        simp only [wc]; rw [accs_cl_unfold_eq hW hg]; exact hwc
      exact ih ha' hv' hwc' n hn
  | @fold ρ W s T o hW hg hau h1 ih =>
      intro ws ha hv hwc n hn
      have hsig := sig_cl_unfold (ρ := ρ) (W := W) hg
      have hn' : wc (cl ρ W 0 0 (unfold1 (.mu s))) = some n := by
        simp only [wc]; rw [accs_cl_unfold_eq hW hg]; exact hn
      have := ih ha hv hwc n hn'
      exact (show Valid (cl ρ W 1 0 s) _ from Valid_of_sig hsig this)

end TermPiece

#print axioms TermPiece.accs_prod_some
#print axioms TermPiece.Piece_accs
#print axioms TermPiece.Piece_pos
#print axioms TermPiece.PSet_mem
#print axioms TermPiece.PSet_cases
#print axioms TermPiece.Piece_disj
#print axioms TermPiece.Piece_PDisj
#print axioms TermPiece.Piece_sub
#print axioms TermPiece.Piece_lift
#print axioms TermPiece.PSet_insert
#print axioms TermPiece.PSet_of
#print axioms TermPiece.sumPerm
#print axioms TermPiece.perm_lift
#print axioms TermPiece.VRR_pset
#print axioms TermPiece.VRR_pieces
#print axioms TermPiece.VRR_at_pieces
#print axioms TermPiece.Valid_at

/-! # (step 2a) Untorn stores and the drop list -/

namespace TermStep
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ### Untorn units: a store's words are the new latest words -/

/-- Unit `B` is **untorn** at `s`: every own promise at `B` is no foreign
promise skipped there, and every later message at `B` is skipped. -/
def UntornU (E : TEnv) (s : St) (B : Address) : Prop :=
  ∀ (t : Ts) (m : Msg), t ∈ s.promises → s.mem[t]? = some m → m.loc = B → t ∉ FpAt E B ∧
    ∀ (t' : Ts) (m' : Msg), t < t' → s.mem[t']? = some m' → m'.loc = B → t' ∈ PromAt E s B

/-- Untornness survives a step that adds no message at `B`, keeps the old
messages, and keeps the own promises at `B`. -/
theorem UntornU_mono {E : TEnv} {s s' : St} {B : Address}
    (m1 : ∀ (t : Ts) (m : Msg), s'.mem[t]? = some m → m.loc = B → s.mem[t]? = some m)
    (p1 : ∀ t, t ∈ s'.promises → t ∈ s.promises)
    (p2 : ∀ (t : Ts) (m : Msg), t ∈ s.promises → s.mem[t]? = some m → m.loc = B → t ∈ s'.promises)
    (h : UntornU E s B) (hfw : ∀ t, AboveFW s.mem B t → AboveFW s'.mem B t) : UntornU E s' B := by
  intro t m ht hm hl
  obtain ⟨hf, hup⟩ := h t m (p1 t ht) (m1 t m hm hl) hl
  refine ⟨hf, fun t' m' hlt hm' hl' => ?_⟩
  have hm2 := m1 t' m' hm' hl'
  have h2 := hup t' m' hlt hm2 hl'
  by_cases hw : VisU E B
  · rw [PromAt_word hw] at h2; cases h2
  by_cases hq : PredU E B
  · rw [mem_PromAt_pred hw hq] at h2 ⊢
    refine ⟨?_, hfw t' h2.2⟩
    rcases List.mem_append.1 h2.1 with h3 | h3
    · exact List.mem_append.2 (Or.inl (p2 t' m' h3 hm2 hl'))
    · exact List.mem_append.2 (Or.inr h3)
  · rw [PromAt_nword hw hq] at h2 ⊢
    rcases List.mem_append.1 h2 with h3 | h3
    · exact List.mem_append.2 (Or.inl (p2 t' m' h3 hm2 hl'))
    · exact List.mem_append.2 (Or.inr h3)

/-- (U3) A store keeps `AboveFW` (memory only grows). -/
theorem stepStore_AboveFW {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {A B : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th A e deps rel) (ha : AboveFW mem B t) : AboveFW mem' B t := by
  rcases stepStore_casesE h with ⟨hmem, -⟩ | ⟨_, _, hmem, -⟩
  · rw [hmem]; exact AboveFW_pushM _ ha
  · rw [hmem]; exact ha

/-- `stepStore_NPsameF` at an untorn unit: the stored word is the latest. -/
theorem stepStore_NPnewF {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {A : Address} {w : Word} {deps : List WeakMem.Reg} {rel : Bool} {V : Ts} {F : List Ts}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th A (dataE 1 w) deps rel) (hr : th.regs 1 = w)
    (hV : V ≤ th.vs.vRelSt) (hP : ∀ t, t ∈ th.promises ++ F → t < mem.size) (hnd : th.promises.Nodup)
    (hU : ∀ (t : Ts) (m : Msg), t ∈ th.promises → mem[t]? = some m → m.loc = A → t ∉ F ∧
      ∀ (t' : Ts) (m' : Msg), t < t' → mem[t']? = some m' → m'.loc = A → t' ∈ th.promises ++ F) :
    ∃ x0 : Word, WLe1 (bumpW V w) x0 ∧ LatestNP mem' (th'.promises ++ F) A x0 := by
  have hw : WLe1 (bumpW V w) ⟨w.val, Promises.storeMview th (dataE 1 w) deps rel, 0⟩ :=
    WLe1_msgB (WLe1_refl _) (storeMview_dataE th 1 w hr deps rel)
      (Nat.le_trans hV (storeMview_relSt th _ deps rel))
  rcases stepStore_casesE h with ⟨hmem, hpr⟩ | ⟨t, m, hmem, htp, hpr, hm, hloc, hval, hmv⟩
  · refine ⟨_, ?_, by rw [hmem, hpr]; exact LatestNP_push_top _ hP⟩
    show WLe1 (bumpW V w) ⟨exprVal th (dataE 1 w), Promises.storeMview th (dataE 1 w) deps rel, 0⟩
    rw [exprVal_dataE th 1 w hr]; exact hw
  · rw [hmem, hpr]
    obtain ⟨hf, hup⟩ := hU t m htp hm hloc
    refine ⟨mw m, WLe1_trans hw ⟨?_, fun _ _ _ => hmv⟩, t, m, fun h1 => ?_, hm, hloc, rfl,
      fun t' m' hlt hm' hl' => ?_⟩
    · show w.val = m.val
      rw [hval, exprVal_dataE th 1 w hr]
    · rcases List.mem_append.1 h1 with h1 | h1
      · exact (List.Nodup.not_mem_erase hnd) h1
      · exact hf h1
    · rcases List.mem_append.1 (hup t' m' hlt hm' hl') with h1 | h1
      · exact List.mem_append.2 (Or.inl ((List.mem_erase_of_ne (Nat.ne_of_gt hlt)).2 h1))
      · exact List.mem_append.2 (Or.inr h1)

open Classical in
/-- (U3) `stepStore_NPnewF` with a filtered skip list: the later messages are
skipped and satisfy `Q`. -/
theorem stepStore_NPnewQ {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {A : Address} {w : Word} {deps : List WeakMem.Reg} {rel : Bool} {V : Ts} {F : List Ts} {Q : Ts → Prop}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th A (dataE 1 w) deps rel) (hr : th.regs 1 = w)
    (hV : V ≤ th.vs.vRelSt) (hP : ∀ t, t ∈ th.promises ++ F → t < mem.size) (hnd : th.promises.Nodup)
    (hU : ∀ (t : Ts) (m : Msg), t ∈ th.promises → mem[t]? = some m → m.loc = A → t ∉ F ∧
      ∀ (t' : Ts) (m' : Msg), t < t' → mem[t']? = some m' → m'.loc = A → t' ∈ th.promises ++ F ∧ Q t') :
    ∃ x0 : Word, WLe1 (bumpW V w) x0 ∧ LatestNP mem' ((th'.promises ++ F).filter (fun t => decide (Q t))) A x0 := by
  have hw : WLe1 (bumpW V w) ⟨w.val, Promises.storeMview th (dataE 1 w) deps rel, 0⟩ :=
    WLe1_msgB (WLe1_refl _) (storeMview_dataE th 1 w hr deps rel)
      (Nat.le_trans hV (storeMview_relSt th _ deps rel))
  rcases stepStore_casesE h with ⟨hmem, hpr⟩ | ⟨t, m, hmem, htp, hpr, hm, hloc, hval, hmv⟩
  · refine ⟨_, ?_, by rw [hmem, hpr]; exact LatestNP_push_top _ (fun t ht => hP t (List.mem_filter.1 ht).1)⟩
    show WLe1 (bumpW V w) ⟨exprVal th (dataE 1 w), Promises.storeMview th (dataE 1 w) deps rel, 0⟩
    rw [exprVal_dataE th 1 w hr]; exact hw
  · rw [hmem, hpr]
    obtain ⟨hf, hup⟩ := hU t m htp hm hloc
    refine ⟨mw m, WLe1_trans hw ⟨?_, fun _ _ _ => hmv⟩, t, m, fun h1 => ?_, hm, hloc, rfl,
      fun t' m' hlt hm' hl' => ?_⟩
    · show w.val = m.val
      rw [hval, exprVal_dataE th 1 w hr]
    · rcases List.mem_append.1 (List.mem_filter.1 h1).1 with h1 | h1
      · exact (List.Nodup.not_mem_erase hnd) h1
      · exact hf h1
    · obtain ⟨h2, hq⟩ := hup t' m' hlt hm' hl'
      refine List.mem_filter.2 ⟨?_, decide_eq_true hq⟩
      rcases List.mem_append.1 h2 with h1 | h1
      · exact List.mem_append.2 (Or.inl ((List.mem_erase_of_ne (Nat.ne_of_gt hlt)).2 h1))
      · exact List.mem_append.2 (Or.inr h1)

/-- `stepStore_NPsame0` at an untorn unit (no later message at all). -/
theorem stepStore_NPnew0 {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {A : Address} {w : Word} {deps : List WeakMem.Reg} {rel : Bool} {V : Ts}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th A (dataE 1 w) deps rel) (hr : th.regs 1 = w)
    (hV : V ≤ th.vs.vRelSt)
    (hU : ∀ (t : Ts) (m : Msg), t ∈ th.promises → mem[t]? = some m → m.loc = A →
      ∀ (t' : Ts) (m' : Msg), t < t' → mem[t']? = some m' → m'.loc = A → False) :
    ∃ x0 : Word, WLe1 (bumpW V w) x0 ∧ LatestNP mem' [] A x0 := by
  have hw : WLe1 (bumpW V w) ⟨w.val, Promises.storeMview th (dataE 1 w) deps rel, 0⟩ :=
    WLe1_msgB (WLe1_refl _) (storeMview_dataE th 1 w hr deps rel)
      (Nat.le_trans hV (storeMview_relSt th _ deps rel))
  rcases stepStore_casesE h with ⟨hmem, -⟩ | ⟨t, m, hmem, htp, -, hm, hloc, hval, hmv⟩
  · refine ⟨_, ?_, by rw [hmem]; exact LatestNP_push_top _ (fun t ht => by cases ht)⟩
    show WLe1 (bumpW V w) ⟨exprVal th (dataE 1 w), Promises.storeMview th (dataE 1 w) deps rel, 0⟩
    rw [exprVal_dataE th 1 w hr]; exact hw
  · rw [hmem]
    refine ⟨mw m, WLe1_trans hw ⟨?_, fun _ _ _ => hmv⟩, t, m, by simp, hm, hloc, rfl,
      fun t' m' hlt hm' hl' => (hU t m htp hm hloc t' m' hlt hm' hl').elim⟩
    show w.val = m.val
    rw [hval, exprVal_dataE th 1 w hr]

/-- A one-word store at `A` keeps the untornness of every other unit. -/
theorem stepStore_untorn {E : TEnv} {s : St} {k : Promises.Knobs} {arch : Arch} {mem' : Memory}
    {th th' : Promises.Thread} {A B : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (hth : th.promises = s.promises)
    (h : (mem', th') ∈ Promises.stepStore k arch s.mem th A e deps rel) (hB : B ≠ A)
    (hU : UntornU E s B) :
    UntornU E { s with mem := mem', vs := th'.vs, promises := th'.promises } B := by
  refine UntornU_mono (fun t m hm hl => ?_) (fun t ht => ?_) (fun t m ht hm hl => ?_) hU
    (fun t h0 => stepStore_AboveFW h h0)
  · rcases stepStore_casesE h with ⟨hmem, -⟩ | ⟨_, _, hmem, -⟩
    · have hm' : mem'[t]? = some m := hm
      rw [hmem, Array.getElem?_push] at hm'
      by_cases e1 : t = s.mem.size
      · rw [ite_eq_left e1, Option.some.injEq] at hm'; subst hm'; exact absurd hl hB.symm
      · rw [ite_eq_right e1] at hm'; exact hm'
    · have hm' : mem'[t]? = some m := hm
      rw [hmem] at hm'; exact hm'
  · rw [← hth]; exact stepStore_promSub h t ht
  · show t ∈ th'.promises
    rcases stepStore_casesE h with ⟨-, hpr⟩ | ⟨t0, m0, -, -, hpr, hm0, hl0, -⟩
    · rw [hpr, hth]; exact ht
    · rw [hpr]
      have hne : t ≠ t0 := fun e1 => by
        subst e1; rw [hm] at hm0; cases hm0; exact hB (hl.symm.trans hl0)
      rw [hth]; exact (List.mem_erase_of_ne hne).2 ht

/-- ** A store at untorn units**: its stored words are the cell's new latest
words (no mix with the old ones). -/
theorem storeUnits_NPnew {E : TEnv} {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St) (V : Ts),
      s' ∈ storeUnits k arch pw a rel us ws i s → V ≤ s.vs.vRelSt → (∀ t, t ∈ s.promises → t < s.mem.size) →
      (∀ t, t ∈ E.fp → t < s.mem.size) → ws.length = nWords us → s.promises.Nodup →
      (∀ j, j < nWords us → UntornU E s (offs a (i + j))) →
      ∃ vals : List Word, WLe (ws.map (bumpW V)) vals ∧
        ∀ j x, vals[j]? = some x → LatestNP s'.mem (PromAt E s' (offs a (i + j))) (offs a (i + j)) x
  | [], ws, _, s, s', V, hs, _, _, _, hl, _, _ => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero (by simpa [nWords] using hl)
      exact ⟨[], trivial, fun j x h => by simp at h⟩
  | .one :: us, w :: ws, i, s, s', V, hs, hV, hP, hF, hl, hnd, hU => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      rw [TermMem.nWords_one] at hl hU
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      obtain ⟨-, -, -, hrs⟩ := stepStore_cases hst
      have hpsub := stepStore_promSub hst
      have hsz : s.mem.size ≤ mem'.size := by
        rcases stepStore_casesE hst with ⟨hmem, -⟩ | ⟨_, _, hmem, -⟩
        · rw [hmem, Array.size_push]; exact Nat.le_succ _
        · rw [hmem]; exact Nat.le_refl _
      have hne : ∀ j, offs a (i + 1 + j) ≠ offs a i := fun j e => by
        have := congrArg WeakMem.Address.offset e; simp [offs] at this; omega
      have hU0 := hU 0 (by omega)
      simp only [Nat.add_zero] at hU0
      obtain ⟨x0, hb, h0⟩ : ∃ x0 : Word, WLe1 (bumpW V w) x0 ∧
          LatestNP mem' (PromAt E { s with mem := mem', vs := th.vs, promises := th.promises } (offs a i))
            (offs a i) x0 := by
        by_cases hWU : VisU E (offs a i)
        · rw [PromAt_word hWU]
          exact stepStore_NPnew0 (V := V) hst (by simp [mth, regsOf]) hV
            (fun t m ht hm hl t' m' hlt hm' hl' => by
              have := (hU0 t m ht hm hl).2 t' m' hlt hm' hl'
              rw [PromAt_word hWU] at this; cases this)
        by_cases hq : PredU E (offs a i)
        · rw [PromAt_pred hWU hq]
          exact stepStore_NPnewQ (V := V) (Q := fun t => AboveFW mem' (offs a i) t) hst (by simp [mth, regsOf]) hV
            (fun t ht => (List.mem_append.1 ht).elim (hP t) (fun h => hF t (FpAt_sub h))) hnd
            (fun t m ht hm hl => by
              obtain ⟨a1, a2⟩ := hU0 t m ht hm hl
              refine ⟨a1, fun t' m' hlt hm' hl' => ?_⟩
              have := a2 t' m' hlt hm' hl'
              rw [mem_PromAt_pred hWU hq] at this
              exact ⟨this.1, stepStore_AboveFW hst this.2⟩)
        · rw [PromAt_nword hWU hq]
          exact stepStore_NPnewF (V := V) hst (by simp [mth, regsOf]) hV
            (fun t ht => (List.mem_append.1 ht).elim (hP t) (fun h => hF t (FpAt_sub h))) hnd
            (fun t m ht hm hl => by
              obtain ⟨a1, a2⟩ := hU0 t m ht hm hl
              refine ⟨a1, fun t' m' hlt hm' hl' => ?_⟩
              have := a2 t' m' hlt hm' hl'
              rw [PromAt_nword hWU hq] at this; exact this)
      obtain ⟨vals', hW', hL'⟩ := storeUnits_NPnew us ws (i + 1)
        { s with mem := mem', vs := th.vs, promises := th.promises } s' V hs
        (by show V ≤ th.vs.vRelSt; rw [hrs]; exact hV)
        (fun t ht => Nat.lt_of_lt_of_le (hP t (hpsub t ht)) hsz) (fun t ht => Nat.lt_of_lt_of_le (hF t ht) hsz) hl
        ((stepStore_promSubl hst).1.nodup hnd)
        (fun j hj => stepStore_untorn rfl hst (hne j) (by
          have := hU (j + 1) (by omega)
          rwa [show i + (j + 1) = i + 1 + j by omega] at this))
      have h0' := storeUnits_NPkeep us ws (i + 1) _ s' hs (offs a i) x0 (fun j _ e => hne j e.symm) h0
      refine ⟨x0 :: vals', ⟨hb, hW'⟩, fun j x hj => ?_⟩
      cases j with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; simpa using h0'
      | succ j =>
          have := hL' j x (by simpa using hj)
          rwa [show i + 1 + j = i + (j + 1) by omega] at this
  | .two :: us, w0 :: w1 :: ws, i, s, s', V, hs, hV, hP, hF, hl, hnd, hU => by
      simp only [storeUnits] at hs
      rw [TermMem.nWords_two] at hl hU
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have e0 : exprVal (mth s pw w0 w1) (dataE 1 w0) = w0.val :=
        exprVal_dataE _ 1 w0 (by simp [mth, regsOf])
      have e1 : exprVal (mth s pw w0 w1) (dataE 2 w1) = w1.val :=
        exprVal_dataE _ 2 w1 (by simp [mth, regsOf])
      have hV0 : V ≤ max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel) :=
        Nat.le_trans hV (Nat.le_trans (storeMview_relSt (mth s pw w0 w1) _ [0] rel) (Nat.le_max_left _ _))
      have hw0 : WLe1 (bumpW V w0) ⟨w0.val, max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel), 0⟩ :=
        WLe1_msgB (WLe1_refl _) (fun x g hx =>
          Nat.le_trans (storeMview_dataE _ 1 w0 (by simp [mth, regsOf]) [0] rel x g hx) (Nat.le_max_left _ _)) hV0
      have hw1 : WLe1 (bumpW V w1) ⟨w1.val, max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel), 0⟩ :=
        WLe1_msgB (WLe1_refl _) (fun x g hx =>
          Nat.le_trans (storeMview_dataE _ 2 w1 (by simp [mth, regsOf]) [0] rel x g hx) (Nat.le_max_right _ _)) hV0
      obtain ⟨q1, _, _, q4, q5⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q1 q4 q5 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q4 q5 hs
      rw [e0, e1] at q1
      generalize max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel) = mv at q1 hw0 hw1
      have en : (offs a i).next = offs a (i + 1) := by simp [offs, WeakMem.Address.next, Nat.add_assoc]
      have hnx : (offs a i).next ≠ offs a i := WeakMem.Address.next_ne _
      have hne : ∀ j, offs a (i + 2 + j) ≠ offs a i := fun j e => by
        have := congrArg WeakMem.Address.offset e; simp [offs] at this; omega
      have hne1 : ∀ j, offs a (i + 2 + j) ≠ (offs a i).next := fun j e => by
        rw [en] at e; have := congrArg WeakMem.Address.offset e; simp [offs] at this; omega
      have hP0 : ∀ t, t ∈ (mth s pw w0 w1).promises → t < s.mem.size := hP
      have hPt : ∀ (Q : List Ts) t, (∀ t, t ∈ Q → t ∈ th.promises ∨ t ∈ E.fp) → t ∈ Q → t < s.mem.size :=
        fun Q t hQ ht => by
          rcases hQ t ht with h | h
          · rw [q4] at h; exact hP0 t h
          · exact hF t h
      have h0 : ∀ Q : List Ts, (∀ t, t ∈ Q → t ∈ th.promises ∨ t ∈ E.fp) →
          LatestNP mem' Q (offs a i) (mw ⟨offs a i, w0.val, mv⟩) := fun Q hQ => by
        rw [q1]
        exact LatestNP_push_other (LatestNP_push_top ⟨offs a i, w0.val, mv⟩ (fun t ht => hPt Q t hQ ht)) hnx
      have h1 : ∀ Q : List Ts, (∀ t, t ∈ Q → t ∈ th.promises ∨ t ∈ E.fp) →
          LatestNP mem' Q (offs a i).next (mw ⟨(offs a i).next, w1.val, mv⟩) := fun Q hQ => by
        rw [q1]
        exact LatestNP_push_top ⟨(offs a i).next, w1.val, mv⟩
          (fun t ht => by rw [Array.size_push]; exact Nat.lt_succ_of_lt (hPt Q t hQ ht))
      have hsz : s.mem.size ≤ mem'.size := by rw [q1, Array.size_push, Array.size_push]; omega
      obtain ⟨vals', hW', hL'⟩ := storeUnits_NPnew us ws (i + 2)
        { s with mem := mem', pairs := pairs', vs := th.vs, promises := th.promises } s' V hs
        (by show V ≤ th.vs.vRelSt; rw [q5]; exact hV)
        (fun t ht => by
          have ht' : t ∈ s.promises := by have := ht; simp only at this; rw [q4] at this; exact this
          exact Nat.lt_of_lt_of_le (hP t ht') hsz) (fun t ht => Nat.lt_of_lt_of_le (hF t ht) hsz) hl
        (by show th.promises.Nodup; rw [q4]; exact hnd)
        (fun j hj => by
          have hU2 := hU (j + 2) (by omega)
          rw [show i + (j + 2) = i + 2 + j by omega] at hU2
          refine UntornU_mono (fun t m hm hl => ?_) (fun t ht => ?_) (fun t m ht hm hl => ?_) hU2
            (fun t h0 => by
              show AboveFW mem' _ t
              rw [q1]; exact AboveFW_pushM _ (AboveFW_pushM _ h0))
          · have hm' : mem'[t]? = some m := hm
            rw [q1, Array.getElem?_push] at hm'
            by_cases f1 : t = (s.mem.push ⟨offs a i, w0.val, mv⟩).size
            · rw [ite_eq_left f1, Option.some.injEq] at hm'; subst hm'; exact absurd hl (hne1 j).symm
            · rw [ite_eq_right f1, Array.getElem?_push] at hm'
              by_cases f2 : t = s.mem.size
              · rw [ite_eq_left f2, Option.some.injEq] at hm'; subst hm'; exact absurd hl (hne j).symm
              · rw [ite_eq_right f2] at hm'; exact hm'
          · have ht' : t ∈ th.promises := ht
            rw [q4] at ht'; exact ht'
          · show t ∈ th.promises
            rw [q4]; exact ht)
      have h0' := storeUnits_NPkeep (E := E) us ws (i + 2) _ s' hs (offs a i) _ (fun j _ e => hne j e.symm)
        (h0 _ (fun t ht => PromAt_sub ht))
      have h1' := storeUnits_NPkeep (E := E) us ws (i + 2) _ s' hs (offs a i).next _ (fun j _ e => hne1 j e.symm)
        (h1 _ (fun t ht => PromAt_sub ht))
      refine ⟨mw ⟨offs a i, w0.val, mv⟩ :: mw ⟨(offs a i).next, w1.val, mv⟩ :: vals', ⟨hw0, hw1, hW'⟩,
        fun j x hj => ?_⟩
      match j, hj with
      | 0, hj => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; simpa using h0'
      | 1, hj =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
          rw [← en]; exact h1'
      | j + 2, hj =>
          have := hL' j x (by simpa using hj)
          rwa [show i + 2 + j = i + (j + 2) by omega] at this
  | .one :: _, [], _, _, s', _, hs, _, _, _, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', _, hs, _, _, _, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', _, hs, _, _, _, _, _, _ => by simp [storeUnits] at hs

end TermStep

namespace TermPiece
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Funding the plant credits a store overtakes -/

/-- An entry of a store's drop list: the old words `ws` of the piece `S` at
word `b` of cell `l`, holding `R`. -/
structure GdE where
  l : AllocLabel
  b : Nat
  S : Ty
  ws : List Word
  R : Res
  /-- (§11) the words whose latest-ness the entry records -/
  L : Nat → Bool := fun _ => true

/-- The piece a drop entry names. -/
def GdE.key (g : GdE) : AllocLabel × Nat × Ty := (g.l, g.b, g.S)

/-- A drop entry is OK at `E`, `s`: a piece of another thread's cell with a
frontier, `ws` its latest (skipped-promise-free) words, holding `R`. -/
def GdOK (E : TEnv) (s : St) (g : GdE) : Prop :=
  ∃ c, E.sto g.l = some c ∧ c.owner ≠ some E.tid ∧ E.pfr g.l ≠ none ∧ Piece c.ty g.b g.S ∧
    wc g.S = some g.ws.length ∧
    (∀ j w, g.L j = true → g.ws[j]? = some w → LatestNP s.mem (PromAt E s ⟨g.l, g.b + j⟩) ⟨g.l, g.b + j⟩ w) ∧
    ValOfR E g.S g.ws g.R

/-- **A store's drop list**: OK entries at distinct pieces. -/
def Drop (E : TEnv) (s : St) (Gd : List GdE) : Prop :=
  (∀ g ∈ Gd, GdOK E s g) ∧ (Gd.map GdE.key).Nodup

theorem Drop_nil {E : TEnv} {s : St} : Drop E s [] := ⟨fun _ h => (by cases h), List.nodup_nil⟩

/-- **Coverage** of a drop list for a store to `n` words at `⟨l, o⟩`: when
the target units are untorn, every piece of another thread's cell meeting a
foreign promise in the target is in the list. -/
def GdCov (E : TEnv) (s : St) (Gd : List GdE) (l : AllocLabel) (o n : Nat) : Prop :=
  (∀ j, j < n → UntornU E s ⟨l, o + j⟩) →
    ∀ (c : Cell) (b : Nat) (S : Ty) (vs : List Acc) (t : Ts) (m : Msg), E.sto l = some c →
      c.owner ≠ some E.tid → Piece c.ty b S → accs S = some vs → t ∈ E.fp → s.mem[t]? = some m →
      m.loc.label = l → b ≤ m.loc.offset → b + nWords vs > m.loc.offset → o ≤ m.loc.offset →
      o + n > m.loc.offset → ∃ g ∈ Gd, g.l = l ∧ g.b = b ∧ g.S = S

theorem GdCov_nil {E : TEnv} {s : St} {l : AllocLabel} {o n : Nat} {Gd : List GdE}
    (h : ¬ ∀ j, j < n → UntornU E s ⟨l, o + j⟩) : GdCov E s Gd l o n := fun hu => absurd hu h

theorem GdCov_own {E : TEnv} {s : St} {l : AllocLabel} {o n : Nat} {c : Cell} (hsto : E.sto l = some c)
    (hown : c.owner = some E.tid) (Gd : List GdE) : GdCov E s Gd l o n :=
  fun _ c' _ _ _ _ _ hc' ho' => by rw [hsto] at hc'; cases hc'; exact absurd hown ho'

/-- **Unconditional coverage** of a drop list for a store to `n` words at
`⟨l, o⟩`: `GdCov` without the untorn antecedent. -/
def GdCovU (E : TEnv) (s : St) (Gd : List GdE) (l : AllocLabel) (o n : Nat) : Prop :=
  ∀ (c : Cell) (b : Nat) (S : Ty) (vs : List Acc) (t : Ts) (m : Msg), E.sto l = some c →
    c.owner ≠ some E.tid → Piece c.ty b S → accs S = some vs → t ∈ E.fp → s.mem[t]? = some m →
    m.loc.label = l → b ≤ m.loc.offset → b + nWords vs > m.loc.offset → o ≤ m.loc.offset →
    o + n > m.loc.offset → ∃ g ∈ Gd, g.l = l ∧ g.b = b ∧ g.S = S

theorem GdCovU.toCov {E : TEnv} {s : St} {Gd : List GdE} {l : AllocLabel} {o n : Nat}
    (h : GdCovU E s Gd l o n) : GdCov E s Gd l o n := fun _ => h

theorem GdCovU_own {E : TEnv} {s : St} {l : AllocLabel} {o n : Nat} {c : Cell} (hsto : E.sto l = some c)
    (hown : c.owner = some E.tid) (Gd : List GdE) : GdCovU E s Gd l o n :=
  fun c' _ _ _ _ _ hc' ho' => by rw [hsto] at hc'; cases hc'; exact absurd hown ho'

/-! ### (option 3) Coverage on a word mask -/

/-- (option 3) **The store's word mask is exact off the mask**: a target word whose mask bit is
off gets no newly visible message. -/
def GdLT0 (E : TEnv) (s s' : St) (l : AllocLabel) (o n : Nat) (L0 : Nat → Bool) : Prop :=
  ∀ k, k < n → L0 k = false → TermNPmixW.NoNewVis E s s' ⟨l, o + k⟩

theorem GdLT0_true {E : TEnv} {s s' : St} {l : AllocLabel} {o n : Nat} : GdLT0 E s s' l o n (fun _ => true) :=
  fun _ _ h => Bool.noConfusion h

/-- (option 3) `GdCovU` on the units of a word mask `L0`. -/
def GdCovUL (E : TEnv) (s : St) (Gd : List GdE) (l : AllocLabel) (o n : Nat) (L0 : Nat → Bool) : Prop :=
  ∀ (c : Cell) (b : Nat) (S : Ty) (vs : List Acc) (t : Ts) (m : Msg), E.sto l = some c →
    c.owner ≠ some E.tid → Piece c.ty b S → accs S = some vs → t ∈ E.fp → s.mem[t]? = some m →
    m.loc.label = l → b ≤ m.loc.offset → b + nWords vs > m.loc.offset → o ≤ m.loc.offset →
    o + n > m.loc.offset → L0 (m.loc.offset - o) = true → ∃ g ∈ Gd, g.l = l ∧ g.b = b ∧ g.S = S

theorem GdCovU.toL {E : TEnv} {s : St} {Gd : List GdE} {l : AllocLabel} {o n : Nat}
    (h : GdCovU E s Gd l o n) (L0 : Nat → Bool) : GdCovUL E s Gd l o n L0 :=
  fun c b S vs t m a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 _ => h c b S vs t m a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11

theorem GdCovUL_true {E : TEnv} {s : St} {Gd : List GdE} {l : AllocLabel} {o n : Nat}
    (h : GdCovUL E s Gd l o n (fun _ => true)) : GdCovU E s Gd l o n :=
  fun c b S vs t m a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 => h c b S vs t m a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 rfl

theorem GdCovUL_own {E : TEnv} {s : St} {l : AllocLabel} {o n : Nat} {c : Cell} (hsto : E.sto l = some c)
    (hown : c.owner = some E.tid) (Gd : List GdE) (L0 : Nat → Bool) : GdCovUL E s Gd l o n L0 :=
  (GdCovU_own hsto hown Gd).toL L0

/-- **The drop list's latest-ness mask is exact on the target**: a target word of an entry
whose mask is off (the store kept the old words there) has no newly visible message. -/
def GdLT (E : TEnv) (s s' : St) (Gd : List GdE) (l : AllocLabel) (o n : Nat) : Prop :=
  ∀ g ∈ Gd, ∀ k, g.l = l → g.b ≤ k → o ≤ k → k < o + n → g.L (k - g.b) = false →
    TermNPmixW.NoNewVis E s s' ⟨l, k⟩

theorem GdLT_nil {E : TEnv} {s s' : St} {l : AllocLabel} {o n : Nat} : GdLT E s s' [] l o n :=
  fun _ hg => by cases hg

/-- `GdLT` from a mask shifted from a word mask `L0` on the target. -/
theorem GdLT_of {E : TEnv} {s s' : St} {Gd : List GdE} {l : AllocLabel} {o n : Nat} {L0 : Nat → Bool}
    (hG : ∀ g ∈ Gd, g.l = l ∧ o ≤ g.b ∧ ∀ j, g.L j = L0 (g.b - o + j))
    (hL0 : ∀ k, k < n → L0 k = false → TermNPmixW.NoNewVis E s s' ⟨l, o + k⟩) : GdLT E s s' Gd l o n := by
  intro g hg k _ hb hk1 hk2 hf
  obtain ⟨-, hob, hL⟩ := hG g hg
  rw [hL, show g.b - o + (k - g.b) = k - o by omega] at hf
  have := hL0 (k - o) (by omega) hf
  rwa [show o + (k - o) = k by omega] at this

/-- **The footprint of a store to `n` words at `⟨l, o⟩`**: old messages are
unchanged, new messages lie in the target, and own promises outside the target
stay outstanding. -/
def TgtFoot (s s' : St) (l : AllocLabel) (o n : Nat) : Prop :=
  (∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) ∧
  (∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
    m.loc.label = l ∧ o ≤ m.loc.offset ∧ o + n > m.loc.offset) ∧
  (∀ (t : Ts) (m : Msg), t ∈ s.promises → s.mem[t]? = some m →
    ¬ (m.loc.label = l ∧ o ≤ m.loc.offset ∧ o + n > m.loc.offset) → t ∈ s'.promises)

/-- **The target of a store term**: `n` words at `⟨l, o⟩`, as evaluated. -/
def TgtSyn (th : TTh) (l : AllocLabel) (o n : Nat) : Prop :=
  ∃ x rel a v tok e rt ru pw ad us, th.term = .let_ x (.store rel a v tok) e ∧
    evalAt th.env a = some (rt, [pw]) ∧ pw.val = .loc ad 0 ∧ (∃ μ, rt = .ptr μ ru ∨ rt = .loc μ ru) ∧
    accs ru = some us ∧ l = ad.label ∧ o = ad.offset ∧ n = nWords us

/-- **Coverage export** of a `pub` store step: its target, footprint, and the
drop list's coverage of that target; the coverage is unconditional
(`GdCovU`, which gives `GdCov` by `GdCovU.toCov`); (option 3) on the units of a word mask
`L0` (`GdCovUL`), off which the store makes nothing newly visible (`GdLT0`). -/
def GdCovT (E : TEnv) (s s' : St) (Gd : List GdE) (th : TTh) : Prop :=
  ∃ l o n L0, TgtSyn th l o n ∧ TgtFoot s s' l o n ∧ GdCovUL E s Gd l o n L0 ∧ GdLT E s s' Gd l o n ∧
    GdLT0 E s s' l o n L0

/-- A `pub` store at a non-word reference (the steps `tstepMCF_stepG` covers). -/
def PubShape (cx : Cx) (th : TTh) : Prop :=
  ∃ x rel a v tok e u, th.term = .let_ x (.store rel a v tok) e ∧
    ((cx.peek a = .ok (.ptr .pub u) ∧ wordOf (Ty.ptr .pub u) = none) ∨
      (cx.peek a = .ok (.loc .pub u) ∧ wordOf (Ty.loc .pub u) = none))

theorem TgtFoot_of_units {k : Promises.Knobs} {arch : Arch} {pw : Word} {ad : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {s s' : St} (hs : s' ∈ storeUnits k arch pw ad rel us ws 0 s) :
    TgtFoot s s' ad.label ad.offset (nWords us) := by
  obtain ⟨u1, u2, -, u4⟩ := storeUnits_untouched us ws 0 s s' hs
  refine ⟨u1, fun t m ht hm => ?_, fun t m ht hm hn => u4 t m ht hm fun j hj he => hn ?_⟩
  · obtain ⟨j, hj, he⟩ := u2 t m ht hm
    rw [he]; simp only [offs, Nat.zero_add]; refine ⟨trivial, ?_, ?_⟩ <;> simp only [WeakMem.Offset] <;> omega
  · rw [he]; simp only [offs, Nat.zero_add]; refine ⟨trivial, ?_, ?_⟩ <;> simp only [WeakMem.Offset] <;> omega

open Classical in
/-- A classical duplicate-free copy of a list. -/
noncomputable def dedupC {α : Type} : List α → List α
  | [] => []
  | a :: l => if a ∈ dedupC l then dedupC l else a :: dedupC l

theorem mem_dedupC {α : Type} {x : α} : ∀ {l : List α}, x ∈ dedupC l ↔ x ∈ l
  | [] => by simp [dedupC]
  | a :: l => by
      unfold dedupC
      split
      next h =>
        rw [mem_dedupC, List.mem_cons]
        exact ⟨Or.inr, fun h' => h'.elim (fun e => by subst e; exact mem_dedupC.1 h) id⟩
      next h => rw [List.mem_cons, List.mem_cons, mem_dedupC]

theorem nodup_dedupC {α : Type} : ∀ (l : List α), (dedupC l).Nodup
  | [] => by simp [dedupC]
  | a :: l => by
      unfold dedupC
      split
      next => exact nodup_dedupC l
      next h => exact List.nodup_cons.2 ⟨h, nodup_dedupC l⟩

theorem nodup_map_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
      obtain ⟨h1, h2⟩ := List.nodup_cons.1 h
      refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_map_of_inj hf h2⟩
      obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
      rw [hf _ _ e] at hb; exact h1 hb

/-- The pieces of `U` (at word `o` of cell `l`) meeting a promise `t`'s message. -/
def PcHit (s : St) (l : AllocLabel) (o : Nat) (U : Ty) (t : Ts) (p : Nat × Ty) : Prop :=
  Piece U p.1 p.2 ∧ ∃ m vs, s.mem[t]? = some m ∧ m.loc.label = l ∧ accs p.2 = some vs ∧
    o + p.1 ≤ m.loc.offset ∧ o + p.1 + nWords vs > m.loc.offset

open Classical in
/-- A piece of `U` meeting `t`'s message, if any. -/
noncomputable def pcAt (s : St) (l : AllocLabel) (o : Nat) (U : Ty) (t : Ts) : Option (Nat × Ty) :=
  if h : ∃ p, PcHit s l o U t p then some (Classical.choose h) else none

theorem pcAt_some {s : St} {l : AllocLabel} {o : Nat} {U : Ty} {t : Ts} {p : Nat × Ty}
    (h : pcAt s l o U t = some p) : PcHit s l o U t p := by
  unfold pcAt at h
  split at h
  next h' => cases h; exact Classical.choose_spec h'
  next => cases h

theorem pcAt_of {s : St} {l : AllocLabel} {o : Nat} {U : Ty} {t : Ts} {p : Nat × Ty}
    (hp : PcHit s l o U t p) : pcAt s l o U t = some p := by
  unfold pcAt
  split
  next h' =>
    have hq := Classical.choose_spec h'
    generalize Classical.choose h' = q at hq
    obtain ⟨hP, m, vs, hm, hl, hvs, h1, h2⟩ := hp
    obtain ⟨hQ, m', vs', hm', -, hvs', h1', h2'⟩ := hq
    rw [hm] at hm'; cases hm'
    rcases Piece_disj hP hQ hvs hvs' with ⟨e1, e2⟩ | h3 | h3
    · exact congrArg some (Prod.ext e1.symm e2.symm)
    · omega
    · omega
  next h' => exact absurd ⟨p, hp⟩ h'

/-! ## Natural-number sums over selections -/

theorem rsum_apply : ∀ (L : List Res) (k : Key), Res.sum L k = (L.map (fun R => R k)).sum
  | [], k => by simp [Res.sum]
  | R :: L, k => by rw [Res.sum_cons, Res.add_apply, rsum_apply L k]; simp

theorem nsum_add {α : Type} (f g : α → Nat) : ∀ (L : List α),
    (L.map (fun j => f j + g j)).sum = (L.map f).sum + (L.map g).sum
  | [] => rfl
  | a :: L => by simp only [List.map_cons, List.sum_cons, nsum_add f g L]; omega

theorem nsum_ite_zero {x r : Nat} : ∀ {L : List Nat}, x ∉ L → (L.map (fun j => if x = j then r else 0)).sum = 0
  | [], _ => rfl
  | j :: L, h => by
      have hne : x ≠ j := fun e => h (e ▸ List.mem_cons_self)
      have ih := nsum_ite_zero (x := x) (r := r) (L := L) (fun hm => h (List.mem_cons_of_mem _ hm))
      simp only [List.map_cons, List.sum_cons, hne, ite_false, ih]

theorem nsum_ite_le {x r : Nat} : ∀ {L : List Nat}, L.Nodup → (L.map (fun j => if x = j then r else 0)).sum ≤ r
  | [], _ => Nat.zero_le _
  | j :: L, h => by
      obtain ⟨h1, h2⟩ := List.nodup_cons.1 h
      simp only [List.map_cons, List.sum_cons]
      by_cases e : x = j
      · subst e
        rw [nsum_ite_zero h1]
        simp
      · simp only [e, ite_false, Nat.zero_add]
        exact nsum_ite_le h2

theorem nle_sum_of_mem {a : Nat} : ∀ {L : List Nat}, a ∈ L → a ≤ L.sum
  | [], h => by cases h
  | b :: L, h => by
      rw [List.sum_cons]
      rcases List.mem_cons.1 h with e | h'
      · subst e; omega
      · have := nle_sum_of_mem h'; omega

theorem nsum_const_zero {α : Type} : ∀ (L : List α), (L.map (fun _ => (0 : Nat))).sum = 0
  | [] => rfl
  | _ :: L => by rw [List.map_cons, List.sum_cons, nsum_const_zero L]

/-- The total share of the entries of `G` at word `j`. -/
def gsel (G : List ((Nat × Ty) × Res)) (j : Nat) : Res :=
  Res.sum ((G.filter (fun g => decide (g.1.1 = j))).map Prod.snd)

theorem nsum_gsel_le (k : Key) : ∀ (G : List ((Nat × Ty) × Res)) {Lx : List Nat}, Lx.Nodup →
    (Lx.map (fun j => ((G.filter (fun g => decide (g.1.1 = j))).map (fun g => g.2 k)).sum)).sum ≤
      (G.map (fun g => g.2 k)).sum
  | [], Lx, _ => by
      simp only [List.filter_nil, List.map_nil, List.sum_nil]
      exact Nat.le_of_eq (nsum_const_zero Lx)
  | x :: G, Lx, h => by
      have ih := nsum_gsel_le k G h
      have hx := nsum_ite_le (x := x.1.1) (r := x.2 k) h
      have e : ∀ j, (((x :: G).filter (fun g => decide (g.1.1 = j))).map (fun g => g.2 k)).sum =
          (if x.1.1 = j then x.2 k else 0) + ((G.filter (fun g => decide (g.1.1 = j))).map (fun g => g.2 k)).sum := by
        intro j
        by_cases e : x.1.1 = j
        · simp [e]
        · simp [e]
      rw [List.map_congr_left (fun j _ => e j), nsum_add]
      simp only [List.map_cons, List.sum_cons]
      omega

theorem gsel_sum_le (G : List ((Nat × Ty) × Res)) {Lx : List Nat} (h : Lx.Nodup) :
    Res.sum (Lx.map (gsel G)) ≤ Res.sum (G.map Prod.snd) := by
  refine Res.le_def.2 fun k => ?_
  rw [rsum_apply, rsum_apply, List.map_map, List.map_map]
  have e : ((fun R => R k) ∘ gsel G) =
      fun j => ((G.filter (fun g => decide (g.1.1 = j))).map (fun g => g.2 k)).sum := by
    funext j
    simp only [Function.comp, gsel, rsum_apply, List.map_map]
    rfl
  rw [e]
  exact nsum_gsel_le k G h

theorem le_gsel {G : List ((Nat × Ty) × Res)} {g : (Nat × Ty) × Res} {j : Nat} (hg : g ∈ G) (hj : g.1.1 = j) :
    g.2 ≤ gsel G j := by
  refine Res.le_def.2 fun k => ?_
  simp only [gsel]
  rw [rsum_apply, List.map_map]
  exact nle_sum_of_mem (List.mem_map.2 ⟨g, List.mem_filter.2 ⟨hg, by simp [hj]⟩, rfl⟩)

/-! ## The word arm -/

/-- (option 3) A protocol word's value holds at least what `wr` charges. -/
theorem wr_le_word {η : TEnv} {n : Nat} {P : Proto} {x : Word} {R : Res}
    (hv : VRR (fun _ => 0) η (.word (.lit n) P) (shp (.word (.lit n) P)) [x] R) : wr P n x.val ≤ R := by
  simp only [VRR, List.map_cons, List.map_nil, ev] at hv
  by_cases hw : WordHolds P [x.val]
  · rw [wr_holds hw]
    rcases hv.2 with ⟨-, e⟩ | ⟨hn, -⟩
    · rw [e]; exact Res.le_add_right _ _
    · exact absurd hw hn
  · rw [wr_nholds hw]; exact Res.zero_le _

theorem take_one_drop {q : List Word} {j : Nat} {x : Word} (h : q[j]? = some x) : (q.drop j).take 1 = [x] := by
  rw [List.take_one, List.head?_drop, h]
  rfl

theorem nodup_filterMap_fst {α : Type} {f : Nat → Option (Nat × α)} (hf : ∀ j p, f j = some p → p.1 = j) :
    ∀ {L : List Nat}, L.Nodup → (L.filterMap f).Nodup
  | [], _ => List.nodup_nil
  | j :: L, h => by
      obtain ⟨h1, h2⟩ := List.nodup_cons.1 h
      have ih := nodup_filterMap_fst hf h2
      rw [List.filterMap_cons]
      cases e : f j with
      | none => exact ih
      | some p =>
          refine List.nodup_cons.2 ⟨fun hm => ?_, ih⟩
          obtain ⟨j', hj', e'⟩ := List.mem_filterMap.1 hm
          have := hf j' p e'
          rw [hf j p e] at this
          exact h1 (this ▸ hj')

/-! ## The carve: drop pieces plus single-word shares -/

open Classical in
/-- The word piece at word `j` of the component at `ad`, if `j` is a protocol word. -/
noncomputable def wpc (E : TEnv) (ad : Address) (j : Nat) : Option (Nat × Ty) :=
  if h : ∃ q : Nat × Proto, WordAt E (offs ad j) q.1 q.2 then
    some (j, .word (.lit (Classical.choose h).1) (Classical.choose h).2)
  else none

theorem wpc_some {E : TEnv} {ad : Address} {j : Nat} {p : Nat × Ty} (h : wpc E ad j = some p) :
    p.1 = j ∧ ∃ n P, p.2 = .word (.lit n) P ∧ WordAt E (offs ad j) n P := by
  unfold wpc at h
  split at h
  next h' =>
    cases h
    exact ⟨rfl, _, _, rfl, Classical.choose_spec h'⟩
  next => cases h

theorem wpc_of {E : TEnv} {ad : Address} {j n : Nat} {P : Proto} (hw : WordAt E (offs ad j) n P) :
    wpc E ad j = some (j, .word (.lit n) P) := by
  unfold wpc
  split
  next h' =>
    obtain ⟨e1, e2⟩ := WordAt_uniq (Classical.choose_spec h') hw
    rw [e1, e2]
  next h' => exact absurd ⟨(n, P), hw⟩ h'

/-- A protocol word unit inside a component is a piece of it. -/
theorem piece_word {E : TEnv} {ad : Address} {c : Cell} {U : Ty} {us : List Acc} {j n : Nat} {P : Proto}
    (hsto : E.sto ad.label = some c) (hat : AtOff c.ty ad.offset U) (hus : accs U = some us)
    (hj : j < nWords us) (hw : WordAt E (offs ad j) n P) : Piece U j (.word (.lit n) P) := by
  obtain ⟨c', hc', hat', hg⟩ := hw
  have hc'' : E.sto ad.label = some c' := hc'
  rw [hsto] at hc''; cases hc''
  have hvs : accs (Ty.word (.lit n) P) = some [Acc.one] := by simp [accs, hg]
  have hS : Solid (Ty.word (.lit n) P) := by refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp
  have hP : Piece c.ty (ad.offset + j) (.word (.lit n) P) :=
    ⟨hat', hS, by rw [wc_of_accs hvs]; simp [nWords, Acc.size]⟩
  have h1 : nWords [Acc.one] = 1 := rfl
  obtain ⟨-, -, hPU⟩ := Piece_sub hat hus hP hvs (by rw [h1]; omega) (by omega)
  rwa [Nat.add_sub_cancel_left] at hPU

/-- **(option 3) The carve with word shares**: a value `q` of a component `U` (at `ad` of a cell)
holding `R` splits over a nodup piece family `L` of `U` and the single-word pieces of a nodup
word list `Lx` (disjoint from `L`), with the word shares `Gx` paying what each word's `wr` charges. -/
theorem vrr_carveX (E' : TEnv) {ad : Address} {c : Cell} {U : Ty} {us : List Acc} {q : List Word} {R : Res}
    (hsto : E'.sto ad.label = some c) (hat : AtOff c.ty ad.offset U) (hus : accs U = some us)
    (hv : VRR (fun _ => 0) (CE E') U (shp U) q R) (hwq : q.length = nWords us)
    {L : List (Nat × Ty)} (hL : ∀ p ∈ L, Piece U p.1 p.2) (hnd : L.Nodup)
    {Lx : List Nat} (hLxnd : Lx.Nodup) (hLx : ∀ j ∈ Lx, j < nWords us)
    (hdis : ∀ j ∈ Lx, ∀ n P, WordAt E' (offs ad j) n P → (j, Ty.word (.lit n) P) ∉ L) :
    ∃ G : List ((Nat × Ty) × Res), G.map Prod.fst = L ∧ (∀ g ∈ G, PcR (fun _ => 0) E' q g) ∧
      ∃ Gx : Nat → Res, Res.sum (G.map Prod.snd) + Res.sum (Lx.map Gx) ≤ R ∧
        ∀ j ∈ Lx, ∀ n P x, WordAt E' (offs ad j) n P → q[j]? = some x → wr P n x.val ≤ Gx j := by
  let Lw := Lx.filterMap (wpc E' ad)
  have hLw : ∀ p ∈ Lw, ∃ j ∈ Lx, p.1 = j ∧ ∃ n P, p.2 = .word (.lit n) P ∧ WordAt E' (offs ad j) n P :=
    fun p hp => by
      obtain ⟨j, hj, e⟩ := List.mem_filterMap.1 hp
      exact ⟨j, hj, wpc_some e⟩
  have hLwP : ∀ p ∈ Lw, Piece U p.1 p.2 := fun p hp => by
    obtain ⟨j, hj, e1, n, P, e2, hw⟩ := hLw p hp
    rw [e1, e2]
    exact piece_word hsto hat hus (hLx j hj) hw
  have hndw : Lw.Nodup := nodup_filterMap_fst (fun j p e => (wpc_some e).1) hLxnd
  have hnd2 : (L ++ Lw).Nodup := List.nodup_append.2 ⟨hnd, hndw, fun a ha b hb e => by
    subst e
    obtain ⟨j, hj, e1, n, P, e2, hw⟩ := hLw a hb
    have ha' : (j, Ty.word (.lit n) P) ∈ L := by
      have : a = (j, Ty.word (.lit n) P) := Prod.ext e1 e2
      rw [← this]; exact ha
    exact hdis j hj n P hw ha'⟩
  have hT : accs U ≠ none := by rw [hus]; simp
  have hwc : wc U = some q.length := by rw [wc_of_accs hus, hwq]
  obtain ⟨G, eG, Rr, hR, hG⟩ := VRR_pieces E' hT (fun p hp => (List.mem_append.1 hp).elim (hL p) (hLwP p))
    hnd2 hv hwc
  obtain ⟨G1, G2, rfl, e1, e2⟩ := List.map_eq_append_iff.1 eG
  refine ⟨G1, e1, fun g hg => hG g (List.mem_append_left _ hg), gsel G2, ?_, ?_⟩
  · have h2 := gsel_sum_le G2 hLxnd
    rw [hR, List.map_append, Res.sum_append]
    refine Res.le_def.2 fun k => ?_
    have := Res.le_def.1 h2 k
    simp only [Res.add_apply]
    omega
  · intro j hj n P x hw hx
    have hm : (j, Ty.word (.lit n) P) ∈ Lw := List.mem_filterMap.2 ⟨j, hj, wpc_of hw⟩
    rw [← e2] at hm
    obtain ⟨g, hg, eg⟩ := List.mem_map.1 hm
    obtain ⟨n', hwn, -, hvn⟩ := hG g (List.mem_append_right _ hg)
    have hg1 : g.1.1 = j := by rw [eg]
    have hg2 : g.1.2 = Ty.word (.lit n) P := by rw [eg]
    obtain ⟨-, -, -, hgh⟩ := id hw
    have hn1 : n' = 1 := by
      rw [hg2] at hwn
      have : wc (Ty.word (.lit n) P) = some 1 := by simp [wc, accs, hgh, nWords, Acc.size]
      rw [this] at hwn; exact (Option.some.inj hwn).symm
    rw [hn1, hg1, hg2, take_one_drop hx] at hvn
    exact Res.le_trans (wr_le_word hvn) (le_gsel hg hg1)

#print axioms vrr_carveX

/-- **(option 3) `StoreLeafPay` holds at every component of every cell** (no premises): the
carve `vrr_carveX` with no drop pieces. -/
theorem storeLeafPay_of {η : TEnv} : StoreLeafPayAll (CE η) := by
  intro ad c U us hsto hat hus comp Rb Lx hnd hLx hcl hv
  obtain ⟨G, -, -, Gx, hle, hGx⟩ := vrr_carveX η hsto hat hus hv hcl (L := []) (fun _ h => by cases h)
    List.nodup_nil hnd hLx (fun _ _ _ _ _ h => by cases h)
  refine ⟨Gx, Res.le_trans ?_ hle, fun j hj n P x hw hx => hGx j hj n P x hw hx⟩
  exact Res.le_def.2 fun k => by simp only [Res.add_apply]; omega

#print axioms storeLeafPay_of

/-! ## Funding with word shares -/

open Classical in
/-- **(option 3) Funding with word shares**: `gd_fund` restricted to the mask `L0`, together with the
shares `Gx` of the single-word pieces at the words `Lx` (off the mask), jointly paid by `Rq`. -/
theorem gd_fundX {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o : Nat} {U : Ty} {us : List Acc}
    {q : List Word} {Rq : Res} (hsto : E.sto l = some c) (hown : c.owner ≠ some E.tid) (hpf : E.pfr l ≠ none)
    (hat : AtOff c.ty o U) (hus : accs U = some us) (hq : ValOfR E U q Rq) (hwq : wc U = some q.length)
    (L0 : Nat → Bool) (hL : ∀ j w, L0 j = true → q[j]? = some w → LatestNP s.mem (PromAt E s ⟨l, o + j⟩) ⟨l, o + j⟩ w)
    (Lx : List Nat) (hLxnd : Lx.Nodup) (hLx : ∀ j ∈ Lx, j < nWords us) (hLx0 : ∀ j ∈ Lx, L0 j = false) :
    ∃ (Gd : List GdE) (Gx : Nat → Res), Drop E s Gd ∧ Res.sum (Gd.map GdE.R) + Res.sum (Lx.map Gx) ≤ Rq ∧
      GdCovUL E s Gd l o (nWords us) L0 ∧ (∀ g ∈ Gd, g.l = l ∧ o ≤ g.b ∧ ∀ j, g.L j = L0 (g.b - o + j)) ∧
      ∀ j ∈ Lx, ∀ n P x, WordAt E ⟨l, o + j⟩ n P → q[j]? = some x → wr P n x.val ≤ Gx j := by
  let hit : Ts → Bool := fun t => decide (∃ m, s.mem[t]? = some m ∧ L0 (m.loc.offset - o) = true)
  let L := dedupC ((E.fp.filter hit).filterMap (pcAt s l o U))
  have hLp : ∀ p ∈ L, Piece U p.1 p.2 := fun p hp => by
    obtain ⟨t, -, ht⟩ := List.mem_filterMap.1 (mem_dedupC.1 hp)
    exact (pcAt_some ht).1
  have hwq' : q.length = nWords us := by
    rw [wc_of_accs hus] at hwq; exact (Option.some.inj hwq).symm
  have hdis : ∀ j ∈ Lx, ∀ n P, WordAt E.unsee (offs ⟨l, o⟩ j) n P → (j, Ty.word (.lit n) P) ∉ L := by
    intro j hj n P hw hm
    obtain ⟨t, ht, hpc⟩ := List.mem_filterMap.1 (mem_dedupC.1 hm)
    obtain ⟨-, m, vs, hm1, -, hvs, h1, h2⟩ := pcAt_some hpc
    obtain ⟨-, -, -, hgh⟩ := hw
    have hvs1 : vs = [Acc.one] := by
      have : accs (Ty.word (.lit n) P) = some [Acc.one] := by simp [accs, hgh]
      rw [this] at hvs; exact (Option.some.inj hvs).symm
    subst hvs1
    have h1' : nWords [Acc.one] = 1 := rfl
    simp only [h1'] at h2
    obtain ⟨m', hm', hL0⟩ := of_decide_eq_true (List.mem_filter.1 ht).2
    rw [hm1] at hm'; cases hm'
    have h1'' : o + j ≤ m.loc.offset := h1
    have h2'' : o + j + 1 > m.loc.offset := h2
    have e : m.loc.offset - o = j := by simp only [WeakMem.Offset] at h1'' h2'' ⊢; omega
    rw [e, hLx0 j hj] at hL0
    cases hL0
  obtain ⟨G, eG, hG, Gx, hle, hGx⟩ := vrr_carveX E.unsee (ad := ⟨l, o⟩) hsto hat hus hq.1 hwq' hLp
    (nodup_dedupC _) hLxnd hLx hdis
  let f : (Nat × Ty) × Res → GdE := fun g => ⟨l, o + g.1.1, g.1.2, (q.drop g.1.1).take ((wc g.1.2).getD 0), g.2, fun j => L0 (g.1.1 + j)⟩
  have hk : (G.map f).map GdE.key = L.map (fun p => (l, o + p.1, p.2)) := by
    rw [← eG, List.map_map, List.map_map]; rfl
  refine ⟨G.map f, Gx, ⟨fun g hg => ?_, ?_⟩, ?_, fun c' b S vs t m hc' ho' hP hvs ht hm hl h1 h2 h3 h4 hL0 => ?_,
    fun g hg => ?_, fun j hj n P x hw hx => hGx j hj n P x hw hx⟩
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨n, hwn, hle, hvn⟩ := hG g0 hg0
    have hP : Piece U g0.1.1 g0.1.2 := hLp _ (by rw [← eG]; exact List.mem_map_of_mem hg0)
    have hgl : ((q.drop g0.1.1).take n).length = n := by simp; omega
    refine ⟨c, hsto, hown, hpf, Piece_lift hat hP, ?_, fun j w hLj hj => ?_, ?_⟩
    · show wc g0.1.2 = some ((q.drop g0.1.1).take ((wc g0.1.2).getD 0)).length
      rw [hwn, Option.getD_some, hgl]
    · have hj' : ((q.drop g0.1.1).take n)[j]? = some w := by
        have := hj; simp only [f, hwn, Option.getD_some] at this; exact this
      have hjn : j < n := by
        rcases Nat.lt_or_ge j n with hc | hc
        · exact hc
        · rw [List.getElem?_eq_none (by rw [hgl]; omega)] at hj'; cases hj'
      rw [List.getElem?_take_of_lt hjn, List.getElem?_drop] at hj'
      have := hL _ w hLj hj'
      show LatestNP s.mem (PromAt E s ⟨l, o + g0.1.1 + j⟩) ⟨l, o + g0.1.1 + j⟩ w
      rwa [Nat.add_assoc]
    · show ValOfR E g0.1.2 ((q.drop g0.1.1).take ((wc g0.1.2).getD 0)) g0.2
      rw [hwn, Option.getD_some]
      exact ⟨hvn, Valid_at hP.1 (by rw [hus]; simp) hq.2 hwq n hwn⟩
  · rw [hk]
    refine nodup_map_of_inj (fun p p' e => ?_) (nodup_dedupC _)
    simp only [Prod.mk.injEq] at e
    exact Prod.ext (by omega) e.2.2
  · have e1 : (G.map f).map GdE.R = G.map Prod.snd := by rw [List.map_map]; rfl
    rw [e1]
    exact hle
  · rw [hsto] at hc'; cases hc'
    have hm1 : o < b + nWords vs := by omega
    have hm2 : b < o + nWords us := by omega
    obtain ⟨hob, -, hPU⟩ := Piece_sub hat hus hP hvs hm1 hm2
    have hhit : PcHit s l o U t (b - o, S) :=
      ⟨hPU, m, vs, hm, hl, hvs, by simp only; omega, by simp only; omega⟩
    have hft : t ∈ E.fp.filter hit := List.mem_filter.2 ⟨ht, decide_eq_true ⟨m, hm, hL0⟩⟩
    have hmem : (b - o, S) ∈ L := mem_dedupC.2 (List.mem_filterMap.2 ⟨t, hft, pcAt_of hhit⟩)
    rw [← eG] at hmem
    obtain ⟨g0, hg0, e0⟩ := List.mem_map.1 hmem
    refine ⟨f g0, List.mem_map_of_mem hg0, rfl, ?_, ?_⟩
    · show o + g0.1.1 = b
      rw [e0]; simp only; omega
    · show g0.1.2 = S
      rw [e0]
  · obtain ⟨g0, -, rfl⟩ := List.mem_map.1 hg
    refine ⟨rfl, Nat.le_add_right _ _, fun j => ?_⟩
    show L0 (g0.1.1 + j) = L0 (o + g0.1.1 - o + j)
    rw [Nat.add_sub_cancel_left]

#print axioms gd_fundX

/-- ** Funding**: the old words `q` of a store target `U` (at word `o` of
another thread's cell `l` with a frontier), holding `Rq`, give a drop list of
the pieces of `U` meeting a foreign promise at a unit of the mask `L0`, holding at most
`Rq` together. (option 3) `gd_fundX` with no word shares (copy rule). -/
theorem gd_fund {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o : Nat} {U : Ty} {us : List Acc}
    {q : List Word} {Rq : Res} (hsto : E.sto l = some c) (hown : c.owner ≠ some E.tid) (hpf : E.pfr l ≠ none)
    (hat : AtOff c.ty o U) (hus : accs U = some us) (hq : ValOfR E U q Rq) (hwq : wc U = some q.length)
    (L0 : Nat → Bool) (hL : ∀ j w, L0 j = true → q[j]? = some w → LatestNP s.mem (PromAt E s ⟨l, o + j⟩) ⟨l, o + j⟩ w) :
    ∃ Gd : List GdE, Drop E s Gd ∧ Res.sum (Gd.map GdE.R) ≤ Rq ∧ GdCovUL E s Gd l o (nWords us) L0 ∧
      ∀ g ∈ Gd, g.l = l ∧ o ≤ g.b ∧ ∀ j, g.L j = L0 (g.b - o + j) := by
  obtain ⟨Gd, Gx, hD, hR, hC, hG, -⟩ := gd_fundX hsto hown hpf hat hus hq hwq L0 hL [] List.nodup_nil
    (fun _ h => by cases h) (fun _ h => by cases h)
  exact ⟨Gd, hD, Res.le_trans (Res.le_add_right _ _) hR, hC, hG⟩

end TermPiece

namespace TermTear
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound
open TermStep
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound

theorem nWords_take_succ_cons (u : Acc) (us : List Acc) (i : Nat) :
    nWords ((u :: us).take (i + 1)) = u.size + nWords (us.take i) := by
  rw [List.take_succ_cons, nWords_cons]

/-- (§11) A mix's word in access unit `i` is the selected side's. -/
theorem mixU_getElem : ∀ (us : List Acc) (sel : Nat → Bool) (ws1 ws2 : List Word) (i o : Nat),
    ws1.length = nWords us → ws2.length = nWords us → InAcc us i o →
    (mixU us sel ws1 ws2)[o]? = if sel i then ws1[o]? else ws2[o]?
  | [], _, _, _, i, o, _, _, h => by
      exfalso; obtain ⟨-, h2⟩ := h; simp [nWords] at h2
  | u :: us, sel, ws1, ws2, i, o, l1, l2, h => by
      rw [nWords_cons] at l1 l2
      have hal : (if sel 0 then ws1.take u.size else ws2.take u.size).length = u.size := by
        split <;> simp <;> omega
      simp only [mixU]
      match i, h with
      | 0, h =>
          obtain ⟨-, h2⟩ := h
          have h2' : o < u.size := by
            have := h2; rw [nWords_take_succ_cons] at this; simp [nWords] at this; omega
          rw [List.getElem?_append_left (by rw [hal]; exact h2')]
          split <;> rw [List.getElem?_take_of_lt h2']
      | i + 1, h =>
          obtain ⟨h1, h2⟩ := h
          rw [nWords_take_succ_cons] at h1 h2
          have hge : u.size ≤ o := by omega
          rw [List.getElem?_append_right (by rw [hal]; exact hge), hal]
          have ih := mixU_getElem us (fun i => sel (i + 1)) (ws1.drop u.size) (ws2.drop u.size) i (o - u.size)
            (by simp; omega) (by simp; omega) ⟨by omega, by omega⟩
          rw [ih]
          simp only [List.getElem?_drop, Nat.add_sub_cancel' hge]

end TermTear

namespace TermPiece
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## (OvW3 R2) Re-pin items at own fulfils: definitions

Relocated from `TermPlant` (which keeps aliases): the plant credit item `CrItem` and the
names it needs, the re-pin definitions, and the item lemmas; `CrKeysP`, `opAtomP`, `OpTgtP`
are copies of `TermPlant`'s `CrKeys`, `opAtom`, `OpTgt` (bridged there by `Iff.rfl`). -/

theorem lt_size_of_some {mem : Memory} {t : Ts} {m : Msg} (h : mem[t]? = some m) : t < mem.size := by
  apply Classical.byContradiction
  intro hn
  rw [Array.getElem?_eq_none (by (try simp only [WeakMem.Ts] at *); omega)] at h
  cases h

/-- **Pieces meeting at a unit coincide.** -/
theorem piece_match {T S S' : Ty} {b b' n n' x : Nat} (h : Piece T b S) (h' : Piece T b' S')
    (hw : wc S = some n) (hw' : wc S' = some n') (h1 : b ≤ x) (h2 : x < b + n) (h1' : b' ≤ x) (h2' : x < b' + n') :
    b = b' ∧ S = S' := by
  obtain ⟨us, hu⟩ := Piece_accs h
  obtain ⟨us', hu'⟩ := Piece_accs h'
  have e1 : n = nWords us := Option.some.inj (hw.symm.trans (wc_of_accs hu))
  have e2 : n' = nWords us' := Option.some.inj (hw'.symm.trans (wc_of_accs hu'))
  rcases Piece_disj h h' hu hu' with e | e | e
  · exact e
  · omega
  · omega

/-- (KeepPl) A sum over a list splits along a pointwise sum. -/
theorem sum_map_split {f g h : Ts → Res} (e : ∀ t, f t = g t + h t) :
    ∀ (L : List Ts), Res.sum (L.map f) = Res.sum (L.map g) + Res.sum (L.map h)
  | [] => Res.ext fun k => by simp
  | x :: L => Res.ext fun k => by
      have ih := congrArg (fun R : Res => R k) (sum_map_split e L)
      have ex := congrArg (fun R : Res => R k) (e x)
      simp only [List.map_cons, Res.sum_cons, Res.add_apply] at ih ex ⊢
      omega
#print axioms TermPiece.sum_map_split

/-- A plant credit carries no own-handle key (pub cells are `noOwnIn`).
Word and region keys are not excluded: `sharedOK` admits tokens behind `pub`. -/
def CrKeysP (R : Res) : Prop := ∀ l, R (.own l) = 0

theorem CrKeysP_zero : CrKeysP .zero := fun _ => rfl

/-- `tw` is the thread's lowest promise at `a`. -/
def LowOwn (s : St) (a : Address) (tw : Ts) : Prop :=
  tw ∈ s.promises ∧ (∃ m, s.mem[tw]? = some m ∧ m.loc = a) ∧
    ∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc = a → tw ≤ t'

theorem LowOwn_uniq {s : St} {a : Address} {t1 t2 : Ts} (h1 : LowOwn s a t1) (h2 : LowOwn s a t2) :
    t1 = t2 := by
  obtain ⟨m1, hm1, hl1⟩ := h1.2.1
  obtain ⟨m2, hm2, hl2⟩ := h2.2.1
  exact Nat.le_antisymm (h1.2.2 t2 m2 h2.1 hm2 hl2) (h2.2.2 t1 m1 h1.1 hm1 hl1)

/-- Unit `a` is overtaken above `tw`: a message there that memory's reading does not skip. -/
def OverT (E : TEnv) (s : St) (a : Address) (tw : Ts) : Prop :=
  ∃ t m, tw < t ∧ s.mem[t]? = some m ∧ m.loc = a ∧ t ∉ PromAt E s a

/-- A plant credit item `(th, q, S, ws, R0, K)` for cell `l` (type `c.ty`).  (plantOpG b)
Per item: at every unit `K` selects, the pinned word is the predecessor of the unit's lowest
own promise (no window bound; the credit's window stays inside the credit invariant). -/
def CrItem (E : TEnv) (s : St) (cr : Ts → Res) (l : AllocLabel) (c : Cell)
    (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) : Prop :=
  ∃ mh usS, s.mem[x.1]? = some mh ∧ mh.loc.label = l ∧ LowOwn s mh.loc x.1 ∧
    ¬ WordUnit E mh.loc ∧ AtOff c.ty x.2.1 x.2.2.1 ∧ Solid x.2.2.1 ∧ accs x.2.2.1 = some usS ∧
    x.2.1 ≤ mh.loc.offset ∧ mh.loc.offset < x.2.1 + nWords usS ∧
    x.2.2.2.1.length = nWords usS ∧ ValOfR E x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 ∧ x.2.2.2.2.1 ≤ cr x.1 ∧
    ∀ i o w tw', x.2.2.2.2.2 i = true → InAcc usS i o → x.2.2.2.1[o]? = some w →
      LowOwn s ⟨l, x.2.1 + o⟩ tw' → PredAt s.mem ⟨l, x.2.1 + o⟩ tw' w

/-- (switch) The address atom of an own-path op (`OwnOpT`). -/
def opAtomP : Expr → Option At
  | .let_ _ (.xchg a _) _ => some a
  | .let_ _ (.xchgAt b _ _) _ => some b
  | .let_ _ (.xchgAtF b _ _ _) _ => some b
  | .let_ _ (.stlw b _ _ _) _ => some b
  | .let_ _ (.stl b _ _) _ => some b
  | .let_ _ (.bufInit b _ _) _ => some b
  | .let_ _ (.store _ a _ _) _ => some a
  | _ => none

/-- (switch) **The op's target label**: the op's address atom evaluates to a
location of `lab`. -/
def OpTgtP (th : TTh) (lab : AllocLabel) : Prop :=
  ∃ q rt w ad off, opAtomP th.term = some q ∧ evalAt th.env q = some (rt, [w]) ∧ w.val = .loc ad off ∧
    ad.label = lab

/-- (OvW3 R2) A credit item `(holder, q, S, ws, R0, K)`. -/
abbrev CrIt := Ts × Nat × Ty × List Word × Res × (Nat → Bool)

/-- (OvW3 R2) The re-pin credit at `t`: the items of `RS` held by `t`. -/
noncomputable def rpSum (RS : List (AllocLabel × Cell × CrIt)) (t : Ts) : Res :=
  Res.sum ((RS.filter fun y => decide (y.2.2.1 = t)).map fun y => y.2.2.2.2.2.2.1)

/-- (OvW3 R2) Item `x` covers word `o` of its cell. -/
def CrCov (x : CrIt) (o : Nat) : Prop :=
  ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true

/-- (OvW3 R2) the `WinG` (window conditions (A)+(B) at bound `tw`), inlined. -/
def WinGI (E : TEnv) (s : St) (l : AllocLabel) (tw : Ts) : Prop :=
  (∀ t m, s.mem[t]? = some m → m.loc.label = l → t ≤ tw → t ∈ s.promises ∨ t ≤ s.vs.coh m.loc) ∧
  ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc.label = l → tw < t

/-- (OvW3 R2) **Re-pin items**: credit items at own frontier cells at the post-state, key-free,
held by the lowest own promise of their piece, with an own promise in the window at every
covered unit. -/
def RepinQ (E' : TEnv) (s' : St) (cr' : Ts → Res) (RS : List (AllocLabel × Cell × CrIt)) : Prop :=
  ∀ y ∈ RS, E'.sto y.1 = some y.2.1 ∧ y.2.1.owner = some E'.tid ∧ E'.pfr y.1 ≠ none ∧
    CrItem E' s' cr' y.1 y.2.1 y.2.2 ∧ CrKeysP y.2.2.2.2.2.2.1 ∧
    (∀ usS, accs y.2.2.2.2.1 = some usS → ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m →
      m.loc.label = y.1 → y.2.2.2.1 ≤ m.loc.offset → m.loc.offset < y.2.2.2.1 + nWords usS → y.2.2.1 ≤ t) ∧
    ∀ o, CrCov y.2.2 o → ∃ tw, LowOwn s' ⟨y.1, o⟩ tw ∧ WinGI E' s' y.1 tw

/-- (OvW3 R2) **Re-pin cover** at an atomic operation off a `bufInit` at its buffer's real count
`rc`: every unit, inside a solid piece, of the operation's own target cell whose lowest own
promise the step fulfilled, non-visible, overtaken at the post-state above the new lowest own
promise `tw` below every frontier promise, is covered by a re-pin item.
OPEN: bufInit CRITICAL at slot `rc` (KQ3WS-PL), pending the SlotPaySX design decision; the
exclusion is removed when it lands. -/
def RepinCov (E E' : TEnv) (s s' : St) (th : TTh) (RS : List (AllocLabel × Cell × CrIt)) : Prop :=
  ∀ lab, (∀ x b i v e, th.term = .let_ x (.bufInit b i v) e → ∀ rti wi n,
      evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → n ≠ E.rc lab) →
    OpTgtP th lab →
  ∀ c (o : Nat) th0 tw, E.sto lab = some c → c.owner = some E.tid → E.pfr lab ≠ none →
    ¬ VisU E ⟨lab, o⟩ → LowOwn s ⟨lab, o⟩ th0 → th0 ∉ s'.promises →
    LowOwn s' ⟨lab, o⟩ tw → OverT E' s' ⟨lab, o⟩ tw → WinGI E' s' lab tw →
    (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
    ∃ y ∈ RS, y.1 = lab ∧ CrCov y.2.2 o

/-- (OvW3 R2) The re-pin items' plant credits: each holder is a plant credit for any credit
covering its item's value. -/
def RepinPl (E' : TEnv) (s' : St) (RS : List (AllocLabel × Cell × CrIt)) : Prop :=
  ∀ y ∈ RS, ∃ m, s'.mem[y.2.2.1]? = some m ∧ ∀ R, y.2.2.2.2.2.2.1 ≤ R → PlantCr E' s' m y.2.2.1 R


theorem rpSum_nil (t : Ts) : rpSum [] t = .zero := rfl
#print axioms TermPiece.rpSum_nil

theorem rpSum_cons (y : AllocLabel × Cell × CrIt) (RS : List (AllocLabel × Cell × CrIt)) (t : Ts) :
    rpSum (y :: RS) t = (if y.2.2.1 = t then y.2.2.2.2.2.2.1 else .zero) + rpSum RS t := by
  unfold rpSum
  by_cases h : y.2.2.1 = t
  · simp [h]
  · simp [h]
#print axioms TermPiece.rpSum_cons

theorem rpSum_ge : ∀ {RS : List (AllocLabel × Cell × CrIt)} {y : AllocLabel × Cell × CrIt}, y ∈ RS →
    y.2.2.2.2.2.2.1 ≤ rpSum RS y.2.2.1
  | y' :: RS, y, h => by
      rw [rpSum_cons]
      rcases List.mem_cons.mp h with rfl | h
      · simp only [ite_true]; exact Res.le_add_right _ _
      · intro k
        have := rpSum_ge h k
        simp only [Res.add_apply]; omega
#print axioms TermPiece.rpSum_ge

theorem rpSum_none : ∀ {RS : List (AllocLabel × Cell × CrIt)} {t : Ts}, (∀ y ∈ RS, y.2.2.1 ≠ t) →
    rpSum RS t = .zero
  | [], _, _ => rfl
  | y :: RS, t, h => by
      rw [rpSum_cons, rpSum_none (fun y' hy' => h y' (List.mem_cons_of_mem _ hy'))]
      simp only [h y List.mem_cons_self, ite_false, Res.add_zero]
#print axioms TermPiece.rpSum_none

theorem crKeys_rpSum : ∀ {RS : List (AllocLabel × Cell × CrIt)} (t : Ts), (∀ y ∈ RS, CrKeysP y.2.2.2.2.2.2.1) →
    CrKeysP (rpSum RS t)
  | [], _, _ => CrKeysP_zero
  | y :: RS, t, h => by
      rw [rpSum_cons]
      intro l
      have h1 := crKeys_rpSum (RS := RS) t (fun y' hy' => h y' (List.mem_cons_of_mem _ hy')) l
      have h2 := h y List.mem_cons_self l
      simp only [Res.add_apply, h1]
      split
      · exact h2
      · rfl
#print axioms TermPiece.crKeys_rpSum

theorem sum_ite_out {x : Ts} {R : Res} : ∀ {L : List Ts}, x ∉ L →
    Res.sum (L.map fun t => if x = t then R else .zero) = .zero
  | [], _ => rfl
  | t :: L, h => by
      have hne : x ≠ t := fun e => h (e ▸ List.mem_cons_self)
      simp only [List.map_cons, Res.sum_cons, hne, ite_false,
        sum_ite_out (fun h' => h (List.mem_cons_of_mem _ h')), Res.zero_add]
#print axioms TermPiece.sum_ite_out

theorem sum_ite_le {x : Ts} {R : Res} : ∀ {L : List Ts}, L.Nodup →
    Res.sum (L.map fun t => if x = t then R else .zero) ≤ R
  | [], _ => Res.zero_le _
  | t :: L, hnd => by
      simp only [List.map_cons, Res.sum_cons]
      by_cases e : x = t
      · subst e
        rw [sum_ite_out (List.nodup_cons.mp hnd).1]
        simp only [ite_true, Res.add_zero]; exact Res.le_refl _
      · simp only [e, ite_false, Res.zero_add]; exact sum_ite_le (List.nodup_cons.mp hnd).2
#print axioms TermPiece.sum_ite_le

/-- (OvW3 R2) Over duplicate-free holders, the re-pin credits total at most the items'. -/
theorem sum_rpSum_le : ∀ (RS : List (AllocLabel × Cell × CrIt)) {L : List Ts}, L.Nodup →
    Res.sum (L.map (rpSum RS)) ≤ Res.sum (RS.map fun y => y.2.2.2.2.2.2.1)
  | [], L, _ => by
      have hz : ∀ L : List Ts, Res.sum (L.map (rpSum [])) = .zero := fun L => by
        induction L with
        | nil => rfl
        | cons _ _ ih => simp only [List.map_cons, Res.sum_cons, ih, rpSum_nil, Res.zero_add]
      rw [hz L]; exact Res.zero_le _
  | y :: RS, L, hnd => by
      have e := sum_map_split (rpSum_cons y RS) L
      rw [e]
      have h1 := sum_ite_le (x := y.2.2.1) (R := y.2.2.2.2.2.2.1) hnd
      have h2 := sum_rpSum_le RS hnd
      intro k
      have a1 := h1 k; have a2 := h2 k
      simp only [List.map_cons, Res.sum_cons, Res.add_apply] at a1 a2 ⊢
      omega
#print axioms TermPiece.sum_rpSum_le

theorem CrItem_mono {E : TEnv} {s : St} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell} {x : CrIt}
    (hle : ∀ t, cr t ≤ cr' t) (h : CrItem E s cr l c x) : CrItem E s cr' l c x := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  exact ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, Res.le_trans a12 (hle _), a13⟩
#print axioms TermPiece.CrItem_mono

theorem RepinQ_mono {E' : TEnv} {s' : St} {cr cr' : Ts → Res} {RS : List (AllocLabel × Cell × CrIt)}
    (hle : ∀ t, cr t ≤ cr' t) (h : RepinQ E' s' cr RS) : RepinQ E' s' cr' RS := fun y hy =>
  let ⟨a1, a2, a3, a4, a5⟩ := h y hy
  ⟨a1, a2, a3, CrItem_mono hle a4, a5⟩
#print axioms TermPiece.RepinQ_mono

/-- (OvW3 R2) At a `bufInit` at its buffer's real count the re-pin cover holds with any items
(the OPEN exclusion, KQ3WS-PL). -/
theorem RepinCov_biP {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    (h : ∃ x b i v e rti wi n, th.term = .let_ x (.bufInit b i v) e ∧ evalAt th.env i = some (rti, [wi]) ∧
      numOf [wi] = some n ∧ ∀ lab, OpTgtP th lab → n = E.rc lab) : RepinCov E E' s s' th RS := by
  intro lab hx hot
  obtain ⟨x, b, i, v, e, rti, wi, n, ht, hei, hn, heq⟩ := h
  exact absurd (heq lab hot) (hx x b i v e ht rti wi n hei hn)
#print axioms TermPiece.RepinCov_biP

/-- (OvW3 R2b) Off atomic operations the re-pin cover holds with any items. -/
theorem RepinCov_nop {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    (h : opAtomP th.term = none) : RepinCov E E' s s' th RS := by
  intro _ _ hot
  obtain ⟨q, _, _, _, _, hq, _⟩ := hot
  rw [h] at hq
  cases hq
#print axioms TermPiece.RepinCov_nop

/-- (OvW3 R2b) A step keeping every promise needs no re-pin items. -/
theorem RepinCov_keep {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    (h : ∀ t, t ∈ s.promises → t ∈ s'.promises) : RepinCov E E' s s' th RS :=
  fun _ _ _ _ _ _ _ _ _ _ _ hlo hth => absurd (h _ hlo.1) hth
#print axioms TermPiece.RepinCov_keep

/-- (OvW3 R2, copied) A least element of a nonempty predicate on `Nat`. -/
theorem exists_minN {P : Nat → Prop} : ∀ n, P n → ∃ k, P k ∧ ∀ j, P j → k ≤ j
  | n, h => by
      classical
      by_cases hex : ∃ j, j < n ∧ P j
      · obtain ⟨j, hj, hP⟩ := hex
        exact exists_minN j hP
      · exact ⟨n, h, fun j hj => Nat.le_of_not_lt fun hlt => hex ⟨j, hlt, hj⟩⟩
  termination_by n => n
#print axioms TermPiece.exists_minN

/-- (OvW3 R2, copied) **The lowest own promise of a range** exists once one does. -/
theorem lowest_inR {s : St} {l : AllocLabel} {lo hi : Nat} {tw : Ts} {mw : Msg}
    (ht : tw ∈ s.promises) (hm : s.mem[tw]? = some mw) (hl : mw.loc.label = l)
    (h1 : lo ≤ mw.loc.offset) (h2 : mw.loc.offset < hi) :
    ∃ t m, t ∈ s.promises ∧ s.mem[t]? = some m ∧ m.loc.label = l ∧ lo ≤ m.loc.offset ∧
      m.loc.offset < hi ∧ t ≤ tw ∧
      ∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = l → lo ≤ m'.loc.offset →
        m'.loc.offset < hi → t ≤ t' := by
  obtain ⟨k, ⟨m, hk, hmk, hlk, h1k, h2k⟩, hmin⟩ := exists_minN
    (P := fun n => ∃ m, n ∈ s.promises ∧ s.mem[n]? = some m ∧ m.loc.label = l ∧ lo ≤ m.loc.offset ∧
      m.loc.offset < hi) tw ⟨mw, ht, hm, hl, h1, h2⟩
  exact ⟨k, m, hk, hmk, hlk, h1k, h2k, hmin tw ⟨mw, ht, hm, hl, h1, h2⟩,
    fun t' m' ht' hm' hl' h1' h2' => hmin t' ⟨m', ht', hm', hl', h1', h2'⟩⟩
#print axioms TermPiece.lowest_inR

/-- (OvW3 R2, copied) **A solid component lies in a segment**. -/
theorem seg_of_atOffS {T S : Ty} {b : Nat} (hlay : LayT T) (h : AtOff T b S) (hS : Solid S) :
    ∃ sb S0 b0, SegOf T sb S0 ∧ AtOff S0 b0 S ∧ sb + b0 = b := by
  by_cases harr : ∃ N e, T = .array (.lit N) e
  · obtain ⟨N, e, rfl⟩ := harr
    cases h with
    | here _ => exact absurd rfl (hS.2.1 _ _)
    | @elem _ _ _ j o us hus hj hat =>
        exact ⟨j * nWords us, e, o, Or.inr ⟨N, us, j, rfl, hus, hj, rfl⟩, hat, rfl⟩
    | fold _ _ _ _ => exact absurd (cl_mu_eq _ _ _) (hS.2.2 _)
  · rcases hlay with hacc | ⟨N, e, hTe, -⟩
    · exact ⟨0, T, b, Or.inl ⟨rfl, rfl, hacc⟩, h, Nat.zero_add _⟩
    · exact absurd ⟨N, e, hTe⟩ harr
#print axioms TermPiece.seg_of_atOffS

/-- (OvW3 R2) **The fulfilled message is the predecessor** of the new lowest own promise `tw`
under the window conditions: coherence sits at the fulfilled `th0 < tw`, and every message
in between is an own promise (`WinGI`), none below `tw` (`LowOwn`). -/
theorem predAt_of_winGI {E : TEnv} {s : St} {l : AllocLabel} {o : Nat} {th0 tw : Ts} {m0 : Msg}
    (hcoh : s.vs.coh ⟨l, o⟩ = th0) (hlt : th0 < tw) (hm0 : s.mem[th0]? = some m0) (hl0 : m0.loc = ⟨l, o⟩)
    (hlow : LowOwn s ⟨l, o⟩ tw) (hW : WinGI E s l tw) : PredAt s.mem ⟨l, o⟩ tw (mw m0) := by
  refine ⟨th0, m0, hlt, hm0, hl0, rfl, fun t' m' h1 h2 h3 h4 => ?_⟩
  rcases hW.1 t' m' h3 (by rw [h4]) (Nat.le_of_lt h2) with h | h
  · exact absurd (hlow.2.2 t' m' h h3 h4) (Nat.not_le.mpr h2)
  · rw [h4, hcoh] at h; exact absurd h (Nat.not_le.mpr h1)
#print axioms TermPiece.predAt_of_winGI

/-- (OvW3 R2) **Bumping a value's words** up (`WLe1`) to chosen targets keeps its resources
and validity. -/
theorem bump_sel {ρ : Nat → Nat} {η : TEnv} {T : Ty} {rt : Shp} {vals : List Word} {R : Res}
    (hv : VRR ρ η T rt vals R) (hV : Valid T vals) (sel : Nat → Prop) (tgt : Nat → Word)
    (h : ∀ o v, vals[o]? = some v → sel o → WLe1 v (tgt o)) :
    ∃ ws, ws.length = vals.length ∧ VRR ρ η T rt ws R ∧ Valid T ws ∧
      ∀ o w, ws[o]? = some w → (sel o → w = tgt o) ∧ (¬ sel o → vals[o]? = some w) := by
  classical
  obtain ⟨ws, hW, hP⟩ := exists_WLe_pick (P := fun o w => (sel o → w = tgt o) ∧ (¬ sel o → vals[o]? = some w))
    vals (fun o v hv' => by
      by_cases hs : sel o
      · exact ⟨tgt o, h o v hv' hs, fun _ => rfl, fun hn => absurd hs hn⟩
      · exact ⟨v, WLe1_refl v, fun h' => absurd h' hs, fun _ => hv'⟩)
  exact ⟨ws, hW.length.symm, VRR_up T rt vals ws R hW hv, Valid_vals T _ _ hW.vals hV, hP⟩
#print axioms TermPiece.bump_sel

/-- (OvW3 R2) The re-pinned unit mask: the units of `K` whose words all have a lowest own
promise in the window (`WinGI`) whose predecessor is the item's word there. -/
noncomputable def kPin (E : TEnv) (s : St) (l : AllocLabel) (q : Nat) (usS : List Acc) (ws : List Word)
    (K : Nat → Bool) : Nat → Bool := fun i =>
  @decide (K i = true ∧ ∀ o, InAcc usS i o → ∃ tw', LowOwn s ⟨l, q + o⟩ tw' ∧ WinGI E s l tw' ∧
    ∀ w, ws[o]? = some w → PredAt s.mem ⟨l, q + o⟩ tw' w) (Classical.propDecidable _)

theorem kPin_iff {E : TEnv} {s : St} {l : AllocLabel} {q : Nat} {usS : List Acc} {ws : List Word}
    {K : Nat → Bool} {i : Nat} :
    kPin E s l q usS ws K i = true ↔ (K i = true ∧ ∀ o, InAcc usS i o → ∃ tw', LowOwn s ⟨l, q + o⟩ tw' ∧
      WinGI E s l tw' ∧ ∀ w, ws[o]? = some w → PredAt s.mem ⟨l, q + o⟩ tw' w) := by
  unfold kPin; exact @decide_eq_true_iff _ (Classical.propDecidable _)
#print axioms TermPiece.kPin_iff

/-- (OvW3 R2) One re-pin item: `RepinQ` and `RepinPl` at the singleton, for any credits
covering its value at its holder. -/
def RepinIt (E' : TEnv) (s' : St) (y : AllocLabel × Cell × CrIt) : Prop :=
  (∀ cr', y.2.2.2.2.2.2.1 ≤ cr' y.2.2.1 → RepinQ E' s' cr' [y]) ∧ RepinPl E' s' [y]

theorem repin_of_items {E' : TEnv} {s' : St} {RS : List (AllocLabel × Cell × CrIt)}
    (h : ∀ y ∈ RS, RepinIt E' s' y) : RepinQ E' s' (rpSum RS) RS ∧ RepinPl E' s' RS :=
  ⟨fun y hy => (h y hy).1 _ (rpSum_ge hy) y List.mem_cons_self,
    fun y hy => (h y hy).2 y List.mem_cons_self⟩
#print axioms TermPiece.repin_of_items

/-- (OvW3 R2) **The re-pin item of a piece**: a value `ws` (holding the key-free `R0`) of a
non-word piece `S` at word `q` of an own frontier cell, with a unit `i0` of `K` re-pinnable
(`kPin`), is a re-pin item held by the lowest own promise in the piece, at the units
`kPin … K`. -/
theorem repin_item {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {q : Nat} {S : Ty} {usS : List Acc}
    {ws : List Word} {R0 : Res} (K : Nat → Bool)
    (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hpf : E.pfr l ≠ none) (hlay : LayT c.ty)
    (hP : Piece c.ty q S) (hus : accs S = some usS)
    (hnw : ∀ o', q ≤ o' → o' < q + nWords usS → ¬ WordUnit E ⟨l, o'⟩)
    (hwl : ws.length = nWords usS) (hv : ValOfR E S ws R0) (hk : CrKeysP R0)
    {i0 o0 : Nat} (hI0 : InAcc usS i0 o0) (hK0 : kPin E s l q usS ws K i0 = true) :
    ∃ t, RepinIt E s (l, c, (t, q, S, ws, R0, kPin E s l q usS ws K)) := by
  obtain ⟨-, hU⟩ := kPin_iff.mp hK0
  obtain ⟨tw0, hlo0, hW0, -⟩ := hU o0 hI0
  have ho0 : o0 < nWords usS := Nat.lt_of_lt_of_le hI0.2 (TermTear.nWords_take_le _ _)
  obtain ⟨htw0, ⟨mw0, hmw0, hlw0⟩, -⟩ := hlo0
  obtain ⟨t, m, ht, hm, hl, hb1, hb2, hle, hmin⟩ := lowest_inR (l := l) (lo := q) (hi := q + nWords usS) htw0 hmw0
    (by rw [hlw0]) (by rw [hlw0]; exact Nat.le_add_right _ _) (by rw [hlw0]; exact Nat.add_lt_add_left ho0 _)
  obtain ⟨sb, S0, b0, hseg, hat, e⟩ := seg_of_atOffS hlay hP.1 hP.2.1
  have hnw' : ¬ WordUnit E m.loc := by
    have := hnw m.loc.offset hb1 hb2
    rw [← hl] at this
    exact this
  have hpl : ∀ R, R0 ≤ R → PlantCr E s m t R := fun R hR =>
    ⟨c, sb, S0, b0, S, usS, t, by rw [hl]; exact hsto, hown, by rw [hl]; exact hpf, hseg, hat, hP.2.1, hnw', hus,
      Piece_pos hP hus, by rw [e]; exact hb1, by rw [e]; exact hb2, Nat.le_refl _, lt_size_of_some hm,
      fun tf mf h0 h3 h4 => Nat.lt_of_le_of_lt hle (hW0.2 tf mf (by rw [← hl]; exact h0) h3 (by rw [h4, hl])),
      fun t' m' h3 h4 h5 h6 h7 _ => hmin t' m' h3 h4 (by rw [h5, hl]) (by rw [← e]; exact h6) (by rw [← e]; exact h7),
      Or.inl ⟨fun _ => false, ws, R0, hwl, hv, hR, fun i _ _ _ hK => by cases hK⟩⟩
  refine ⟨t, fun cr' hcr y hy => ?_, fun y hy => ?_⟩
  · rw [List.mem_singleton] at hy; subst hy
    refine ⟨hsto, hown, hpf, ⟨m, usS, hm, hl, ⟨ht, ⟨m, hm, rfl⟩, fun t' m' ht' hm' hl' =>
      hmin t' m' ht' hm' (by rw [hl', hl]) (by rw [hl']; exact hb1) (by rw [hl']; exact hb2)⟩, hnw', hP.1, hP.2.1,
      hus, hb1, hb2, hwl, hv, hcr, fun i o w tw' hK hI hw hL => ?_⟩, hk, fun usS' hus' t' m' ht' hm' hl' h1 h2 => ?_,
      fun o hc => ?_⟩
    · obtain ⟨-, hall⟩ := kPin_iff.mp hK
      obtain ⟨tw'', hlo, -, hpd⟩ := hall o hI
      rw [LowOwn_uniq hL hlo]
      exact hpd w hw
    · rw [hus] at hus'; cases hus'
      exact hmin t' m' ht' hm' hl' h1 h2
    · obtain ⟨usS', i, hus', hq, hI, hK⟩ := hc
      change accs S = some usS' at hus'
      rw [hus] at hus'; cases hus'
      obtain ⟨-, hall⟩ := kPin_iff.mp hK
      obtain ⟨tw', hlo, hW, -⟩ := hall _ hI
      change q ≤ o at hq
      rw [Nat.add_sub_cancel' hq] at hlo
      exact ⟨tw', hlo, hW⟩
  · rw [List.mem_singleton] at hy; subst hy
    exact ⟨m, hm, hpl⟩
#print axioms TermPiece.repin_item

/-- (OvW3 R2) A re-pinnable unit of `K` is covered by the item. -/
theorem kPin_cov {E : TEnv} {s : St} {l : AllocLabel} {q : Nat} {S : Ty} {usS : List Acc} {ws : List Word}
    {R0 : Res} {K : Nat → Bool} {t : Ts} {i o : Nat} (hus : accs S = some usS)
    (hK : kPin E s l q usS ws K i = true) (hq : q ≤ o) (hI : InAcc usS i (o - q)) :
    CrCov (t, q, S, ws, R0, kPin E s l q usS ws K) o :=
  ⟨usS, i, hus, hq, hI, hK⟩
#print axioms TermPiece.kPin_cov

/-- (pool) **The window conditions at the unit `⟨l, o⟩`** (the `TermOverCr.WinG`, inlined):
(A) and (B) restricted to the messages at the unit itself. -/
def WinGU (E : TEnv) (s : St) (l : AllocLabel) (o : Nat) (tw : Ts) : Prop :=
  (∀ t m, s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≤ tw → t ∈ s.promises ∨ t ≤ s.vs.coh m.loc) ∧
  ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → tw < t

/-- (pool) The label-wide window gives the per-unit one. -/
theorem winGU_of_I {E : TEnv} {s : St} {l : AllocLabel} {tw : Ts} (h : WinGI E s l tw) (o : Nat) :
    WinGU E s l o tw :=
  ⟨fun t m hm hl ht => h.1 t m hm (by rw [hl]) ht, fun t m ht hm hl => h.2 t m ht hm (by rw [hl])⟩
#print axioms TermPiece.winGU_of_I

/-- (pool) **The split key**: the item's holder lies below every frontier message of its label. -/
def HolderFp (E : TEnv) (s : St) (y : AllocLabel × Cell × CrIt) : Prop :=
  ∀ t m, t ∈ FpAt E ⟨y.1, 0⟩ → s.mem[t]? = some m → m.loc.label = y.1 → y.2.2.1 < t

/-- (pool) `CrItem` without the credit bound `R0 ≤ cr holder`. -/
def CrItemH (E : TEnv) (s : St) (l : AllocLabel) (c : Cell)
    (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) : Prop :=
  ∃ mh usS, s.mem[x.1]? = some mh ∧ mh.loc.label = l ∧ LowOwn s mh.loc x.1 ∧
    ¬ WordUnit E mh.loc ∧ AtOff c.ty x.2.1 x.2.2.1 ∧ Solid x.2.2.1 ∧ accs x.2.2.1 = some usS ∧
    x.2.1 ≤ mh.loc.offset ∧ mh.loc.offset < x.2.1 + nWords usS ∧
    x.2.2.2.1.length = nWords usS ∧ ValOfR E x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 ∧
    ∀ i o w tw', x.2.2.2.2.2 i = true → InAcc usS i o → x.2.2.2.1[o]? = some w →
      LowOwn s ⟨l, x.2.1 + o⟩ tw' → PredAt s.mem ⟨l, x.2.1 + o⟩ tw' w

/-- (pool) **Credited re-pin items, per-unit windows**: `RepinQ` with `WinGU` at each covered
unit in place of the label-wide `WinGI`. -/
def RepinQU (E' : TEnv) (s' : St) (cr' : Ts → Res) (RS : List (AllocLabel × Cell × CrIt)) : Prop :=
  ∀ y ∈ RS, E'.sto y.1 = some y.2.1 ∧ y.2.1.owner = some E'.tid ∧ E'.pfr y.1 ≠ none ∧
    CrItem E' s' cr' y.1 y.2.1 y.2.2 ∧ CrKeysP y.2.2.2.2.2.2.1 ∧
    (∀ usS, accs y.2.2.2.2.1 = some usS → ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m →
      m.loc.label = y.1 → y.2.2.2.1 ≤ m.loc.offset → m.loc.offset < y.2.2.2.1 + nWords usS → y.2.2.1 ≤ t) ∧
    ∀ o, CrCov y.2.2 o → ∃ tw, LowOwn s' ⟨y.1, o⟩ tw ∧ WinGU E' s' y.1 o tw

/-- (pool) **Pool re-pin items**: `RepinQU` without the credit bound (`CrItemH`). -/
def RepinQh (E' : TEnv) (s' : St) (RS : List (AllocLabel × Cell × CrIt)) : Prop :=
  ∀ y ∈ RS, E'.sto y.1 = some y.2.1 ∧ y.2.1.owner = some E'.tid ∧ E'.pfr y.1 ≠ none ∧
    CrItemH E' s' y.1 y.2.1 y.2.2 ∧ CrKeysP y.2.2.2.2.2.2.1 ∧
    (∀ usS, accs y.2.2.2.2.1 = some usS → ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m →
      m.loc.label = y.1 → y.2.2.2.1 ≤ m.loc.offset → m.loc.offset < y.2.2.2.1 + nWords usS → y.2.2.1 ≤ t) ∧
    ∀ o, CrCov y.2.2 o → ∃ tw, LowOwn s' ⟨y.1, o⟩ tw ∧ WinGU E' s' y.1 o tw

/-- (pool) **Re-pin cover, per-unit window**: `RepinCov` with `WinGU` at the unit in place of
`WinGI`, covered by a credited or a pool item. -/
def RepinCovS (E E' : TEnv) (s s' : St) (th : TTh) (RSc RSh : List (AllocLabel × Cell × CrIt)) : Prop :=
  ∀ lab, (∀ x b i v e, th.term = .let_ x (.bufInit b i v) e → ∀ rti wi n,
      evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → n ≠ E.rc lab) →
    OpTgtP th lab →
  ∀ c (o : Nat) th0 tw, E.sto lab = some c → c.owner = some E.tid → E.pfr lab ≠ none →
    ¬ VisU E ⟨lab, o⟩ → LowOwn s ⟨lab, o⟩ th0 → th0 ∉ s'.promises →
    LowOwn s' ⟨lab, o⟩ tw → OverT E' s' ⟨lab, o⟩ tw → WinGU E' s' lab o tw →
    (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
    ∃ y ∈ RSc ++ RSh, y.1 = lab ∧ CrCov y.2.2 o

/-- (pool) **Re-pin cover, per-unit window, one item list** (the producers' form):
`RepinCovS` before the credited/pool split. -/
def RepinCovU (E E' : TEnv) (s s' : St) (th : TTh) (RS : List (AllocLabel × Cell × CrIt)) : Prop :=
  ∀ lab, (∀ x b i v e, th.term = .let_ x (.bufInit b i v) e → ∀ rti wi n,
      evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → n ≠ E.rc lab) →
    OpTgtP th lab →
  ∀ c (o : Nat) th0 tw, E.sto lab = some c → c.owner = some E.tid → E.pfr lab ≠ none →
    ¬ VisU E ⟨lab, o⟩ → LowOwn s ⟨lab, o⟩ th0 → th0 ∉ s'.promises →
    LowOwn s' ⟨lab, o⟩ tw → OverT E' s' ⟨lab, o⟩ tw → WinGU E' s' lab o tw →
    (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
    ∃ y ∈ RS, y.1 = lab ∧ CrCov y.2.2 o

/-- (BI) **`RepinCovS` without the `bufInit`-at-`rc` exclusion.** -/
def RepinCovSB (E E' : TEnv) (s s' : St) (th : TTh) (RSc RSh : List (AllocLabel × Cell × CrIt)) : Prop :=
  ∀ lab, OpTgtP th lab →
  ∀ c (o : Nat) th0 tw, E.sto lab = some c → c.owner = some E.tid → E.pfr lab ≠ none →
    ¬ VisU E ⟨lab, o⟩ → LowOwn s ⟨lab, o⟩ th0 → th0 ∉ s'.promises →
    LowOwn s' ⟨lab, o⟩ tw → OverT E' s' ⟨lab, o⟩ tw → WinGU E' s' lab o tw →
    (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
    ∃ y ∈ RSc ++ RSh, y.1 = lab ∧ CrCov y.2.2 o

/-- (BI) **`RepinCovU` without the `bufInit`-at-`rc` exclusion.** -/
def RepinCovUB (E E' : TEnv) (s s' : St) (th : TTh) (RS : List (AllocLabel × Cell × CrIt)) : Prop :=
  ∀ lab, OpTgtP th lab →
  ∀ c (o : Nat) th0 tw, E.sto lab = some c → c.owner = some E.tid → E.pfr lab ≠ none →
    ¬ VisU E ⟨lab, o⟩ → LowOwn s ⟨lab, o⟩ th0 → th0 ∉ s'.promises →
    LowOwn s' ⟨lab, o⟩ tw → OverT E' s' ⟨lab, o⟩ tw → WinGU E' s' lab o tw →
    (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
    ∃ y ∈ RS, y.1 = lab ∧ CrCov y.2.2 o

/-- (pool, FulP) **An own-path op at a frontier target fulfils whole pieces**: when memory is
unchanged, an own non-word promise the step discharges at an own frontier cell lies at the op's
target, and every unit of a piece of that cell containing it has its lowest own promise
discharged. -/
def FulP (E : TEnv) (s s' : St) (th : TTh) : Prop :=
  s'.mem = s.mem → (opAtomP th.term).isSome = true → (∃ lab, OpTgtP th lab ∧ E.pfr lab ≠ none) →
    ∀ t m c, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → E.sto m.loc.label = some c →
      c.owner = some E.tid → E.pfr m.loc.label ≠ none → ¬ WordUnit E m.loc →
      OpTgtP th m.loc.label ∧ ∀ q S usS, Piece c.ty q S → accs S = some usS → q ≤ m.loc.offset →
        m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
          LowOwn s ⟨m.loc.label, o⟩ th0 → th0 ∉ s'.promises

/-- (pool, FulP) **`FulP` from a whole-component fulfilment**: a store of the component `U` at
`⟨lab, b⟩` (the op's only target) that, with memory unchanged, discharges one promise `F[j]` per
written unit, ending at coherence there, fulfils whole pieces (`Piece_sub`). -/
theorem fulP_of_fulAll {E : TEnv} {s s' : St} {th : TTh} {lab : AllocLabel} {b : Nat} {c : Cell} {U : Ty}
    {us : List Acc}
    (htg : ∀ l, OpTgtP th l → l = lab) (hsto : E.sto lab = some c) (hU : AtOff c.ty b U)
    (hus : accs U = some us) (hpa : PromAbove s')
    (hF : s'.mem = s.mem → ∃ F : List Ts, F.length = nWords us ∧
      (∀ t, t ∈ s.promises → t ∈ s'.promises ∨ t ∈ F) ∧
      ∀ (j : Nat) t, F[j]? = some t → t ∈ s.promises ∧ t ∉ s'.promises ∧
        ∃ m, s.mem[t]? = some m ∧ m.loc = ⟨lab, b + j⟩ ∧ s'.vs.coh ⟨lab, b + j⟩ = t) :
    FulP E s s' th := by
  intro hmq _ hex t m c' ht hn hm hc' _ _ _
  obtain ⟨lab0, hot0, -⟩ := hex
  obtain ⟨F, hFl, hFm, hFj⟩ := hF hmq
  have hFt : t ∈ F := (hFm t ht).resolve_left hn
  obtain ⟨j, hj, hjt⟩ := List.getElem_of_mem hFt
  obtain ⟨-, -, m0, hm0, hl0, -⟩ := hFj j t (by rw [List.getElem?_eq_getElem hj, hjt])
  rw [hm] at hm0
  cases hm0
  rw [hl0] at hc' ⊢
  rw [hsto] at hc'
  cases hc'
  refine ⟨by rw [← htg lab0 hot0]; exact hot0, fun q S usS hP hS h1 h2 o th0 h3 h4 hlo hth0 => ?_⟩
  change q ≤ b + j at h1
  change b + j < q + nWords usS at h2
  have hjl : j < nWords us := hFl ▸ hj
  obtain ⟨hb1, hb2, -⟩ := Piece_sub hU hus hP hS (by omega) (by omega)
  have hk : o - b < F.length := by rw [hFl]; omega
  obtain ⟨h5, -, m', hm', hl', hco⟩ := hFj (o - b) (F[o - b]'hk) (List.getElem?_eq_getElem hk)
  have e : b + (o - b) = o := by omega
  rw [e] at hl' hco
  have hle := hlo.2.2 _ m' h5 hm' hl'
  obtain ⟨m1, hm1, hml1⟩ := hlo.2.1
  have hlt := hpa th0 hth0 m1 (by rw [hmq]; exact hm1)
  rw [hml1, hco] at hlt
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)
#print axioms TermPiece.fulP_of_fulAll

/-- (pool) One re-pin item, split-ready: credited (`RepinQU`) for any credits covering its value at
its holder, a pool item (`RepinQh`), and a plant credit when its holder is below the label's
frontier messages (`HolderFp`). -/
def RepinItU (E' : TEnv) (s' : St) (y : AllocLabel × Cell × CrIt) : Prop :=
  (∀ cr', y.2.2.2.2.2.2.1 ≤ cr' y.2.2.1 → RepinQU E' s' cr' [y]) ∧ RepinQh E' s' [y] ∧
    (HolderFp E' s' y → RepinPl E' s' [y])

/-- (pool) The credited items of a list (holder below the frontier messages). -/
noncomputable def rpC (E' : TEnv) (s' : St) (RS : List (AllocLabel × Cell × CrIt)) :
    List (AllocLabel × Cell × CrIt) :=
  RS.filter fun y => @decide (HolderFp E' s' y) (Classical.propDecidable _)

/-- (pool) The pool items of a list. -/
noncomputable def rpH (E' : TEnv) (s' : St) (RS : List (AllocLabel × Cell × CrIt)) :
    List (AllocLabel × Cell × CrIt) :=
  RS.filter fun y => !(@decide (HolderFp E' s' y) (Classical.propDecidable _))

theorem mem_rpC {E' : TEnv} {s' : St} {RS : List (AllocLabel × Cell × CrIt)} {y : AllocLabel × Cell × CrIt} :
    y ∈ rpC E' s' RS ↔ y ∈ RS ∧ HolderFp E' s' y := by
  unfold rpC; rw [List.mem_filter]; exact and_congr Iff.rfl (@decide_eq_true_iff _ (Classical.propDecidable _))
#print axioms TermPiece.mem_rpC

theorem mem_rpH {E' : TEnv} {s' : St} {RS : List (AllocLabel × Cell × CrIt)} {y : AllocLabel × Cell × CrIt} :
    y ∈ rpH E' s' RS ↔ y ∈ RS ∧ ¬ HolderFp E' s' y := by
  unfold rpH; rw [List.mem_filter]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h hf; rw [@decide_eq_true _ (Classical.propDecidable _) hf] at h; cases h
  · intro h; rw [@decide_eq_false _ (Classical.propDecidable _) h]; rfl
#print axioms TermPiece.mem_rpH

/-- (pool) The split keeps the items' total. -/
theorem sum_rpC_rpH (E' : TEnv) (s' : St) (f : AllocLabel × Cell × CrIt → Res) :
    ∀ RS : List (AllocLabel × Cell × CrIt),
      Res.sum ((rpC E' s' RS).map f) + Res.sum ((rpH E' s' RS).map f) = Res.sum (RS.map f)
  | [] => Res.ext fun k => by simp [rpC, rpH]
  | y :: RS => by
      have ih := sum_rpC_rpH E' s' f RS
      unfold rpC rpH at ih ⊢
      by_cases h : HolderFp E' s' y
      · have hd : @decide (HolderFp E' s' y) (Classical.propDecidable _) = true :=
          @decide_eq_true _ (Classical.propDecidable _) h
        simp only [List.filter_cons, hd, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
        refine Res.ext fun k => ?_
        have e := congrArg (fun R : Res => R k) ih
        simp only [List.map_cons, Res.sum_cons, Res.add_apply] at e ⊢
        omega
      · have hd : @decide (HolderFp E' s' y) (Classical.propDecidable _) = false :=
          @decide_eq_false _ (Classical.propDecidable _) h
        simp only [List.filter_cons, hd, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
        refine Res.ext fun k => ?_
        have e := congrArg (fun R : Res => R k) ih
        simp only [List.map_cons, Res.sum_cons, Res.add_apply] at e ⊢
        omega
#print axioms TermPiece.sum_rpC_rpH

/-- (pool) **The split of split-ready items**: the credited part with credits `rpSum` of
itself and plant credits, the pool part, the split key, and the cover's two lists. -/
theorem repin_splitU {E' : TEnv} {s' : St} {RS : List (AllocLabel × Cell × CrIt)}
    (h : ∀ y ∈ RS, RepinItU E' s' y) :
    RepinQU E' s' (rpSum (rpC E' s' RS)) (rpC E' s' RS) ∧ RepinPl E' s' (rpC E' s' RS) ∧
      (∀ y ∈ rpC E' s' RS, HolderFp E' s' y) ∧ RepinQh E' s' (rpH E' s' RS) ∧
      (∀ y ∈ rpH E' s' RS, ¬ HolderFp E' s' y) ∧ (∀ y ∈ RS, y ∈ rpC E' s' RS ++ rpH E' s' RS) := by
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => (mem_rpC.1 hy).2, fun y hy => ?_,
    fun y hy => (mem_rpH.1 hy).2, fun y hy => ?_⟩
  · exact (h y (mem_rpC.1 hy).1).1 _ (rpSum_ge hy) y List.mem_cons_self
  · obtain ⟨hy1, hy2⟩ := mem_rpC.1 hy
    exact (h y hy1).2.2 hy2 y List.mem_cons_self
  · exact (h y (mem_rpH.1 hy).1).2.1 y List.mem_cons_self
  · rw [List.mem_append]
    by_cases hf : HolderFp E' s' y
    · exact Or.inl (mem_rpC.2 ⟨hy, hf⟩)
    · exact Or.inr (mem_rpH.2 ⟨hy, hf⟩)
#print axioms TermPiece.repin_splitU

/-- (pool) The producers' cover gives the split cover. -/
theorem RepinCovS_of_U {E E' : TEnv} {s s' : St} {th : TTh} {RS RSc RSh : List (AllocLabel × Cell × CrIt)}
    (h : RepinCovU E E' s s' th RS) (hm : ∀ y ∈ RS, y ∈ RSc ++ RSh) : RepinCovS E E' s s' th RSc RSh :=
  fun lab hb hot c o th0 tw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    let ⟨y, hy, hy1, hy2⟩ := h lab hb hot c o th0 tw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    ⟨y, hm y hy, hy1, hy2⟩
#print axioms TermPiece.RepinCovS_of_U

/-- (BI) The producers' cover gives the split cover, without the exclusion. -/
theorem RepinCovSB_of_U {E E' : TEnv} {s s' : St} {th : TTh} {RS RSc RSh : List (AllocLabel × Cell × CrIt)}
    (h : RepinCovUB E E' s s' th RS) (hm : ∀ y ∈ RS, y ∈ RSc ++ RSh) : RepinCovSB E E' s s' th RSc RSh :=
  fun lab hot c o th0 tw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    let ⟨y, hy, hy1, hy2⟩ := h lab hot c o th0 tw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    ⟨y, hm y hy, hy1, hy2⟩
#print axioms TermPiece.RepinCovSB_of_U

/-- (BI) Off `bufInit` the exclusion is vacuous. -/
theorem repinCovUB_of_nbi {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    (hn : ∀ x b i v e, th.term ≠ .let_ x (.bufInit b i v) e) (h : RepinCovU E E' s s' th RS) :
    RepinCovUB E E' s s' th RS :=
  fun lab hot => h lab (fun x b i v e ht => absurd ht (hn x b i v e)) hot
#print axioms TermPiece.repinCovUB_of_nbi

/-- (BI) Off the real count at every target the exclusion holds. -/
theorem repinCovUB_of_ne {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    (hn : ∀ lab, OpTgtP th lab → ∀ x b i v e, th.term = .let_ x (.bufInit b i v) e → ∀ rti wi n,
      evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → n ≠ E.rc lab)
    (h : RepinCovU E E' s s' th RS) : RepinCovUB E E' s s' th RS :=
  fun lab hot => h lab (hn lab hot) hot
#print axioms TermPiece.repinCovUB_of_ne

/-- (BI) The exclusion-free split cover gives the split cover. -/
theorem repinCovS_of_SB {E E' : TEnv} {s s' : St} {th : TTh} {RSc RSh : List (AllocLabel × Cell × CrIt)}
    (h : RepinCovSB E E' s s' th RSc RSh) : RepinCovS E E' s s' th RSc RSh :=
  fun lab _ hot => h lab hot
#print axioms TermPiece.repinCovS_of_SB

/-- (pool) Off atomic operations the cover holds with any items. -/
theorem RepinCovU_nop {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    (h : opAtomP th.term = none) : RepinCovU E E' s s' th RS := by
  intro _ _ hot
  obtain ⟨q, _, _, _, _, hq, _⟩ := hot
  rw [h] at hq
  cases hq
#print axioms TermPiece.RepinCovU_nop

/-- (pool) A step keeping every promise needs no re-pin items. -/
theorem RepinCovU_keep {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    (h : ∀ t, t ∈ s.promises → t ∈ s'.promises) : RepinCovU E E' s s' th RS :=
  fun _ _ _ _ _ _ _ _ _ _ _ hlo hth => absurd (h _ hlo.1) hth
#print axioms TermPiece.RepinCovU_keep

/-- (pool) At a `bufInit` at its buffer's real count the cover holds with any items (the OPEN
exclusion, KQ3WS-PL). -/
theorem RepinCovU_biP {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    (h : ∃ x b i v e rti wi n, th.term = .let_ x (.bufInit b i v) e ∧ evalAt th.env i = some (rti, [wi]) ∧
      numOf [wi] = some n ∧ ∀ lab, OpTgtP th lab → n = E.rc lab) : RepinCovU E E' s s' th RS := by
  intro lab hx hot
  obtain ⟨x, b, i, v, e, rti, wi, n, ht, hei, hn, heq⟩ := h
  exact absurd (heq lab hot) (hx x b i v e ht rti wi n hei hn)
#print axioms TermPiece.RepinCovU_biP

/-- (pool) `RepinCov_of` for the per-unit cover. -/
theorem RepinCovU_of {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)} {l : AllocLabel}
    (htg : ∀ lab, OpTgtP th lab → lab = l)
    (h : ∀ c (o : Nat) th0 tw, E.sto l = some c → c.owner = some E.tid → E.pfr l ≠ none → ¬ VisU E ⟨l, o⟩ →
      LowOwn s ⟨l, o⟩ th0 → th0 ∉ s'.promises → LowOwn s' ⟨l, o⟩ tw → OverT E' s' ⟨l, o⟩ tw →
      WinGU E' s' l o tw → (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
      ∃ y ∈ RS, y.1 = l ∧ CrCov y.2.2 o) : RepinCovU E E' s s' th RS := by
  intro lab _ hot
  obtain rfl := htg lab hot
  exact h
#print axioms TermPiece.RepinCovU_of

/-- (pool) At another thread's cell the cover holds with any items. -/
theorem RepinCovU_foreign {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    {l : AllocLabel} {c : Cell} (htg : ∀ lab, OpTgtP th lab → lab = l) (hsto : E.sto l = some c)
    (hown : c.owner ≠ some E.tid) : RepinCovU E E' s s' th RS :=
  RepinCovU_of htg fun c' _ _ _ hc' hown' => by
    rw [hsto] at hc'
    cases hc'
    exact absurd hown' hown
#print axioms TermPiece.RepinCovU_foreign

/-- (pool) **The fulfilled message is the predecessor**, per-unit window: only clause (A) at the
unit is used. -/
theorem predAt_of_winGU {E : TEnv} {s : St} {l : AllocLabel} {o : Nat} {th0 tw : Ts} {m0 : Msg}
    (hcoh : s.vs.coh ⟨l, o⟩ = th0) (hlt : th0 < tw) (hm0 : s.mem[th0]? = some m0) (hl0 : m0.loc = ⟨l, o⟩)
    (hlow : LowOwn s ⟨l, o⟩ tw) (hW : WinGU E s l o tw) : PredAt s.mem ⟨l, o⟩ tw (mw m0) := by
  refine ⟨th0, m0, hlt, hm0, hl0, rfl, fun t' m' h1 h2 h3 h4 => ?_⟩
  rcases hW.1 t' m' h3 h4 (Nat.le_of_lt h2) with h | h
  · exact absurd (hlow.2.2 t' m' h h3 h4) (Nat.not_le.mpr h2)
  · rw [h4, hcoh] at h; exact absurd h (Nat.not_le.mpr h1)
#print axioms TermPiece.predAt_of_winGU

/-- (pool) The re-pinned unit mask, per-unit windows: the units of `K` whose words all have a
lowest own promise in the unit's window (`WinGU`) whose predecessor is the item's word there. -/
noncomputable def kPinU (E : TEnv) (s : St) (l : AllocLabel) (q : Nat) (usS : List Acc) (ws : List Word)
    (K : Nat → Bool) : Nat → Bool := fun i =>
  @decide (K i = true ∧ ∀ o, InAcc usS i o → ∃ tw', LowOwn s ⟨l, q + o⟩ tw' ∧ WinGU E s l (q + o) tw' ∧
    ∀ w, ws[o]? = some w → PredAt s.mem ⟨l, q + o⟩ tw' w) (Classical.propDecidable _)

theorem kPinU_iff {E : TEnv} {s : St} {l : AllocLabel} {q : Nat} {usS : List Acc} {ws : List Word}
    {K : Nat → Bool} {i : Nat} :
    kPinU E s l q usS ws K i = true ↔ (K i = true ∧ ∀ o, InAcc usS i o → ∃ tw', LowOwn s ⟨l, q + o⟩ tw' ∧
      WinGU E s l (q + o) tw' ∧ ∀ w, ws[o]? = some w → PredAt s.mem ⟨l, q + o⟩ tw' w) := by
  unfold kPinU; exact @decide_eq_true_iff _ (Classical.propDecidable _)
#print axioms TermPiece.kPinU_iff

/-- (pool) A re-pinnable unit of `K` is covered by the item. -/
theorem kPinU_cov {E : TEnv} {s : St} {l : AllocLabel} {q : Nat} {S : Ty} {usS : List Acc} {ws : List Word}
    {R0 : Res} {K : Nat → Bool} {t : Ts} {i o : Nat} (hus : accs S = some usS)
    (hK : kPinU E s l q usS ws K i = true) (hq : q ≤ o) (hI : InAcc usS i (o - q)) :
    CrCov (t, q, S, ws, R0, kPinU E s l q usS ws K) o :=
  ⟨usS, i, hus, hq, hI, hK⟩
#print axioms TermPiece.kPinU_cov

/-- (pool) **The re-pin item of a piece, split-ready** (`repin_item` at per-unit windows): the
item is credited and pool-ready at the units `kPinU … K`; its plant credit comes from
`HolderFp`. -/
theorem repin_itemU {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {q : Nat} {S : Ty} {usS : List Acc}
    {ws : List Word} {R0 : Res} (K : Nat → Bool)
    (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hpf : E.pfr l ≠ none) (hlay : LayT c.ty)
    (hP : Piece c.ty q S) (hus : accs S = some usS)
    (hnw : ∀ o', q ≤ o' → o' < q + nWords usS → ¬ WordUnit E ⟨l, o'⟩)
    (hwl : ws.length = nWords usS) (hv : ValOfR E S ws R0) (hk : CrKeysP R0)
    {i0 o0 : Nat} (hI0 : InAcc usS i0 o0) (hK0 : kPinU E s l q usS ws K i0 = true) :
    ∃ t, RepinItU E s (l, c, (t, q, S, ws, R0, kPinU E s l q usS ws K)) := by
  obtain ⟨-, hU⟩ := kPinU_iff.mp hK0
  obtain ⟨tw0, hlo0, -, -⟩ := hU o0 hI0
  have ho0 : o0 < nWords usS := Nat.lt_of_lt_of_le hI0.2 (TermTear.nWords_take_le _ _)
  obtain ⟨htw0, ⟨mw0, hmw0, hlw0⟩, -⟩ := hlo0
  obtain ⟨t, m, ht, hm, hl, hb1, hb2, -, hmin⟩ := lowest_inR (l := l) (lo := q) (hi := q + nWords usS) htw0 hmw0
    (by rw [hlw0]) (by rw [hlw0]; exact Nat.le_add_right _ _) (by rw [hlw0]; exact Nat.add_lt_add_left ho0 _)
  obtain ⟨sb, S0, b0, hseg, hat, e⟩ := seg_of_atOffS hlay hP.1 hP.2.1
  have hnw' : ¬ WordUnit E m.loc := by
    have := hnw m.loc.offset hb1 hb2
    rw [← hl] at this
    exact this
  have hcrit : ∀ cr', R0 ≤ cr' t → CrItem E s cr' l c (t, q, S, ws, R0, kPinU E s l q usS ws K) := fun cr' hcr =>
    ⟨m, usS, hm, hl, ⟨ht, ⟨m, hm, rfl⟩, fun t' m' ht' hm' hl' =>
      hmin t' m' ht' hm' (by rw [hl', hl]) (by rw [hl']; exact hb1) (by rw [hl']; exact hb2)⟩, hnw', hP.1, hP.2.1,
      hus, hb1, hb2, hwl, hv, hcr, fun i o w tw' hK hI hw hL => by
        obtain ⟨-, hall⟩ := kPinU_iff.mp hK
        obtain ⟨tw'', hlo, -, hpd⟩ := hall o hI
        rw [LowOwn_uniq hL hlo]
        exact hpd w hw⟩
  have hlowc : ∀ usS', accs S = some usS' → ∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' →
      m'.loc.label = l → q ≤ m'.loc.offset → m'.loc.offset < q + nWords usS' → t ≤ t' := by
    intro usS' hus' t' m' ht' hm' hl' h1 h2
    rw [hus] at hus'; cases hus'
    exact hmin t' m' ht' hm' hl' h1 h2
  have hcov : ∀ o, CrCov (t, q, S, ws, R0, kPinU E s l q usS ws K) o →
      ∃ tw, LowOwn s ⟨l, o⟩ tw ∧ WinGU E s l o tw := by
    intro o hc
    obtain ⟨usS', i, hus', hq, hI, hK⟩ := hc
    change accs S = some usS' at hus'
    rw [hus] at hus'; cases hus'
    obtain ⟨-, hall⟩ := kPinU_iff.mp hK
    obtain ⟨tw', hlo, hW, -⟩ := hall _ hI
    change q ≤ o at hq
    rw [Nat.add_sub_cancel' hq] at hlo hW
    exact ⟨tw', hlo, hW⟩
  refine ⟨t, fun cr' hcr y hy => ?_, fun y hy => ?_, fun hHF y hy => ?_⟩
  · rw [List.mem_singleton] at hy; subst hy
    exact ⟨hsto, hown, hpf, hcrit cr' hcr, hk, hlowc, hcov⟩
  · rw [List.mem_singleton] at hy; subst hy
    refine ⟨hsto, hown, hpf, ⟨m, usS, hm, hl, ⟨ht, ⟨m, hm, rfl⟩, fun t' m' ht' hm' hl' =>
      hmin t' m' ht' hm' (by rw [hl', hl]) (by rw [hl']; exact hb1) (by rw [hl']; exact hb2)⟩, hnw', hP.1, hP.2.1,
      hus, hb1, hb2, hwl, hv, fun i o w tw' hK hI hw hL => ?_⟩, hk, hlowc, hcov⟩
    obtain ⟨-, hall⟩ := kPinU_iff.mp hK
    obtain ⟨tw'', hlo, -, hpd⟩ := hall o hI
    rw [LowOwn_uniq hL hlo]
    exact hpd w hw
  · rw [List.mem_singleton] at hy; subst hy
    refine ⟨m, hm, fun R hR => ?_⟩
    exact ⟨c, sb, S0, b0, S, usS, t, by rw [hl]; exact hsto, hown, by rw [hl]; exact hpf, hseg, hat, hP.2.1, hnw', hus,
      Piece_pos hP hus, by rw [e]; exact hb1, by rw [e]; exact hb2, Nat.le_refl _, lt_size_of_some hm,
      fun tf mf h0 h3 h4 => hHF tf mf (by rw [← hl]; exact h0) h3 (by rw [h4, hl]),
      fun t' m' h3 h4 h5 h6 h7 _ => hmin t' m' h3 h4 (by rw [h5, hl]) (by rw [← e]; exact h6) (by rw [← e]; exact h7),
      Or.inl ⟨fun _ => false, ws, R0, hwl, hv, hR, fun i _ _ _ hK => by cases hK⟩⟩
#print axioms TermPiece.repin_itemU

/-- (OvW3 R2) **Carving**: a value of `T` holding `R` splits over a duplicate-free list of
pieces into their sub-values, totalling at most `R`. -/
theorem carveVRR (E : TEnv) {ρ₀ : Nat → Nat} {T : Ty} {L : List (Nat × Ty)} (hT : accs T ≠ none)
    (hL : ∀ p ∈ L, Piece T p.1 p.2) (hnd : L.Nodup) {ws : List Word} {R : Res}
    (hv : VRR ρ₀ (CE E) T (shp T) ws R) (hwc : wc T = some ws.length) :
    ∃ G : List ((Nat × Ty) × Res), G.map Prod.fst = L ∧ (∀ g ∈ G, PcR ρ₀ E ws g) ∧
      Res.sum (G.map Prod.snd) ≤ R := by
  obtain ⟨G, eG, Rr, hR, hG⟩ := VRR_pieces E hT hL hnd hv hwc
  exact ⟨G, eG, hG, by rw [hR]; exact Res.le_add_right _ _⟩
#print axioms TermPiece.carveVRR

/-- (OvW3 R2) A carved piece of a valid value is a value of the piece (`ValOfR`). -/
theorem pcR_valOf {E : TEnv} {T : Ty} {ws : List Word} {g : (Nat × Ty) × Res}
    (hg : PcR (fun _ => 0) E.unsee ws g) (hP : Piece T g.1.1 g.1.2) (hT : accs T ≠ none) (hV : Valid T ws)
    (hwc : wc T = some ws.length) :
    ∃ n, wc g.1.2 = some n ∧ ((ws.drop g.1.1).take n).length = n ∧ ValOfR E g.1.2 ((ws.drop g.1.1).take n) g.2 := by
  obtain ⟨n, hn, hle, hv⟩ := hg
  refine ⟨n, hn, by simp only [List.length_take, List.length_drop]; omega, hv, ?_⟩
  exact Valid_at hP.1 hT hV hwc n hn
#print axioms TermPiece.pcR_valOf


/-- (OvW3 R2) **A piece meeting a non-word unit has no word unit** (pieces meeting at a unit
coincide, `piece_match`, and a word's or pair's piece is all word units). -/
theorem nword_piece {E : TEnv} {l : AllocLabel} {c : Cell} {q : Nat} {S : Ty} {usS : List Acc} {o1 : Nat}
    (hsto : E.sto l = some c) (hP : Piece c.ty q S) (hus : accs S = some usS) (h1 : q ≤ o1)
    (h2 : o1 < q + nWords usS) (hn1 : ¬ WordUnit E ⟨l, o1⟩) :
    ∀ o', q ≤ o' → o' < q + nWords usS → ¬ WordUnit E ⟨l, o'⟩ := by
  intro o' ho1 ho2 ⟨c', hc', hw⟩
  change E.sto l = some c' at hc'
  rw [hsto] at hc'; cases hc'
  have hwS := wc_of_accs hus
  have e2 : nWords [Acc.two] = 2 := rfl
  rcases hw with ⟨r, P, hg, hA⟩ | ⟨r, P, hA⟩ | ⟨r, P, h0, hA⟩
  · change AtOff c.ty o' _ at hA
    have hPw : Piece c.ty o' (.word r P) := ⟨hA, Solid_word r P, by rw [wc_word hg]; simp⟩
    obtain ⟨rfl, rfl⟩ := piece_match hP hPw hwS (wc_word hg) ho1 ho2 (Nat.le_refl _) (by omega)
    have e : nWords usS = 1 := Option.some.inj (hwS.symm.trans (wc_word hg))
    have : o1 = q := by omega
    subst this
    exact hn1 ⟨c, hsto, Or.inl ⟨r, P, hg, hA⟩⟩
  · change AtOff c.ty o' _ at hA
    have hw2 : wc (.word2 r P) = some 2 := wc_of_accs accs_word2
    have hPw : Piece c.ty o' (.word2 r P) := ⟨hA, Solid_word2 r P, by rw [hw2]; simp⟩
    obtain ⟨rfl, rfl⟩ := piece_match hP hPw hwS hw2 ho1 ho2 (Nat.le_refl _) (by omega)
    have e : nWords usS = 2 := Option.some.inj (hwS.symm.trans hw2)
    by_cases h : o1 = q
    · subst h; exact hn1 ⟨c, hsto, Or.inr (Or.inl ⟨r, P, hA⟩)⟩
    · have e1 : o1 - 1 = q := by omega
      exact hn1 ⟨c, hsto, Or.inr (Or.inr ⟨r, P, show 1 ≤ o1 by omega, show AtOff c.ty (o1 - 1) _ by rw [e1]; exact hA⟩)⟩
  · change 1 ≤ o' at h0
    change AtOff c.ty (o' - 1) _ at hA
    have hw2 : wc (.word2 r P) = some 2 := wc_of_accs accs_word2
    have hPw : Piece c.ty (o' - 1) (.word2 r P) := ⟨hA, Solid_word2 r P, by rw [hw2]; simp⟩
    obtain ⟨e0, rfl⟩ := piece_match hP hPw hwS hw2 ho1 ho2 (by omega) (by omega)
    have e : nWords usS = 2 := Option.some.inj (hwS.symm.trans hw2)
    by_cases h : o1 = q
    · subst h; exact hn1 ⟨c, hsto, Or.inr (Or.inl ⟨r, P, by rw [e0]; exact hA⟩)⟩
    · have e1 : o1 - 1 = o' - 1 := by omega
      exact hn1 ⟨c, hsto, Or.inr (Or.inr ⟨r, P, show 1 ≤ o1 by omega, show AtOff c.ty (o1 - 1) _ by rw [e1]; exact hA⟩)⟩
#print axioms TermPiece.nword_piece

/-- (OvW3 R2) **Picking a sublist of candidates**: from a list of sources, a list of items, each
built from some source (`Q`), one for every source that admits one, costing at most the sources. -/
theorem pick_list {α β : Type} (Q : α → β → Prop) (w : α → Res) (r : β → Res) (hQ : ∀ a y, Q a y → r y ≤ w a) :
    ∀ L : List α, ∃ RS : List β, (∀ y ∈ RS, ∃ a ∈ L, Q a y) ∧ (∀ a ∈ L, (∃ y, Q a y) → ∃ y ∈ RS, Q a y) ∧
      Res.sum (RS.map r) ≤ Res.sum (L.map w)
  | [] => ⟨[], fun y hy => absurd hy List.not_mem_nil, fun a ha => absurd ha List.not_mem_nil, Res.le_refl _⟩
  | a :: L => by
      classical
      obtain ⟨RS, h1, h2, h3⟩ := pick_list Q w r hQ L
      by_cases hex : ∃ y, Q a y
      · obtain ⟨y, hy⟩ := hex
        refine ⟨y :: RS, fun y' hy' => ?_, fun a' ha' _ => ?_, ?_⟩
        · rcases List.mem_cons.mp hy' with rfl | hy'
          · exact ⟨a, List.mem_cons_self, hy⟩
          · obtain ⟨a', ha', hq⟩ := h1 y' hy'
            exact ⟨a', List.mem_cons_of_mem _ ha', hq⟩
        · rcases List.mem_cons.mp ha' with rfl | ha'
          · exact ⟨y, List.mem_cons_self, hy⟩
          · obtain ⟨y', hy', hq⟩ := h2 a' ha' ‹_›
            exact ⟨y', List.mem_cons_of_mem _ hy', hq⟩
        · intro k
          have := hQ a y hy k; have := h3 k
          simp only [List.map_cons, Res.sum_cons, Res.add_apply]; omega
      · refine ⟨RS, fun y' hy' => ?_, fun a' ha' hq => ?_, ?_⟩
        · obtain ⟨a', ha', hq⟩ := h1 y' hy'
          exact ⟨a', List.mem_cons_of_mem _ ha', hq⟩
        · rcases List.mem_cons.mp ha' with rfl | ha'
          · exact absurd hq hex
          · exact h2 a' ha' hq
        · intro k
          have := h3 k
          simp only [List.map_cons, Res.sum_cons, Res.add_apply]; omega
#print axioms TermPiece.pick_list



theorem G_nil {X Y : Res} (h : X ≤ Y) : X + Res.sum (([] : List GdE).map GdE.R) ≤ Y := by
  simpa using h

/-! ## (OvW3 R2c) Re-pin at own store fulfils -/

/-- (OvW3 R2c) **A store fulfils at one-word units**: an own promise the store discharges
lies at a one-word unit `j` of the target, holds the stored value with a view covering the
release view (and a stored pointer's view), and the post-state coherence there is it. -/
theorem storeUnits_fulU {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s.promises.Nodup →
      (∀ t, t ∈ s.promises → t < s.mem.size) → s' ∈ storeUnits k arch pw a rel us ws i s →
      ∀ t, t ∈ s.promises → t ∉ s'.promises → ∃ n j m w, us[n]? = some .one ∧ j = nWords (us.take n) ∧
        s.mem[t]? = some m ∧ ws[j]? = some w ∧ m.loc = offs a (i + j) ∧ m.val = w.val ∧
        s.vs.vRelSt ≤ m.view ∧ (∀ x g, w.val = .loc x g → w.view ≤ m.view) ∧
        s'.vs.coh (offs a (i + j)) = t
  | [], _, _, s, s', _, _, hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      intro t h1 h2; exact absurd h1 h2
  | .one :: us, w :: ws, i, s, s', hnd, hP, hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t0, hcase, hcoh, hrs, -⟩ := stepStore_casesC hst
      have ev : exprVal (mth s pw w w) (dataE 1 w) = w.val := exprVal_dataE _ 1 w (by simp [mth, regsOf])
      have hmw : ∀ x g, w.val = .loc x g → w.view ≤ Promises.storeMview (mth s pw w w) (dataE 1 w) [0] rel :=
        storeMview_dataE _ 1 w (by simp [mth, regsOf]) [0] rel
      have hmr : s.vs.vRelSt ≤ Promises.storeMview (mth s pw w w) (dataE 1 w) [0] rel :=
        storeMview_relSt (mth s pw w w) _ [0] rel
      have hco : ∀ j, s'.vs.coh (offs a (i + 1 + j)) = s'.vs.coh (offs a (i + 1 + j)) := fun _ => rfl
      clear hco
      intro t ht htn
      rcases hcase with ⟨hmem, -, hprom⟩ | ⟨hmem, htp, hprom, hlt, m0, hm0, hma, hmv, hmv'⟩
      · -- appended: recurse
        have hnd1 : th.promises.Nodup := by rw [hprom]; exact hnd
        have hP1 : ∀ t, t ∈ th.promises → t < mem'.size := fun t ht' => by
          rw [hprom] at ht'; rw [hmem, Array.size_push]; exact Nat.lt_succ_of_lt (hP t ht')
        have ht1 : t ∈ th.promises := by rw [hprom]; exact ht
        obtain ⟨n, j, m, w', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
          storeUnits_fulU us ws (i + 1) { s with mem := mem', vs := th.vs, promises := th.promises } s' hnd1 hP1 hs
            t ht1 htn
        have h3' : s.mem[t]? = some m := by
          have h3' : mem'[t]? = some m := h3
          rw [← h3', hmem, Array.getElem?_push, if_neg (Nat.ne_of_lt (hP t ht))]
        refine ⟨n + 1, j + 1, m, w', by simpa using h1, ?_, h3', by simpa using h4,
          by rw [h5, show i + 1 + j = i + (j + 1) by omega], h6, Nat.le_trans (Nat.le_of_eq hrs.symm) h7, h8,
          by rw [show i + (j + 1) = i + 1 + j by omega]; exact h9⟩
        rw [h2, List.take_succ_cons, TermTear.nWords_cons]; simp [Acc.size, Nat.add_comm]
      · by_cases e : t = t0
        · subst e
          refine ⟨0, 0, m0, w, rfl, by simp [nWords], hm0, rfl, by rw [hma]; rfl, by rw [hmv, ev],
            Nat.le_trans hmr hmv', fun x g hx => Nat.le_trans (hmw x g hx) hmv', ?_⟩
          have e2 : s'.vs.coh (offs a (i + 0)) = th.vs.coh (offs a (i + 0)) :=
            storeUnits_cohOff us ws (i + 1) _ s' hs _ fun j => offs_ne a (by omega)
          rw [e2, hcoh]; simp
        · have hnd1 : th.promises.Nodup := by rw [hprom]; exact hnd.erase _
          have hP1 : ∀ t, t ∈ th.promises → t < mem'.size := fun t ht' => by
            rw [hprom] at ht'; rw [hmem]; exact hP t (List.mem_of_mem_erase ht')
          have ht1 : t ∈ th.promises := by rw [hprom]; exact (List.mem_erase_of_ne e).2 ht
          obtain ⟨n, j, m, w', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
            storeUnits_fulU us ws (i + 1) { s with mem := mem', vs := th.vs, promises := th.promises } s' hnd1 hP1 hs
              t ht1 htn
          have h3' : mem'[t]? = some m := h3
          rw [hmem] at h3'
          refine ⟨n + 1, j + 1, m, w', by simpa using h1, ?_, h3', by simpa using h4,
            by rw [h5, show i + 1 + j = i + (j + 1) by omega], h6, Nat.le_trans (Nat.le_of_eq hrs.symm) h7, h8,
            by rw [show i + (j + 1) = i + 1 + j by omega]; exact h9⟩
          rw [h2, List.take_succ_cons, TermTear.nWords_cons]; simp [Acc.size, Nat.add_comm]
  | .two :: us, w0 :: w1 :: ws, i, s, s', hnd, hP, hs => by
      simp only [storeUnits] at hs
      obtain ⟨q1, -, -, q4, q5⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R
        at q1 q4 q5 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q4 q5 hs
      intro t ht htn
      have hnd1 : th.promises.Nodup := by rw [q4]; exact hnd
      have hP1 : ∀ t, t ∈ th.promises → t < mem'.size := fun t ht' => by
        rw [q4] at ht'; rw [q1, Array.size_push, Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt (hP t ht'))
      have ht1 : t ∈ th.promises := by rw [q4]; exact ht
      obtain ⟨n, j, m, w', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        storeUnits_fulU us ws (i + 2) { s with mem := mem', pairs := pairs', vs := th.vs, promises := th.promises } s'
          hnd1 hP1 hs t ht1 htn
      have hlt := hP t ht
      have h3' : s.mem[t]? = some m := by
        have h3' : mem'[t]? = some m := h3
        rw [← h3', q1, Array.getElem?_push, if_neg (by rw [Array.size_push]; exact Nat.ne_of_lt (Nat.lt_succ_of_lt hlt)),
          Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]
      refine ⟨n + 1, j + 2, m, w', by simpa using h1, ?_, h3', by simpa using h4,
        by rw [h5, show i + 2 + j = i + (j + 2) by omega], h6, Nat.le_trans (Nat.le_of_eq q5.symm) h7, h8,
        by rw [show i + (j + 2) = i + 2 + j by omega]; exact h9⟩
      rw [h2, List.take_succ_cons, TermTear.nWords_cons]; simp [Acc.size, Nat.add_comm]
  | .one :: _, [], _, _, _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, _, _, hs => by simp [storeUnits] at hs
#print axioms TermPiece.storeUnits_fulU

/-- (FulP, copy of TermPlant's `storeUnits_fulAll` for the pub stores) **A store that does not
grow memory fulfils every unit**. -/
theorem storeUnits_fulAllP {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s.promises.Nodup →
      s' ∈ storeUnits k arch pw a rel us ws i s → s'.mem.size ≤ s.mem.size →
      s'.mem = s.mem ∧ (∀ u, u ∈ us → u = .one) ∧ ∃ F : List Ts, F.length = nWords us ∧
        (∀ f : Ts → Res, Res.sum (s.promises.map f) = Res.sum (s'.promises.map f) + Res.sum (F.map f)) ∧
        (∀ x, (∀ j, j < nWords us → x ≠ offs a (i + j)) → s'.vs.coh x = s.vs.coh x) ∧
        (∀ t, t ∈ s.promises → t ∈ s'.promises ∨ t ∈ F) ∧
        ∀ j t, F[j]? = some t → t ∈ s.promises ∧ t ∉ s'.promises ∧ ∃ m w, s.mem[t]? = some m ∧
          ws[j]? = some w ∧ m.loc = offs a (i + j) ∧ m.val = w.val ∧ s.vs.coh (offs a (i + j)) < t ∧
          s.vs.vRelSt ≤ m.view ∧ (∀ x g, w.val = .loc x g → w.view ≤ m.view) ∧
          s'.vs.coh (offs a (i + j)) = t
  | [], _, _, s, s', _, hs, _ => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      exact ⟨rfl, fun u h => by simp at h, [], rfl, fun f => Res.ext fun k => by simp, fun _ _ => rfl,
        fun t h => Or.inl h, fun j t h => by simp at h⟩
  | .one :: us, w :: ws, i, s, s', hnd, hs, hsz => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t0, hcase, hcoh, hrs, -⟩ := stepStore_casesC hst
      have ev : exprVal (mth s pw w w) (dataE 1 w) = w.val := exprVal_dataE _ 1 w (by simp [mth, regsOf])
      have hmw : ∀ x g, w.val = .loc x g → w.view ≤ Promises.storeMview (mth s pw w w) (dataE 1 w) [0] rel :=
        storeMview_dataE _ 1 w (by simp [mth, regsOf]) [0] rel
      have hmr : s.vs.vRelSt ≤ Promises.storeMview (mth s pw w w) (dataE 1 w) [0] rel :=
        storeMview_relSt (mth s pw w w) _ [0] rel
      have hg := (storeUnits_growsF us ws (i + 1) _ s' hs)
      rcases hcase with ⟨hmem, -, -⟩ | ⟨hmem, htp, hprom, hlt, m0, hm0, hma, hmv, hmv'⟩
      · exfalso
        have : mem'.size ≤ s'.mem.size := hg.1.1
        rw [hmem, Array.size_push] at this; omega
      · have hnd1 : th.promises.Nodup := by rw [hprom]; exact hnd.erase _
        have hsz1 : s'.mem.size ≤ mem'.size := by rw [hmem]; exact hsz
        obtain ⟨e1, h1s, F, hFl, hFs, hco, hmem1, g⟩ := storeUnits_fulAllP us ws (i + 1)
          { s with mem := mem', vs := th.vs, promises := th.promises } s' hnd1 hs hsz1
        have hsub : ∀ t, t ∈ th.promises → t ∈ s.promises := fun t ht => by
          rw [hprom] at ht; exact List.mem_of_mem_erase ht
        refine ⟨e1.trans hmem, fun u hu => ?_, t0 :: F, by rw [List.length_cons, hFl, TermMem.nWords_one], fun f => ?_,
          fun x hx => ?_, fun t ht => ?_, fun j t hj => ?_⟩
        · rcases List.mem_cons.1 hu with rfl | hu
          · rfl
          · exact h1s u hu
        · have h1 : Res.sum (s.promises.map f) = f t0 + Res.sum ((s.promises.erase t0).map f) :=
            sum_map_erase (f := f) htp
          have h2 := hFs f
          have e : th.promises = s.promises.erase t0 := hprom
          rw [← e] at h1
          change Res.sum (th.promises.map f) = _ at h2
          rw [h2] at h1
          rw [h1]
          refine Res.ext fun k => ?_
          simp only [Res.add_apply, List.map_cons, Res.sum_cons]
          omega
        · have e2 : s'.vs.coh x = th.vs.coh x := hco x fun j hj => by
            have := hx (j + 1) (by rw [TermMem.nWords_one]; omega)
            rwa [show i + (j + 1) = i + 1 + j by omega] at this
          rw [e2, hcoh]
          have hx0 : x ≠ offs a i := by simpa using hx 0 (by rw [TermMem.nWords_one]; omega)
          simp only [hx0, ite_false]
          rfl
        · by_cases e : t = t0
          · exact Or.inr (e ▸ List.mem_cons_self ..)
          · have : t ∈ th.promises := by rw [hprom]; exact (List.mem_erase_of_ne e).2 ht
            rcases hmem1 t this with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons_of_mem _ h)
        rcases j with _ | j
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
          refine ⟨htp, fun h => ?_, m0, w, hm0, rfl, by rw [hma]; rfl, by rw [hmv, ev], hlt,
            Nat.le_trans hmr hmv', fun x g hx => Nat.le_trans (hmw x g hx) hmv', ?_⟩
          · have h2 : t0 ∈ th.promises := hg.2.1 t0 h
            rw [hprom] at h2; exact (List.Nodup.not_mem_erase hnd) h2
          · have e2 : s'.vs.coh (offs a (i + 0)) = th.vs.coh (offs a (i + 0)) := hco _ fun j _ =>
              offs_ne a (by omega)
            rw [e2, hcoh]; simp
        · simp only [List.getElem?_cons_succ] at hj
          obtain ⟨h1, h2, m, w', h3, hw, h4, hv, h5, h6, h7, h8⟩ := g j t hj
          have hne : offs a (i + 1 + j) ≠ offs a i := offs_ne a (by omega)
          have h3' : mem'[t]? = some m := h3
          rw [hmem] at h3'
          refine ⟨hsub t h1, h2, m, w', h3', by simpa using hw,
            by rw [h4, show i + 1 + j = i + (j + 1) by omega], hv, ?_,
            Nat.le_trans (Nat.le_of_eq hrs.symm) h6, h7, ?_⟩
          have h5' : th.vs.coh (offs a (i + 1 + j)) < t := h5
          rw [hcoh] at h5'; simp only [hne, ite_false] at h5'
          · rw [show i + (j + 1) = i + 1 + j by omega]; exact h5'
          · rw [show i + (j + 1) = i + 1 + j by omega]; exact h8
  | .two :: us, w0 :: w1 :: ws, i, s, s', _, hs, hsz => by
      simp only [storeUnits] at hs
      obtain ⟨q1, _, _, _, _⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q1 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 hs
      exfalso
      have : mem'.size ≤ s'.mem.size := (storeUnits_growsF us ws (i + 2) _ s' hs).1.1
      rw [q1, Array.size_push, Array.size_push] at this; omega
  | .one :: _, [], _, _, _, _, hs, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, _, hs, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, _, hs, _ => by simp [storeUnits] at hs
#print axioms TermPiece.storeUnits_fulAllP

/-- (OvW3 R2c) **A store's new messages end at coherence**: each message the store appends is
the post-state coherence at its address. -/
theorem storeUnits_newCoh {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → s'.vs.coh m.loc = t
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      intro t m ht hm
      rw [Array.getElem?_eq_none ht] at hm; cases hm
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t0, hcase, hcoh, -, -⟩ := stepStore_casesC hst
      have ih := storeUnits_newCoh us ws (i + 1) _ s' hs
      have hg := (storeUnits_growsF us ws (i + 1) _ s' hs).1
      intro t m ht hm
      rcases hcase with ⟨hmem, rfl, -⟩ | ⟨hmem, -⟩
      · by_cases e : t = s.mem.size
        · subst e
          have h1 : mem'[s.mem.size]? = some m := by
            rw [← hm]; exact (hg.2.1 _ (by rw [hmem, Array.size_push]; exact Nat.lt_succ_self _)).symm
          rw [hmem, Array.getElem?_push_size, Option.some.injEq] at h1
          subst h1
          have e2 : s'.vs.coh (offs a i) = th.vs.coh (offs a i) :=
            storeUnits_cohOff us ws (i + 1) _ s' hs _ fun j => offs_ne a (by omega)
          show s'.vs.coh (offs a i) = _
          rw [e2, hcoh]; simp
        · exact ih t m (by show mem'.size ≤ t; rw [hmem, Array.size_push]; omega) hm
      · exact ih t m (by show mem'.size ≤ t; rw [hmem]; exact ht) hm
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨q1, -, q3, -, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R
        at q1 q3 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q3 hs
      have ih := storeUnits_newCoh us ws (i + 2) _ s' hs
      have hg := (storeUnits_growsF us ws (i + 2) _ s' hs).1
      have hnx : (offs a i).next = offs a (i + 1) := by simp only [offs, Address.next, Nat.add_assoc]
      intro t m ht hm
      have hsz : mem'.size = s.mem.size + 2 := by rw [q1, Array.size_push, Array.size_push]
      by_cases e : s.mem.size + 2 ≤ t
      · exact ih t m (by show mem'.size ≤ t; omega) hm
      · have h1 : mem'[t]? = some m := by rw [← hm]; exact (hg.2.1 _ (by show _ < mem'.size; omega)).symm
        rw [q1] at h1
        by_cases e1 : t = s.mem.size
        · subst e1
          rw [Array.getElem?_push, if_neg (by rw [Array.size_push]; omega), Array.getElem?_push_size,
            Option.some.injEq] at h1
          subst h1
          have e2 : s'.vs.coh (offs a i) = th.vs.coh (offs a i) :=
            storeUnits_cohOff us ws (i + 2) _ s' hs _ fun j => offs_ne a (by omega)
          show s'.vs.coh (offs a i) = _
          rw [e2, q3]; simp
        · have e1' : t = s.mem.size + 1 := by omega
          subst e1'
          rw [Array.getElem?_push, if_pos (by rw [Array.size_push]), Option.some.injEq] at h1
          subst h1
          have e2 : s'.vs.coh (offs a i).next = th.vs.coh (offs a i).next :=
            storeUnits_cohOff us ws (i + 2) _ s' hs _ fun j => by rw [hnx]; exact offs_ne a (by omega)
          show s'.vs.coh (offs a i).next = _
          have hne : (offs a i).next ≠ offs a i := by rw [hnx]; exact offs_ne a (by omega)
          rw [e2, q3]; simp [hne]
  | .one :: _, [], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, hs => by simp [storeUnits] at hs
#print axioms TermPiece.storeUnits_newCoh

/-- (OvW3 R2c) `FirstW` survives a memory extension adding no message at `A`. -/
theorem firstW_ext {M M' : Memory} {A : Address} (hold : ∀ t, t < M.size → M'[t]? = M[t]?)
    (hnew : ∀ (t : Nat) (m : Msg), M.size ≤ t → M'[t]? = some m → m.loc ≠ A) {h : Ts} :
    FirstW M' A h ↔ FirstW M A h := by
  constructor
  · rintro ⟨⟨m, hm, hl, hv⟩, hb⟩
    have hh : h < M.size := Classical.byContradiction fun hn => hnew h m (Nat.le_of_not_lt hn) hm hl
    refine ⟨⟨m, by rw [← hold h hh]; exact hm, hl, hv⟩, fun t m' ht hm' hl' => hb t m' ht ?_ hl'⟩
    rw [hold t (Nat.lt_trans ht hh)]; exact hm'
  · rintro ⟨⟨m, hm, hl, hv⟩, hb⟩
    have hh : h < M.size := lt_size_of_some hm
    refine ⟨⟨m, by rw [hold h hh]; exact hm, hl, hv⟩, fun t m' ht hm' hl' => hb t m' ht ?_ hl'⟩
    rw [← hold t (Nat.lt_trans ht hh)]; exact hm'
#print axioms TermPiece.firstW_ext

/-- (OvW3 R2c) **The skipped promises across a store**, at an address the store adds no message
to: they only shrink, by promises the store discharged. -/
theorem promAt_ext {E : TEnv} {s s' : St} {A : Address} (hold : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hnew : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → m.loc ≠ A)
    (hsub : ∀ u, u ∈ s'.promises → u ∈ s.promises) :
    (∀ u, u ∈ PromAt E s' A → u ∈ PromAt E s A) ∧
      (∀ u, u ∈ PromAt E s A → u ∉ PromAt E s' A → u ∈ s.promises ∧ u ∉ s'.promises) := by
  have hfw : ∀ u, AboveFW s'.mem A u ↔ AboveFW s.mem A u := fun u =>
    ⟨fun ⟨h, h1, h2⟩ => ⟨h, (firstW_ext hold hnew).1 h1, h2⟩, fun ⟨h, h1, h2⟩ => ⟨h, (firstW_ext hold hnew).2 h1, h2⟩⟩
  unfold PromAt
  by_cases hv : VisU E A
  · simp only [hv, ite_true]
    exact ⟨fun u h => h, fun u h _ => absurd h List.not_mem_nil⟩
  · by_cases hq : PredU E A
    · simp only [hv, hq, ite_true, ite_false, List.mem_filter, List.mem_append, decide_eq_true_eq]
      refine ⟨fun u ⟨h1, h2⟩ => ⟨h1.imp (hsub u) id, (hfw u).1 h2⟩, fun u ⟨h1, h2⟩ hn => ?_⟩
      rcases h1 with h1 | h1
      · exact ⟨h1, fun h => hn ⟨Or.inl h, (hfw u).2 h2⟩⟩
      · exact absurd ⟨Or.inr h1, (hfw u).2 h2⟩ hn
    · simp only [hv, hq, ite_false, List.mem_append]
      refine ⟨fun u h => h.imp (hsub u) id, fun u h1 hn => ?_⟩
      rcases h1 with h1 | h1
      · exact ⟨h1, fun h => hn (Or.inl h)⟩
      · exact absurd (Or.inr h1) hn
#print axioms TermPiece.promAt_ext

/-- (OvW3 R2c) **An overtaken fulfil keeps the latest word**: if the step discharged only
`th0` among `A`'s skipped promises, adds no message at `A`, and leaves a non-skipped message
above `th0` there, `A`'s latest word is unchanged. -/
theorem latestNP_keepO {E : TEnv} {s s' : St} {A : Address} {x : Word} {th0 : Ts}
    (hold : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hnew : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → m.loc ≠ A)
    (hP1 : ∀ u, u ∈ PromAt E s' A → u ∈ PromAt E s A)
    (hP2 : ∀ u m, s.mem[u]? = some m → m.loc = A → u ∈ PromAt E s A → u ∉ PromAt E s' A → u = th0)
    (hx : LatestNP s.mem (PromAt E s A) A x)
    (hov : ∃ (t : Ts) (m : Msg), th0 < t ∧ s'.mem[t]? = some m ∧ m.loc = A ∧ t ∉ PromAt E s' A) :
    LatestNP s'.mem (PromAt E s' A) A x := by
  obtain ⟨tx, mx, hxn, hmx, hlx, hwx, hlast⟩ := hx
  obtain ⟨t, m, h0t, hm, hl, htn⟩ := hov
  have htz : t < s.mem.size := Classical.byContradiction fun hn => hnew t m (Nat.le_of_not_lt hn) hm hl
  have hm0 : s.mem[t]? = some m := by rw [← hold t htz]; exact hm
  have htP : t ∉ PromAt E s A := fun h => absurd (hP2 t m hm0 hl h htn) (Nat.ne_of_gt h0t)
  have htx : t ≤ tx := Nat.le_of_not_lt fun h => htP (hlast t m h hm0 hl)
  have hxz : tx < s.mem.size := lt_size_of_some hmx
  refine ⟨tx, mx, fun h => hxn (hP1 tx h), by rw [hold tx hxz]; exact hmx, hlx, hwx, fun t' m' h1 h2 h3 => ?_⟩
  have h1z : t' < s.mem.size := Classical.byContradiction fun hn => hnew t' m' (Nat.le_of_not_lt hn) h2 h3
  have h2' : s.mem[t']? = some m' := by rw [← hold t' h1z]; exact h2
  have hin := hlast t' m' h1 h2' h3
  exact Classical.byContradiction fun hn =>
    absurd (hP2 t' m' h2' h3 hin hn) (Nat.ne_of_gt (Nat.lt_of_lt_of_le h0t (Nat.le_trans htx (Nat.le_of_lt h1))))
#print axioms TermPiece.latestNP_keepO

theorem nWords_take_monoR (us : List Acc) {i i' : Nat} (h : i ≤ i') : nWords (us.take i) ≤ nWords (us.take i') := by
  have e : (us.take i').take i = us.take i := by rw [List.take_take, Nat.min_eq_left h]
  rw [← e]; exact TermStep.nWords_take_le _ _
#print axioms TermPiece.nWords_take_monoR

/-- (OvW3 R2c) A word lies in one access unit. -/
theorem inAcc_uniqR {us : List Acc} {i i' o : Nat} (h : InAcc us i o) (h' : InAcc us i' o) : i = i' := by
  rcases Nat.lt_trichotomy i i' with hl | rfl | hl
  · have := nWords_take_monoR us (show i + 1 ≤ i' by omega)
    have := h.2; have := h'.1; omega
  · rfl
  · have := nWords_take_monoR us (show i' + 1 ≤ i by omega)
    have := h'.2; have := h.1; omega
#print axioms TermPiece.inAcc_uniqR

/-- (OvW3 R2c) A one-word unit holds one word. -/
theorem inAcc_oneR {us : List Acc} {i o : Nat} (hu : us[i]? = some .one) (h : InAcc us i o) :
    o = nWords (us.take i) := by
  have e := TermNPmixW.nWords_take_succ_get us i _ hu
  have := h.1; have := h.2
  simp only [Acc.size] at e
  omega
#print axioms TermPiece.inAcc_oneR

/-- (OvW3 R2c) A unit of an embedded layout is a unit of the whole, shifted. -/
theorem inAcc_embR {pre usS post : List Acc} {i o : Nat} (h : InAcc usS i o) :
    InAcc (pre ++ usS ++ post) (pre.length + i) (nWords pre + o) ∧ (pre ++ usS ++ post)[pre.length + i]? = usS[i]? := by
  have hi : i < usS.length := by
    apply Classical.byContradiction
    intro hn
    have h1 : usS.take i = usS := List.take_of_length_le (by omega)
    have h2 : usS.take (i + 1) = usS := List.take_of_length_le (by omega)
    have := h.1; have := h.2; rw [h1] at *; rw [h2] at *; omega
  have e1 : (pre ++ usS ++ post).take (pre.length + i) = pre ++ usS.take i := by
    rw [List.append_assoc, List.take_append, List.take_append_of_le_length (by omega)]; simp [List.take_of_length_le]
  have e2 : (pre ++ usS ++ post).take (pre.length + (i + 1)) = pre ++ usS.take (i + 1) := by
    rw [List.append_assoc, List.take_append, List.take_append_of_le_length (by omega)]; simp [List.take_of_length_le]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [e1, TermTear.nWords_append]; have := h.1; omega
  · rw [show pre.length + i + 1 = pre.length + (i + 1) by omega, e2, TermTear.nWords_append]; have := h.2; omega
  · rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hi]
#print axioms TermPiece.inAcc_embR

theorem wle_getR : ∀ {a b : List Word}, WLe a b → ∀ (k : Nat) x y, a[k]? = some x → b[k]? = some y → WLe1 x y
  | [], [], _, _, _, _, h, _ => by simp at h
  | x0 :: a, y0 :: b, h, k, x, y, hx, hy => by
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy; subst hx; subst hy; exact h.1
      · simp only [List.getElem?_cons_succ] at hx hy; exact wle_getR h.2 k x y hx hy
  | [], _ :: _, h, _, _, _, _, _ => (h : False).elim
  | _ :: _, [], h, _, _, _, _, _ => (h : False).elim
#print axioms TermPiece.wle_getR

theorem wle_ofR : ∀ {a b : List Word}, a.length = b.length →
    (∀ (k : Nat) x y, a[k]? = some x → b[k]? = some y → WLe1 x y) → WLe a b
  | [], [], _, _ => trivial
  | x0 :: a, y0 :: b, hl, h => ⟨h 0 x0 y0 rfl rfl, wle_ofR (by simpa using hl) fun k x y hx hy => h (k + 1) x y hx hy⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
#print axioms TermPiece.wle_ofR

/-- (OvW3 R2c) **Re-selecting a store's mix**: units whose old words are still the latest
after the step can be taken from the old words; the selection then keeps them old. -/
theorem mix_flip {E : TEnv} {s' : St} {ad : Address} {us : List Acc} {sel : Nat → Bool} {wsn qold vals : List Word}
    (hln : wsn.length = nWords us) (hlq : qold.length = nWords us)
    (hW : WLe (TermTear.mixU us sel wsn qold) vals)
    (hL : ∀ j x, vals[j]? = some x → LatestNP s'.mem (PromAt E s' (offs ad (0 + j))) (offs ad (0 + j)) x) :
    ∃ (sel' : Nat → Bool) (vals' : List Word), WLe (TermTear.mixU us sel' wsn qold) vals' ∧
      (∀ j x, vals'[j]? = some x → LatestNP s'.mem (PromAt E s' (offs ad (0 + j))) (offs ad (0 + j)) x) ∧
      (∀ n, (∀ j w, InAcc us n j → qold[j]? = some w →
        LatestNP s'.mem (PromAt E s' (offs ad (0 + j))) (offs ad (0 + j)) w) → sel' n = false) ∧
      ∀ n, sel n = false → sel' n = false := by
  classical
  let AL : Nat → Prop := fun n => ∀ j w, InAcc us n j → qold[j]? = some w →
    LatestNP s'.mem (PromAt E s' (offs ad (0 + j))) (offs ad (0 + j)) w
  let fl : Nat → Bool := fun n => decide (sel n = true ∧ AL n)
  let sel' : Nat → Bool := fun n => decide (sel n = true ∧ ¬ AL n)
  have hlv : vals.length = nWords us := by rw [← TermStep.WLe.length hW, TermTear.length_mixU us sel _ _ hln hlq]
  refine ⟨sel', TermTear.mixU us fl qold vals, wle_ofR ?_ ?_, fun j x hx => ?_, fun n hn => ?_,
    fun n hn => by simp only [sel', decide_eq_false_iff_not]; exact fun h => absurd h.1 (by rw [hn]; simp)⟩
  · rw [TermTear.length_mixU us _ _ _ hln hlq, TermTear.length_mixU us _ _ _ hlq hlv]
  · intro k x y hx hy
    have hk : k < nWords us := by
      have := (List.getElem?_eq_some_iff.1 hx).1
      rwa [TermTear.length_mixU us _ _ _ hln hlq] at this
    obtain ⟨i, hI⟩ := TermNPmixW.inAcc_exW us k hk
    rw [TermTear.mixU_getElem us _ _ _ i k hln hlq hI] at hx
    rw [TermTear.mixU_getElem us _ _ _ i k hlq hlv hI] at hy
    by_cases hf : sel i = true ∧ AL i
    · have e1 : sel' i = false := by simp only [sel', decide_eq_false_iff_not]; exact fun h => h.2 hf.2
      have e2 : fl i = true := by simp only [fl, decide_eq_true_eq]; exact hf
      rw [e1] at hx; rw [e2] at hy
      simp only [ite_true] at hy
      simp only [Bool.false_eq_true, ite_false] at hx
      rw [hx] at hy; cases hy; exact WLe1_refl _
    · have e2 : fl i = false := by simp only [fl, decide_eq_false_iff_not]; exact hf
      have e1 : sel' i = sel i := by
        cases h : sel i
        · simp only [sel', h, Bool.false_eq_true, false_and, decide_false]
        · simp only [sel', h, true_and, decide_eq_true_eq]; exact fun ha => hf ⟨h, ha⟩
      rw [e1] at hx; rw [e2] at hy
      simp only [Bool.false_eq_true, ite_false] at hy
      refine wle_getR hW k x y ?_ hy
      rw [TermTear.mixU_getElem us _ _ _ i k hln hlq hI]; exact hx
  · have hk : j < nWords us := by
      have := (List.getElem?_eq_some_iff.1 hx).1
      rwa [TermTear.length_mixU us _ _ _ hlq hlv] at this
    obtain ⟨i, hI⟩ := TermNPmixW.inAcc_exW us j hk
    rw [TermTear.mixU_getElem us _ _ _ i j hlq hlv hI] at hx
    by_cases hf : sel i = true ∧ AL i
    · have e2 : fl i = true := by simp only [fl, decide_eq_true_eq]; exact hf
      rw [e2] at hx; simp only [ite_true] at hx
      exact hf.2 j x hI hx
    · have e2 : fl i = false := by simp only [fl, decide_eq_false_iff_not]; exact hf
      rw [e2] at hx; simp only [Bool.false_eq_true, ite_false] at hx
      exact hL j x hx
  · simp only [sel', decide_eq_false_iff_not]; exact fun h => h.2 hn
#print axioms TermPiece.mix_flip

theorem res_mem_le_sumR {α : Type} {f : α → Res} {x : α} : ∀ {L : List α}, x ∈ L → f x ≤ Res.sum (L.map f)
  | [], h => absurd h List.not_mem_nil
  | y :: L, h => by
      intro kk
      rcases List.mem_cons.1 h with rfl | h
      · simp only [List.map_cons, Res.sum_cons, Res.add_apply]; omega
      · have := res_mem_le_sumR (f := f) h kk
        simp only [List.map_cons, Res.sum_cons, Res.add_apply]; omega
#print axioms TermPiece.res_mem_le_sumR

/-! ### (option 3) The fulfilled visible word units of a store -/

theorem fulUnits_nodup {E : TEnv} {s s' : St} {a : Address} {us : List Acc} : (fulUnits E s s' a us).Nodup :=
  List.nodup_range.sublist List.filter_sublist

theorem fulUnits_lt {E : TEnv} {s s' : St} {a : Address} {us : List Acc} {j : Nat}
    (hj : j ∈ fulUnits E s s' a us) : j < nWords us :=
  List.mem_range.1 (List.mem_filter.1 hj).1

open Classical in
/-- A fulfilled promise at a visible protocol word unit `j` of the store puts `j` in `fulUnits`. -/
theorem mem_fulUnits {E : TEnv} {s s' : St} {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address}
    {rel : Bool} {us : List Acc} {ws : List Word} (hP : PromLt s) (hs : s' ∈ storeUnits k arch pw a rel us ws 0 s)
    {t : Ts} {m : Msg} {j n : Nat} {P : Proto} (ht : t ∈ s.promises) (hn : t ∉ s'.promises)
    (hm : s.mem[t]? = some m) (hl : m.loc = offs a j) (hV : Vis E m.loc.label) (hwa : WordAt E m.loc n P) :
    j ∈ fulUnits E s s' a us := by
  obtain ⟨m1, j1, -, hm1, hj1, -, hl1, -⟩ := storeUnits_fulVal hP hs ht hn
  rw [hm] at hm1; cases hm1
  have e : j = j1 := by
    rw [hl1] at hl; have := congrArg WeakMem.Address.offset hl; simp [offs] at this; omega
  subst e
  exact List.mem_filter.2 ⟨List.mem_range.2 hj1, by
    rw [decide_eq_true_iff]; exact ⟨t, _, n, P, ht, hn, hm, hl, hV, hwa⟩⟩

open Classical in
/-- A unit selection that is off at the fulfilled visible word units leaves `fulUnits` unselected. -/
theorem fulUnits_unsel {E : TEnv} {s s' : St} {a : Address} {us : List Acc} {sel : Nat → Bool} {j : Nat}
    (hj : j ∈ fulUnits E s s' a us)
    (h : ∀ t m n, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc = offs a (0 + j) →
      VisU E m.loc → InAcc us n j → sel n = false) :
    @decide (∃ i, sel i = true ∧ InAcc us i j) (Classical.propDecidable _) = false := by
  obtain ⟨t, m, n, P, ht, hn, hm, hl, hV, hw⟩ := of_decide_eq_true (List.mem_filter.1 hj).2
  refine @decide_eq_false _ (Classical.propDecidable _) ?_
  rintro ⟨i, hsi, hI⟩
  rw [h t m i ht hn hm (by rw [hl, Nat.zero_add]) ⟨WordAt_unit hw, hV⟩ hI] at hsi
  cases hsi

/-- (OvW3 R2c) **Re-pin items from an own store's mix**: at an own cell with a frontier, the
store's mix (re-selected by `mix_flip`) leaves the other mix `Rb`; carving it over the pieces
holding an own promise at the post-state gives re-pin items, covering every fulfilled,
overtaken unit inside a solid piece, together held by `Rb`. -/
theorem repin_mixU {E : TEnv} {s s' : St} {k : Promises.Knobs} {arch : Arch} {pw : Word} {ad : Address}
    {rel : Bool} {c : Cell} {f : Ts} {U : Ty} {us : List Acc} {wsv qold vals : List Word} {Rv Rq : Res}
    {sel : Nat → Bool}
    (hsto : E.sto ad.label = some c) (hown : c.owner = some E.tid) (hf : E.pfr ad.label = some f)
    (hlay : LayT c.ty) (hnoT : Ty.noOwnIn [] c.ty = true) (hat : AtOff c.ty ad.offset U)
    (hus : accs U = some us) (hcpU : Ty.coupledOKIn [] U = true) (hiaU : TermTear.IallOK [] U = true)
    (hs' : s' ∈ storeUnits k arch pw ad rel us wsv 0 s) (hnd : s.promises.Nodup)
    (hPb : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hvn : VRR (fun _ => 0) (CE E.unsee) U (shp U) (wsv.map (bumpW s.vs.vRelSt)) Rv)
    (hVn : Valid U (wsv.map (bumpW s.vs.vRelSt))) (hln : (wsv.map (bumpW s.vs.vRelSt)).length = nWords us)
    (hvq : VRR (fun _ => 0) (CE E.unsee) U (shp U) qold Rq) (hVq : Valid U qold) (hlq : qold.length = nWords us)
    (hLq : ∀ j w, qold[j]? = some w → LatestNP s.mem (PromAt E s (offs ad (0 + j))) (offs ad (0 + j)) w)
    (hW : WLe (TermTear.mixU us sel (wsv.map (bumpW s.vs.vRelSt)) qold) vals)
    (hL : ∀ j x, vals[j]? = some x → LatestNP s'.mem (PromAt E s' (offs ad (0 + j))) (offs ad (0 + j)) x)
    (hselF : ∀ t m j n, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc = offs ad (0 + j) →
      VisU E m.loc → InAcc us n j → sel n = false) :
    ∃ (sel' : Nat → Bool) (vals' : List Word) (Rm : Res) (RS : List (AllocLabel × Cell × CrIt)),
      VRR (fun _ => 0) (CE E.unsee) U (shp U) (TermTear.mixU us sel' (wsv.map (bumpW s.vs.vRelSt)) qold) Rm ∧
      Valid U (TermTear.mixU us sel' (wsv.map (bumpW s.vs.vRelSt)) qold) ∧
      WLe (TermTear.mixU us sel' (wsv.map (bumpW s.vs.vRelSt)) qold) vals' ∧
      (∀ j x, vals'[j]? = some x → LatestNP s'.mem (PromAt E s' (offs ad (0 + j))) (offs ad (0 + j)) x) ∧
      (∀ y ∈ RS, RepinItU E s' y ∧ y.1 = ad.label) ∧
      Rm + Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) + Dsum s s' (fwr E s) ≤ Rv + Rq ∧
      ∀ (o : Nat) th0 tw, ¬ VisU E ⟨ad.label, o⟩ → LowOwn s ⟨ad.label, o⟩ th0 → th0 ∉ s'.promises →
        LowOwn s' ⟨ad.label, o⟩ tw → OverT E s' ⟨ad.label, o⟩ tw → WinGU E s' ad.label o tw →
        (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
        ∃ y ∈ RS, y.1 = ad.label ∧ CrCov y.2.2 o := by
  classical
  generalize hwn : wsv.map (bumpW s.vs.vRelSt) = wsn at hvn hVn hln hW
  obtain ⟨sel', vals', hW', hL', hfl, hsm⟩ := mix_flip (E := E) (ad := ad) hln hlq hW hL
  obtain ⟨Rm, Rb, hvm, hvb, hRm⟩ := TermTear.VRR_mix2 (sel := sel') hcpU hiaU hus hvn hvq hln hlq
  have hVm := TermTear.Valid_mix (sel := sel') hus hVn hVq hln hlq
  have hVb := TermTear.Valid_mix (sel := sel') hus hVq hVn hlq hln
  have hlb := TermTear.length_mixU us sel' _ _ hlq hln
  -- the store's facts
  obtain ⟨hold, -, -, -⟩ := storeUnits_untouched us wsv 0 s s' hs'
  have hsub := (storeUnits_growsF us wsv 0 s s' hs').2.1
  have hful := storeUnits_fulU us wsv 0 s s' hnd hPb hs'
  have hncoh := storeUnits_newCoh us wsv 0 s s' hs'
  -- the bump targets: the fulfilled message at each unit
  let tgt : Nat → Word := fun j => ((s.mem[s'.vs.coh (offs ad (0 + j))]?).map mw).getD (mw ⟨ad, .undef, 0⟩)
  let Cv : Nat → Prop := fun j => (∃ th0 m0, th0 ∈ s.promises ∧ th0 ∉ s'.promises ∧ s.mem[th0]? = some m0 ∧
    m0.loc = offs ad (0 + j)) ∧ ∃ i, InAcc us i j ∧ sel' i = false
  have htg : ∀ j th0 m0, th0 ∈ s.promises → th0 ∉ s'.promises → s.mem[th0]? = some m0 →
      m0.loc = offs ad (0 + j) → s'.vs.coh (offs ad (0 + j)) = th0 ∧ tgt j = mw m0 ∧
      ∃ w, wsv[j]? = some w ∧ WLe1 (bumpW s.vs.vRelSt w) (mw m0) := by
    intro j th0 m0 h1 h2 h3 h4
    obtain ⟨n, j', m, w, -, -, hm, hw, hl, hv, hr, hpv, hc⟩ := hful th0 h1 h2
    rw [h3] at hm; cases hm
    have ejj : j' = j := by
      have := congrArg Address.offset (hl.symm.trans h4); simp [offs] at this; omega
    subst ejj
    refine ⟨hc, by simp only [tgt, hc, h3, Option.map_some, Option.getD_some], w, hw, ?_, ?_⟩
    · show w.val = m0.val; exact hv.symm
    · intro x g hx
      show max w.view s.vs.vRelSt ≤ m0.view
      exact Nat.max_le.2 ⟨hpv x g hx, hr⟩
  have hbump : ∀ j v, (TermTear.mixU us sel' qold wsn)[j]? = some v → Cv j → WLe1 v (tgt j) := by
    rintro j v hv ⟨⟨th0, m0, h1, h2, h3, h4⟩, i, hI, hsi⟩
    obtain ⟨-, e2, w, hw, hle⟩ := htg j th0 m0 h1 h2 h3 h4
    rw [TermTear.mixU_getElem us sel' _ _ i j hlq hln hI, hsi] at hv
    simp only [Bool.false_eq_true, ite_false] at hv
    rw [← hwn, List.getElem?_map, hw, Option.map_some, Option.some.injEq] at hv
    rw [← hv, e2]; exact hle
  obtain ⟨ws1, hl1, hv1, hV1, hp1⟩ := bump_sel hvb hVb Cv tgt hbump
  rw [hlb] at hl1
  -- carve over the pieces of `U` holding an own promise at `s'` off visible units, with the
  -- (option 3) word shares of the fulfilled visible word units
  let hitN : Ts → Bool := fun t => decide (∃ m, s'.mem[t]? = some m ∧ ¬ VisU E m.loc)
  let L := dedupC ((s'.promises.filter hitN).filterMap (pcAt s' ad.label ad.offset U))
  have hLp : ∀ p ∈ L, Piece U p.1 p.2 := fun p hp => by
    obtain ⟨t, -, ht⟩ := List.mem_filterMap.1 (mem_dedupC.1 hp)
    exact (pcAt_some ht).1
  have hT : accs U ≠ none := by rw [hus]; simp
  have hwcU : wc U = some ws1.length := by rw [hl1]; exact wc_of_accs hus
  let Lx := fulUnits E s s' ad us
  have hLxnd : Lx.Nodup := fulUnits_nodup
  have hLxl : ∀ j ∈ Lx, j < nWords us := fun j hj => fulUnits_lt hj
  have hdis : ∀ j ∈ Lx, ∀ n P, WordAt E.unsee (offs ad j) n P → (j, Ty.word (.lit n) P) ∉ L := by
    intro j hj n P hw hm
    obtain ⟨t, ht, hpc⟩ := List.mem_filterMap.1 (mem_dedupC.1 hm)
    obtain ⟨-, m, vs, hm1, hml, hvs, h1, h2⟩ := pcAt_some hpc
    obtain ⟨-, -, -, hgh⟩ := hw
    have hvs1 : vs = [Acc.one] := by
      have : accs (Ty.word (.lit n) P) = some [Acc.one] := by simp [accs, hgh]
      rw [this] at hvs; exact (Option.some.inj hvs).symm
    subst hvs1
    have h1' : nWords [Acc.one] = 1 := rfl
    simp only [h1'] at h2
    obtain ⟨m', hm', hnV⟩ := of_decide_eq_true (List.mem_filter.1 ht).2
    rw [hm1] at hm'; cases hm'
    have h1'' : ad.offset + j ≤ m.loc.offset := h1
    have h2'' : ad.offset + j + 1 > m.loc.offset := h2
    have eo : m.loc.offset = ad.offset + j := by simp only [WeakMem.Offset] at h1'' h2'' ⊢; omega
    have el : m.loc = offs ad j := by
      show m.loc = ⟨ad.label, ad.offset + j⟩
      rw [show m.loc = ⟨m.loc.label, m.loc.offset⟩ from rfl, hml, eo]
    obtain ⟨t1, m1, n1, P1, -, -, -, hl1', hV1, hw1⟩ := of_decide_eq_true (List.mem_filter.1 hj).2
    exact hnV (by rw [el, ← hl1']; exact ⟨WordAt_unit hw1, hV1⟩)
  obtain ⟨G, eG, hG, Gx, hGx2, hGx⟩ := vrr_carveX E.unsee hsto hat hus hv1 hl1 hLp (nodup_dedupC _) hLxnd hLxl hdis
  have hGR : Res.sum (G.map Prod.snd) ≤ Rb := Res.le_trans (Res.le_add_right _ _) hGx2
  -- (option 3) the fulfilled promises' words are paid by the word shares
  have hXs : Dsum s s' (fwr E s) ≤ Res.sum (Lx.map Gx) := by
    refine fwr_le_shares (V := s.vs.vRelSt) (comp := TermTear.mixU us sel' qold wsn) hPb hnd hs'
      (fun t m j ht hn hm hl hV => ?_) (fun t m j n P ht hn hm hl hV hwa => ?_) (fun j hj n P x hw hx => ?_)
    · obtain ⟨m1, j1, -, hm1, hj1, -, hl1', -⟩ := storeUnits_fulVal hPb hs' ht hn
      rw [hm] at hm1; cases hm1
      have e : j = j1 := by
        rw [hl1'] at hl; have := congrArg WeakMem.Address.offset hl; simp [offs] at this; omega
      subst e
      obtain ⟨i, hI⟩ := TermNPmixW.inAcc_exW us j hj1
      have hsi : sel' i = false := hsm i (hselF t m j i ht hn hm (by rw [hl, Nat.zero_add]) hV hI)
      rw [TermTear.mixU_getElem us sel' _ _ i j hlq hln hI, hsi, ← hwn]
      rfl
    · exact mem_fulUnits hPb hs' ht hn hm hl hV hwa
    · obtain ⟨y, hy⟩ : ∃ y, ws1[j]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by rw [hl1]; exact hLxl j hj)⟩
      have hxy : x.val = y.val := by
        by_cases hc : Cv j
        · rw [(hp1 j y hy).1 hc]; exact (hbump j x hx hc).1
        · have := (hp1 j y hy).2 hc; rw [hx] at this; cases this; rfl
      rw [hxy]; exact hGx j hj n P y hw hy
  -- Rb is key-free
  have hkb : CrKeysP Rb := fun l => TermBlkZ.VRR_own_zero l U [] (CE E.unsee) (fun _ => 0) (shp U) _ Rb
    (noOwn_AtOff hat hnoT) (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h) hvb
  let itm : (Nat × Ty) × Res → List Acc → Ts → AllocLabel × Cell × CrIt := fun g usS t =>
    (ad.label, c, (t, ad.offset + g.1.1, g.1.2, (ws1.drop g.1.1).take (nWords usS), g.2,
      kPinU E s' ad.label (ad.offset + g.1.1) usS ((ws1.drop g.1.1).take (nWords usS)) (fun _ => true)))
  let Q : (Nat × Ty) × Res → AllocLabel × Cell × CrIt → Prop := fun g y =>
    ∃ usS t, accs g.1.2 = some usS ∧ y = itm g usS t ∧ RepinItU E s' y
  obtain ⟨RS, hRS1, hRS2, hRS3⟩ := pick_list Q Prod.snd (fun y => y.2.2.2.2.2.2.1)
    (fun g y ⟨usS, t, _, e, _⟩ => by rw [e]; exact Res.le_refl _) G
  refine ⟨sel', vals', Rm, RS, hvm, hVm, hW', hL', fun y hy => ?_, ?_, ?_⟩
  · obtain ⟨g, -, usS, t, -, e, hR⟩ := hRS1 y hy
    exact ⟨hR, by rw [e]⟩
  · intro kk
    have := hRm kk; have := hRS3 kk; have := hGx2 kk; have := hXs kk
    simp only [Res.add_apply] at *; omega
  · intro o th0 tw hnv hlo0 hth0 hlow hov hwin hpc
    obtain ⟨q, S, usS, hP, hvs, hq1, hq2⟩ := hpc
    obtain ⟨hth0s, ⟨m0, hm0, hl0⟩, hmin0⟩ := hlo0
    obtain ⟨n, j, m, w, hun, hjn, hm, hw, hl, -, -, -, hc⟩ := hful th0 hth0s hth0
    rw [hm0] at hm; cases hm
    have hA : offs ad (0 + j) = ⟨ad.label, o⟩ := hl.symm.trans hl0
    have hoj : o = ad.offset + j := by
      have h : ad.offset + (0 + j) = o := congrArg Address.offset hA
      rw [← h, Nat.zero_add]
    have hIn : InAcc us n j := ⟨Nat.le_of_eq hjn.symm, by
      rw [TermNPmixW.nWords_take_succ_get us n _ hun, ← hjn]; simp [Acc.size]⟩
    have hjlt : j < nWords us := Nat.lt_of_lt_of_le hIn.2 (TermStep.nWords_take_le _ _)
    have hc' : s'.vs.coh ⟨ad.label, o⟩ = th0 := by rw [← hA]; exact hc
    -- the new lowest own promise
    have hlowc := hlow
    obtain ⟨htw', ⟨mt, hmt, hlt⟩, -⟩ := hlow
    have htws := hsub tw htw'
    have hmt0 : s.mem[tw]? = some mt := by rw [← hold tw (hPb tw htws)]; exact hmt
    have hlt0 : th0 < tw := Nat.lt_of_le_of_ne (hmin0 tw mt htws hmt0 hlt) (fun e => hth0 (e ▸ htw'))
    have hm0' : s'.mem[th0]? = some m0 := by rw [hold th0 (hPb th0 hth0s)]; exact hm0
    have hpd : PredAt s'.mem ⟨ad.label, o⟩ tw (mw m0) := predAt_of_winGU hc' hlt0 hm0' hl0 hlowc hwin
    -- the unit is re-selected old
    have hsn : sel' n = false := by
      refine hfl n fun j' w' hI' hq' => ?_
      have ej : j' = j := by rw [inAcc_oneR hun hI', hjn]
      subst ej
      have hnew : ∀ (t : Nat) (mm : Msg), s.mem.size ≤ t → s'.mem[t]? = some mm → mm.loc ≠ offs ad (0 + j') :=
        fun t mm ht hmm hll => by
          have e := hncoh t mm ht hmm
          rw [hll, hc] at e
          exact absurd (hPb th0 hth0s) (by rw [e]; exact Nat.not_lt.mpr ht)
      obtain ⟨hP1, hP2'⟩ := promAt_ext (E := E) hold hnew hsub
      refine latestNP_keepO (th0 := th0) hold hnew hP1 (fun u mu hmu hlu hin hnin => ?_) (hLq j' w' hq') ?_
      · obtain ⟨h1, h2⟩ := hP2' u hin hnin
        obtain ⟨nu, ju, mu', wu, -, -, hmu', -, hlu', -, -, -, hcu⟩ := hful u h1 h2
        have e := Option.some.inj (hmu.symm.trans hmu'); subst e
        rw [← hlu', hlu, hc] at hcu
        exact hcu.symm
      · obtain ⟨t, mm, h1, h2, h3, h4⟩ := hov
        exact ⟨t, mm, Nat.lt_trans hlt0 h1, h2, by rw [hA]; exact h3, by rw [hA]; exact h4⟩
    have hCv : Cv j := ⟨⟨th0, m0, hth0s, hth0, hm0, hl0.trans hA.symm⟩, n, hIn, hsn⟩
    obtain ⟨-, htgj, -⟩ := htg j th0 m0 hth0s hth0 hm0 (hl0.trans hA.symm)
    have hw1 : ws1[j]? = some (mw m0) := by
      obtain ⟨w1, hw1⟩ : ∃ w1, ws1[j]? = some w1 := ⟨_, List.getElem?_eq_getElem (by rw [hl1]; exact hjlt)⟩
      rw [hw1, ← htgj, (hp1 j w1 hw1).1 hCv]
    -- the piece, inside `U`
    obtain ⟨hoq, hqe, hPU⟩ := Piece_sub hat hus hP hvs (by omega) (by omega)
    have hhit : PcHit s' ad.label ad.offset U tw (q - ad.offset, S) :=
      ⟨hPU, mt, usS, hmt, by rw [hlt], hvs, by rw [hlt]; show ad.offset + (q - ad.offset) ≤ o; rw [Nat.add_sub_cancel' hoq]; exact hq1,
        by rw [hlt]; show ad.offset + (q - ad.offset) + nWords usS > o; rw [Nat.add_sub_cancel' hoq]; exact hq2⟩
    have hmem : (q - ad.offset, S) ∈ L := mem_dedupC.2 (List.mem_filterMap.2 ⟨tw,
      List.mem_filter.2 ⟨htw', decide_eq_true ⟨mt, hmt, by rw [hlt]; exact hnv⟩⟩, pcAt_of hhit⟩)
    rw [← eG] at hmem
    obtain ⟨g0, hg0, e0⟩ := List.mem_map.1 hmem
    have hg01 : g0.1.1 = q - ad.offset := by rw [e0]
    have hg02 : g0.1.2 = S := by rw [e0]
    have hPg : Piece U g0.1.1 g0.1.2 := by rw [hg01, hg02]; exact hPU
    obtain ⟨nn, hnn, hlen, hval⟩ := pcR_valOf (hG g0 hg0) hPg hT hV1 hwcU
    have hvs' : accs g0.1.2 = some usS := by rw [hg02]; exact hvs
    have enn : nn = nWords usS := Option.some.inj (hnn.symm.trans (wc_of_accs hvs'))
    subst enn
    have hPc : Piece c.ty (ad.offset + g0.1.1) g0.1.2 := Piece_lift hat hPg
    have eq0 : ad.offset + g0.1.1 = q := by rw [hg01]; exact Nat.add_sub_cancel' hoq
    have ho0 : o - q < nWords usS := by omega
    obtain ⟨i0, hI0⟩ := TermNPmixW.inAcc_exW usS (o - q) ho0
    obtain ⟨pre, post, epre, hnpre⟩ := AtOff_embed hPU.1 hus hvs
    have hnw1 : ¬ WordUnit E ⟨ad.label, o⟩ := fun hwu => hnv ⟨hwu, Vis_pfr hf⟩
    have hK0 : kPinU E s' ad.label (ad.offset + g0.1.1) usS ((ws1.drop g0.1.1).take (nWords usS)) (fun _ => true) i0
        = true := by
      refine kPinU_iff.2 ⟨rfl, fun o' hI' => ?_⟩
      have e1 := inAcc_embR (pre := pre) (post := post) hI'
      have e2 := inAcc_embR (pre := pre) (post := post) hI0
      rw [← epre] at e1 e2
      have ej : nWords pre + (o - q) = j := by omega
      rw [ej] at e2
      have ein : pre.length + i0 = n := inAcc_uniqR e2.1 hIn
      rw [ein] at e1
      have eo := inAcc_oneR hun e1.1
      have eo' : o' = o - q := by omega
      subst eo'
      refine ⟨tw, by rw [eq0, show q + (o - q) = o by omega]; exact ⟨htw', ⟨mt, hmt, hlt⟩, hlowc.2.2⟩,
        by rw [eq0, show q + (o - q) = o by omega]; exact hwin,
        fun w hw => ?_⟩
      rw [List.getElem?_take_of_lt ho0, List.getElem?_drop, show g0.1.1 + (o - q) = j by omega, hw1] at hw
      cases hw
      rw [eq0, show q + (o - q) = o by omega]; exact hpd
    have hnw : ∀ o', ad.offset + g0.1.1 ≤ o' → o' < ad.offset + g0.1.1 + nWords usS → ¬ WordUnit E ⟨ad.label, o'⟩ :=
      nword_piece hsto hPc hvs' (by omega) (by omega) hnw1
    have hkg : CrKeysP g0.2 := fun l => by
      have h1 := hkb l
      have h2 := hGR (.own l)
      have h3 := res_mem_le_sumR (f := Prod.snd) hg0 (.own l)
      omega
    obtain ⟨t, hRt⟩ := repin_itemU (K := fun _ => true) hsto hown (by rw [hf]; simp) hlay hPc hvs' hnw
      (by simpa using hlen) hval hkg hI0 hK0
    obtain ⟨y, hy, usS', t', hvs'', ey, -⟩ := hRS2 g0 hg0 ⟨_, usS, t, hvs', rfl, hRt⟩
    rw [hvs'] at hvs''; cases hvs''
    refine ⟨y, hy, by rw [ey], ?_⟩
    rw [ey]
    exact kPinU_cov hvs' hK0 (by omega) (by rw [eq0]; exact hI0)
#print axioms TermPiece.repin_mixU

/-- (OvW3 R2c) A held cell's type has a layout. -/
theorem LayT_of_CellR {η : TEnv} {n nr : Nat} {T : Ty} {vals : List Word} {Rs : List Res}
    (h : CellR η n nr T vals Rs) : LayT T := by
  rcases h with ⟨hwc, -⟩ | ⟨N, e, us, hT, hus, -⟩
  · left; intro h; simp [wc, h] at hwc
  · exact Or.inr ⟨N, e, hT, by rw [hus]; simp⟩
#print axioms TermPiece.LayT_of_CellR

/-- (OvW3 R2c) No re-pin items add nothing. -/
theorem R_nil {X Y : Res} (h : X ≤ Y) :
    X + Res.sum (([] : List (AllocLabel × Cell × CrIt)).map fun y => y.2.2.2.2.2.2.1) ≤ Y := by
  simpa using h
#print axioms TermPiece.R_nil

/-- (OvW3 R2c) A store's target label is its evaluated address's label. -/
theorem opTgtP_store {th : TTh} {x : String} {rel : Bool} {a v : At} {tok : Option At} {e : Expr}
    {rt : Ty} {pw : Word} {ad : Address} {off : Nat}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hea : evalAt th.env a = some (rt, [pw]))
    (hpw : pw.val = .loc ad off) : ∀ lab, OpTgtP th lab → lab = ad.label := by
  rintro lab ⟨q, rt', w, ad', off', hq, hev, hw, rfl⟩
  rw [hterm] at hq
  simp only [opAtomP, Option.some.injEq] at hq
  subst hq
  rw [hea, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at hev
  obtain ⟨-, rfl, -⟩ := hev
  rw [hpw] at hw
  injection hw with h1
  rw [h1]
#print axioms TermPiece.opTgtP_store

/-- (OvW3 R2b) An atomic operation's target label is its evaluated address's label. -/
theorem opTgtP_of {th : TTh} {q : At} {rt : Ty} {pw : Word} {ad : Address} {off : Nat}
    (hq : opAtomP th.term = some q) (hea : evalAt th.env q = some (rt, [pw]))
    (hpw : pw.val = .loc ad off) : ∀ lab, OpTgtP th lab → lab = ad.label := by
  rintro lab ⟨q', rt', w, ad', off', hq', hev, hw, rfl⟩
  rw [hq, Option.some.injEq] at hq'
  subst hq'
  rw [hea, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at hev
  obtain ⟨-, rfl, -⟩ := hev
  rw [hpw] at hw
  injection hw with h1
  rw [h1]
#print axioms TermPiece.opTgtP_of

/-- (OvW3 R2c) The re-pin cover at a store with a known target label. -/
theorem RepinCov_of {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)} {l : AllocLabel}
    (htg : ∀ lab, OpTgtP th lab → lab = l)
    (h : ∀ c (o : Nat) th0 tw, E.sto l = some c → c.owner = some E.tid → E.pfr l ≠ none → ¬ VisU E ⟨l, o⟩ →
      LowOwn s ⟨l, o⟩ th0 → th0 ∉ s'.promises → LowOwn s' ⟨l, o⟩ tw → OverT E' s' ⟨l, o⟩ tw →
      WinGI E' s' l tw → (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
      ∃ y ∈ RS, y.1 = l ∧ CrCov y.2.2 o) : RepinCov E E' s s' th RS := by
  intro lab _ hot
  obtain rfl := htg lab hot
  exact h
#print axioms TermPiece.RepinCov_of

/-- (OvW3 R2c) At another thread's cell the re-pin cover holds with any items. -/
theorem RepinCov_foreign {E E' : TEnv} {s s' : St} {th : TTh} {RS : List (AllocLabel × Cell × CrIt)}
    {l : AllocLabel} {c : Cell} (htg : ∀ lab, OpTgtP th lab → lab = l) (hsto : E.sto l = some c)
    (hown : c.owner ≠ some E.tid) : RepinCov E E' s s' th RS :=
  RepinCov_of htg fun c' _ _ _ hc' hown' => by
    rw [hsto] at hc'
    cases hc'
    exact absurd hown' hown
#print axioms TermPiece.RepinCov_foreign

/-- (OvW3 R2c) **`heldMixAtL` with re-pin items**: at an own cell with a frontier, the store's
mix is re-selected (`repin_mixU`); memory holds the mix, and the other mix's pieces holding an
own promise give re-pin items covering every fulfilled, overtaken unit inside a solid piece. -/
theorem heldMixAtLD {g : G} {E : TEnv} {s : St} {H : Res} {Sl : AllocLabel → List Res} {a : Address} {c : Cell}
    {us : List Acc} {nI : AllocLabel → Nat} (hnI : nI a.label ≤ E.ini a.label)
    {ws : List Word} {U : Ty} {Rv : Res} {f : Ts} (hm : MemInv g E s) (hH : MemHeldL E s H Sl)
    (hsto : E.sto a.label = some c) (hf : E.pfr a.label = some f) (hown : c.owner = some E.tid)
    (hat : AtOff c.ty a.offset U)
    (hini : IniAt nI c a U) (hna : ∀ N e, U ≠ .array (.lit N) e)
    (hiaU : TermTear.IallOK [] U = true) (hfo1 : ∀ t, t ∈ E.fp → t < s.mem.size)
    (hU : EnvValR E U ws Rv) (hus : accs U = some us) (hlen : ws.length = nWords us)
    {k : Promises.Knobs} {arch : Arch} {pw : Word} {rel : Bool} {s' : St}
    (hs' : s' ∈ storeUnits k arch pw a rel us ws 0 s) :
    ∃ (H2 : Res) (Sl' : AllocLabel → List Res) (RS : List (AllocLabel × Cell × CrIt)),
      H2 + Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) + Dsum s s' (fwr E s) ≤ Rv + H ∧ MemHeldL E s' H2 Sl' ∧
      SSet E nI Sl Sl' a.label ∧ (∀ y ∈ RS, RepinItU E s' y ∧ y.1 = a.label) ∧
      ∀ (o : Nat) th0 tw, ¬ VisU E ⟨a.label, o⟩ → LowOwn s ⟨a.label, o⟩ th0 → th0 ∉ s'.promises →
        LowOwn s' ⟨a.label, o⟩ tw → OverT E s' ⟨a.label, o⟩ tw → WinGU E s' a.label o tw →
        (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
        ∃ y ∈ RS, y.1 = a.label ∧ CrCov y.2.2 o := by
  have hwU : wc U = some (nWords us) := wc_of_accs hus
  have hcpU := coupledOK_AtOff hat (MemInv_cplT hm hsto hf)
  obtain ⟨H0, rfl, hent0, hX⟩ := MemHeldL_focus hH a.label
  obtain ⟨vals0, hL0, hC0⟩ := hent0.2 c hsto
  rcases own_segL hnI hC0 hat hini hna with ⟨b, oS, S, wS, kk, Rsg, -, hbo, hatS, hwS, hbw, hkk, ⟨hvs, hVs⟩, hkb, hput⟩ |
    ⟨-, -, -, -, -, -, -, hz0⟩
  rotate_left
  · obtain rfl := nWords_zero_nil (hz0 _ hus)
    simp only [storeUnits, List.mem_singleton] at hs'
    subst hs'
    exact ⟨_, Sl, [], fun k => by
      rw [Dsum_self]; simp only [List.map_nil, Res.sum_nil, Res.add_apply, Res.zero_apply]; omega, hH,
      SSet_refl _ _ _ _, fun y hy => absurd hy List.not_mem_nil, fun _ _ _ _ hlo hth => absurd hlo.1 hth⟩
  have hsl : ((vals0.drop b).take wS).length = wS := by
    simp only [List.length_take, List.length_drop]; omega
  obtain ⟨n, Rq, Rr2, hwn, hle2, hRs, hvq, hput2⟩ := VRR_at E.unsee hatS hvs (by rw [hsl]; exact hwS)
  rw [hwU] at hwn
  obtain rfl : nWords us = n := Option.some.inj hwn
  rw [hsl] at hle2
  obtain ⟨n', hwn', -, -, hVq⟩ := VR_at E.unsee hatS (VRR_VR S (RLink_of (Coh_CE _) (CohR_CE _)) hvs) hVs
    (by rw [hsl]; exact hwS)
  rw [hwU] at hwn'
  obtain rfl : nWords us = n' := Option.some.inj hwn'
  have hlenv : a.offset + nWords us ≤ vals0.length := by
    rw [← hbo, Nat.add_assoc]; exact Nat.le_trans (Nat.add_le_add_left hle2 b) hbw
  have hvqe : (((vals0.drop b).take wS).drop oS).take (nWords us) = (vals0.drop a.offset).take (nWords us) := by
    rw [take_drop_take hle2, drop_drop', hbo]
  rw [hvqe] at hvq hVq
  generalize hqo : (vals0.drop a.offset).take (nWords us) = qold at hvq hVq
  have hlq : qold.length = nWords us := by rw [← hqo]; simp; omega
  have hPb : ∀ t, t ∈ s.promises → t < s.mem.size := fun t ht => hm.2.2.1 t ht
  have hLq : ∀ j w, qold[j]? = some w → LatestNP s.mem (PromAt E s (offs a (0 + j))) (offs a (0 + j)) w :=
    fun j w hj => by
      have hj' : vals0[a.offset + j]? = some w := by
        rw [← hqo] at hj
        by_cases hjn : j < nWords us
        · rw [List.getElem?_take_of_lt hjn, List.getElem?_drop] at hj; exact hj
        · rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
      have e : offs a (0 + j) = ⟨a.label, a.offset + j⟩ := by simp [offs]
      rw [e]; exact hL0 _ w hj'
  obtain ⟨sel0, vals1, hWv1, hLv1, -, hselF, -⟩ := TermNPmixW.storeUnits_NPmixWF (E := E) (us := us) (ws := ws)
    (i := 0) (s := s) (s' := s') (V := s.vs.vRelSt) (old := qold) hs' (Nat.le_refl _) hPb hfo1 hlq hLq
  have hst := hU.store hm.2.2.2.2.1
  have hln : (ws.map (bumpW s.vs.vRelSt)).length = nWords us := by
    rw [List.length_map, hlen]
  -- (OvW3 R2c) re-select the mix; the other mix's pieces give the re-pin items
  obtain ⟨sel, vals', Rm, RS, hvm, hVm, hWv, hLv, hRS, hRm, hcov⟩ := repin_mixU (E := E) hsto hown hf
    (LayT_of_CellR hC0) (MemInv_noOwnT hm hsto hf) hat hus hcpU hiaU hs' hm.2.2.2.2.2.2.2.2.2.2.1 hPb hst.1 hst.2 hln
    hvq hVq hlq hLq hWv1 hLv1 hselF
  have hlm0 := TermTear.length_mixU us sel _ _ hln hlq
  generalize hqm : TermTear.mixU us sel (ws.map (bumpW s.vs.vRelSt)) qold = qm
    at hvm hVm hWv hlm0
  have hQ := hput2 qm Rm hvm hlm0
  have hQV := (VR_put E.unsee hatS (VRR_VR S (RLink_of (Coh_CE _) (CohR_CE _)) hvs) hVs
    (by rw [hsl]; exact hwS) (VRR_VR _ (RLink_of (Coh_CE _) (CohR_CE _)) hvm) hVm (by rw [hlm0]; exact hwU)).2.2
  rw [hlm0] at hQV
  have hQl : (((vals0.drop b).take wS).take oS ++ qm ++ ((vals0.drop b).take wS).drop (oS + nWords us)).length = wS := by
    simp only [List.length_append, List.length_take, List.length_drop, hlm0]; omega
  have hcell' := hput _ _ ⟨hQ, hQV⟩ hQl
  have hsp := splice_seg vals0 qm b wS oS (by rw [hlm0]; exact hle2)
  rw [hlm0] at hsp
  rw [hsp, hbo] at hcell'
  have hlv' : vals'.length = nWords us := by rw [← TermStep.WLe.length hWv, hlm0]
  have hcell2 := CellR_up (WLe.append (WLe.append (WLe_refl (vals0.take a.offset)) hWv)
    (WLe_refl (vals0.drop (a.offset + nWords us)))) hcell'
  have hlat' : ∀ o w, (vals0.take a.offset ++ vals' ++ vals0.drop (a.offset + nWords us))[o]? = some w →
      LatestNP s'.mem (PromAt E s' ⟨a.label, o⟩) ⟨a.label, o⟩ w := by
    intro o w hov
    rw [splice_get vals0 vals' a.offset (nWords us) o hlv' hlenv] at hov
    by_cases hr : a.offset ≤ o ∧ o < a.offset + nWords us
    · rw [iteT hr] at hov
      have := hLv (o - a.offset) w hov
      have e2 : offs a (0 + (o - a.offset)) = ⟨a.label, o⟩ := by
        simp only [offs, Nat.zero_add]; congr 1; exact Nat.add_sub_of_le hr.1
      rw [e2] at this; exact this
    · rw [iteF hr] at hov
      refine storeUnits_NPkeep us ws 0 _ s' hs' _ w (fun j hj e => ?_) (hL0 o w hov)
      have h' : o = a.offset + j := by simpa [offs] using congrArg WeakMem.Address.offset e
      subst h'
      exact hr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩
  have hent : HeldEntryL E s' a.label ((Sl a.label).set kk (Rm + Rr2)) := by
    refine ⟨fun h => (by rw [hsto] at h; cases h), fun c2 hc2 => ?_⟩
    rw [hsto] at hc2; cases hc2
    exact ⟨_, hlat', hcell2⟩
  have hX' : MemHeldXL E s' a.label H0 Sl := MemHeldXL_tr hX (fun _ _ => rfl) (fun _ _ => rfl)
    (fun l' hne o w hl => storeUnits_NPkeep us ws 0 _ s' hs' ⟨l', o⟩ w
      (fun j _ he => hne (by have := congrArg WeakMem.Address.label he; simpa [offs] using this)) hl) id
  have hkl : kk < (Sl a.label).length := (List.getElem?_eq_some_iff.1 hkk).1
  have hkv : (Sl a.label)[kk] = Rsg := (List.getElem?_eq_some_iff.1 hkk).2
  refine ⟨_, _, RS, Res.le_def.2 fun k => ?_, MemHeldL_unfocus hX' hent,
    ⟨fun l' hl' => updS_other Sl _ hl', Or.inr ⟨kk, Rm + Rr2, updS_self _ _ _, fun c1 N e hc1 hT => ?_⟩⟩,
    hRS, hcov⟩
  · rw [Res.sum_set _ kk _ hkl, Res.sum_set_zero _ kk hkl, hkv]
    subst hRs
    have h2 := hRm k
    simp only [Res.add_apply] at h2 ⊢
    omega
  · rw [hsto] at hc1; cases hc1
    obtain ⟨us1, hu1⟩ : ∃ us1, accs e = some us1 := by
      have := MemInv_cplT hm hsto hf
      rcases hini N e hT with ⟨hUc, -⟩ | ⟨us1, -, -, hu1, -⟩
      · exact absurd (hUc.trans hT) (hna N e)
      · exact ⟨us1, hu1⟩
    exact (hkb N e us1 hT hu1).2
#print axioms TermPiece.heldMixAtLD

/-- (OvW3 G-b) `ThInvMPL` with `Q` on the witness. -/
def ThInvMPLQ (Q : TEnv → Prop) (p : Prog) (g : G) (E0 : TEnv) (s : St) (S0 : AllocLabel → List Res) (mem : Memory)
    (pairs : List Ts) (th : TTh) (Tot H : Res) : Prop :=
  ∃ E, Q E ∧ EFoot g E0 E s (stOf mem pairs th) ∧ SeenKeep E0 E ∧ BoxNewV E0 E s th ∧ ThInvRE p E th Tot ∧
    MemInv g E (stOf mem pairs th) ∧ MemHeldK E0 s S0 E (stOf mem pairs th) H ∧ CrPackLe E0 E s (stOf mem pairs th)

/-- (OvW3 G-b) `ThInvMPLQ` forgetting `Q`. -/
theorem ThInvMPLQ.toPL {Q : TEnv → Prop} {p : Prog} {g : G} {E0 : TEnv} {s : St} {S0 : AllocLabel → List Res}
    {mem : Memory} {pairs : List Ts} {th : TTh} {Tot H : Res}
    (h : ThInvMPLQ Q p g E0 s S0 mem pairs th Tot H) : ThInvMPL p g E0 s S0 mem pairs th Tot H :=
  let ⟨E, _, h0⟩ := h
  ⟨E, h0⟩
#print axioms TermPiece.ThInvMPLQ.toPL

/-- (option 3) `ThInvMPLQ` with `CrPackLeX`: the step's credits pack up to `X`, which the
store stepper's resource bound pays (`TermStep.ThInvMPLX` with `Q` on the witness). -/
def ThInvMPLQX (Q : TEnv → Prop) (p : Prog) (g : G) (E0 : TEnv) (s : St) (S0 : AllocLabel → List Res) (mem : Memory)
    (pairs : List Ts) (th : TTh) (Tot H X : Res) : Prop :=
  ∃ E, Q E ∧ EFoot g E0 E s (stOf mem pairs th) ∧ SeenKeep E0 E ∧ BoxNewV E0 E s th ∧ ThInvRE p E th Tot ∧
    MemInv g E (stOf mem pairs th) ∧ MemHeldK E0 s S0 E (stOf mem pairs th) H ∧ CrPackLeX E0 E s (stOf mem pairs th) X

/-- (option 3) `ThInvMPLQX` forgetting `Q`. -/
theorem ThInvMPLQX.toPLX {Q : TEnv → Prop} {p : Prog} {g : G} {E0 : TEnv} {s : St} {S0 : AllocLabel → List Res}
    {mem : Memory} {pairs : List Ts} {th : TTh} {Tot H X : Res}
    (h : ThInvMPLQX Q p g E0 s S0 mem pairs th Tot H X) : ThInvMPLX p g E0 s S0 mem pairs th Tot H X :=
  let ⟨E, _, h0⟩ := h
  ⟨E, h0⟩
#print axioms TermPiece.ThInvMPLQX.toPLX

/-- (OvW3 G-b) `tstepMR_storePubG` with its witness tied to `CE η` (`ThInvMPLQ`), so the
re-pin cover holds at the witness. -/
theorem tstepMR_storePubGQ {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {Sp : AllocLabel → List Res} (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H' X Gd RS, ThInvMPLQX (fun E' => E' = CE η) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' X ∧
        Drop (CE η) (stOf mem pairs th) Gd ∧
        Tot + H' + X + Res.sum (Gd.map GdE.R) + Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) ≤ Rf + Rs + H ∧
        GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th ∧
        (∀ y ∈ RS, RepinItU (CE η) (stOf r.1 r.2.1 r.2.2) y) ∧
        RepinCovU (CE η) (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th RS ∧
        (PromAbove (stOf r.1 r.2.1 r.2.2) → FulP (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
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
  have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  replace hval := (Fd_EnvVal (CE η) hcty).2 hval
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hvalR : EnvValR (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRR ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_sub hsat hsub _ _ _ hvrv
    have hvc : VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_close hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRR η hcty).2 hvc
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hsn := hm.2.2.2.2.1
  have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  have hpkX : CrPackLeX (CE η) (CE η) (stOf mem pairs th) s' (Dsum (stOf mem pairs th) s' (fwr (CE η) (stOf mem pairs th))) :=
    storeUnits_packLeX hm hs'
      (fun j hj => hdw.1 x rel a v tok e hterm _ pw ⟨lab, 0⟩ .pub ru us j hea (by simp [addrOf, hpw]) rfl hus hj)
  obtain ⟨R0, H0, rfl, hent0, hX⟩ := MemHeldL_focusE hH lab
  have hTS : TgtSyn th lab 0 (nWords us) :=
    ⟨x, rel, a, v, tok, e, _, ru, pw, ⟨lab, 0⟩, us, hterm, hea, hpw, ⟨.pub, Or.inl rfl⟩, hus, rfl, rfl, rfl⟩
  have hTF : TgtFoot (stOf mem pairs th) s' lab 0 (nWords us) := TgtFoot_of_units hs'
  have htg : ∀ l, OpTgtP th l → l = lab := opTgtP_store hterm hea hpw
  have hfp : PromAbove s' → FulP (CE η) (stOf mem pairs th) s' th := fun hpa =>
    fulP_of_fulAll (b := 0) htg hsto (.here (Or.inl (by rw [husc]; simp))) husc hpa fun hmq => by
      obtain ⟨-, -, F, hFl, -, -, hFm, hFj⟩ := storeUnits_fulAllP us wsv 0 (stOf mem pairs th) s'
        (MemInv_nodup hm) hs' (Nat.le_of_eq (congrArg Array.size hmq))
      refine ⟨F, hFl, hFm, fun j t hj => ?_⟩
      obtain ⟨h1, h2, m, w, h3, -, h5, -, -, -, -, h8⟩ := hFj j t hj
      have e0 : offs ⟨lab, 0⟩ (0 + j) = ⟨lab, 0 + j⟩ := by simp [offs]
      rw [e0] at h5 h8
      exact ⟨h1, h2, m, h3, h5, h8⟩
  by_cases hown : c.owner = some η.tid
  · -- the thread's own cell: as an own store
    rcases hpfl : (CE η).pfr lab with _ | f
    · obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 (stOf mem pairs th)
        (stOf mem pairs th).vs.vRelSt hm.2.2.1 (MemInv_nodup hm) (Nat.le_refl _) s' hs'
      have htail : ∀ j : Nat, j < nWords us → TailP (stOf mem pairs th) (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
        have := OwnOKPF_tail hm.2.1 hsto hown hpfl hus' j hj
        simpa [offs] using this
      have hX' : MemHeldXL (CE η) s' lab H0 Sp := MemHeldXL_store (a := ⟨lab, 0⟩) hX hm.2.2.1 hs'
      have hnv : ∀ o, ¬ VisU (CE η) ⟨lab, o⟩ := fun o hv => hv.2 (Priv_of hsto hown hpfl)
      have hent : HeldEntry (CE η) s' lab Rv :=
        HeldEntry_ownN hsto (NVP_store (NVP_priv (Priv_of hsto hown hpfl)) hm.2.2.1 hs') (storeOwn_latestP hlen (g2 htail))
        (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hsn⟩)
      refine ⟨Rr + Rs, Rv + H0, .zero, [], [], ⟨CE η, rfl, EFoot_refl, (by seenT), (by boxT), ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
        MemInv_storeF hm hsto hown husc hval hlen s' hs', MemHeldK_unfocus hX' hent (fun _ h => h.1 hpfl),
        CrPackLe_X (CrPack_le (CrKeep_pack (MemInv_promLt hm) (MemInv_nodup hm) (CrKeep_store hm hs' (fun o => not_VisD_priv (Priv_of hsto hown hpfl)))))⟩,
        Drop_nil, R_nil (G_nil (Res.le_def.2 fun k => ?_)),
        ⟨lab, 0, _, _, hTS, hTF, GdCovUL_own (E := CE η) hsto hown _ (fun _ => true), GdLT_nil, GdLT0_true⟩,
        fun y hy => absurd hy List.not_mem_nil, RepinCovU_of htg fun _ _ _ _ _ _ hpf => absurd hpfl hpf, hfp⟩
      have h1 := hle k
      simp only [Res.add_apply, Res.zero_apply] at h1 ⊢
      omega
    · -- (F2) an own cell with a frontier: memory's holding by the mix (`heldMixAt`)
      have hatC : AtOff c.ty (⟨lab, 0⟩ : Address).offset c.ty := .here (Or.inl (by rw [husc]; simp))
      obtain ⟨H2, Sl2, RS, hH2, hHs0, hss, hRS, hcov⟩ := heldMixAtLD (E := CE η) (nI := (CE η).rc) (TEnv.rc_le_ini (CE η) _) (a := ⟨lab, 0⟩) hm hH hsto hpfl hown hatC
        (IniAt_of_ne fun N e he => hna N e he) hna
        ((hia x rel a v tok e _ hterm hpk hnw _ pw ⟨lab, 0⟩ hea (by simp [addrOf, hpw]) c hsto).1 _ _ rfl 0 c.ty hatC) hfo.1 hvalR husc hlen hs'
      have hHs := MemHeldK_ofSSet (s0 := stOf mem pairs th) hHs0 hss (Or.inl (Nat.le_refl _))
      refine ⟨Rr + Rs, H2, Dsum (stOf mem pairs th) s' (fwr (CE η) (stOf mem pairs th)), [], RS, ⟨CE η, rfl, EFoot_refl, (by seenT), (by boxT), ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
        MemInv_storeF hm hsto hown husc hval hlen s' hs', hHs, hpkX⟩, Drop_nil, (Res.le_def.2 fun k => ?_),
        ⟨lab, 0, _, _, hTS, hTF, GdCovUL_own (E := CE η) hsto hown _ (fun _ => true), GdLT_nil, GdLT0_true⟩, fun y hy => (hRS y hy).1,
        (RepinCovU_of htg fun c2 o th0 tw hc2 _ _ hnv hlo hth hlw hov hwin hpc => by
          rw [show (CE η).sto lab = η.sto lab from rfl, hsto] at hc2
          cases hc2
          exact hcov o th0 tw hnv hlo hth hlw hov hwin hpc), hfp⟩
      have h1 := hle k
      have h2 := hH2 k
      simp only [Res.add_apply, List.map_nil, Res.sum_nil, Res.zero_apply] at h1 h2 ⊢
      omega
  · -- another thread's published cell: a mix of the stored value and the old words (torn or not);
    -- the overwritten old words fund the drop list, the stored words at the fulfilled visible
    -- word units pay the credits (option 3: `gd_fundX`, one selection `storeUnits_NPmixWF`)
    obtain ⟨vals0, hL0, hC0⟩ := hent0.2 c hsto
    obtain ⟨hw0, hv0⟩ : wc c.ty = some vals0.length ∧ ValOfR (CE η) c.ty vals0 R0 := by
      rcases hC0 with h | ⟨N, e', _, _, hT, _⟩
      · exact h
      · exact absurd hT (hna N e')
    have hl0 : vals0.length = nWords us := by rw [hus'] at hw0; exact (Option.some.inj hw0).symm
    have hPb : ∀ t, t ∈ (stOf mem pairs th).promises → t < (stOf mem pairs th).mem.size :=
      fun t ht => hm.2.2.1 t ht
    obtain ⟨sel, vals', hWv, hLv, hNV, hselF, hcomp⟩ := TermNPmixW.storeUnits_NPmixWF (E := CE η) (us := us) (ws := wsv)
      (i := 0) (s := stOf mem pairs th) (s' := s') (V := (stOf mem pairs th).vs.vRelSt) (old := vals0) hs' (Nat.le_refl _)
      hPb hfo.1 hl0 (fun j w hj => by simpa [offs] using hL0 j w hj)
    obtain ⟨hvn, hVn⟩ := hvalR.store hsn
    have hln : (wsv.map (bumpW (stOf mem pairs th).vs.vRelSt)).length = nWords us := by
      rw [List.length_map, hlen]
    obtain ⟨R', Rb, hvR', hvRb, hR'⟩ := TermTear.VRR_mix2 (sel := sel) (MemInv_cplT hm hsto hf)
      ((hia x rel a v tok e _ hterm hpk hnw _ pw ⟨lab, 0⟩ hea (by simp [addrOf, hpw]) c hsto).1 _ _ rfl 0 c.ty (.here (Or.inl (by rw [husc]; simp)))) husc
      hvn hv0.1 hln hl0
    have hVm := TermTear.Valid_mix (sel := sel) husc hVn hv0.2 hln hl0
    have hlm := TermTear.length_mixU us sel _ _ hln hl0
    have hVb := TermTear.Valid_mix (sel := sel) husc hv0.2 hVn hl0 hln
    have hlb := TermTear.length_mixU us sel _ _ hl0 hln
    -- (§11) the overwritten old words (at the selected units) fund the drop list
    have hLb : ∀ k w, @decide (∃ i, sel i = true ∧ InAcc us i k) (Classical.propDecidable _) = true →
        (TermTear.mixU us sel vals0 (wsv.map (bumpW (stOf mem pairs th).vs.vRelSt)))[k]? = some w →
        LatestNP (stOf mem pairs th).mem (PromAt (CE η) (stOf mem pairs th) ⟨lab, 0 + k⟩) ⟨lab, 0 + k⟩ w := by
      intro k w hk hw
      obtain ⟨i, hsi, hI⟩ := @of_decide_eq_true _ (Classical.propDecidable _) hk
      rw [TermTear.mixU_getElem us sel _ _ i k hl0 hln hI, hsi] at hw
      simp only [ite_true] at hw
      simpa using hL0 k w hw
    -- (option 3) the fulfilled visible word units are off the selection
    have hLx0 : ∀ j ∈ fulUnits (CE η) (stOf mem pairs th) s' ⟨lab, 0⟩ us,
        @decide (∃ i, sel i = true ∧ InAcc us i j) (Classical.propDecidable _) = false :=
      fun j hj => fulUnits_unsel hj fun t m n ht hn hm1 hl hV hI => hselF t m j n ht hn hm1 hl hV hI
    obtain ⟨Gd, Gx, hGd, hGR, hCov, hGL, hGx⟩ := gd_fundX (E := CE η) (s := stOf mem pairs th) (o := 0) hsto hown
      (fun h => by cases h.symm.trans hf) (.here (Or.inl (by rw [husc]; simp))) husc ⟨hvRb, hVb⟩
      (by rw [hus', hlb]) _ hLb (fulUnits (CE η) (stOf mem pairs th) s' ⟨lab, 0⟩ us) fulUnits_nodup
      (fun j hj => fulUnits_lt hj) hLx0
    have hXs : Dsum (stOf mem pairs th) s' (fwr (CE η) (stOf mem pairs th)) ≤
        Res.sum ((fulUnits (CE η) (stOf mem pairs th) s' ⟨lab, 0⟩ us).map Gx) :=
      fwr_le_shares (V := (stOf mem pairs th).vs.vRelSt)
        (comp := TermTear.mixU us sel vals0 (wsv.map (bumpW (stOf mem pairs th).vs.vRelSt)))
        (MemInv_promLt hm) (MemInv_nodup hm) hs'
        (fun t m j ht hn hm1 hl hV => hcomp t m j ht hn hm1 (by rw [hl, Nat.zero_add]) hV)
        (fun t m j n P ht hn hm1 hl hV hwa => mem_fulUnits (MemInv_promLt hm) hs' ht hn hm1 hl hV hwa)
        (fun j hj n P x hw hx => hGx j hj n P x hw hx)
    have hent : HeldEntry (CE η) s' lab R' := by
      refine ⟨fun h => (by rw [show (CE η).sto lab = η.sto lab from rfl, hsto] at h; cases h), fun c2 hc2 => ?_⟩
      rw [show (CE η).sto lab = η.sto lab from rfl, hsto] at hc2; cases hc2
      refine ⟨vals', fun o w hw => by simpa [offs] using hLv o w hw, Or.inl ⟨?_, ValOfR_up hWv ⟨hvR', hVm⟩⟩⟩
      rw [hus', ← TermStep.WLe.length hWv, hlm]
    have hX' : MemHeldXL (CE η) s' lab H0 Sp := MemHeldXL_tr hX (fun _ _ => rfl) (fun _ _ => rfl)
      (fun l' hne o w hl => storeUnits_NPkeep us wsv 0 _ s' hs' ⟨l', o⟩ w
        (fun j _ he => hne (by have := congrArg WeakMem.Address.label he; simpa [offs] using this)) hl) id
    refine ⟨Rr + Rs, R' + H0, Dsum (stOf mem pairs th) s' (fwr (CE η) (stOf mem pairs th)), Gd, [],
      ⟨CE η, rfl, EFoot_refl, (by seenT), (by boxT), ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_storePubAt (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen s' hs',
      MemHeldK_unfocusNA hX' hent (fun c1 N e hc1 => by
        rw [show (CE η).sto lab = η.sto lab from rfl, hsto] at hc1; cases hc1; exact hna N e), hpkX⟩, hGd,
      R_nil (Res.le_def.2 fun k => ?_),
      ⟨lab, 0, _, _, hTS, hTF, hCov, GdLT_of hGL (TermNPmixW.nnv_sel (ad := ⟨lab, 0⟩) hNV),
        TermNPmixW.nnv_sel (ad := ⟨lab, 0⟩) hNV⟩,
      fun y hy => absurd hy List.not_mem_nil, RepinCovU_foreign (E := CE η) htg hsto hown, hfp⟩
    have h1 := hle k
    have h2 := hR' k
    have h3 := hGR k
    have h4 := hXs k
    simp only [Res.add_apply] at h1 h2 h3 h4 ⊢
    omega
#print axioms TermPiece.tstepMR_storePubGQ

/-- **`tstepMR_storePub` with a drop list**: at another thread's cell whose
target units are untorn (`UntornU`), the stored value replaces the cell's words
(`storeUnits_NPnew`), so the old words' resources fund the drop list of the
pieces meeting a foreign promise (`gd_fund`); at torn target units the overwritten
old words fund it as well, so the coverage is unconditional (`GdCovU`). -/
theorem tstepMR_storePubG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {Sp : AllocLabel → List Res} (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H' X Gd RS, ThInvMPLX p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' X ∧
        Drop (CE η) (stOf mem pairs th) Gd ∧
        Tot + H' + X + Res.sum (Gd.map GdE.R) + Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) ≤ Rf + Rs + H ∧
        GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th ∧
        (∀ y ∈ RS, RepinItU (CE η) (stOf r.1 r.2.1 r.2.2) y) ∧
        RepinCovU (CE η) (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th RS := by
  have h := tstepMR_storePubGQ hterm hP hpk hnw hT hCk hi hE htv hm hH hia hdw hfo hRP hPS
  exact ⟨h.1, fun r hr =>
    let ⟨Tot, H', X, Gd, RS, hK, h2, h3, h4, h5, h6, _⟩ := h.2 r hr
    ⟨Tot, H', X, Gd, RS, hK.toPLX, h2, h3, h4, h5, h6⟩⟩

/-- (OvW3 G-b) `tstepMR_storePubLocG` with its witness tied to `CE η` (`ThInvMPLQ`), so
the re-pin cover holds at the witness. -/
theorem tstepMR_storePubLocGQ {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {Sp : AllocLabel → List Res} (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H' X Gd RS, ThInvMPLQX (fun E' => E' = CE η) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' X ∧
        Drop (CE η) (stOf mem pairs th) Gd ∧
        Tot + H' + X + Res.sum (Gd.map GdE.R) + Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) ≤ Rf + Rs + H ∧
        GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th ∧
        (∀ y ∈ RS, RepinItU (CE η) (stOf r.1 r.2.1 r.2.2) y) ∧
        RepinCovU (CE η) (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th RS ∧
        (PromAbove (stOf r.1 r.2.1 r.2.2) → FulP (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
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
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
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
  have htg : ∀ l, OpTgtP th l → l = ad.label := opTgtP_store hterm hea hpw
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact hsigu
  have hlr := pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := hlr.symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := rel)
    us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  -- (S7c) the cell has a frontier (`ModeOK .pub`), so it is visible: memory's
  -- reading is the pub one whoever owns it (an own cell reached by a pub locative
  -- is shared-own); mix the component, put it back
  simp only [ModeOK] at hmode
  obtain ⟨f, hf, -⟩ := hmode
  have hcpU := coupledOK_AtOff hat (MemInv_cplT hm hsto hf)
  have hfp : PromAbove s' → FulP (CE η) (stOf mem pairs th) s' th := fun hpa =>
    fulP_of_fulAll htg hsto hat hwUA hpa fun hmq => by
      obtain ⟨-, -, F, hFl, -, -, hFm, hFj⟩ := storeUnits_fulAllP us wsv 0 (stOf mem pairs th) s'
        (MemInv_nodup hm) hs' (Nat.le_of_eq (congrArg Array.size hmq))
      refine ⟨F, hFl, hFm, fun j t hj => ?_⟩
      obtain ⟨h1, h2, m, w, h3, -, h5, -, -, -, -, h8⟩ := hFj j t hj
      have e0 : offs ad (0 + j) = ⟨ad.label, ad.offset + j⟩ := by simp [offs]
      rw [e0] at h5 h8
      exact ⟨h1, h2, m, h3, h5, h8⟩
  have hpkX : CrPackLeX (CE η) (CE η) (stOf mem pairs th) s' (Dsum (stOf mem pairs th) s' (fwr (CE η) (stOf mem pairs th))) :=
    storeUnits_packLeX hm hs'
      (fun j hj => hdw.1 x rel a v tok e hterm _ pw ad μr ru us j hea (by simp [addrOf, hpw]) rfl hus hj)
  have hiaU := (hia x rel a v tok e _ hterm hpk hnw _ pw ad hea (by simp [addrOf, hpw]) c hsto).2 _ _ _ rfl hat .refl
  obtain ⟨H0, rfl, hent0, hX⟩ := MemHeldL_focus hH ad.label
  obtain ⟨vals0, hL0, hC0⟩ := hent0.2 c hsto
  by_cases hnz : nWords us = 0
  · -- (H) a zero-width component: the store writes nothing
    obtain rfl := nWords_zero_nil hnz
    have hs1 := hs'
    simp only [storeUnits, List.mem_singleton] at hs1
    subst hs1
    refine ⟨Rr + Rs, Res.sum (Sp ad.label) + H0, Dsum (stOf mem pairs th) (stOf mem pairs th)
      (fwr (CE η) (stOf mem pairs th)), [], [], ⟨CE η, rfl, EFoot_refl, (by seenT), (by boxT), ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      (by by_cases hown : c.owner = some η.tid
          exact MemInv_storeAtI hm hsto hown hat hini hna hval hwUA hlen _ hs'
          exact MemInv_storePubAt hm hsto hown hf hat hini hna hval husU hlen _ hs'),
      MemHeldK_of hH, hpkX⟩, Drop_nil, (Res.le_def.2 fun k => ?_),
      ⟨ad.label, ad.offset, _, fun _ => true, ⟨x, rel, a, v, tok, e, _, ru, pw, ad, [], hterm, hea, hpw, ⟨μr, Or.inr rfl⟩, hus, rfl, rfl, rfl⟩,
        TgtFoot_of_units hs', fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 _ => absurd h2 (by simp [nWords]; omega), GdLT_nil,
        GdLT0_true⟩,
        fun y hy => absurd hy List.not_mem_nil, RepinCovU_of htg fun _ _ _ _ _ _ _ _ hlo hth => absurd hlo.1 hth, hfp⟩
    have h1 := hle k
    rw [Dsum_self]
    simp only [Res.add_apply, List.map_nil, Res.sum_nil, Res.zero_apply] at h1 ⊢
    omega
  have htA : ∀ lo hi, lo ≤ ad.offset → ad.offset < hi → TouchS (stOf mem pairs th) s' ad.label lo hi :=
    fun lo hi h1 h2 => TouchS_store (s0 := stOf mem pairs th) hs' (Nat.pos_of_ne_zero hnz) rfl (fun _ => Nat.le_refl _) h1 h2
  rcases own_segL (Nat.le_refl _) hC0 hat hini hna with ⟨b, oS, S, wS, kk, Rsg, hseg, hbo, hatS, hwS, hbw, hkk, ⟨hvs, hVs⟩, hkb, hput⟩ |
    ⟨-, -, -, -, -, -, -, hz0⟩
  rotate_left
  · exact absurd (hz0 _ husU) hnz
  have hsl : ((vals0.drop b).take wS).length = wS := by
    simp only [List.length_take, List.length_drop]; omega
  obtain ⟨n, Rq, Rr2, hwn, hle2, hRs, hvq, hput2⟩ := VRR_at (CE η).unsee hatS hvs (by rw [hsl]; exact hwS)
  rw [hwU] at hwn
  obtain rfl : nWords us = n := Option.some.inj hwn
  rw [hsl] at hle2
  obtain ⟨n', hwn', -, -, hVq⟩ := VR_at (CE η).unsee hatS (VRR_VR S (RLink_of (Coh_CE _) (CohR_CE _)) hvs) hVs
    (by rw [hsl]; exact hwS)
  rw [hwU] at hwn'
  obtain rfl : nWords us = n' := Option.some.inj hwn'
  have hlenv : ad.offset + nWords us ≤ vals0.length := by
    rw [← hbo, Nat.add_assoc]; exact Nat.le_trans (Nat.add_le_add_left hle2 b) hbw
  have hvqe : (((vals0.drop b).take wS).drop oS).take (nWords us) = (vals0.drop ad.offset).take (nWords us) := by
    rw [take_drop_take hle2, drop_drop', hbo]
  rw [hvqe] at hvq hVq
  generalize hqo : (vals0.drop ad.offset).take (nWords us) = qold at hvq hVq
  have hlq : qold.length = nWords us := by rw [← hqo]; simp; omega
  have hPb : ∀ t, t ∈ (stOf mem pairs th).promises → t < (stOf mem pairs th).mem.size :=
    fun t ht => hm.2.2.1 t ht
  have hLq : ∀ j w, qold[j]? = some w → LatestNP (stOf mem pairs th).mem
      (PromAt (CE η) (stOf mem pairs th) (offs ad (0 + j))) (offs ad (0 + j)) w := fun j w hj => by
    have hj' : vals0[ad.offset + j]? = some w := by
      rw [← hqo] at hj
      by_cases hjn : j < nWords us
      · rw [List.getElem?_take_of_lt hjn, List.getElem?_drop] at hj; exact hj
      · rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
    have e : offs ad (0 + j) = ⟨ad.label, ad.offset + j⟩ := by simp [offs]
    rw [e]; exact hL0 _ w hj'
  have hst := hvalR.store hm.2.2.2.2.1
  have hln : (wsv.map (bumpW (stOf mem pairs th).vs.vRelSt)).length = nWords us := by
    rw [List.length_map, hlen]
  -- (option 3) mix the component (torn or not): at an own cell re-select it, the other mix
  -- gives re-pin items; at another thread's cell the overwritten old words fund the drop list;
  -- the stored words at the fulfilled visible word units pay the credits (`X`)
  obtain ⟨qm, Rm, vals', Gd, RS, L0, hvm, hVm, hWv, hlm0, hLv, hGd, hRm, hCov, hLT, hLT0, hRS, hRC⟩ : ∃ (qm : List Word)
      (Rm : Res) (vals' : List Word) (Gd : List GdE) (RS : List (AllocLabel × Cell × CrIt)) (L0 : Nat → Bool),
      VRR (fun _ => 0) (CE (CE η).unsee) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) qm Rm ∧
      Valid (cl ρ η.wit 0 0 u) qm ∧ WLe qm vals' ∧ qm.length = nWords us ∧
      (∀ j w, vals'[j]? = some w → LatestNP s'.mem (PromAt (CE η) s' (offs ad (0 + j))) (offs ad (0 + j)) w) ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Rm + Res.sum (Gd.map GdE.R) + Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) +
        Dsum (stOf mem pairs th) s' (fwr (CE η) (stOf mem pairs th)) ≤ Rv + Rq ∧
      GdCovUL (CE η) (stOf mem pairs th) Gd ad.label ad.offset (nWords us) L0 ∧
      GdLT (CE η) (stOf mem pairs th) s' Gd ad.label ad.offset (nWords us) ∧
      GdLT0 (CE η) (stOf mem pairs th) s' ad.label ad.offset (nWords us) L0 ∧
      (∀ y ∈ RS, RepinItU (CE η) s' y) ∧
      (c.owner = some η.tid → ∀ (o : Nat) th0 tw, ¬ VisU (CE η) ⟨ad.label, o⟩ →
        LowOwn (stOf mem pairs th) ⟨ad.label, o⟩ th0 → th0 ∉ s'.promises → LowOwn s' ⟨ad.label, o⟩ tw →
        OverT (CE η) s' ⟨ad.label, o⟩ tw → WinGU (CE η) s' ad.label o tw →
        (∃ q S usS, Piece c.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
        ∃ y ∈ RS, y.1 = ad.label ∧ CrCov y.2.2 o) := by
    obtain ⟨sel, vals', hWv, hLv, hNV, hselF, hcomp⟩ := TermNPmixW.storeUnits_NPmixWF (E := CE η) (us := us) (ws := wsv)
      (i := 0) (s := stOf mem pairs th) (s' := s') (V := (stOf mem pairs th).vs.vRelSt) (old := qold) hs' (Nat.le_refl _)
      hPb hfo.1 hlq hLq
    obtain ⟨Rm, Rb, hvm, hvb, hRm⟩ := TermTear.VRR_mix2 (sel := sel) hcpU hiaU husU hst.1 hvq hln hlq
    have hVm := TermTear.Valid_mix (sel := sel) husU hst.2 hVq hln hlq
    have hlm0 := TermTear.length_mixU us sel _ _ hln hlq
    by_cases hown : c.owner = some η.tid
    · -- (OvW3 R2c) an own cell: re-select the mix, the other mix gives re-pin items
      obtain ⟨sel', vals2, Rm2, RS, hvm2, hVm2, hWv2, hLv2, hRS, hRm2, hcov⟩ := repin_mixU (E := CE η)
        hsto hown hf (LayT_of_CellR hC0) (MemInv_noOwnT hm hsto hf) hat husU hcpU hiaU hs' (MemInv_nodup hm)
        hPb hst.1 hst.2 hln hvq hVq hlq hLq hWv hLv hselF
      exact ⟨_, Rm2, vals2, [], RS, fun _ => true, hvm2, hVm2, hWv2, TermTear.length_mixU us sel' _ _ hln hlq, hLv2,
        Drop_nil,
        Res.le_def.2 (fun k => by
          have := hRm2 k
          simp only [Res.add_apply, List.map_nil, Res.sum_nil, Res.zero_apply] at this ⊢; omega),
        GdCovUL_own (E := CE η) hsto hown _ _, GdLT_nil, GdLT0_true, fun y hy => (hRS y hy).1, fun _ => hcov⟩
    · -- (§11) another thread's cell: the overwritten old words fund the drop list
      have hVb := TermTear.Valid_mix (sel := sel) husU hVq hst.2 hlq hln
      have hlb := TermTear.length_mixU us sel _ _ hlq hln
      have hLb : ∀ k w, @decide (∃ i, sel i = true ∧ InAcc us i k) (Classical.propDecidable _) = true →
          (TermTear.mixU us sel qold (wsv.map (bumpW (stOf mem pairs th).vs.vRelSt)))[k]? = some w →
          LatestNP (stOf mem pairs th).mem (PromAt (CE η) (stOf mem pairs th) ⟨ad.label, ad.offset + k⟩)
            ⟨ad.label, ad.offset + k⟩ w := by
        intro k w hk hw
        obtain ⟨i, hsi, hI⟩ := @of_decide_eq_true _ (Classical.propDecidable _) hk
        rw [TermTear.mixU_getElem us sel _ _ i k hlq hln hI, hsi] at hw
        simp only [ite_true] at hw
        have := hLq k w hw; simpa [offs] using this
      have hLx0 : ∀ j ∈ fulUnits (CE η) (stOf mem pairs th) s' ad us,
          @decide (∃ i, sel i = true ∧ InAcc us i j) (Classical.propDecidable _) = false :=
        fun j hj => fulUnits_unsel hj fun t m n ht hn hm1 hl hV hI => hselF t m j n ht hn hm1 hl hV hI
      obtain ⟨Gd, Gx, hGd, hGR, hCov, hGL, hGx⟩ := gd_fundX (E := CE η) (s := stOf mem pairs th) hsto hown
        (fun h => by cases h.symm.trans hf) hat husU ⟨hvb, hVb⟩ (by rw [hwU, hlb]) _ hLb
        (fulUnits (CE η) (stOf mem pairs th) s' ad us) fulUnits_nodup (fun j hj => fulUnits_lt hj) hLx0
      have hXs : Dsum (stOf mem pairs th) s' (fwr (CE η) (stOf mem pairs th)) ≤
          Res.sum ((fulUnits (CE η) (stOf mem pairs th) s' ad us).map Gx) :=
        fwr_le_shares (V := (stOf mem pairs th).vs.vRelSt)
          (comp := TermTear.mixU us sel qold (wsv.map (bumpW (stOf mem pairs th).vs.vRelSt)))
          (MemInv_promLt hm) (MemInv_nodup hm) hs'
          (fun t m j ht hn hm1 hl hV => hcomp t m j ht hn hm1 (by rw [hl, Nat.zero_add]) hV)
          (fun t m j n P ht hn hm1 hl hV hwa => mem_fulUnits (MemInv_promLt hm) hs' ht hn hm1 hl hV hwa)
          (fun j hj n P x hw hx => hGx j hj n P x hw hx)
      exact ⟨_, Rm, vals', Gd, [], _, hvm, hVm, hWv, hlm0, hLv, hGd,
        Res.le_def.2 (fun k => by
          have h1 := hGR k; have h2 := hRm k; have h3 := hXs k
          simp only [Res.add_apply, List.map_nil, Res.sum_nil, Res.zero_apply] at h1 h2 h3 ⊢; omega),
        hCov, GdLT_of hGL (TermNPmixW.nnv_sel hNV), TermNPmixW.nnv_sel hNV, fun y hy => absurd hy List.not_mem_nil,
        fun h => absurd h hown⟩
  -- put the mixed component back into the segment, then the cell
  have hQ := hput2 qm Rm hvm hlm0
  have hQV := (VR_put (CE η).unsee hatS (VRR_VR S (RLink_of (Coh_CE _) (CohR_CE _)) hvs) hVs
    (by rw [hsl]; exact hwS) (VRR_VR _ (RLink_of (Coh_CE _) (CohR_CE _)) hvm) hVm (by rw [hlm0]; exact hwU)).2.2
  rw [hlm0] at hQV
  have hQl : (((vals0.drop b).take wS).take oS ++ qm ++ ((vals0.drop b).take wS).drop (oS + nWords us)).length = wS := by
    simp only [List.length_append, List.length_take, List.length_drop, hlm0]; omega
  have hcell' := hput _ _ ⟨hQ, hQV⟩ hQl
  have hsp := splice_seg vals0 qm b wS oS (by rw [hlm0]; exact hle2)
  rw [hlm0] at hsp
  rw [hsp, hbo] at hcell'
  have hlv' : vals'.length = nWords us := by rw [← TermStep.WLe.length hWv, hlm0]
  have hcell2 := CellR_up (WLe.append (WLe.append (WLe_refl (vals0.take ad.offset)) hWv)
    (WLe_refl (vals0.drop (ad.offset + nWords us)))) hcell'
  have hlat' : ∀ o w, (vals0.take ad.offset ++ vals' ++ vals0.drop (ad.offset + nWords us))[o]? = some w →
      LatestNP s'.mem (PromAt (CE η) s' ⟨ad.label, o⟩) ⟨ad.label, o⟩ w := by
    intro o w hov
    rw [splice_get vals0 vals' ad.offset (nWords us) o hlv' hlenv] at hov
    by_cases hr : ad.offset ≤ o ∧ o < ad.offset + nWords us
    · rw [iteT hr] at hov
      have := hLv (o - ad.offset) w hov
      have e2 : offs ad (0 + (o - ad.offset)) = ⟨ad.label, o⟩ := by
        simp only [offs, Nat.zero_add]; congr 1; exact Nat.add_sub_of_le hr.1
      rw [e2] at this; exact this
    · rw [iteF hr] at hov
      refine storeUnits_NPkeep us wsv 0 _ s' hs' _ w (fun j hj e => ?_) (hL0 o w hov)
      have h' : o = ad.offset + j := by simpa [offs] using congrArg WeakMem.Address.offset e
      subst h'
      exact hr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩
  have hent : HeldEntryL (CE η) s' ad.label ((Sp ad.label).set kk (Rm + Rr2)) := by
    refine ⟨fun h => (by rw [show (CE η).sto ad.label = η.sto ad.label from rfl, hsto] at h; cases h),
      fun c2 hc2 => ?_⟩
    rw [show (CE η).sto ad.label = η.sto ad.label from rfl, hsto] at hc2; cases hc2
    exact ⟨_, hlat', hcell2⟩
  have hX' : MemHeldXL (CE η) s' ad.label H0 Sp := MemHeldXL_tr hX (fun _ _ => rfl) (fun _ _ => rfl)
    (fun l' hne o w hl => storeUnits_NPkeep us wsv 0 _ s' hs' ⟨l', o⟩ w
      (fun j _ he => hne (by have := congrArg WeakMem.Address.label he; simpa [offs] using this)) hl) id
  have hkl : kk < (Sp ad.label).length := (List.getElem?_eq_some_iff.1 hkk).1
  have hR0 : Res.sum (Sp ad.label) = Rsg + Res.sum ((Sp ad.label).set kk .zero) := by
    rw [Res.sum_set_zero _ kk hkl, (List.getElem?_eq_some_iff.1 hkk).2]
  have hK := MemHeldK_slotSet (E0 := CE η) (s0 := stOf mem pairs th) hX' hent (fun c1 N e us1 hc1 hT hu1 => by
    rw [show (CE η).sto ad.label = η.sto ad.label from rfl, hsto] at hc1; cases hc1
    obtain ⟨hb, -⟩ := hkb N e us1 hT hu1
    have hw := seg_arr_width hseg hT hu1 hwS
    refine htA _ _ (by rw [← hbo, hb]; exact Nat.le_add_right _ _) ?_
    have h1 : oS + nWords us ≤ wS := hle2
    have h0 : 0 < nWords us := Nat.pos_of_ne_zero hnz
    rw [← hbo, hb, Nat.succ_mul]; exact Nat.add_lt_add_left (by rw [← hw]; omega) _)
  rw [Res.sum_set _ kk _ hkl] at hK
  rw [hR0]; subst hRs
  refine ⟨Rr + Rs, Rm + Rr2 + Res.sum ((Sp ad.label).set kk .zero) + H0,
    Dsum (stOf mem pairs th) s' (fwr (CE η) (stOf mem pairs th)), Gd, RS, ⟨CE η, rfl, EFoot_refl, (by seenT), (by boxT), ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
    (by by_cases hown : c.owner = some η.tid
        exact MemInv_storeAtI hm hsto hown hat hini hna hval hwUA hlen s' hs'
        exact MemInv_storePubAt hm hsto hown hf hat hini hna hval husU hlen s' hs'),
    hK, hpkX⟩, hGd, (Res.le_def.2 fun k => ?_),
    ⟨ad.label, ad.offset, _, L0, ⟨x, rel, a, v, tok, e, _, ru, pw, ad, us, hterm, hea, hpw, ⟨μr, Or.inr rfl⟩, hus, rfl, rfl, rfl⟩,
      TgtFoot_of_units hs', hCov, hLT, hLT0⟩, fun y hy => hRS y hy,
    (RepinCovU_of htg fun c2 o th0 tw hc2 hown2 _ hnv hlo hth hlw hov hwin hpc => by
      rw [show (CE η).sto ad.label = η.sto ad.label from rfl, hsto] at hc2
      cases hc2
      exact hRC hown2 o th0 tw hnv hlo hth hlw hov hwin hpc), hfp⟩
  have h1 := hle k
  have h2 := hRm k
  simp only [Res.add_apply] at h1 h2 ⊢
  omega
#print axioms TermPiece.tstepMR_storePubLocGQ

/-- **`tstepMR_storePubLoc` with a drop list**: at another thread's cell
whose target units are untorn, the stored value replaces the component's words,
whose resources fund the drop list (`gd_fund`); at torn target units the
overwritten old words fund it as well (`GdCovU`). -/
theorem tstepMR_storePubLocG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {Sp : AllocLabel → List Res} (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H' X Gd RS, ThInvMPLX p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' X ∧
        Drop (CE η) (stOf mem pairs th) Gd ∧
        Tot + H' + X + Res.sum (Gd.map GdE.R) + Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) ≤ Rf + Rs + H ∧
        GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th ∧
        (∀ y ∈ RS, RepinItU (CE η) (stOf r.1 r.2.1 r.2.2) y) ∧
        RepinCovU (CE η) (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th RS := by
  have h := tstepMR_storePubLocGQ hterm hP hpk hnw hT hCk hi hE htv hm hH hia hdw hfo hRP hPS
  exact ⟨h.1, fun r hr =>
    let ⟨Tot, H', X, Gd, RS, hK, h2, h3, h4, h5, h6, _⟩ := h.2 r hr
    ⟨Tot, H', X, Gd, RS, hK.toPLX, h2, h3, h4, h5, h6⟩⟩

/-- (option 3) `mc_ofPLG` from `ThInvMPLX`: the store's credit surplus `Y` is paid on the left. -/
theorem mc_ofPLGX {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : TTh} {η : TEnv} {Tot H' Y Rf Rs H X : Res} {cr db : Ts → Res}
    (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hK : ThInvMPLX p g (CE η) (stOf mem pairs th) Sp mem' pairs' th' Tot H' Y) (hle : Tot + H' + Y + X ≤ Rf + Rs + H) :
    ∃ Tot H' C F, ThInvMCFS p g (CE η) (stOf mem pairs th) Sp mem' pairs' th' Tot H' cr db ∧
      MintStepN g η (stOf mem pairs th) (stOf mem' pairs' th') C F ∧
      Tot + H' + pSum (stOf mem' pairs' th') cr + pSum (stOf mem pairs th) db + C + X ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem' pairs' th') db + F := by
  obtain ⟨Hm, hHm⟩ : ∃ Hm : Res, ∀ k, Hm k = (Rf + Rs + H) k - X k := ⟨fun k => (Rf + Rs + H) k - X k, fun _ => rfl⟩
  obtain ⟨Tot2, H2, C, F, h1, h2, h3⟩ := mc_ofPLX (Rf := Hm) (Rs := Res.zero) (H := Res.zero) hC hK
    (Res.le_def.2 fun k => by
      have e1 := hle k; have e2 := hHm k
      simp only [Res.add_apply, Res.zero_apply] at e1 e2 ⊢; omega)
  refine ⟨Tot2, H2, C, F, h1, h2, Res.le_def.2 fun k => ?_⟩
  have e1 := hle k; have e2 := hHm k; have e3 := h3 k
  simp only [Res.add_apply, Res.zero_apply] at e1 e2 e3 ⊢; omega
#print axioms TermPiece.mc_ofPLGX

/-- `mc_ofPL` with an extra `X` on both sides' left: the credits' step
inequality keeps it.  (Corollary of `mc_ofPLGX` at `Y = 0`.) -/
theorem mc_ofPLG {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem mem' : Memory} {pairs pairs' : List Ts} {th th' : TTh}
    {η : TEnv} {Tot H' Rf Rs H X : Res} {cr db : Ts → Res}
    (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hK : ThInvMPL p g (CE η) (stOf mem pairs th) Sp mem' pairs' th' Tot H') (hle : Tot + H' + X ≤ Rf + Rs + H) :
    ∃ Tot H' C F, ThInvMCFS p g (CE η) (stOf mem pairs th) Sp mem' pairs' th' Tot H' cr db ∧
      MintStepN g η (stOf mem pairs th) (stOf mem' pairs' th') C F ∧
      Tot + H' + pSum (stOf mem' pairs' th') cr + pSum (stOf mem pairs th) db + C + X ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem' pairs' th') db + F := by
  obtain ⟨E, a1, a2, a3, a4, a5, a6, a7⟩ := hK
  exact mc_ofPLGX (Y := .zero) hC ⟨E, a1, a2, a3, a4, a5, a6, CrPackLe_X a7⟩
    (Res.le_def.2 fun k => by have e := hle k; simp only [Res.add_apply, Res.zero_apply] at e ⊢; omega)

/-- **The thread step with a drop list**: `tstepMCF_stepP`, but a `pub`
store at another thread's untorn cell drops the pieces meeting a foreign promise
(`tstepMR_storePubG`, `tstepMR_storePubLocG`): their old words' resources
leave memory's holding on the left. -/
theorem tstepMCF_stepGL {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {Sp : AllocLabel → List Res} (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hC : PromCrP (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th) (hnvp : OwnOpT cx th.term → OwnNVPF (CE η) (stOf mem pairs th))
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRF : OwnFrontierRMWT (CE η) (stOf mem pairs th) th.term) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hown1 : PubLe1 th Rf Rs H := by assumption)
    (hZ : ZOK g (CE η) th := by exact fun _ _ h => False.elim h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F cr' db' Gd,
      ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) := by
  have hP0 := tstepMCF_stepP (hZ := hZ) (hPb := hPb) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia hdw hnvp hwp hwin hfo hRF hrmw hbf hRP hPS hSub hSig
  have hdef : ¬ PubShape cx th → tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' C F cr' db' Gd,
      ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) :=
    fun hns => ⟨hP0.1, fun r hr hpa => by
      obtain ⟨Tot, H', C, F, cr', db', h1, h2, hcl, h3⟩ := hP0.2 r hr hpa
      exact ⟨Tot, H', C, F, cr', db', [], h1, h2, hcl, Drop_nil, G_nil h3, fun hps => absurd hps hns⟩⟩
  have hC' := PromCrP_drop hC
  have lift : (∀ x a e, th.term ≠ .let_ x (.publish a) e) → (tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ Tot H' X Gd RS,
      ThInvMPLX p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' X ∧
        Drop (CE η) (stOf mem pairs th) Gd ∧
        Tot + H' + X + Res.sum (Gd.map GdE.R) + Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) ≤ Rf + Rs + H ∧
        GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th ∧
        (∀ y ∈ RS, RepinItU (CE η) (stOf r.1 r.2.1 r.2.2) y) ∧
        RepinCovU (CE η) (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th RS) →
      tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' C F cr' db' Gd,
      ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) := fun hnpL hG =>
    ⟨hG.1, fun r hr _ => by
      obtain ⟨Tot, H', X, Gd, RS, hK, hD, hle0, hcv, -, -⟩ := hG.2 r hr
      have hle : Tot + H' + X + Res.sum (Gd.map GdE.R) ≤ Rf + Rs + H := Res.le_trans (Res.le_add_right _ _) hle0
      obtain ⟨Tot2, H2, C, F, h1, h2, h3⟩ := mc_ofPLGX hC' hK hle
      refine ⟨Tot2, H2, C, F, _, db, Gd, h1, h2.toM, ClaimAtP.of_not (h2.claimAt _) hnpL, hD, (Res.le_def.2 fun k => ?_), fun _ => hcv⟩
      have e3 := h3 k
      have e4 := (pSum_dropP_le (E := CE η) (s := stOf mem pairs th) (s0 := stOf mem pairs th) (cr := cr)) k
      simp only [Res.add_apply] at e3 e4 ⊢; omega⟩
  by_cases hR : StepScopeR th.σs cx th.term
  · exact hdef fun ⟨_, _, _, _, _, _, _, ht, _⟩ => by rw [ht] at hR; simp only [StepScopeR, OpScopeR] at hR
  by_cases hs1 : ∃ x rel a v tok e u, th.term = .let_ x (.store rel a v tok) e ∧
      cx.peek a = .ok (.ptr .pub u) ∧ wordOf (Ty.ptr .pub u) = none
  · obtain ⟨x, rel, a, v, tok, e, u, ht, hpk, hnw⟩ := hs1
    exact lift (fun _ _ _ h => by rw [ht] at h; cases h) (tstepMR_storePubG ht hP hpk hnw hT hCk hi hE htv hm hH hia hdw hfo hRP hPS)
  by_cases hs2 : ∃ x rel a v tok e u, th.term = .let_ x (.store rel a v tok) e ∧
      cx.peek a = .ok (.loc .pub u) ∧ wordOf (Ty.loc .pub u) = none
  · obtain ⟨x, rel, a, v, tok, e, u, ht, hpk, hnw⟩ := hs2
    exact lift (fun _ _ _ h => by rw [ht] at h; cases h) (tstepMR_storePubLocG ht hP hpk hnw hT hCk hi hE htv hm hH hia hdw hfo hRP hPS)
  exact hdef fun ⟨x, rel, a, v, tok, e, u, ht, h⟩ => h.elim (fun h1 => hs1 ⟨x, rel, a, v, tok, e, u, ht, h1⟩)
    (fun h2 => hs2 ⟨x, rel, a, v, tok, e, u, ht, h2⟩)


theorem tstepMCF_stepG {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hpx : PAx g mem pairs th) (hC : PromCrP (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th) (hnvp : OwnOpT cx th.term → OwnNVPF (CE η) (stOf mem pairs th))
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRF : OwnFrontierRMWT (CE η) (stOf mem pairs th) th.term) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hown1 : PubLe1 th Rf Rs H := by assumption)
    (hZ : ZOK g (CE η) th := by exact fun _ _ h => False.elim h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F cr' db' Gd,
      ThInvMCF p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) := by
  obtain ⟨Sp, hH⟩ := hH.toS
  have h := tstepMCF_stepGL (hZ := hZ) (hPb := hPb) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia hdw hnvp hwp hwin hfo hRF hrmw hbf hRP hPS hSub hSig
  exact ⟨h.1, fun r hr hpa => let ⟨Tot, H', C, F, cr', db', Gd, h1, h2⟩ := h.2 r hr hpa
    ⟨Tot, H', C, F, cr', db', Gd, h1.toF, h2⟩⟩
#print axioms tstepMCF_stepG

/-- **A drop entry covers a `DetT` pin**: the resources a `DetT` sub-piece
`U` at offset `o` of an OK drop entry's piece carries in its words are bounded by the
entry's resources. -/
theorem pin_le_gdOK {E : TEnv} {s : St} {g : GdE} (hg : GdOK E s g) {o n : Nat} {U : Ty}
    (h : AtOff g.S o U) (hd : DetT U = true) (hn : wc U = some n) {RP : Res}
    (hp : VRR (fun _ => 0) (CE E.unsee) U (shp U) ((g.ws.drop o).take n) RP) : RP ≤ g.R := by
  obtain ⟨c, -, -, -, -, hwc, -, hv, -⟩ := hg
  exact pin_le_at E.unsee h hd hv hwc hn hp

end TermPiece


#print axioms TermStep.UntornU_mono
#print axioms TermStep.stepStore_AboveFW
#print axioms TermStep.stepStore_NPnewQ
#print axioms TermStep.stepStore_NPnewF
#print axioms TermStep.stepStore_NPnew0
#print axioms TermStep.stepStore_untorn
#print axioms TermStep.storeUnits_NPnew
#print axioms TermPiece.Drop_nil
#print axioms TermPiece.GdCov_nil
#print axioms TermPiece.GdCov_own
#print axioms TermPiece.GdCovU.toCov
#print axioms TermPiece.GdCovU_own
#print axioms TermPiece.TgtFoot_of_units
#print axioms TermPiece.mem_dedupC
#print axioms TermPiece.nodup_dedupC
#print axioms TermPiece.nodup_map_of_inj
#print axioms TermPiece.pcAt_some
#print axioms TermPiece.pcAt_of
#print axioms TermPiece.gd_fund
#print axioms TermPiece.GdLT_of
#print axioms TermTear.mix2_wrap
#print axioms TermTear.mixR2_gen
#print axioms TermTear.VRR_mix2
#print axioms TermTear.nWords_take_succ_cons
#print axioms TermTear.mixU_getElem
#print axioms TermPiece.G_nil
#print axioms TermPiece.tstepMR_storePubG
#print axioms TermPiece.tstepMR_storePubLocG
#print axioms TermPiece.mc_ofPLG
#print axioms TermPiece.tstepMCF_stepG
#print axioms TermPiece.pin_le_gdOK
