import WeakCore.TermBlkZ

/-!
# TermSlotS: the exact split of a slot value over its atoms

(R1 groundwork for slot-PaidB.)  A closed laid-out type whose `μ` bodies are guarded (`mg`) has
a full list of atomic components (`AtL`: descend pairs and `μ` unfoldings, stop at atoms), each
reached by `AtOff`; a value's resources split **exactly** over them (no remainder).
-/

namespace TermSlotS

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermBlkZ
open WeakMem (Msg Memory Address Ts AllocLabel)

/-- Shift an offset. -/
def shO (n : Nat) (p : Nat × Ty) : Nat × Ty := (n + p.1, p.2)

/-- The atomic components of a type with their offsets, in layout order. -/
inductive AtL : Ty → List (Nat × Ty) → Prop
  | atom {t : Ty} : AtomT t → accs t ≠ none → AtL t [(0, t)]
  | prod {a b : Ty} {A B : List (Nat × Ty)} {us : List Acc} : accs a = some us → AtL a A → AtL b B →
      AtL (.prod a b) (A ++ B.map (shO (nWords us)))
  | mu {t : Ty} {L : List (Nat × Ty)} : AtL (unfold1 (.mu t)) L → AtL (.mu t) L

/-- A closed guarded `μ` reads like its unfolding. -/
theorem mu_unfold_vrr {s : Ty} (hc : Clo (.mu s)) (hg : s.unguarded 0 = false) :
    shp (unfold1 (.mu s)) = shp (.mu s) ∧ wc (unfold1 (.mu s)) = wc (.mu s) ∧
      ∀ (ρ : Nat → Nat) (E : TEnv) (Rsh : Shp) (ws : List Word) (X : Res),
        VRR ρ (CE E) (unfold1 (.mu s)) Rsh ws X ↔ VRR ρ (CE E) (.mu s) Rsh ws X := by
  have hW : ∀ k : Nat, Clo ((fun _ : Nat => Ty.void) k) := fun _ => Clo_void
  have hU : cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (unfold1 (.mu s)) = unfold1 (.mu s) := by
    rw [TermStep.cl_unfold1 hW, hc.2]
  have hM : cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (.mu s) = .mu s := hc.2 _ _ _ _
  have hsig := TermStep.sig_cl_unfold (ρ := fun _ : Nat => 0) (W := fun _ : Nat => Ty.void) hg
  refine ⟨?_, ?_, fun ρ E Rsh ws X => ?_⟩
  · calc shp (unfold1 (.mu s)) = shp (cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (unfold1 (.mu s))) := by
          rw [hU]
      _ = shp (cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 1 0 s) := shp_of_sig hsig
      _ = shp (cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (.mu s)) := rfl
      _ = shp (.mu s) := by rw [hM]
  · calc wc (unfold1 (.mu s)) = wc (cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (unfold1 (.mu s))) := by
          rw [hU]
      _ = wc (cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 1 0 s) := wc_of_sig hsig
      _ = wc (cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (.mu s)) := rfl
      _ = wc (.mu s) := by rw [hM]
  · have := TermStep.VRR_cl_unfold E (ρ := fun _ : Nat => 0) (ρ₀ := ρ) hW hg (R := Rsh) (ws := ws) (X := X)
    rwa [hU, hM] at this

/-- **Existence** of the atom list, every atom reached by `AtOff`. -/
theorem atl_existsM : ∀ (n : Nat) (e : Ty), skN e < n → Clo e → mg e = true → accs e ≠ none →
    ∃ L, AtL e L ∧ ∀ p ∈ L, AtOff e p.1 p.2
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, e, hn, hc, hm, hne => by
    cases e with
    | prod a b =>
      simp only [skN] at hn
      simp only [mg, Bool.and_eq_true] at hm
      obtain ⟨hca, hcb⟩ := Clo_prod hc
      have hna : accs a ≠ none := by
        intro h; apply hne; simp [accs, h]
      have hnb : accs b ≠ none := by
        intro h; apply hne; simp [accs, h]
      obtain ⟨ua, hua⟩ := Option.ne_none_iff_exists'.1 hna
      obtain ⟨A, hA, hA2⟩ := atl_existsM n a (by omega) hca hm.1 hna
      obtain ⟨B, hB, hB2⟩ := atl_existsM n b (by omega) hcb hm.2 hnb
      refine ⟨A ++ B.map (shO (nWords ua)), .prod hua hA hB, fun p hp => ?_⟩
      rcases List.mem_append.1 hp with h | h
      · exact .fst (hA2 p h)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
        exact .snd hua (hB2 q hq)
    | mu s =>
      have hm0 := hm
      simp only [mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨hcU, haU, hat⟩ := mu_unfold_facts hc hm.1
      have hsk : skN (unfold1 (.mu s)) < n := by
        show skN (Ty.substT 0 (.mu s) s) < n
        rw [skN_substT s 0 _ hm.1]; simp only [skN] at hn; omega
      obtain ⟨L, hL, hL2⟩ := atl_existsM n _ hsk hcU (mg_unfold1 hm0) (by rw [haU]; exact hne)
      exact ⟨L, .mu hL, fun p hp => hat p.1 p.2 (hL2 p hp)⟩
    | _ => exact ⟨_, .atom ⟨fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩ hne,
        fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact .here (Or.inl hne)⟩

theorem atl_exists {e : Ty} (hc : Clo e) (hm : mg e = true) (hne : accs e ≠ none) :
    ∃ L, AtL e L ∧ ∀ p ∈ L, AtOff e p.1 p.2 :=
  atl_existsM (skN e + 1) e (Nat.lt_succ_self _) hc hm hne

/-- An atom with its resources, read off the words `ws` of the whole. -/
def AtR (ρ : Nat → Nat) (E : TEnv) (ws : List Word) (g : (Nat × Ty) × Res) : Prop :=
  ∃ n, wc g.1.2 = some n ∧ g.1.1 + n ≤ ws.length ∧
    VRR ρ (CE E) g.1.2 (shp g.1.2) ((ws.drop g.1.1).take n) g.2

/-- **The exact split**: a value's resources are the sum of its atoms' shares. -/
theorem VRR_atl (E : TEnv) {ρ : Nat → Nat} {T : Ty} {L : List (Nat × Ty)} (h : AtL T L) :
    Clo T → mg T = true → ∀ {ws : List Word} {R : Res}, VRR ρ (CE E) T (shp T) ws R → wc T = some ws.length →
      ∃ G : List ((Nat × Ty) × Res), G.map Prod.fst = L ∧ R = Res.sum (G.map Prod.snd) ∧
        ∀ g ∈ G, AtR ρ E ws g := by
  induction h with
  | @atom t _ _ =>
    intro _ _ ws R hv hwc
    refine ⟨[((0, t), R)], rfl, by simp, fun g hg => ?_⟩
    simp only [List.mem_singleton] at hg
    subst hg
    exact ⟨ws.length, hwc, by simp, by simpa using hv⟩
  | @prod a b A B us hus _ _ ihA ihB =>
    intro hc hm ws R hv hwc
    simp only [mg, Bool.and_eq_true] at hm
    obtain ⟨hca, hcb⟩ := Clo_prod hc
    cases hb' : accs b with
    | none => simp [wc, accs, hus, hb'] at hwc
    | some ub =>
    have hwa : wc a = some (nWords us) := wc_of_accs hus
    have hwb : wc b = some (nWords ub) := wc_of_accs hb'
    simp only [VRR] at hv
    obtain ⟨ra, rb, e, Ra, Rb, hR, -, hsplit⟩ := hv
    simp only [shp, Shp.prod.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have hlen : ws.length = nWords us + nWords ub := by
      simp [wc, accs, hus, hb', TermSound.nWords_append] at hwc; omega
    obtain ⟨_, hva, hvb⟩ := hsplit _ (by rw [shp_wc]; exact hwa)
    have hla : (ws.take (nWords us)).length = nWords us := by simp; omega
    have hlb : (ws.drop (nWords us)).length = nWords ub := by simp; omega
    obtain ⟨GA, eA, hRA, hGA⟩ := ihA hca hm.1 hva (by rw [hla]; exact hwa)
    obtain ⟨GB, eB, hRB, hGB⟩ := ihB hcb hm.2 hvb (by rw [hlb]; exact hwb)
    let f : (Nat × Ty) × Res → (Nat × Ty) × Res := fun g => (shO (nWords us) g.1, g.2)
    have hsn : (GB.map f).map Prod.snd = GB.map Prod.snd := by rw [List.map_map]; rfl
    have hfs : (GB.map f).map Prod.fst = (GB.map Prod.fst).map (shO (nWords us)) := by
      rw [List.map_map, List.map_map]; rfl
    refine ⟨GA ++ GB.map f, by rw [List.map_append, eA, hfs, eB], ?_, fun g hg => ?_⟩
    · rw [List.map_append, Res.sum_append, hsn, hR, hRA, hRB]
    · rcases List.mem_append.1 hg with hg | hg
      · obtain ⟨n, hwn, hle, hvn⟩ := hGA g hg
        rw [hla] at hle
        refine ⟨n, hwn, by omega, ?_⟩
        rwa [take_drop_take hle] at hvn
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        obtain ⟨n, hwn, hle, hvn⟩ := hGB g0 hg0
        rw [hlb] at hle
        refine ⟨n, hwn, by simp only [f, shO]; omega, ?_⟩
        rw [drop_drop'] at hvn
        exact hvn
  | @mu s L0 _ ih =>
    intro hc hm ws R hv hwc
    have hm0 := hm
    simp only [mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
    obtain ⟨hcU, -, -⟩ := mu_unfold_facts hc hm.1
    obtain ⟨hshp, hwcU, hvr⟩ := mu_unfold_vrr hc hm.1
    have hv' := (hvr ρ E _ ws R).2 hv
    rw [← hshp] at hv'
    exact ih hcU (mg_unfold1 hm0) hv' (by rw [hwcU]; exact hwc)

/-- The zero-width atoms of a type. -/
def zws (L : List (Nat × Ty)) : List Ty := (L.filter (fun p => wc p.2 == some 0)).map Prod.snd

theorem zws_append (A B : List (Nat × Ty)) : zws (A ++ B) = zws A ++ zws B := by
  simp [zws, List.filter_append]

theorem zws_shO (n : Nat) (B : List (Nat × Ty)) : zws (B.map (shO n)) = zws B := by
  induction B with
  | nil => rfl
  | cons p B ih =>
    simp only [zws, List.map_cons, List.filter_cons] at ih ⊢
    simp only [shO]
    split <;> simp_all

/-- **The zero-width atoms, in order**, are `ZwL`'s list. -/
theorem zwl_of_atl {T : Ty} {L : List (Nat × Ty)} (h : AtL T L) : ZwL T (zws L) := by
  induction h with
  | @atom t ha hn =>
    obtain ⟨us, hus⟩ := Option.ne_none_iff_exists'.1 hn
    have hw := wc_of_accs hus
    cases hk : nWords us with
    | zero =>
      rw [hk] at hw
      have : zws [(0, t)] = [t] := by simp [zws, hw]
      rw [this]; exact .zero ha hw
    | succ k =>
      rw [hk] at hw
      have : zws [(0, t)] = [] := by simp [zws, hw]
      rw [this]; exact .pos ha hw
  | prod _ _ _ ihA ihB =>
    rw [zws_append, zws_shO]; exact .prod ihA ihB
  | mu _ ih => exact .mu ih

/-! ## Bounds and disjointness of the atoms -/

/-- Every atom lies within the type's words. -/
theorem atl_bound {T : Ty} {L : List (Nat × Ty)} (h : AtL T L) :
    Clo T → mg T = true → ∀ {ut : List Acc}, accs T = some ut →
      ∀ p ∈ L, ∃ up, accs p.2 = some up ∧ p.1 + nWords up ≤ nWords ut := by
  induction h with
  | @atom t _ _ =>
    intro _ _ ut hut p hp
    simp only [List.mem_singleton] at hp; subst hp
    exact ⟨ut, hut, by simp⟩
  | @prod a b A B us hus _ _ ihA ihB =>
    intro hc hm ut hut p hp
    simp only [mg, Bool.and_eq_true] at hm
    obtain ⟨hca, hcb⟩ := Clo_prod hc
    cases hb : accs b with
    | none => simp [accs, hus, hb] at hut
    | some ub =>
    have e : ut = us ++ ub := by simp [accs, hus, hb] at hut; exact hut.symm
    subst e
    rw [TermSound.nWords_append]
    rcases List.mem_append.1 hp with h | h
    · obtain ⟨up, h1, h2⟩ := ihA hca hm.1 hus p h; exact ⟨up, h1, by omega⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
      obtain ⟨up, h1, h2⟩ := ihB hcb hm.2 hb q hq
      exact ⟨up, h1, by simp only [shO]; omega⟩
  | @mu s L0 _ ih =>
    intro hc hm ut hut p hp
    have hm0 := hm
    simp only [mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
    obtain ⟨hcU, haU, -⟩ := mu_unfold_facts hc hm.1
    exact ih hcU (mg_unfold1 hm0) (by rw [haU]; exact hut) p hp

/-- Two atoms of positive width are word-disjoint. -/
def PDj (p q : Nat × Ty) : Prop :=
  ∀ up uq, accs p.2 = some up → accs q.2 = some uq → 0 < nWords up → 0 < nWords uq →
    p.1 + nWords up ≤ q.1 ∨ q.1 + nWords uq ≤ p.1

theorem atl_disj {T : Ty} {L : List (Nat × Ty)} (h : AtL T L) :
    Clo T → mg T = true → L.Pairwise PDj := by
  induction h with
  | atom _ _ => intro _ _; exact List.pairwise_singleton _ _
  | @prod a b A B us hus hA _ ihA ihB =>
    intro hc hm
    simp only [mg, Bool.and_eq_true] at hm
    obtain ⟨hca, hcb⟩ := Clo_prod hc
    refine List.pairwise_append.2 ⟨ihA hca hm.1, ?_, fun p hp q hq => ?_⟩
    · refine List.pairwise_map.2 ((ihB hcb hm.2).imp fun {p q} hpq => ?_)
      intro up uq h1 h2 h3 h4
      have := hpq up uq h1 h2 h3 h4
      simp only [shO]; omega
    · intro up uq h1 h2 h3 h4
      obtain ⟨up', h1', h2'⟩ := atl_bound hA hca hm.1 hus p hp
      rw [h1] at h1'; cases h1'
      obtain ⟨q0, -, rfl⟩ := List.mem_map.1 hq
      left; simp only [shO]; omega
  | @mu s L0 _ ih =>
    intro hc hm
    have hm0 := hm
    simp only [mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
    obtain ⟨hcU, -, -⟩ := mu_unfold_facts hc hm.1
    exact ih hcU (mg_unfold1 hm0)

/-! ## Regrouping a sum by offsets -/

theorem sum_ite_range (x : Res) : ∀ (M k : Nat), k < M →
    Res.sum ((List.range M).map fun o => if k = o then x else Res.zero) = x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | M + 1, k, h => by
    rw [List.range_succ, List.map_append, Res.sum_append]
    by_cases hk : k = M
    · subst hk
      have : Res.sum ((List.range k).map fun o => if k = o then x else Res.zero) = Res.zero := by
        rw [show ((List.range k).map fun o => if k = o then x else Res.zero) =
            (List.range k).map (fun _ => Res.zero) from
          List.map_congr_left (fun o ho => by
            have := List.mem_range.1 ho
            simp only [show k ≠ o from by omega, ite_false])]
        exact TermStep.sum_map_zero _
      rw [this]; simp
    · rw [sum_ite_range x M k (by omega)]; simp [hk]

theorem sum_map_add' {α : Type} (A B : α → Res) : ∀ L : List α,
    Res.sum (L.map fun o => A o + B o) = Res.sum (L.map A) + Res.sum (L.map B)
  | [] => by simp
  | x :: L => by
    simp only [List.map_cons, Res.sum_cons, sum_map_add' A B L]
    exact Res.ext fun k => by simp only [Res.add_apply]; omega

/-- A sum regrouped by a key below `M`. -/
theorem sum_regroup {α : Type} (f : α → Res) (key : α → Nat) (M : Nat) : ∀ G : List α, (∀ g ∈ G, key g < M) →
    Res.sum (G.map f) = Res.sum ((List.range M).map fun o => Res.sum ((G.filter (fun g => key g == o)).map f))
  | [], _ => by simp only [List.map_nil, List.filter_nil, Res.sum_nil]; exact (TermStep.sum_map_zero _).symm
  | g :: G, hG => by
    have ih := sum_regroup f key M G (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg'))
    have e : ((List.range M).map fun o => Res.sum (((g :: G).filter (fun g => key g == o)).map f)) =
        (List.range M).map (fun o => (if key g = o then f g else Res.zero) +
          Res.sum ((G.filter (fun g => key g == o)).map f)) := by
      apply List.map_congr_left; intro o _
      by_cases h : key g = o
      · simp [h]
      · simp [h]
    rw [e, sum_map_add', sum_ite_range _ M _ (hG g (List.mem_cons_self ..)), ← ih]
    simp

/-! ## Completeness: every atomic laid-out component is listed -/

theorem atl_atom_inv {T : Ty} {L : List (Nat × Ty)} (h : AtL T L) (hT : AtomT T) : L = [(0, T)] := by
  cases h with
  | atom _ _ => rfl
  | prod _ _ _ => exact absurd rfl (hT.1 _ _)
  | mu _ => exact absurd rfl (hT.2 _)

theorem atl_complete {T : Ty} {o : Nat} {U : Ty} (h : AtOff T o U) :
    ∀ {L : List (Nat × Ty)}, AtL T L → AtomT U → (o, U) ∈ L := by
  induction h with
  | here _ =>
    intro L hL hU
    rw [atl_atom_inv hL hU]; exact List.mem_singleton_self _
  | @fst a b u o _ ih =>
    intro L hL hU
    cases hL with
    | prod _ hA _ => exact List.mem_append_left _ (ih hA hU)
    | atom hT _ => exact absurd rfl (hT.1 _ _)
  | @snd a b u o us hus _ ih =>
    intro L hL hU
    cases hL with
    | @prod _ _ A B us' hus' _ hB =>
      rw [hus] at hus'; cases hus'
      exact List.mem_append_right _ (List.mem_map.2 ⟨(o, u), ih hB hU, rfl⟩)
    | atom hT _ => exact absurd rfl (hT.1 _ _)
  | elem hu _ _ _ =>
    intro L hL _
    cases hL with
    | atom _ hn => simp [accs] at hn
  | @mu ρ W s u o hW _ _ ih =>
    intro L hL hU
    rw [cl_mu_eq] at hL
    cases hL with
    | mu hL' =>
      rw [← cl_mu_eq, ← TermStep.cl_unfold1 hW] at hL'
      exact ih hL' hU
    | atom hT _ => exact absurd rfl (hT.2 _)
  | @fold ρ W s T o _ _ _ _ _ =>
    intro L _ hU
    exact absurd (cl_mu_eq ρ W s) (hU.2 _)

/-! ## The slot split by classes: zero-width atoms, blocks, protocol words -/

/-- A zero-width atom. -/
def cz (U : Ty) : Bool := wc U == some 0
/-- A non-ghost protocol word. -/
def cw : Ty → Bool
  | .word _ P => !P.ghost
  | _ => false

theorem sum_filter_split {α : Type} (f : α → Res) (p : α → Bool) : ∀ G : List α,
    Res.sum (G.map f) = Res.sum ((G.filter p).map f) + Res.sum ((G.filter (fun g => !p g)).map f)
  | [] => by simp
  | g :: G => by
    have ih := sum_filter_split f p G
    cases hp : p g with
    | true =>
      simp only [List.filter_cons, hp, ite_true, Bool.not_true, List.map_cons, Res.sum_cons, ih]
      simp; exact (Res.add_assoc _ _ _).symm
    | false =>
      simp only [List.filter_cons, hp, Bool.not_false, ite_true, List.map_cons, Res.sum_cons, ih]
      simp
      exact Res.ext fun k => by simp only [Res.add_apply]; omega

theorem len_le_one {α : Type} {R : α → α → Prop} (hR : ∀ x y, R x y → False) :
    ∀ {K : List α}, K.Pairwise R → K = [] ∨ ∃ x, K = [x]
  | [], _ => .inl rfl
  | [x], _ => .inr ⟨x, rfl⟩
  | x :: y :: _, h => absurd ((List.pairwise_cons.1 h).1 y (List.mem_cons_self ..)) (hR x y)

/-- The class sum at offset `o` of the entries satisfying `q`. -/
def offSum (G : List ((Nat × Ty) × Res)) (q : Ty → Bool) (o : Nat) : Res :=
  Res.sum (((G.filter (fun g => q g.1.2)).filter (fun g => g.1.1 == o)).map Prod.snd)

/-- At an offset there is at most one positive-width entry of a class. -/
theorem offSum_single {G : List ((Nat × Ty) × Res)} {ρ : Nat → Nat} {E : TEnv} {ws : List Word}
    (hG : ∀ g ∈ G, AtR ρ E ws g) (hd : (G.map Prod.fst).Pairwise PDj) (q : Ty → Bool)
    (hq : ∀ U, q U = true → cz U = false) (o : Nat) :
    (offSum G q o = .zero ∧ ∀ g ∈ G, g.1.1 = o → q g.1.2 = true → False) ∨
      ∃ g ∈ G, g.1.1 = o ∧ q g.1.2 = true ∧ offSum G q o = g.2 := by
  have hp : ((G.filter (fun g => q g.1.2)).filter (fun g => g.1.1 == o)).Pairwise (fun x y => PDj x.1 y.1) :=
    ((List.pairwise_map.1 hd).filter _).filter _
  have hpos : ∀ g ∈ G, q g.1.2 = true → ∃ u, accs g.1.2 = some u ∧ 0 < nWords u := by
    intro g hg hqg
    obtain ⟨n, hn, -⟩ := hG g hg
    obtain ⟨u, hu, rfl⟩ := wc_some hn
    have h1 := hq _ hqg
    have h2 : nWords u ≠ 0 := by intro h0; rw [cz, hn, h0] at h1; simp at h1
    exact ⟨u, hu, Nat.pos_of_ne_zero h2⟩
  rcases len_le_one (R := fun x y : (Nat × Ty) × Res => PDj x.1 y.1 ∧
      (x ∈ G ∧ q x.1.2 = true ∧ x.1.1 = o) ∧ (y ∈ G ∧ q y.1.2 = true ∧ y.1.1 = o))
      (fun x y ⟨hxy, ⟨hx, hqx, hox⟩, ⟨hy, hqy, hoy⟩⟩ => by
        obtain ⟨ux, hux, hpx⟩ := hpos x hx hqx
        obtain ⟨uy, huy, hpy⟩ := hpos y hy hqy
        have := hxy ux uy hux huy hpx hpy
        omega)
      (List.Pairwise.imp_of_mem (R := fun x y => PDj x.1 y.1) (fun {x y} hx hy hxy => by
        simp only [List.mem_filter, beq_iff_eq] at hx hy
        exact ⟨hxy, ⟨hx.1.1, hx.1.2, hx.2⟩, ⟨hy.1.1, hy.1.2, hy.2⟩⟩) hp) with h0 | ⟨x, hx⟩
  · left
    refine ⟨by simp [offSum, h0], fun g hg hgo hqg => ?_⟩
    have : g ∈ (G.filter (fun g => q g.1.2)).filter (fun g => g.1.1 == o) := by
      simp [hg, hgo, hqg]
    rw [h0] at this; cases this
  · right
    have hxm : x ∈ (G.filter (fun g => q g.1.2)).filter (fun g => g.1.1 == o) := by rw [hx]; simp
    simp only [List.mem_filter, beq_iff_eq] at hxm
    exact ⟨x, hxm.1.1, hxm.2, hxm.1.2, by simp [offSum, hx]⟩

/-- **The slot split**: a value of a closed guarded type, read on its words `ws`, holds the sum of
its zero-width atoms' shares, its blocks' shares by offset, and its protocol words' shares by
offset. -/
theorem slot_split (E : TEnv) {ρ : Nat → Nat} {e : Ty} {L : List (Nat × Ty)} (hL : AtL e L) (hc : Clo e)
    (hm : mg e = true) {us : List Acc} (hu : accs e = some us) {ws : List Word} {R : Res}
    (hv : VRR ρ (CE E) e (shp e) ws R) (hl : ws.length = nWords us) :
    ∃ G : List ((Nat × Ty) × Res), G.map Prod.fst = L ∧ (∀ g ∈ G, AtR ρ E ws g) ∧
      R = Res.sum ((G.filter (fun g => cz g.1.2)).map Prod.snd) +
        Res.sum ((List.range (nWords us)).map (offSum G (fun U => !cz U && !cw U))) +
        Res.sum ((List.range (nWords us)).map (offSum G (fun U => !cz U && cw U))) := by
  obtain ⟨G, eG, hR, hG⟩ := VRR_atl E hL hc hm hv (by rw [wc_of_accs hu, hl])
  refine ⟨G, eG, hG, ?_⟩
  have hlt : ∀ g ∈ G, cz g.1.2 = false → g.1.1 < nWords us := by
    intro g hg hz
    obtain ⟨n, hn, hle, -⟩ := hG g hg
    have h2 : n ≠ 0 := by intro h0; rw [cz, hn, h0] at hz; simp at hz
    omega
  rw [hR, sum_filter_split Prod.snd (fun g => cz g.1.2) G]
  rw [sum_filter_split Prod.snd (fun g => cw g.1.2) (G.filter (fun g => !cz g.1.2))]
  have hb := sum_regroup Prod.snd (fun g : (Nat × Ty) × Res => g.1.1) (nWords us)
    ((G.filter (fun g => !cz g.1.2)).filter (fun g => !cw g.1.2)) (fun g hg => by
      simp only [List.mem_filter, Bool.not_eq_true'] at hg
      exact hlt g hg.1.1 hg.1.2)
  have hw := sum_regroup Prod.snd (fun g : (Nat × Ty) × Res => g.1.1) (nWords us)
    ((G.filter (fun g => !cz g.1.2)).filter (fun g => cw g.1.2)) (fun g hg => by
      simp only [List.mem_filter, Bool.not_eq_true'] at hg
      exact hlt g hg.1.1 hg.1.2)
  have fb : (G.filter (fun g => !cz g.1.2)).filter (fun g => !cw g.1.2) =
      G.filter (fun g => !cz g.1.2 && !cw g.1.2) := by
    rw [List.filter_filter]; exact List.filter_congr fun g _ => Bool.and_comm _ _
  have fw : (G.filter (fun g => !cz g.1.2)).filter (fun g => cw g.1.2) =
      G.filter (fun g => !cz g.1.2 && cw g.1.2) := by
    rw [List.filter_filter]; exact List.filter_congr fun g _ => Bool.and_comm _ _
  rw [hb, hw, fb, fw]
  rw [Res.add_assoc, Res.add_comm (Res.sum ((List.range (nWords us)).map _)) (Res.sum ((List.range (nWords us)).map _))]
  rfl

/-! ## Atoms are atomic and closed; closed words have literal regions -/

theorem atl_props {T : Ty} {L : List (Nat × Ty)} (h : AtL T L) :
    Clo T → mg T = true → ∀ p ∈ L, AtomT p.2 ∧ Clo p.2 := by
  induction h with
  | @atom t ha _ =>
    intro hc _ p hp
    simp only [List.mem_singleton] at hp; subst hp; exact ⟨ha, hc⟩
  | @prod a b A B us _ _ _ ihA ihB =>
    intro hc hm p hp
    simp only [mg, Bool.and_eq_true] at hm
    obtain ⟨hca, hcb⟩ := Clo_prod hc
    rcases List.mem_append.1 hp with h | h
    · exact ihA hca hm.1 p h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
      exact ihB hcb hm.2 q hq
  | @mu s L0 _ ih =>
    intro hc hm p hp
    have hm0 := hm
    simp only [mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
    obtain ⟨hcU, -, -⟩ := mu_unfold_facts hc hm.1
    exact ih hcU (mg_unfold1 hm0) p hp

theorem clI0_lit (ρ : Nat → Nat) : ∀ r : Idx, ∃ n, clI ρ 0 r = .lit n
  | .lit n => ⟨n, rfl⟩
  | .var k => ⟨ρ (k - 0), by simp [clI]⟩
  | .add i j => by
    obtain ⟨a, ha⟩ := clI0_lit ρ i
    obtain ⟨b, hb⟩ := clI0_lit ρ j
    exact ⟨a + b, by simp [clI, ha, hb, addF]⟩
  | .sub i j => by
    obtain ⟨a, ha⟩ := clI0_lit ρ i
    obtain ⟨b, hb⟩ := clI0_lit ρ j
    exact ⟨a - b, by simp [clI, ha, hb, subF]⟩
  | .smul m i => by
    obtain ⟨a, ha⟩ := clI0_lit ρ i
    exact ⟨m * a, by simp [clI, ha, smulF]⟩

theorem clo_word_lit {r : Idx} {P : Proto} (h : Clo (.word r P)) : ∃ n, r = .lit n := by
  obtain ⟨n, hn⟩ := clI0_lit (fun _ => 0) r
  have := h.2 (fun _ => 0) (fun _ => .void) 0 0
  simp only [cl, Ty.word.injEq] at this
  exact ⟨n, this.1 ▸ hn⟩

/-! ## Slot addresses -/

theorem slot_eq2 {n j j' i o : Nat} (hi : i < n) (ho : o < n) (h : j' * n + o = j * n + i) : j' = j ∧ o = i := by
  have hn : 0 < n := by omega
  have h1 : (j' * n + o) / n = j' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ho, Nat.zero_add]
  have h2 : (j * n + i) / n = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hj : j' = j := by rw [← h1, h, h2]
  subst hj; exact ⟨rfl, by omega⟩

section Addr
variable {E : TEnv} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc} {j i : Nat}

theorem blkStart_iff (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hone : ∀ u ∈ us, u = .one) (hj : j < N) (hi : i < nWords us) {U : Ty} :
    BlkStart E ⟨l, j * nWords us + i⟩ U ↔ AtOff e i U ∧ AtomT U ∧ (∃ w, wc U = some w ∧ 0 < w) ∧
      ∀ r P, U = .word r P → P.ghost = true := by
  constructor
  · rintro ⟨c1, N1, e1, us1, j1, o1, w1, hc1, hT1, hu1, -, hj1, hoff, hat, hA, hw, hw0, hg⟩
    rw [hc] at hc1; cases hc1
    rw [hT] at hT1; cases hT1
    rw [hu] at hu1; cases hu1
    obtain ⟨uU, huU, rfl⟩ := wc_some hw
    have hb := AtOff_bound hat hu huU
    obtain ⟨-, rfl⟩ := slot_eq2 hi (by omega) hoff.symm
    exact ⟨hat, hA, ⟨_, hw, hw0⟩, hg⟩
  · rintro ⟨hat, hA, ⟨w, hw, hw0⟩, hg⟩
    exact ⟨c, N, e, us, j, i, w, hc, hT, hu, hone, hj, rfl, hat, hA, hw, hw0, hg⟩

theorem slotStart_iff (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hone : ∀ u ∈ us, u = .one) (hi : i < nWords us) :
    SlotStart E ⟨l, j * nWords us + i⟩ ↔ i = 0 := by
  constructor
  · rintro ⟨c1, N1, e1, us1, hc1, hT1, hu1, hpos, -, hmod⟩
    rw [hc] at hc1; cases hc1
    rw [hT] at hT1; cases hT1
    rw [hu] at hu1; cases hu1
    simp only [Nat.mul_comm j, Nat.mul_add_mod, Nat.mod_eq_of_lt hi] at hmod
    exact hmod
  · intro h0
    subst h0
    exact ⟨c, N, e, us, hc, hT, hu, by omega, hone, by simp⟩

theorem wordAt_iff (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hj : j < N) (hi : i < nWords us) {n : Nat} {P : Proto} :
    WordAt E ⟨l, j * nWords us + i⟩ n P ↔ AtOff e i (.word (.lit n) P) ∧ P.ghost = false := by
  constructor
  · rintro ⟨c1, hc1, hat, hg⟩
    rw [hc] at hc1; cases hc1
    rw [hT] at hat
    rcases AtOff_array_inv (fun _ h => by cases h) hat with ⟨-, h⟩ | ⟨n1, j1, o2, us1, h1, hu1, hj1, hoff, hat2⟩
    · cases h
    · cases h1
      rw [hu] at hu1; cases hu1
      have hb := AtOff_bound hat2 hu (us := [Acc.one]) (by simp [accs, hg])
      have h1 : nWords [Acc.one] = 1 := by simp [nWords, Acc.size]
      rw [h1] at hb
      have hb' : o2 < nWords us := by omega
      obtain ⟨-, rfl⟩ := slot_eq2 hi hb' hoff.symm
      exact ⟨hat2, hg⟩
  · rintro ⟨hat, hg⟩
    exact ⟨c, hc, by rw [hT]; exact AtOff.elem hu hj hat, hg⟩

end Addr

/-! ## The designated debits of a slot -/

theorem noOwnR_add (X Y : Res) : noOwnR (X + Y) = noOwnR X + noOwnR Y := by
  funext k; cases k <;> simp [noOwnR]

theorem noOwnR_sum {α : Type} (f : α → Res) : ∀ L : List α,
    noOwnR (Res.sum (L.map f)) = Res.sum (L.map fun a => noOwnR (f a))
  | [] => by funext k; cases k <;> simp [noOwnR]
  | a :: L => by simp only [List.map_cons, Res.sum_cons, noOwnR_add, noOwnR_sum f L]

theorem take1_drop {ws : List Word} : ∀ {i : Nat} {w : Word}, ws[i]? = some w → (ws.drop i).take 1 = [w] := by
  induction ws with
  | nil => intro i w h; simp at h
  | cons x xs ih =>
    intro i w h
    cases i with
    | zero => simp at h; simp [h]
    | succ i => simp at h; simpa using ih h

theorem getElem_take_drop {ws : List Word} {i n o : Nat} {x : Word} (h : ((ws.drop i).take n)[o]? = some x) :
    ws[i + o]? = some x := by
  simp only [List.getElem?_take, List.getElem?_drop] at h
  split at h
  · exact h
  · cases h

theorem lt_of_getElem? {ws : List Word} {i : Nat} {w : Word} (h : ws[i]? = some w) : i < ws.length := by
  apply Nat.lt_of_not_le; intro h2; rw [List.getElem?_eq_none h2] at h; cases h

section Debits
variable {E : TEnv} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc} {j : Nat}

/-- **The designated debits of a slot**: a value of a closed guarded all-`.one` element type,
read on the slot's first writes, splits over the slot's units as word parts (`FRes`) plus
non-word parts (`BlkDb`: the block starting there, and at the slot start the zero-width
components). -/
theorem slot_debits (mem : Memory) (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e)
    (hu : accs e = some us) (hone : ∀ u ∈ us, u = .one) (hpos : 0 < nWords us) (hj : j < N)
    (hCl : Clo e) (hm : mg e = true) {ws : List Word} {Rj : Res} (hl : ws.length = nWords us)
    (hws : ∀ o x, ws[o]? = some x → ∃ h m, FirstW mem ⟨l, j * nWords us + o⟩ h ∧ mem[h]? = some m ∧ x = mw m)
    (hv : VRR (fun _ => 0) (CE E.unsee) e (shp e) ws Rj) (hno : noOwnR Rj = Rj) :
    ∃ F Z : Nat → Res, Rj = Res.sum ((List.range (nWords us)).map fun i => F i + Z i) ∧
      (∀ i w, ws[i]? = some w → FRes E ⟨l, j * nWords us + i⟩ w (F i)) ∧
      ∀ i, i < nWords us → BlkDb E mem ⟨l, j * nWords us + i⟩ (Z i) := by
  obtain ⟨L, hL, hLo⟩ := atl_exists hCl hm (by rw [hu]; simp)
  obtain ⟨G, eG, hG, hR⟩ := slot_split E.unsee hL hCl hm hu hv hl
  have hd : (G.map Prod.fst).Pairwise PDj := by rw [eG]; exact atl_disj hL hCl hm
  have hmemL : ∀ g ∈ G, g.1 ∈ L := fun g hg => by rw [← eG]; exact List.mem_map.2 ⟨g, hg, rfl⟩
  have hprops : ∀ g ∈ G, AtomT g.1.2 ∧ Clo g.1.2 := fun g hg => atl_props hL hCl hm g.1 (hmemL g hg)
  have hoff : ∀ g ∈ G, AtOff e g.1.1 g.1.2 := fun g hg => hLo g.1 (hmemL g hg)
  have hinG : ∀ {o : Nat} {U : Ty}, AtOff e o U → AtomT U → ∃ g ∈ G, g.1 = (o, U) := by
    intro o U h hA
    have h1 := atl_complete h hL hA
    rw [← eG] at h1
    exact List.mem_map.1 h1
  have hqb : ∀ U, (fun U => !cz U && !cw U) U = true → cz U = false := by
    intro U h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1
  have hqw : ∀ U, (fun U => !cz U && cw U) U = true → cz U = false := by
    intro U h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1
  refine ⟨offSum G (fun U => !cz U && cw U), fun i => noOwnR (offSum G (fun U => !cz U && !cw U) i +
    if i = 0 then Res.sum ((G.filter (fun g => cz g.1.2)).map Prod.snd) else .zero), ?_, ?_, ?_⟩
  · -- the sum
    rw [sum_map_add' (offSum G (fun U => !cz U && cw U)), ← noOwnR_sum, sum_map_add']
    have hz := sum_ite_range (Res.sum ((G.filter (fun g => cz g.1.2)).map Prod.snd)) (nWords us) 0 hpos
    have hz2 : Res.sum ((List.range (nWords us)).map fun i =>
        if i = 0 then Res.sum ((G.filter (fun g => cz g.1.2)).map Prod.snd) else Res.zero) =
        Res.sum ((G.filter (fun g => cz g.1.2)).map Prod.snd) := by
      have e : ((List.range (nWords us)).map fun i =>
          if i = 0 then Res.sum ((G.filter (fun g => cz g.1.2)).map Prod.snd) else Res.zero) =
          (List.range (nWords us)).map fun o =>
          if 0 = o then Res.sum ((G.filter (fun g => cz g.1.2)).map Prod.snd) else Res.zero := by
        apply List.map_congr_left; intro o _
        by_cases h : o = 0
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [e]; exact hz
    rw [hz2]
    refine Res.ext fun k => ?_
    have hk := congrFun hR k
    have hk0 := congrFun hno k
    simp only [Res.add_apply] at hk ⊢
    cases k with
    | own l0 => simp only [noOwnR_own] at hk0 ⊢; omega
    | _ => simp only [noOwnR, Res.add_apply] at hk0 ⊢; omega
  · -- the word parts
    intro i w hw
    have hi : i < nWords us := by rw [← hl]; exact lt_of_getElem? hw
    rcases offSum_single hG hd _ hqw i with ⟨h0, hno0⟩ | ⟨⟨⟨o, U⟩, Rg⟩, hg, hgo, hqg, hF⟩
    · right
      refine ⟨fun n P hW => ?_, h0⟩
      obtain ⟨hat, hgh⟩ := (wordAt_iff hc hT hu hj hi).1 hW
      obtain ⟨g, hg, e1⟩ := hinG hat ⟨fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩
      refine hno0 g hg (by rw [e1]) ?_
      rw [e1]; simp [cz, cw, hgh, wc, accs, nWords, Acc.size]
    · left
      simp only at hgo hqg hF
      subst o
      obtain ⟨-, hCU⟩ := hprops _ hg
      have hat := hoff _ hg
      obtain ⟨n, hn, -, hvg⟩ := hG _ hg
      simp only at hCU hat hn hvg
      cases U with
      | word r P =>
        simp only [cw, Bool.and_eq_true, Bool.not_eq_true'] at hqg
        obtain ⟨n0, rfl⟩ := clo_word_lit hCU
        have hn1 : n = 1 := by simp [wc, accs, nWords, Acc.size, hqg.2] at hn; omega
        subst hn1
        rw [take1_drop hw] at hvg
        exact ⟨n0, P, (wordAt_iff hc hT hu hj hi).2 ⟨hat, hqg.2⟩, by rw [hF]; exact VRR_word_wr hvg⟩
      | _ => simp [cw] at hqg
  · -- the non-word parts
    intro i hi
    refine ⟨offSum G (fun U => !cz U && !cw U) i,
      if i = 0 then Res.sum ((G.filter (fun g => cz g.1.2)).map Prod.snd) else .zero, ?_, ?_, rfl⟩
    · rcases offSum_single hG hd _ hqb i with ⟨h0, hno0⟩ | ⟨⟨⟨o, U⟩, Rg⟩, hg, hgo, hqg, hB⟩
      · right
        refine ⟨fun U hBs => ?_, h0⟩
        obtain ⟨hat, hA, ⟨w, hw, hw0⟩, hgh⟩ := (blkStart_iff hc hT hu hone hj hi).1 hBs
        obtain ⟨g, hg, e1⟩ := hinG hat hA
        refine hno0 g hg (by rw [e1]) ?_
        rw [e1]
        have hcz : cz U = false := by
          simp [cz, hw]; omega
        have hcw : cw U = false := by
          cases U with
          | word r P => simp [cw, hgh r P rfl]
          | _ => rfl
        simp [hcz, hcw]
      · left
        simp only at hgo hqg hB
        subst o
        obtain ⟨hA, -⟩ := hprops _ hg
        have hat := hoff _ hg
        obtain ⟨n, hn, hle, hvg⟩ := hG _ hg
        simp only at hA hat hn hle hvg
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hqg
        have hn0 : 0 < n := by
          apply Nat.pos_of_ne_zero; intro h0; have := hqg.1; simp [cz, hn, h0] at this
        have hgh : ∀ r P, U = .word r P → P.ghost = true := by
          intro r P hU; subst hU; have := hqg.2; simpa [cw] using this
        refine ⟨U, n, (ws.drop i).take n, (blkStart_iff hc hT hu hone hj hi).2 ⟨hat, hA, ⟨n, hn, hn0⟩, hgh⟩,
          hn, ?_, fun o x hx => ?_, E, fun _ _ h => h, by rw [hB]; exact hvg⟩
        · simp only [List.length_take, List.length_drop]; omega
        · obtain ⟨h, m, hf, hm1, hx1⟩ := hws (i + o) x (getElem_take_drop hx)
          exact ⟨h, m, by simpa [Nat.add_assoc] using hf, hm1, hx1⟩
    · by_cases hi0 : i = 0
      · subst hi0
        simp only [if_true]
        left
        have hzG : zws L = (G.filter (fun g => cz g.1.2)).map (fun g => g.1.2) := by
          rw [← eG, zws, List.filter_map, List.map_map]; rfl
        refine ⟨(slotStart_iff hc hT hu hone hi).2 rfl, c, N, e, us, zws L,
          (G.filter (fun g => cz g.1.2)).map Prod.snd, E, hc, hT, hu, zwl_of_atl hL,
          by rw [hzG]; simp, rfl, fun _ _ h => h, fun i' U Ri hU hRi => ?_⟩
        rw [hzG, List.getElem?_map] at hU
        rw [List.getElem?_map] at hRi
        cases hgi : (G.filter (fun g => cz g.1.2))[i']? with
        | none => rw [hgi] at hU; cases hU
        | some g =>
          rw [hgi] at hU hRi
          simp only [Option.map_some, Option.some.injEq] at hU hRi
          subst hU; subst hRi
          have hgm := List.mem_of_getElem? hgi
          simp only [List.mem_filter] at hgm
          obtain ⟨n, hn, -, hvg⟩ := hG g hgm.1
          have hn0 : n = 0 := by have := hgm.2; simp [cz, hn] at this; exact this
          subst hn0
          simpa using hvg
      · right
        exact ⟨fun hS => hi0 ((slotStart_iff hc hT hu hone hi).1 hS), by simp [hi0]⟩

/-- `slot_debits` from a slot value (`ValOfR`) of an own-free element type. -/
theorem slot_debitsV (mem : Memory) (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e)
    (hu : accs e = some us) (hone : ∀ u ∈ us, u = .one) (hpos : 0 < nWords us) (hj : j < N)
    (hCl : Clo e) (hm : mg e = true) (hno : Ty.noOwnIn [] e = true) {ws : List Word} {Rj : Res}
    (hl : ws.length = nWords us)
    (hws : ∀ o x, ws[o]? = some x → ∃ h m, FirstW mem ⟨l, j * nWords us + o⟩ h ∧ mem[h]? = some m ∧ x = mw m)
    (hv : ValOfR E e ws Rj) :
    ∃ F Z : Nat → Res, Rj = Res.sum ((List.range (nWords us)).map fun i => F i + Z i) ∧
      (∀ i w, ws[i]? = some w → FRes E ⟨l, j * nWords us + i⟩ w (F i)) ∧
      ∀ i, i < nWords us → BlkDb E mem ⟨l, j * nWords us + i⟩ (Z i) :=
  slot_debits mem hc hT hu hone hpos hj hCl hm hl hws hv.1 (noOwnR_valOfR hno hv)

end Debits

end TermSlotS

#print axioms TermSlotS.mu_unfold_vrr
#print axioms TermSlotS.atl_exists
#print axioms TermSlotS.VRR_atl
#print axioms TermSlotS.zwl_of_atl
#print axioms TermSlotS.atl_bound
#print axioms TermSlotS.atl_disj
#print axioms TermSlotS.sum_regroup
#print axioms TermSlotS.atl_complete
#print axioms TermSlotS.offSum_single
#print axioms TermSlotS.slot_split
#print axioms TermSlotS.blkStart_iff
#print axioms TermSlotS.slotStart_iff
#print axioms TermSlotS.wordAt_iff
#print axioms TermSlotS.clo_word_lit
#print axioms TermSlotS.atl_props
#print axioms TermSlotS.slot_debits
#print axioms TermSlotS.slot_debitsV
