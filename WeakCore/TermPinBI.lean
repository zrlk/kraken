import WeakCore.TermPinDet
import WeakCore.TermWdCover

/-! # TermPinBI (PIN P8, route D): a slot's first-write debits are paid by the written value

`dbF_le_val`: at a `bufInit` of a planted slot, the debits of the slot's first-write promises (`DbRes`
at `InitAt`: the word part `FRes`, the block part `BlkZ`, the zero-width part `ZwZ`) sum to at most the
resources of the written value.  Each part is a distinct atom of the slot's element (`AtomL`), and its
debit is that atom's holding (`VRR` is functional at `wrapTop` types, `vrr_detW`); `value_sumR` sums.
* `AtomL` and `AtOff`: a solid laid-out component is an atom (`atomL_of_atOff`); positive-width atoms
  sit at distinct offsets (`atomL_off_inj`); the zero-width atoms are `ZwL`'s (`atomL_zwL`).
-/

namespace TermPinBI
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermA4
open TermPinAtoms TermPinDet
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
/-! ## Atoms and components -/

/-- A closed `μ` type is not atomic. -/
theorem not_atomT_mu {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} : ¬ AtomT (cl ρ W 0 0 (.mu s)) :=
  fun h => h.2 _ (cl_mu_eq ρ W s)

/-- Inversion of `AtomL` at a closed `μ` type: the atoms of its unfolding. -/
theorem atomL_mu_inv {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} (hW : ∀ k, Clo (W k)) {As : List (Nat × Ty)}
    (h : AtomL (cl ρ W 0 0 (.mu s)) As) : AtomL (cl ρ W 0 0 (unfold1 (.mu s))) As := by
  generalize hT : cl ρ W 0 0 (.mu s) = T at h
  cases h with
  | atom ht => exact absurd (hT ▸ ht) not_atomT_mu
  | prod _ _ _ => rw [cl_mu_eq] at hT; cases hT
  | @mu ρ' W' s' L hW' _ hL =>
      rw [cl_unfold1 hW, hT, ← cl_unfold1 hW']
      exact hL

/-- Inversion of `AtomL` at a pair. -/
theorem atomL_prod_inv {a b : Ty} {As : List (Nat × Ty)} (h : AtomL (.prod a b) As) :
    ∃ A B us, accs a = some us ∧ AtomL a A ∧ AtomL b B ∧ As = A ++ B.map (TermPiece.sh (nWords us)) := by
  generalize hT : Ty.prod a b = T at h
  cases h with
  | atom ht => exact absurd hT.symm (ht.1 a b)
  | prod hus hA hB => cases hT; exact ⟨_, _, _, hus, hA, hB, rfl⟩
  | mu _ _ _ => rw [cl_mu_eq] at hT; cases hT

/-- Inversion of `AtomL` at an atomic type. -/
theorem atomL_atom_inv {t : Ty} (ht : AtomT t) {As : List (Nat × Ty)} (h : AtomL t As) : As = [(0, t)] := by
  cases h with
  | atom _ => rfl
  | prod _ _ _ => exact absurd rfl (ht.1 _ _)
  | mu _ _ _ => exact absurd (cl_mu_eq _ _ _) (ht.2 _)

/-- **A solid laid-out component is an atom**, at its offset. -/
theorem atomL_of_atOff {T V : Ty} {o : Nat} (h : AtOff T o V) :
    Solid V → accs T ≠ none → ∀ {As : List (Nat × Ty)}, AtomL T As → ∃ k : Nat, As[k]? = some (o, V) := by
  induction h with
  | @here t _ =>
      intro hV _ As hA
      rw [atomL_atom_inv ⟨hV.1, hV.2.2⟩ hA]
      exact ⟨0, rfl⟩
  | @fst a b u o _ ih =>
      intro hV hn As hA
      obtain ⟨A, B, us, hus, hA0, -, rfl⟩ := atomL_prod_inv hA
      have hna : accs a ≠ none := by rw [hus]; simp
      obtain ⟨k, hk⟩ := ih hV hna hA0
      have hkA : k < A.length := by
        rcases Nat.lt_or_ge k A.length with h1 | h1
        · exact h1
        · rw [List.getElem?_eq_none h1] at hk; cases hk
      exact ⟨k, by rw [List.getElem?_append_left hkA]; exact hk⟩
  | @snd a b u o us hus0 _ ih =>
      intro hV hn As hA
      obtain ⟨A, B, us', hus, -, hB0, rfl⟩ := atomL_prod_inv hA
      rw [hus0] at hus; cases hus
      have hnb : accs b ≠ none := by
        intro hb; apply hn; simp [accs, hb]
      obtain ⟨k, hk⟩ := ih hV hnb hB0
      refine ⟨A.length + k, ?_⟩
      rw [List.getElem?_append_right (by omega), List.getElem?_map, Nat.add_sub_cancel_left, hk]; rfl
  | elem _ _ _ _ =>
      intro _ hn
      exact absurd (by simp [accs]) hn
  | @mu ρ W s u o hW hg _ ih =>
      intro hV hn As hA
      exact ih hV (by rw [accs_cl_unfold_eq hW hg]; exact hn) (atomL_mu_inv hW hA)
  | fold _ _ _ _ _ =>
      intro hV
      exact absurd (cl_mu_eq _ _ _) (hV.2.2 _)
#print axioms atomL_of_atOff

/-- **Positive-width atoms sit at distinct offsets.** -/
theorem atomL_off_inj {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    ∀ {w : Nat}, wc T = some w → ∀ {k1 k2 o : Nat} {U1 U2 : Ty} {w1 w2 : Nat},
      As[k1]? = some (o, U1) → As[k2]? = some (o, U2) → wc U1 = some w1 → wc U2 = some w2 → 0 < w1 → 0 < w2 →
      k1 = k2 := by
  induction hA with
  | @atom t _ =>
      intro w _ k1 k2 o U1 U2 w1 w2 h1 h2 _ _ _ _
      cases k1 with
      | succ k => simp at h1
      | zero =>
        cases k2 with
        | succ k => simp at h2
        | zero => rfl
  | @prod a b A B us ha hA0 hB0 iha ihb =>
      intro w hw k1 k2 o U1 U2 w1 w2 h1 h2 hw1 hw2 hp1 hp2
      obtain ⟨ub, hb, hlen⟩ := wc_prod_split ha hw
      have hwa : wc a = some (nWords us) := by simp [wc, ha]
      have hwb : wc b = some (nWords ub) := by simp [wc, hb]
      rcases getElem?_atoms h1 with ⟨hk1, hA1⟩ | ⟨hk1, ⟨o1, V1⟩, hq1, he1⟩ <;>
        rcases getElem?_atoms h2 with ⟨hk2, hA2⟩ | ⟨hk2, ⟨o2, V2⟩, hq2, he2⟩
      · exact iha hwa hA1 hA2 hw1 hw2 hp1 hp2
      · simp only [Prod.mk.injEq] at he2
        obtain ⟨rfl, rfl⟩ := he2
        obtain ⟨n, hn, hon⟩ := AtomL_bound hA0 hwa k1 _ U1 hA1
        rw [hw1] at hn; cases hn; omega
      · simp only [Prod.mk.injEq] at he1
        obtain ⟨rfl, rfl⟩ := he1
        obtain ⟨n, hn, hon⟩ := AtomL_bound hA0 hwa k2 _ U2 hA2
        rw [hw2] at hn; cases hn; omega
      · simp only [Prod.mk.injEq] at he1 he2
        obtain ⟨e1, rfl⟩ := he1
        obtain ⟨e2, rfl⟩ := he2
        have e : o1 = o2 := by omega
        subst e
        have := ihb hwb hq1 hq2 hw1 hw2 hp1 hp2
        omega
  | @mu ρ W s L hW hg _ ih =>
      intro w hw
      exact ih (by rw [wc_mu_unfold hg]; exact hw)
#print axioms atomL_off_inj

/-- The atoms of a `wrapTop` type are `wrapTop`. -/
theorem atomL_wrapTop {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    wrapTop T = true → ∀ (k o : Nat) (U : Ty), As[k]? = some (o, U) → wrapTop U = true := by
  induction hA with
  | @atom t _ =>
      intro hw k o U hk
      cases k with
      | succ k => simp at hk
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨-, rfl⟩ := hk
        exact hw
  | @prod a b A B us ha _ _ iha ihb =>
      intro hw k o U hk
      simp only [wrapTop, wrapTopE, Bool.and_eq_true] at hw
      rcases getElem?_atoms hk with ⟨-, hkA⟩ | ⟨-, ⟨o', U'⟩, hq, he⟩
      · exact iha hw.1 k o U hkA
      · simp only [Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he
        exact ihb hw.2 _ o' U hq
  | @mu ρ W s L hW hg _ ih =>
      intro hw
      exact ih (wrapTop_unfold hW hw)
#print axioms atomL_wrapTop

/-- **The zero-width atoms are `ZwL`'s**, in order. -/
theorem atomL_zwL {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    ∀ {Us : List Ty}, ZwL T Us → Us = (As.filter fun p => decide (wc p.2 = some 0)).map Prod.snd := by
  induction hA with
  | @atom t ht =>
      intro Us hZ
      cases hZ with
      | zero _ h0 => simp [h0]
      | pos _ hp => simp [hp]
      | prod _ _ => exact absurd rfl (ht.1 _ _)
      | mu _ => exact absurd rfl (ht.2 _)
  | @prod a b A B us ha _ _ iha ihb =>
      intro Us hZ
      generalize hT : Ty.prod a b = T at hZ
      cases hZ with
      | zero ht _ => exact absurd hT.symm (ht.1 a b)
      | pos ht _ => exact absurd hT.symm (ht.1 a b)
      | mu _ => cases hT
      | prod hZa hZb =>
          cases hT
          rw [iha hZa, ihb hZb, List.filter_append, List.map_append, List.filter_map, List.map_map]
          rfl
  | @mu ρ W s L hW hg _ ih =>
      intro Us hZ
      generalize hT : cl ρ W 0 0 (.mu s) = T at hZ
      cases hZ with
      | zero ht _ => exact absurd (hT ▸ ht) not_atomT_mu
      | pos ht _ => exact absurd (hT ▸ ht) not_atomT_mu
      | prod _ _ => rw [cl_mu_eq] at hT; cases hT
      | @mu t L' hZ' =>
          apply ih
          rw [cl_unfold1 hW, hT]
          exact hZ'
#print axioms atomL_zwL

/-! ## Zero-width parts and list helpers -/


/-- The zero-width part of a value of `T` (`ZwZ`'s form): its zero-width atoms' values at some
environment whose boxes `η` keeps. -/
def ZwAt (η : TEnv) (T : Ty) (Zz : Res) : Prop :=
  ∃ (Us : List Ty) (Rz : List Res) (E0 : TEnv), ZwL T Us ∧ Rz.length = Us.length ∧ Zz = Res.sum Rz ∧
    (∀ l B, E0.box l = some B → η.box l = some B) ∧
    ∀ (i : Nat) (U : Ty) (Ri : Res), Us[i]? = some U → Rz[i]? = some Ri → VRR (fun _ => 0) (CE E0.unsee) U (shp U) [] Ri

theorem sum_filter_split {α : Type} (p : α → Bool) (f : α → Nat) : ∀ (L : List α),
    (L.map f).sum = ((L.filter p).map f).sum + ((L.filter fun x => !p x).map f).sum
  | [] => rfl
  | x :: L => by
    have ih := sum_filter_split p f L
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by simp [hp])]
      simp only [List.map_cons, List.sum_cons]
      omega
    · rw [List.filter_cons_of_neg hp, List.filter_cons_of_pos (by simp [hp])]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- A nodup list whose elements all equal `x` has at most one element. -/
theorem nodup_const {α : Type} {x : α} : ∀ {L : List α}, L.Nodup → (∀ y ∈ L, y = x) → L = [] ∨ L = [x]
  | [], _, _ => Or.inl rfl
  | [y], _, h => Or.inr (by rw [h y (List.mem_singleton_self _)])
  | y :: z :: L, hn, h => by
    have e1 := h y (List.mem_cons_self ..)
    have e2 := h z (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [List.nodup_cons] at hn
    exact (hn.1 (by rw [e1, ← e2]; exact List.mem_cons_self ..)).elim

/-- Inversion of `ZwL` at a pair. -/
theorem zwL_prod_inv {a b : Ty} {Us : List Ty} (h : ZwL (.prod a b) Us) :
    ∃ Ua Ub, ZwL a Ua ∧ ZwL b Ub ∧ Us = Ua ++ Ub := by
  generalize hT : Ty.prod a b = T at h
  cases h with
  | zero ht _ => exact absurd hT.symm (ht.1 a b)
  | pos ht _ => exact absurd hT.symm (ht.1 a b)
  | mu _ => cases hT
  | prod hZa hZb => cases hT; exact ⟨_, _, hZa, hZb, rfl⟩

/-- Inversion of `ZwL` at a closed `μ` type. -/
theorem zwL_mu_inv {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} (hW : ∀ k, Clo (W k)) {Us : List Ty}
    (h : ZwL (cl ρ W 0 0 (.mu s)) Us) : ZwL (cl ρ W 0 0 (unfold1 (.mu s))) Us := by
  generalize hT : cl ρ W 0 0 (.mu s) = T at h
  cases h with
  | zero ht _ => exact absurd (hT ▸ ht) not_atomT_mu
  | pos ht _ => exact absurd (hT ▸ ht) not_atomT_mu
  | prod _ _ => rw [cl_mu_eq] at hT; cases hT
  | mu hZ' => rw [cl_unfold1 hW, hT]; exact hZ'

/-- A one-element list from a one-element map. -/
theorem single_of_map {α β : Type} {f : α → β} {L : List α} {y : β} (h : L.map f = [y]) : ∃ x, L = [x] := by
  cases L with
  | nil => simp at h
  | cons x L' =>
    cases L' with
    | nil => exact ⟨x, rfl⟩
    | cons _ _ => simp at h

/-- Indicator sum over keys avoiding the point is zero. -/
theorem sum_ite_zero {β : Type} [DecidableEq β] {x : β} (c : Nat) : ∀ {K : List β}, x ∉ K →
    (K.map fun b => if x = b then c else 0).sum = 0
  | [], _ => rfl
  | b :: K, h => by
    simp only [List.map_cons, List.sum_cons]
    have hb : ¬ x = b := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [hb, ↓reduceIte, Nat.zero_add]
    exact sum_ite_zero c fun m => h (List.mem_cons_of_mem _ m)


/-! ## A value's resources over its atoms -/

/-- `g = (o, U, Rg)`: a positive-width solid component `U` of a value of `T` with words `ws`, at
offset `o`, and `Rg` is at most what its words hold there. -/
def ItemAt (η : TEnv) (T : Ty) (ws : List Word) (g : Nat × Ty × Res) : Prop :=
  AtOff T g.1 g.2.1 ∧ Solid g.2.1 ∧ ∃ w, wc g.2.1 = some w ∧ 0 < w ∧
    ∀ Ru, VRR (fun _ => 0) (CE η) g.2.1 (shp g.2.1) ((ws.drop g.1).take w) Ru → g.2.2 ≤ Ru

/-- **A value's resources cover its parts** (`AtomL` induction): items at distinct offsets, each at most
its component's holding, plus the zero-width part, are at most the value's resources. -/
theorem value_sumR (η : TEnv) {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    wrapTop T = true → ∀ {ws : List Word} {R : Res}, wc T = some ws.length →
      VRR (fun _ => 0) (CE η) T (shp T) ws R →
      ∀ (G : List (Nat × Ty × Res)), (G.map Prod.fst).Nodup → (∀ g ∈ G, ItemAt η T ws g) →
      ∀ (Zl : List Res), Zl.length ≤ 1 → (∀ z ∈ Zl, ZwAt η T z) →
      ∀ k, (G.map fun g => g.2.2 k).sum + (Zl.map fun z => z k).sum ≤ R k := by
  induction hA with
  | @atom t ht =>
      intro hw ws R hwc hv G hG hGg Zl hZl hZz k
      have hsol : Solid t := ⟨ht.1, fun i e h => by subst h; simp [wc, accs] at hwc, ht.2⟩
      have hG0 : ∀ g ∈ G, g.1 = 0 ∧ g.2.1 = t := by
        intro g hg
        obtain ⟨h1, h2, -⟩ := hGg g hg
        exact AtOff_solid hsol (fun s h => h2.2.2 s h) h1
      have hZ : ∀ z ∈ Zl, z = (if wc t = some 0 then R else .zero) := by
        intro z hz
        obtain ⟨Us, Rz, E0, hZw, hl, rfl, hb, hvz⟩ := hZz z hz
        cases hZw with
        | prod _ _ => exact absurd rfl (ht.1 _ _)
        | mu _ => exact absurd rfl (ht.2 _)
        | pos _ hp =>
            match Rz, hl with
            | [], _ => simp [hp, Res.sum]
        | zero _ h0 =>
            match Rz, hl with
            | [Ri], _ =>
              rw [h0] at hwc
              have hws : ws = [] := List.eq_nil_of_length_eq_zero (Option.some.inj hwc).symm
              subst hws
              simp only [h0, ↓reduceIte, Res.sum_cons, Res.sum_nil, Res.add_zero]
              exact vrr_detW t [] _ (CE E0.unsee) (CE η) _ _ Ri R hw (RZ_CE _) (RZ_CE _) hb (hvz 0 t Ri rfl rfl) hv
      by_cases h0 : wc t = some 0
      · have e2 : G = [] := List.eq_nil_iff_forall_not_mem.2 fun g hg => by
          obtain ⟨-, -, w, hw1, hw2, -⟩ := hGg g hg
          rw [(hG0 g hg).2, h0] at hw1; cases hw1; omega
        subst e2
        simp only [List.map_nil, List.sum_nil, Nat.zero_add]
        match Zl, hZl with
        | [], _ => exact Nat.zero_le _
        | [z], _ =>
          rw [hZ z (List.mem_singleton_self _)]
          simp [h0]
      · have eZ : (Zl.map fun z => z k).sum = 0 := by
          match Zl, hZl with
          | [], _ => rfl
          | [z], _ =>
            rw [hZ z (List.mem_singleton_self _)]
            simp [h0, Res.zero]
        rw [eZ, Nat.add_zero]
        rcases nodup_const hG (fun x hx => by
            obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
            exact (hG0 g hg).1) with e2 | e2
        · rw [List.map_eq_nil_iff.1 e2]; simp
        · obtain ⟨g, hg⟩ := single_of_map e2
          subst hg
          obtain ⟨-, -, w, hw1, -, hle⟩ := hGg g (List.mem_singleton_self _)
          have ht' := (hG0 g (List.mem_singleton_self _)).2
          have hg1 := (hG0 g (List.mem_singleton_self _)).1
          rw [ht', hwc] at hw1
          obtain rfl := Option.some.inj hw1
          have hle' := hle R (by rw [ht', hg1]; simpa using hv)
          simpa using hle' k
  | @prod a b A B us ha hA0 hB0 iha ihb =>
      intro hw ws R hwc hv G hG hGg Zl hZl hZz k
      simp only [wrapTop, wrapTopE, Bool.and_eq_true] at hw
      obtain ⟨ub, hb, hlen⟩ := wc_prod_split ha hwc
      have hwa : wc a = some (nWords us) := by simp [wc, ha]
      have hwb : wc b = some (nWords ub) := by simp [wc, hb]
      simp only [VRR] at hv
      obtain ⟨ra, rb, e, Ra, Rb, hR, -, hsplit⟩ := hv
      simp only [shp, Shp.prod.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨-, hva, hvb⟩ := hsplit _ (by rw [shp_wc]; exact hwa)
      have hla : (ws.take (nWords us)).length = nWords us := by simp; omega
      have hlb : (ws.drop (nWords us)).length = nWords ub := by simp; omega
      subst hR
      simp only [Res.add_apply]
      let GA := G.filter fun g => decide (g.1 < nWords us)
      let GB := (G.filter fun g => !decide (g.1 < nWords us)).map fun g => (g.1 - nWords us, g.2)
      have hGA : ∀ g ∈ GA, ItemAt η a (ws.take (nWords us)) g := by
        intro g hg
        obtain ⟨hm, hlt⟩ := List.mem_filter.1 hg
        simp only [decide_eq_true_eq] at hlt
        obtain ⟨h1, h2, w, hw1, hw2, hle⟩ := hGg g hm
        rcases AtOff_prod_inv (fun t e => h2.2.2 t e) h1 with ⟨-, e⟩ | h1a | ⟨as, o2, has, he, -⟩
        · exact absurd e (h2.1 a b)
        · obtain ⟨uU, huU⟩ : ∃ uU, accs g.2.1 = some uU := by
            cases hu : accs g.2.1 with
            | none => simp [wc, hu] at hw1
            | some uU => exact ⟨uU, rfl⟩
          have hbd := AtOff_bound h1a ha huU
          have hwU : wc g.2.1 = some (nWords uU) := by simp [wc, huU]
          rw [hw1] at hwU; obtain rfl := Option.some.inj hwU
          refine ⟨h1a, h2, nWords uU, hw1, hw2, fun Ru hRu => hle Ru ?_⟩
          rw [take_drop_take (by omega)] at hRu; exact hRu
        · rw [ha] at has; cases has; omega
      have hGB : ∀ g ∈ GB, ItemAt η b (ws.drop (nWords us)) g := by
        intro g'' hg''
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg''
        obtain ⟨hm, hge⟩ := List.mem_filter.1 hg
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hge
        obtain ⟨h1, h2, w, hw1, hw2, hle⟩ := hGg g hm
        rcases AtOff_prod_inv (fun t e => h2.2.2 t e) h1 with ⟨-, e⟩ | h1a | ⟨as, o2, has, he, h1b⟩
        · exact absurd e (h2.1 a b)
        · obtain ⟨uU, huU⟩ : ∃ uU, accs g.2.1 = some uU := by
            cases hu : accs g.2.1 with
            | none => simp [wc, hu] at hw1
            | some uU => exact ⟨uU, rfl⟩
          have hbd := AtOff_bound h1a ha huU
          have hwU : wc g.2.1 = some (nWords uU) := by simp [wc, huU]
          rw [hw1] at hwU; obtain rfl := Option.some.inj hwU
          omega
        · rw [ha] at has; cases has
          have e2 : g.1 - nWords us = o2 := by omega
          refine ⟨by rw [e2]; exact h1b, h2, w, hw1, hw2, fun Ru hRu => hle Ru ?_⟩
          have hRu' : VRR (fun _ => 0) (CE η) g.2.1 (shp g.2.1)
              (((ws.drop (nWords us)).drop (g.1 - nWords us)).take w) Ru := hRu
          rw [List.drop_drop, show nWords us + (g.1 - nWords us) = g.1 by omega] at hRu'
          exact hRu'
      have hGndA : (GA.map Prod.fst).Nodup := List.Nodup.sublist ((List.filter_sublist (l := G)).map Prod.fst) hG
      have eGB : GB.map Prod.fst =
          ((G.filter fun g => !decide (g.1 < nWords us)).map Prod.fst).map (· - nWords us) := by
        simp only [GB, List.map_map]; rfl
      have hGndB : (GB.map Prod.fst).Nodup := by
        rw [eGB]
        refine TermWdCover.nodup_map_on _ (fun x hx y hy hxy => ?_)
          (List.Nodup.sublist ((List.filter_sublist (l := G)).map Prod.fst) hG)
        obtain ⟨gx, hgx, rfl⟩ := List.mem_map.1 hx
        obtain ⟨gy, hgy, rfl⟩ := List.mem_map.1 hy
        have h1 := (List.mem_filter.1 hgx).2
        have h2 := (List.mem_filter.1 hgy).2
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at h1 h2
        omega
      have hGs : (G.map fun g => g.2.2 k).sum =
          (GA.map fun g => g.2.2 k).sum + (GB.map fun g => g.2.2 k).sum := by
        rw [sum_filter_split (fun g => decide (g.1 < nWords us)) (fun g => g.2.2 k) G]
        simp only [GA, GB, List.map_map]; rfl
      obtain ⟨ZlA, ZlB, hZA, hZB, hlA, hlB, hZs⟩ : ∃ ZlA ZlB : List Res, (∀ z ∈ ZlA, ZwAt η a z) ∧
          (∀ z ∈ ZlB, ZwAt η b z) ∧ ZlA.length ≤ 1 ∧ ZlB.length ≤ 1 ∧
          (Zl.map fun z => z k).sum = (ZlA.map fun z => z k).sum + (ZlB.map fun z => z k).sum := by
        match Zl, hZl with
        | [], _ => exact ⟨[], [], by simp, by simp, by simp, by simp, rfl⟩
        | [z], _ =>
          obtain ⟨Us, Rz, E0, hZw, hl, rfl, hb0, hvz⟩ := hZz z (List.mem_singleton_self _)
          obtain ⟨Ua, Ub, hZa, hZb, rfl⟩ := zwL_prod_inv hZw
          simp only [List.length_append] at hl
          refine ⟨[Res.sum (Rz.take Ua.length)], [Res.sum (Rz.drop Ua.length)], ?_, ?_, by simp, by simp, ?_⟩
          · intro z hz; rw [List.mem_singleton] at hz; subst hz
            refine ⟨Ua, Rz.take Ua.length, E0, hZa, by simp; omega, rfl, hb0, fun i U Ri hU hR => ?_⟩
            have hi : i < Ua.length := by
              rcases Nat.lt_or_ge i Ua.length with h1 | h1
              · exact h1
              · rw [List.getElem?_eq_none h1] at hU; cases hU
            exact hvz i U Ri (by rw [List.getElem?_append_left hi]; exact hU)
              (by rw [List.getElem?_take_of_lt hi] at hR; exact hR)
          · intro z hz; rw [List.mem_singleton] at hz; subst hz
            refine ⟨Ub, Rz.drop Ua.length, E0, hZb, by simp; omega, rfl, hb0, fun i U Ri hU hR => ?_⟩
            exact hvz (Ua.length + i) U Ri (by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hU)
              (by rw [List.getElem?_drop] at hR; exact hR)
          · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
            rw [← Res.add_apply, ← Res.sum_append, List.take_append_drop]
      have x1 := iha hw.1 (by rw [hla]; exact hwa) hva GA hGndA hGA ZlA hlA hZA k
      have x2 := ihb hw.2 (by rw [hlb]; exact hwb) hvb GB hGndB hGB ZlB hlB hZB k
      omega
  | @mu ρ W s L hW hg _ ih =>
      intro hw ws R hwc hv G hG hGg Zl hZl hZz k
      have hv' := (VRR_cl_unfold η hW hg).2 hv
      rw [← shp_mu_unfold hg] at hv'
      refine ih (wrapTop_unfold hW hw) (by rw [wc_mu_unfold hg]; exact hwc) hv' G hG
        (fun g hg' => ?_) Zl hZl (fun z hz => ?_) k
      · obtain ⟨h1, h2, rest⟩ := hGg g hg'
        rcases AtOff_mu_inv hW hg h1 with ⟨-, e⟩ | h1'
        · exact absurd (e.trans (cl_mu_eq ρ W s)) (h2.2.2 _)
        · exact ⟨h1', h2, rest⟩
      · obtain ⟨Us, Rz, E0, hZw, rest⟩ := hZz z hz
        exact ⟨Us, Rz, E0, zwL_mu_inv hW hZw, rest⟩
#print axioms value_sumR

/-! ## The slot's first-write debits -/

/-- Pointwise `WLe1` at equal lengths is `WLe`. -/
theorem WLe_of_getElem : ∀ {L L' : List Word}, L.length = L'.length →
    (∀ (i : Nat) (a b : Word), L[i]? = some a → L'[i]? = some b → WLe1 a b) → WLe L L'
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: L, b :: L', h, hp => by
    simp only [WLe]
    exact ⟨hp 0 a b rfl rfl, WLe_of_getElem (by simpa using h) (fun i x y hx hy => hp (i + 1) x y hx hy)⟩

/-- Slot coordinates are unique. -/
theorem slot_eq {W j j' o o2 : Nat} (h : j * W + o = j' * W + o2) (ho : o < W) (ho2 : o2 < W) :
    j = j' ∧ o = o2 := by
  have e1 := TermWdCover.div_slot (j := j) ho
  have e2 := TermWdCover.div_slot (j := j') ho2
  rw [h] at e1
  rw [e1] at e2
  subst e2
  exact ⟨rfl, by omega⟩

/-- A positive-width component at a slot offset of a buffer is a component of the element. -/
theorem atoff_slot {N : Nat} {e V : Ty} {us vs : List Acc} {j o : Nat} (hus : accs e = some us)
    (hV : ∀ t, V ≠ .mu t) (hVa : ∀ i e', V ≠ .array i e') (hvs : accs V = some vs) (hpos : 0 < nWords vs)
    (ho : o < nWords us) (h : AtOff (.array (.lit N) e) (j * nWords us + o) V) : AtOff e o V := by
  rcases AtOff_array_inv hV h with ⟨-, e1⟩ | ⟨n', j', o2, us', -, hus', -, he, hat⟩
  · exact absurd e1 (hVa _ _)
  · rw [hus] at hus'; cases hus'
    have hb := AtOff_bound hat hus hvs
    obtain ⟨-, rfl⟩ := slot_eq he ho (by omega)
    exact hat

/-- A non-ghost word and a block atom never share an offset. -/
theorem word_blk_excl {e U : Ty} {As : List (Nat × Ty)} {us : List Acc} {o w n : Nat} {P : Proto}
    (hA : AtomL e As) (hus : accs e = some us) (hw1 : AtOff e o (.word (.lit n) P)) (hg : P.ghost = false)
    (hU : AtOff e o U) (hsU : Solid U) (hwU : wc U = some w) (hpos : 0 < w)
    (hgU : ∀ r P, U = .word r P → P.ghost = true) : False := by
  have hne : accs e ≠ none := by rw [hus]; simp
  obtain ⟨k1, hk1⟩ := atomL_of_atOff hw1 (Solid_word _ _) hne hA
  obtain ⟨k2, hk2⟩ := atomL_of_atOff hU hsU hne hA
  have e := atomL_off_inj hA (w := nWords us) (by simp [wc, hus]) hk1 hk2 (wc_word hg) hwU Nat.one_pos hpos
  subst e
  rw [hk1] at hk2
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hk2
  have h := hgU _ _ hk2.symm
  rw [hg] at h; cases h

/-- **One unit of the slot**: the debit of the unit's first write is at most an item (its word leaf or
its block atom) plus, at the slot start, the zero-width part. -/
theorem unit_item {E : TEnv} {mem : Memory} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc}
    {As : List (Nat × Ty)} {j : Nat} {F : List Ts} {ws : List Word} {db : Ts → Res}
    (hsto : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hus : accs e = some us)
    (hA : AtomL e As) (hwt : wrapTop e = true) (hF : F.length = nWords us) (hws : ws.length = nWords us)
    (hFo : ∀ o t, F[o]? = some t → ∃ m x, mem[t]? = some m ∧ ws[o]? = some x ∧
      m.loc = ⟨l, j * nWords us + o⟩ ∧ m.val = x.val ∧ WLe1 x (mw m) ∧ FirstW mem m.loc t ∧
      DbRes E mem m t (db t))
    {o : Nat} (ho : o < nWords us) :
    ∃ (Gi : List (Nat × Ty × Res)) (Zi : List Res), Gi.length ≤ 1 ∧ (∀ g ∈ Gi, g.1 = o ∧ ItemAt E.unsee e ws g) ∧
      Zi.length ≤ 1 ∧ (o ≠ 0 → Zi = []) ∧ (∀ z ∈ Zi, ZwAt E.unsee e z) ∧
      ∀ k, ((F.map db)[o]?.getD .zero) k ≤ (Gi.map fun g => g.2.2 k).sum + (Zi.map fun z => z k).sum := by
  have hne : accs e ≠ none := by rw [hus]; simp
  rw [List.getElem?_map]
  cases hFo' : F[o]? with
  | none => exact ⟨[], [], by simp, by simp, by simp, fun _ => rfl, by simp, fun k => by simp [Res.zero]⟩
  | some t =>
    obtain ⟨m, x, hm, hx, hloc, hval, hwl, hfw, hdb⟩ := hFo o t hFo'
    have hlab : m.loc.label = l := by rw [hloc]
    have hoff : m.loc.offset = j * nWords us + o := by rw [hloc]
    -- the zero-width part
    have hZI : ∀ Zz, ZwZ E m.loc Zz → ∃ Zi : List Res, Zi.length ≤ 1 ∧ (o ≠ 0 → Zi = []) ∧
        (∀ z ∈ Zi, ZwAt E.unsee e z) ∧ ∀ k, Zz k ≤ (Zi.map fun z => z k).sum := by
      intro Zz hZ
      rcases hZ with ⟨hss, c', N', e', us', Us, Rz, E0, hc', hT', hus', hZw, hl, hZe, hb, hvz⟩ | ⟨-, hz0⟩
      · have hc2 : E.sto l = some c' := by rw [← hlab]; exact hc'
        rw [hsto] at hc2; cases hc2
        rw [hT] at hT'; cases hT'
        refine ⟨[Zz], by simp, fun hne0 => ?_, ?_, fun k => by simp⟩
        · exfalso; apply hne0
          obtain ⟨cl, N2, e2, us2, hc3, hT2, hus2, -, -, hmod⟩ := hss
          have hc4 : E.sto l = some cl := by rw [← hlab]; exact hc3
          rw [hsto] at hc4; cases hc4
          rw [hT] at hT2; cases hT2
          rw [hus] at hus2; cases hus2
          rw [hoff, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho] at hmod
          exact hmod
        · intro z hz; rw [List.mem_singleton] at hz; subst hz
          exact ⟨Us, Rz, E0, hZw, hl, hZe, hb, hvz⟩
      · exact ⟨[], by simp, fun _ => rfl, by simp, fun k => by simp [hz0]⟩
    -- the word leaf
    have hWI : ∀ n P, WordAt E m.loc n P → AtOff e o (.word (.lit n) P) ∧ P.ghost = false ∧
        ItemAt E.unsee e ws (o, .word (.lit n) P, wr P n (mw m).val + wdW P n) := by
      intro n P ⟨c', hc', hat, hg⟩
      have hc2 : E.sto l = some c' := by rw [← hlab]; exact hc'
      rw [hsto] at hc2; cases hc2
      rw [hT, hoff] at hat
      have hat2 : AtOff e o (.word (.lit n) P) :=
        atoff_slot hus (fun _ h => by cases h) (fun _ _ h => by cases h) (accs_word hg)
          (by rw [TermWdCover.nWords_one]; exact Nat.one_pos) ho hat
      refine ⟨hat2, hg, hat2, Solid_word _ _, 1, wc_word hg, Nat.one_pos, fun Ru hRu => ?_⟩
      have hsl : (ws.drop o).take 1 = [x] := by
        apply List.ext_getElem?; intro i
        rw [List.getElem?_take, List.getElem?_drop]
        rcases i with _ | i
        · simp [hx]
        · simp
      rw [hsl] at hRu
      rw [VRR_word_wr hRu]
      show wr P n m.val + wdW P n ≤ wr P n x.val + wdW P n
      rw [hval]; exact Res.le_refl _
    -- the block atom
    have hBI : ∀ Zb, BlkZ E mem m.loc Zb → (∃ U, AtOff e o U ∧ Solid U ∧ (∃ w, wc U = some w ∧ 0 < w) ∧
        (∀ r P, U = .word r P → P.ghost = true) ∧ ItemAt E.unsee e ws (o, U, Zb)) ∨ Zb = .zero := by
      intro Zb hB
      rcases hB with ⟨U, w, wsF, hbs, hwU, hlF, hFW, E0, hb0, hvF⟩ | ⟨-, hz0⟩
      · left
        obtain ⟨c', N', e', us', j', o', w', hc', hT', hus', -, -, hoff', hat', hAT, hwU', hpos, hgh⟩ := hbs
        have hc2 : E.sto l = some c' := by rw [← hlab]; exact hc'
        rw [hsto] at hc2; cases hc2
        rw [hT] at hT'; cases hT'
        rw [hus] at hus'; cases hus'
        rw [hwU] at hwU'; cases hwU'
        have hsol : Solid U := ⟨hAT.1, fun i e h => by subst h; simp [wc, accs] at hwU, hAT.2⟩
        obtain ⟨vsU, hvsU, hvw⟩ : ∃ vsU, accs U = some vsU ∧ nWords vsU = w := by
          cases h : accs U with
          | none => simp [wc, h] at hwU
          | some vsU => simp [wc, h] at hwU; exact ⟨vsU, rfl, hwU⟩
        have hb := AtOff_bound hat' hus hvsU
        rw [hoff] at hoff'
        obtain ⟨rfl, rfl⟩ := slot_eq hoff' ho (by omega)
        obtain ⟨kU, hkU⟩ := atomL_of_atOff hat' hsol hne hA
        have hwtU := atomL_wrapTop hA hwt kU o U hkU
        refine ⟨U, hat', hsol, ⟨w, hwU, hpos⟩, hgh, hat', hsol, w, hwU, hpos, fun Ru hRu => ?_⟩
        have hWL : WLe ((ws.drop o).take w) wsF := by
          refine WLe_of_getElem (by simp; omega) (fun i a b ha hb' => ?_)
          rw [List.getElem?_take, List.getElem?_drop] at ha
          by_cases hi : i < w
          · simp only [hi, ↓reduceIte] at ha
            obtain ⟨h0, m0, hfw0, hm0, rfl⟩ := hFW i b hb'
            obtain ⟨t', ht'⟩ : ∃ t', F[o + i]? = some t' :=
              ⟨_, List.getElem?_eq_getElem (by omega : o + i < F.length)⟩
            obtain ⟨m1, x1, hm1, hx1, hloc1, -, hwl1, hfw1, -⟩ := hFo (o + i) t' ht'
            rw [ha] at hx1; cases hx1
            have hl1 : m1.loc = ⟨m.loc.label, m.loc.offset + i⟩ := by
              rw [hloc1, hlab, hoff, Nat.add_assoc]
            rw [hl1] at hfw1
            have := FirstW_uniq hfw0 hfw1
            subst this
            rw [hm0] at hm1; cases hm1
            exact hwl1
          · simp only [hi, ↓reduceIte] at ha; cases ha
        have hvU := VRR_up U (shp U) _ wsF Ru hWL hRu
        have e := vrr_detW U [] (fun _ => 0) (CE E0.unsee) (CE E.unsee) (shp U) wsF Zb Ru hwtU (RZ_CE _) (RZ_CE _)
          hb0 hvF hvU
        rw [e]; exact Res.le_refl _
      · exact Or.inr hz0
    rcases hdb with ⟨-, -, hI, -⟩ | ⟨-, hz⟩
    rotate_left
    · exact ⟨[], [], by simp, by simp, by simp, fun _ => rfl, by simp, fun k => by simp [hz, Res.zero]⟩
    obtain ⟨R₁, Z, hfr, hdes, hndes, hR⟩ := hI (FirstW_initAt hfw)
    by_cases hD : DesigAt E mem m.loc t
    · obtain ⟨Zb, Zz, hBZ, hZZ, hZe⟩ := hdes hD
      obtain ⟨Zi, hZi1, hZi0, hZiA, hZik⟩ := hZI Zz hZZ
      have hZle : ∀ k, Z k ≤ Zb k + Zz k := fun k => by
        have := noOwnR_le (Zb + Zz) k
        rw [hZe]; simpa only [Res.add_apply] using this
      rcases hfr with ⟨n, P, hWA, hR1⟩ | ⟨-, hR1⟩
      · obtain ⟨hatW, hg, hItem⟩ := hWI n P hWA
        have hZb0 : Zb = .zero := by
          rcases hBI Zb hBZ with ⟨U, hatU, hsU, ⟨w, hwU, hpos⟩, hgU, -⟩ | h
          · exact (word_blk_excl hA hus hatW hg hatU hsU hwU hpos hgU).elim
          · exact h
        refine ⟨[(o, .word (.lit n) P, R₁)], Zi, by simp, ?_, hZi1, hZi0, hZiA, fun k => ?_⟩
        · intro g hg'; rw [List.mem_singleton] at hg'; subst hg'
          refine ⟨rfl, ?_⟩
          rw [hR1]; exact hItem
        · have h1 := hZle k
          have h2 := hZik k
          rw [hZb0] at h1
          simp only [Option.map_some, Option.getD_some, hR, Res.add_apply, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Res.zero_apply] at h1 ⊢
          omega
      · rcases hBI Zb hBZ with ⟨U, -, -, -, -, hItem⟩ | hZb0
        · refine ⟨[(o, U, Zb)], Zi, by simp, ?_, hZi1, hZi0, hZiA, fun k => ?_⟩
          · intro g hg'; rw [List.mem_singleton] at hg'; subst hg'
            exact ⟨rfl, hItem⟩
          · have h1 := hZle k
            have h2 := hZik k
            simp only [Option.map_some, Option.getD_some, hR, hR1, Res.add_apply, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, Res.zero_apply] at h1 ⊢
            omega
        · refine ⟨[], Zi, by simp, by simp, hZi1, hZi0, hZiA, fun k => ?_⟩
          have h1 := hZle k
          have h2 := hZik k
          rw [hZb0] at h1
          simp only [Option.map_some, Option.getD_some, hR, hR1, Res.add_apply, List.map_nil,
            List.sum_nil, Res.zero_apply] at h1 ⊢
          omega
    · have hZ0 := hndes hD
      rcases hfr with ⟨n, P, hWA, hR1⟩ | ⟨-, hR1⟩
      · obtain ⟨-, -, hItem⟩ := hWI n P hWA
        refine ⟨[(o, .word (.lit n) P, R₁)], [], by simp, ?_, by simp, fun _ => rfl, by simp, fun k => ?_⟩
        · intro g hg'; rw [List.mem_singleton] at hg'; subst hg'
          refine ⟨rfl, ?_⟩
          rw [hR1]; exact hItem
        · simp only [Option.map_some, Option.getD_some, hR, hZ0, Res.add_apply, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Res.zero_apply]
          omega
      · refine ⟨[], [], by simp, by simp, by simp, fun _ => rfl, by simp, fun k => ?_⟩
        simp [hR, hZ0, hR1, Res.zero]

/-- The items of a list of the slot's units. -/
theorem items_of {E : TEnv} {mem : Memory} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc}
    {As : List (Nat × Ty)} {j : Nat} {F : List Ts} {ws : List Word} {db : Ts → Res}
    (hsto : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hus : accs e = some us)
    (hA : AtomL e As) (hwt : wrapTop e = true) (hF : F.length = nWords us) (hws : ws.length = nWords us)
    (hFo : ∀ o t, F[o]? = some t → ∃ m x, mem[t]? = some m ∧ ws[o]? = some x ∧
      m.loc = ⟨l, j * nWords us + o⟩ ∧ m.val = x.val ∧ WLe1 x (mw m) ∧ FirstW mem m.loc t ∧
      DbRes E mem m t (db t)) :
    ∀ (os : List Nat), os.Nodup → (∀ o ∈ os, o < nWords us) →
    ∃ (G : List (Nat × Ty × Res)) (Zl : List Res), (G.map Prod.fst).Nodup ∧
      (∀ g ∈ G, g.1 ∈ os ∧ ItemAt E.unsee e ws g) ∧ Zl.length ≤ 1 ∧ (0 ∉ os → Zl = []) ∧
      (∀ z ∈ Zl, ZwAt E.unsee e z) ∧
      ∀ k, (os.map fun o => ((F.map db)[o]?.getD .zero) k).sum ≤
        (G.map fun g => g.2.2 k).sum + (Zl.map fun z => z k).sum
  | [], _, _ => ⟨[], [], List.nodup_nil, by simp, by simp, fun _ => rfl, by simp, fun k => by simp⟩
  | o :: os, hnd, hlt => by
    rw [List.nodup_cons] at hnd
    obtain ⟨G, Zl, hGn, hG, hZl1, hZl0, hZl, hle⟩ :=
      items_of hsto hT hus hA hwt hF hws hFo os hnd.2 (fun o' h => hlt o' (List.mem_cons_of_mem _ h))
    obtain ⟨Gi, Zi, hGi1, hGi, hZi1, hZi0, hZi, hlei⟩ :=
      unit_item hsto hT hus hA hwt hF hws hFo (hlt o (List.mem_cons_self ..))
    refine ⟨Gi ++ G, Zi ++ Zl, ?_, ?_, ?_, ?_, ?_, fun k => ?_⟩
    · match Gi, hGi1 with
      | [], _ => simpa using hGn
      | [g], _ =>
        simp only [List.cons_append, List.nil_append, List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, hGn⟩
        obtain ⟨g', hg', he⟩ := List.mem_map.1 hm
        have h1 := (hGi g (List.mem_singleton_self _)).1
        have h2 := (hG g' hg').1
        rw [he, h1] at h2
        exact hnd.1 h2
    · intro g hg
      rcases List.mem_append.1 hg with h | h
      · obtain ⟨e1, h2⟩ := hGi g h
        exact ⟨by rw [e1]; exact List.mem_cons_self .., h2⟩
      · obtain ⟨e1, h2⟩ := hG g h
        exact ⟨List.mem_cons_of_mem _ e1, h2⟩
    · by_cases ho : o = 0
      · subst ho
        rw [hZl0 hnd.1, List.append_nil]; exact hZi1
      · rw [hZi0 ho, List.nil_append]; exact hZl1
    · intro h0
      have ho : o ≠ 0 := fun e => h0 (by rw [e]; exact List.mem_cons_self ..)
      rw [hZi0 ho, hZl0 (fun h => h0 (List.mem_cons_of_mem _ h))]; rfl
    · intro z hz
      rcases List.mem_append.1 hz with h | h
      · exact hZi z h
      · exact hZl z h
    · have h1 := hle k
      have h2 := hlei k
      simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
      omega

/-- **(P8 L1) The slot's first-write debits are paid by the written value**: at slot `j` of a buffer
cell, if each unit `o` has a first-write promise `F[o]` whose message carries the written word's value
(`WLe1` above it), the debits of `F` sum to at most the written value's resources. -/
theorem dbF_le_val {E : TEnv} {mem : Memory} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc}
    {As : List (Nat × Ty)} {j : Nat} {F : List Ts} {ws : List Word} {Rv : Res} {db : Ts → Res}
    (hsto : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hus : accs e = some us)
    (hA : AtomL e As) (hwt : wrapTop e = true) (hF : F.length = nWords us) (hws : ws.length = nWords us)
    (hv : ValOfR E e ws Rv)
    (hFo : ∀ o t, F[o]? = some t → ∃ m x, mem[t]? = some m ∧ ws[o]? = some x ∧
      m.loc = ⟨l, j * nWords us + o⟩ ∧ m.val = x.val ∧ WLe1 x (mw m) ∧ FirstW mem m.loc t ∧
      DbRes E mem m t (db t)) :
    Res.sum (F.map db) ≤ Rv := by
  obtain ⟨G, Zl, hGn, hG, hZl1, -, hZl, hle⟩ := items_of hsto hT hus hA hwt hF hws hFo (List.range (nWords us))
    List.nodup_range (fun o h => List.mem_range.1 h)
  intro k
  have h1 := hle k
  have h2 := value_sumR E.unsee hA hwt (ws := ws) (R := Rv) (by simp [wc, hus, hws]) hv.1 G hGn
    (fun g hg => (hG g hg).2) Zl hZl1 hZl k
  rw [← TermWdCover.sum_range_getD k (F.map db), List.length_map, hF]
  omega
#print axioms dbF_le_val

end TermPinBI
