import WeakCore.TermDwf

/-!
# TermWdCover: the `wd n` debits are matched by memory

`TermDwf.storeCrZ_of` closes its non-epoch case by `KeyNet` at `wd n`: the
storer's frame and memory's unit both carry `wd n`.  The outstanding `wd n`
debits are the slack of that bound.  Each such debit is an init holder's
(`DbRes`, `FRes` branch) at a visible, initialised (`IniW`) word unit of region
`n`, and memory's held part counts that very unit (`wd_held`).  So memory
carries `wd n` once at the stored unit plus once per holder, which uses up
the slack.  This module proves the memory side: the unit count
(`held_count`) and the holder inversion (`db_wd_pos`).
-/

namespace TermWdCover

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermLiveHeld TermDwf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Leaves and single units -/

theorem leaf_word {E : TEnv} {ρ₀ : Nat → Nat} {n : Nat} {P : Proto} (hep : P.epoch = false) :
    ∀ q Rq, VRR ρ₀ (CE E) (.word (.lit n) P) (shp (.word (.lit n) P)) q Rq → 1 ≤ Rq (.wd n) := by
  intro q Rq h
  have h' := wdW_le_VRR_word h (.wd n)
  rw [wdW_nepoch hep] at h'
  simp only [Res.one, ite_true] at h'
  omega

theorem one_at (E : TEnv) {ρ₀ : Nat → Nat} {k : Key} {T V : Ty} {o : Nat} (h : AtOff T o V)
    {ws : List Word} {R : Res} (hv : VRR ρ₀ (CE E) T (shp T) ws R) (hwc : wc T = some ws.length)
    (hl : ∀ q Rq, VRR ρ₀ (CE E) V (shp V) q Rq → 1 ≤ Rq k) : 1 ≤ R k := by
  obtain ⟨n, Rq, Rr, -, -, hR, hvq, -⟩ := VRR_at E h hv hwc
  have := hl _ _ hvq
  subst hR
  simp only [Res.add_apply]
  omega

theorem le_sum_mem {α : Type} (f : α → Res) (k : Key) :
    ∀ {L : List α} {x : α}, x ∈ L → f x k ≤ Res.sum (L.map f) k
  | [], _, h => by cases h
  | y :: L, x, h => by
    simp only [List.map_cons, Res.sum_cons, Res.add_apply]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_mem f k h
      omega

/-- **Holder inversion** (current `DbRes`): a promise's debit at `wd n` is
nonzero only at an init holder of a visible, initialised, non-epoch word unit
of region `n`. -/
theorem db_wd_pos {E : TEnv} {mem : Memory} {m : Msg} {tw : Ts} {R : Res} {n : Nat}
    (h : DbRes E mem m tw R) (hp : 1 ≤ R (.wd n))
    (hZ : DesigAt E mem m.loc tw → ∀ Z, BlkDb E mem m.loc Z → Z (.wd n) = 0) :
    Vis E m.loc.label ∧ IniW E m.loc ∧ InitAt mem m.loc tw ∧ ∃ P, WordAt E m.loc n P ∧ P.epoch = false := by
  rcases h with ⟨hvis, hiw, hI, hnI⟩ | ⟨-, rfl⟩
  · by_cases hin : InitAt mem m.loc tw
    · obtain ⟨R₁, Z, hF, hD, hND, rfl⟩ := hI hin
      have hz : Z (.wd n) = 0 := by
        by_cases hd : DesigAt E mem m.loc tw
        · exact hZ hd Z (hD hd)
        · rw [hND hd]; rfl
      have hp' : 1 ≤ R₁ (.wd n) := by
        have := hp
        simp only [Res.add_apply, hz, Nat.add_zero] at this
        exact this
      replace hp := hp'
      rcases hF with ⟨n', P, hw, rfl⟩ | ⟨-, rfl⟩
      · have hr : wr P n' (mw m).val (.wd n) = 0 := by
          unfold wr
          split <;> simp [Res.one]
        cases hep : P.epoch
        · have hn : n' = n := by
            by_cases hne : n' = n
            · exact hne
            · exfalso
              have hk : Key.wd n ≠ Key.wd n' := fun h => hne (by cases h; rfl)
              simp [Res.add_apply, hr, wdW, hep, Res.one, hk] at hp
          subst hn
          exact ⟨hvis, hiw, hin, P, hw, hep⟩
        · simp [Res.add_apply, hr, wdW, hep] at hp
      · simp at hp
    · have := TermOnce.WRes_wd (hnI hin) n
      omega
  · simp at hp

/-! ## List helpers -/

theorem nodup_filter {α : Type} (p : α → Bool) : ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    rw [List.nodup_cons] at h
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.nodup_cons]
      exact ⟨fun hm => h.1 (List.mem_filter.1 hm).1, nodup_filter p h.2⟩
    · rw [List.filter_cons_of_neg hp]
      exact nodup_filter p h.2

theorem nodup_map_on {α β : Type} (f : α → β) : ∀ {l : List α},
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, hi, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on f (fun a ha b hb => hi a (List.mem_cons_of_mem _ ha) b
      (List.mem_cons_of_mem _ hb)) h.2⟩
    obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hm
    have e := hi y (List.mem_cons_of_mem _ hy) x (List.mem_cons_self ..) hxy
    subst e
    exact h.1 hy

theorem length_filter_split {α : Type} (p : α → Bool) : ∀ (l : List α),
    (l.filter p).length + (l.filter fun x => !p x).length = l.length
  | [] => rfl
  | x :: l => by
    have ih := length_filter_split p l
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by simp [hp])]
      simp only [List.length_cons]
      omega
    · rw [List.filter_cons_of_neg hp, List.filter_cons_of_pos (by simp [hp])]
      simp only [List.length_cons]
      omega

theorem sum_le_mem {β : Type} {f g : β → Nat} : ∀ {K : List β}, (∀ b ∈ K, f b ≤ g b) →
    (K.map f).sum ≤ (K.map g).sum
  | [], _ => Nat.le_refl _
  | b :: K, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h b (List.mem_cons_self ..)) (sum_le_mem fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem sum_map_add {β : Type} (f g : β → Nat) : ∀ (K : List β),
    (K.map fun b => f b + g b).sum = (K.map f).sum + (K.map g).sum
  | [] => rfl
  | b :: K => by
    simp only [List.map_cons, List.sum_cons, sum_map_add f g K]
    omega

theorem sum_map_zeroG {β : Type} : ∀ (K : List β), (K.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: K => by simp only [List.map_cons, List.sum_cons, sum_map_zeroG K]

theorem sum_map_congrG {β : Type} {f g : β → Nat} : ∀ (K : List β), (∀ b, f b = g b) →
    (K.map f).sum = (K.map g).sum
  | [], _ => rfl
  | b :: K, h => by simp only [List.map_cons, List.sum_cons, h b, sum_map_congrG K h]

theorem sum_indicator_zero {β : Type} [DecidableEq β] {x : β} : ∀ {K : List β}, x ∉ K →
    (K.map fun b => if x = b then 1 else 0).sum = 0
  | [], _ => rfl
  | b :: K, h => by
    have hb : x ≠ b := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, hb, ↓reduceIte]
    rw [sum_indicator_zero (fun hm => h (List.mem_cons_of_mem _ hm))]

theorem sum_indicator {β : Type} [DecidableEq β] {x : β} : ∀ {K : List β}, K.Nodup → x ∈ K →
    (K.map fun b => if x = b then 1 else 0).sum = 1
  | [], _, h => by cases h
  | b :: K, hK, h => by
    rw [List.nodup_cons] at hK
    simp only [List.map_cons, List.sum_cons]
    by_cases hb : x = b
    · subst hb
      simp only [↓reduceIte]
      rw [sum_indicator_zero hK.1]
    · simp only [hb, ↓reduceIte]
      rcases List.mem_cons.1 h with e | h
      · exact absurd e hb
      · rw [sum_indicator hK.2 h]

theorem count_split {α β : Type} [DecidableEq β] (κ : α → β) {K : List β} (hK : K.Nodup) :
    ∀ (U : List α), (∀ u ∈ U, κ u ∈ K) →
      U.length = (K.map fun b => (U.filter fun u => κ u = b).length).sum
  | [], _ => by
    simp only [List.filter_nil, List.length_nil]
    exact (sum_map_zeroG K).symm
  | u :: U, h => by
    have ih := count_split κ hK U fun v hv => h v (List.mem_cons_of_mem _ hv)
    have e : ∀ b, ((u :: U).filter fun v => κ v = b).length =
        (if κ u = b then 1 else 0) + (U.filter fun v => κ v = b).length := by
      intro b
      by_cases hb : κ u = b
      · simp only [List.filter_cons, hb, decide_true, ↓reduceIte, List.length_cons]
        omega
      · simp [hb]
    rw [sum_map_congrG K e, sum_map_add, sum_indicator hK (h u (List.mem_cons_self ..)), ← ih,
      List.length_cons]
    omega

theorem len_le_sum {α β : Type} [DecidableEq β] (κ : α → β) {K : List β} (hK : K.Nodup) {U : List α}
    (hU : ∀ u ∈ U, κ u ∈ K) {g : β → Nat} (hg : ∀ b ∈ K, (U.filter fun u => κ u = b).length ≤ g b) :
    U.length ≤ (K.map g).sum := by
  rw [count_split κ hK U hU]
  exact sum_le_mem hg

theorem res_sum_apply {α : Type} (f : α → Res) (k : Key) : ∀ (L : List α),
    Res.sum (L.map f) k = (L.map fun x => f x k).sum
  | [] => rfl
  | x :: L => by
    simp only [List.map_cons, Res.sum_cons, Res.add_apply, List.sum_cons, res_sum_apply f k L]

theorem sum_range_getD (k : Key) : ∀ (L : List Res),
    ((List.range L.length).map fun j => (L[j]?.getD .zero) k).sum = Res.sum L k
  | [] => rfl
  | x :: L => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, Res.sum_cons,
      Res.add_apply, ← sum_range_getD k L]
    rfl

/-! ## The unit count: a value carries `wd n` once per word unit of region `n` -/

/-- Offset `o` of `T` is a non-ghost, non-epoch protocol word unit of region `n`. -/
def WUnit (T : Ty) (n o : Nat) : Prop :=
  ∃ P, AtOff T o (.word (.lit n) P) ∧ P.epoch = false ∧ P.ghost = false

theorem nWords_one : nWords [Acc.one] = 1 := by simp [nWords, Acc.size]

/-- The inner induction of `VRR_count`, along the head unit's `AtOff`, with the
outer induction hypothesis `IH` for shorter lists. -/
theorem VRR_count_head (E : TEnv) {ρ₀ : Nat → Nat} {n N : Nat}
    (IH : ∀ {T : Ty} {os : List Nat} {ws : List Word} {R : Res},
      os.length ≤ N → os.Nodup → (∀ o ∈ os, WUnit T n o) →
      VRR ρ₀ (CE E) T (shp T) ws R → wc T = some ws.length → os.length ≤ R (.wd n))
    {T V : Ty} {o : Nat} (h : AtOff T o V) :
    (∀ t, V ≠ .mu t) → Solid V → (∀ q Rq, VRR ρ₀ (CE E) V (shp V) q Rq → 1 ≤ Rq (.wd n)) →
    ∀ {rest : List Nat} {ws : List Word} {R : Res}, rest.length ≤ N → (o :: rest).Nodup →
      (∀ o' ∈ rest, WUnit T n o') →
      VRR ρ₀ (CE E) T (shp T) ws R → wc T = some ws.length → rest.length + 1 ≤ R (.wd n) := by
  induction h with
  | here _ =>
      intro hV hS hl rest ws R _ hnd hu hv _
      have hr : rest = [] := by
        cases rest with
        | nil => rfl
        | cons o' r =>
          exfalso
          obtain ⟨P', h', -⟩ := hu o' (List.mem_cons_self ..)
          have e := (AtOff_solid hS (fun t e => by cases e) h').1
          rw [List.nodup_cons] at hnd
          exact hnd.1 (by rw [← e]; exact List.mem_cons_self ..)
      subst hr
      simpa using hl _ _ hv
  | @fst a b u o h' ih =>
      intro hV hS hl rest ws R hN hnd hu hv hwc
      simp only [VRR] at hv
      obtain ⟨ra, rb, e, Ra, Rb, hR, -, hsplit⟩ := hv
      simp only [shp, Shp.prod.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      cases ha : accs a with
      | none => simp [wc, accs, ha] at hwc
      | some ua =>
      cases hb : accs b with
      | none => simp [wc, accs, ha, hb] at hwc
      | some ub =>
      have hwa : wc a = some (nWords ua) := by simp [wc, ha]
      have hwb : wc b = some (nWords ub) := by simp [wc, hb]
      have hlen : ws.length = nWords ua + nWords ub := by
        simp [wc, accs, ha, hb, nWords_append] at hwc; omega
      obtain ⟨_, hva, hvb⟩ := hsplit _ (by rw [shp_wc]; exact hwa)
      have hla : (ws.take (nWords ua)).length = nWords ua := by simp; omega
      have hlb : (ws.drop (nWords ua)).length = nWords ub := by simp; omega
      subst hR
      simp only [Res.add_apply]
      have hsp := length_filter_split (fun x => decide (x < nWords ua)) rest
      rw [List.nodup_cons] at hnd
      have hA : ∀ o' ∈ rest.filter (fun x => decide (x < nWords ua)), WUnit a n o' := by
        intro o' ho'
        obtain ⟨hm, hlt⟩ := List.mem_filter.1 ho'
        simp only [decide_eq_true_eq] at hlt
        obtain ⟨P', h2, hep', hg'⟩ := hu o' hm
        rcases AtOff_prod_inv (fun t e => by cases e) h2 with ⟨-, e⟩ | h2a | ⟨as, o2, has, rfl, -⟩
        · cases e
        · exact ⟨P', h2a, hep', hg'⟩
        · rw [ha] at has; cases has; omega
      have hB : ∀ o' ∈ (rest.filter (fun x => !decide (x < nWords ua))).map (· - nWords ua), WUnit b n o' := by
        intro o'' ho''
        obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho''
        obtain ⟨hm, hge⟩ := List.mem_filter.1 ho'
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hge
        obtain ⟨P', h2, hep', hg'⟩ := hu o' hm
        rcases AtOff_prod_inv (fun t e => by cases e) h2 with ⟨-, e⟩ | h2a | ⟨as, o2, has, rfl, h2b⟩
        · cases e
        · have := AtOff_bound h2a ha (accs_word hg')
          rw [nWords_one] at this; omega
        · rw [ha] at has; cases has
          refine ⟨P', ?_, hep', hg'⟩
          rw [Nat.add_sub_cancel_left]; exact h2b
      have x1 := ih hV hS hl (rest := rest.filter (fun x => decide (x < nWords ua))) (by omega)
        (List.nodup_cons.2 ⟨fun hm => hnd.1 (List.mem_filter.1 hm).1, nodup_filter _ hnd.2⟩) hA hva
        (by rw [hla]; exact hwa)
      have hndB : ((rest.filter (fun x => !decide (x < nWords ua))).map (· - nWords ua)).Nodup := by
        refine nodup_map_on _ (fun x hx y hy hxy => ?_) (nodup_filter _ hnd.2)
        have h1 := (List.mem_filter.1 hx).2
        have h2 := (List.mem_filter.1 hy).2
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at h1 h2
        omega
      have x2 := IH (by rw [List.length_map]; omega) hndB hB hvb (by rw [hlb]; exact hwb)
      rw [List.length_map] at x2
      omega
  | @snd a b u o ua0 hua h' ih =>
      intro hV hS hl rest ws R hN hnd hu hv hwc
      simp only [VRR] at hv
      obtain ⟨ra, rb, e, Ra, Rb, hR, -, hsplit⟩ := hv
      simp only [shp, Shp.prod.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      cases hb : accs b with
      | none => simp [wc, accs, hua, hb] at hwc
      | some ub =>
      have hwa : wc a = some (nWords ua0) := by simp [wc, hua]
      have hwb : wc b = some (nWords ub) := by simp [wc, hb]
      have hlen : ws.length = nWords ua0 + nWords ub := by
        simp [wc, accs, hua, hb, nWords_append] at hwc; omega
      obtain ⟨_, hva, hvb⟩ := hsplit _ (by rw [shp_wc]; exact hwa)
      have hla : (ws.take (nWords ua0)).length = nWords ua0 := by simp; omega
      have hlb : (ws.drop (nWords ua0)).length = nWords ub := by simp; omega
      subst hR
      simp only [Res.add_apply]
      have hsp := length_filter_split (fun x => decide (x < nWords ua0)) rest
      rw [List.nodup_cons] at hnd
      have hA : ∀ o' ∈ rest.filter (fun x => decide (x < nWords ua0)), WUnit a n o' := by
        intro o' ho'
        obtain ⟨hm, hlt⟩ := List.mem_filter.1 ho'
        simp only [decide_eq_true_eq] at hlt
        obtain ⟨P', h2, hep', hg'⟩ := hu o' hm
        rcases AtOff_prod_inv (fun t e => by cases e) h2 with ⟨-, e⟩ | h2a | ⟨as, o2, has, rfl, -⟩
        · cases e
        · exact ⟨P', h2a, hep', hg'⟩
        · rw [hua] at has; cases has; omega
      have hB : ∀ o' ∈ (rest.filter (fun x => !decide (x < nWords ua0))).map (· - nWords ua0), WUnit b n o' := by
        intro o'' ho''
        obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho''
        obtain ⟨hm, hge⟩ := List.mem_filter.1 ho'
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hge
        obtain ⟨P', h2, hep', hg'⟩ := hu o' hm
        rcases AtOff_prod_inv (fun t e => by cases e) h2 with ⟨-, e⟩ | h2a | ⟨as, o2, has, rfl, h2b⟩
        · cases e
        · have := AtOff_bound h2a hua (accs_word hg')
          rw [nWords_one] at this; omega
        · rw [hua] at has; cases has
          refine ⟨P', ?_, hep', hg'⟩
          rw [Nat.add_sub_cancel_left]; exact h2b
      have x1 := IH (os := rest.filter (fun x => decide (x < nWords ua0))) (by omega)
        (nodup_filter _ hnd.2) hA hva (by rw [hla]; exact hwa)
      have hndB : (o :: (rest.filter (fun x => !decide (x < nWords ua0))).map (· - nWords ua0)).Nodup := by
        refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_map_on _ (fun x hx y hy hxy => ?_) (nodup_filter _ hnd.2)⟩
        · obtain ⟨o', ho', e⟩ := List.mem_map.1 hm
          obtain ⟨hm', hge⟩ := List.mem_filter.1 ho'
          simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hge
          have : o' = nWords ua0 + o := by omega
          exact hnd.1 (this ▸ hm')
        · have h1 := (List.mem_filter.1 hx).2
          have h2 := (List.mem_filter.1 hy).2
          simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at h1 h2
          omega
      have x2 := ih hV hS hl (by rw [List.length_map]; omega) hndB hB hvb (by rw [hlb]; exact hwb)
      rw [List.length_map] at x2
      omega
  | elem _ _ _ _ =>
      intro _ _ _ _ _ _ _ _ _ _ hwc
      simp [wc, accs] at hwc
  | @mu ρ W s u o hW hg _ ih =>
      intro hV hS hl rest ws R hN hnd hu hv hwc
      have hsig := sig_cl_unfold (ρ := ρ) (W := W) hg
      have e1 : cl ρ W 0 0 (.mu s) = .mu (cl ρ W 1 0 s) := rfl
      have hshp : shp (cl ρ W 0 0 (unfold1 (.mu s))) = shp (cl ρ W 0 0 (.mu s)) := by
        rw [shp_of_sig hsig, e1]; rfl
      have hv' := (VRR_cl_unfold E hW hg).2 hv
      rw [← hshp] at hv'
      have hwc' : wc (cl ρ W 0 0 (unfold1 (.mu s))) = some ws.length := by
        rw [wc_of_sig hsig, ← hwc, e1]; rfl
      refine ih hV hS hl hN hnd (fun o' ho' => ?_) hv' hwc'
      obtain ⟨P', h2, hep', hg'⟩ := hu o' ho'
      rcases AtOff_mu_inv hW hg h2 with ⟨-, e⟩ | h2'
      · exact absurd (e.trans (cl_mu_eq ρ W s)) (fun e => by cases e)
      · exact ⟨P', h2', hep', hg'⟩
  | @fold ρ W s T o _ _ _ _ _ =>
      intro hV
      exact absurd (cl_mu_eq ρ W s) (hV _)

/-- **The unit count in a value**: a value carries `wd n` at least once per
(distinct) non-ghost non-epoch word unit of region `n` of its type. -/
theorem VRR_count (E : TEnv) {ρ₀ : Nat → Nat} {n : Nat} : ∀ (N : Nat) {T : Ty} {os : List Nat}
    {ws : List Word} {R : Res}, os.length ≤ N → os.Nodup → (∀ o ∈ os, WUnit T n o) →
    VRR ρ₀ (CE E) T (shp T) ws R → wc T = some ws.length → os.length ≤ R (.wd n)
  | 0, _, os, _, _, hN, _, _, _, _ => by
    have : os.length = 0 := by omega
    rw [this]; exact Nat.zero_le _
  | N + 1, _, os, _, _, hN, hnd, hu, hv, hwc => by
    cases os with
    | nil => exact Nat.zero_le _
    | cons o rest =>
      obtain ⟨P, h, hep, -⟩ := hu o (List.mem_cons_self ..)
      have := VRR_count_head E (VRR_count E N) h (fun t e => by cases e) (Solid_word _ _) (leaf_word hep)
        (by simp only [List.length_cons] at hN; omega) hnd (fun o' ho' => hu o' (List.mem_cons_of_mem _ ho'))
        hv hwc
      simpa using this

theorem div_slot {W j o : Nat} (h : o < W) : (j * W + o) / W = j := by
  have hW : 0 < W := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt h, Nat.zero_add]

/-- **The unit count in a cell**: a cell's held resources carry `wd n` at least
once per distinct initialised word unit of region `n`. -/
theorem cell_count {E : TEnv} {c : Cell} {vals : List Word} {R : Res} {l : AllocLabel} {n : Nat}
    {os : List Nat} (hcell : CellOKR E (E.ini l) (E.rc l) c.ty vals R) (hnd : os.Nodup)
    (hu : ∀ o ∈ os, ∃ P, AtOff c.ty o (.word (.lit n) P) ∧ P.epoch = false ∧ P.ghost = false ∧
      IniAt E.ini c ⟨l, o⟩ (.word (.lit n) P)) :
    os.length ≤ R (.wd n) := by
  rcases hcell with ⟨hwc, hv⟩ | ⟨N, e, us, Rl, hT, hus, hn, hlen, hRl, hR, hslots⟩
  · exact VRR_count E.unsee os.length (Nat.le_refl _) hnd
      (fun o ho => let ⟨P, h1, h2, h3, _⟩ := hu o ho; ⟨P, h1, h2, h3⟩) hv.1 hwc
  · -- each unit lies in an initialised slot
    have hslot : ∀ o ∈ os, ∃ j o2, j < E.ini l ∧ j * nWords us + o2 = o ∧ o2 < nWords us ∧ WUnit e n o2 := by
      intro o ho
      obtain ⟨P, hat, hep, hg, hini⟩ := hu o ho
      rcases hini N e hT with ⟨hU, -⟩ | ⟨us', j, o2, hus', hj, hjo, hat2⟩
      · exact absurd (hU.trans hT) (fun h => by cases h)
      · rw [hus] at hus'; cases hus'
        have hb := AtOff_bound hat2 hus (accs_word hg)
        rw [nWords_one] at hb
        exact ⟨j, o2, hj, hjo, by omega, P, hat2, hep, hg⟩
    have hU : ∀ o ∈ os, o / nWords us ∈ List.range (E.ini l) := by
      intro o ho
      obtain ⟨j, o2, hj, rfl, hlt, -⟩ := hslot o ho
      rw [List.mem_range, div_slot hlt]; exact hj
    have hle := len_le_sum (fun o => o / nWords us) (List.nodup_range (n := E.ini l)) hU
      (g := fun j => (Rl[j]?.getD .zero) (.wd n)) (fun j hj => ?_)
    · rw [hR, ← sum_range_getD, hRl]; exact hle
    -- slot `j`
    rw [List.mem_range] at hj
    have hjl : j < Rl.length := by omega
    rw [List.getElem?_eq_getElem hjl]
    simp only [Option.getD_some]
    have hjN : j + 1 ≤ N := by omega
    have hm := Nat.mul_le_mul_right (nWords us) hjN
    rw [Nat.succ_mul] at hm
    have hsl : ((vals.drop (j * nWords us)).take (nWords us)).length = nWords us := by
      simp only [List.length_take, List.length_drop]; omega
    have hfin : ∀ x ∈ os.filter (fun o => decide (o / nWords us = j)),
        ∃ o2, x = j * nWords us + o2 ∧ o2 < nWords us ∧ WUnit e n o2 := by
      intro x hx
      obtain ⟨hm', hq⟩ := List.mem_filter.1 hx
      simp only [decide_eq_true_eq] at hq
      obtain ⟨j', o2, -, rfl, hlt, hw⟩ := hslot x hm'
      rw [div_slot hlt] at hq
      subst hq
      exact ⟨o2, rfl, hlt, hw⟩
    rcases Nat.eq_zero_or_pos (nWords us) with hz0 | hz
    · have he : os.filter (fun o => decide (o / nWords us = j)) = [] := by
        refine List.filter_eq_nil_iff.2 fun x hx hq => ?_
        obtain ⟨o2, -, hlt, -⟩ := hfin x (List.mem_filter.2 ⟨hx, hq⟩)
        omega
      rw [he]
      exact Nat.zero_le _
    have hv := (hslots j Rl[j] hj (List.getElem?_eq_getElem hjl)).2 (.inr hz)
    have hc := VRR_count E.unsee (n := n) _ (Nat.le_refl _)
      (os := (os.filter (fun o => decide (o / nWords us = j))).map (· - j * nWords us))
      (nodup_map_on _ (fun x hx y hy hxy => ?_) (nodup_filter _ hnd)) (fun o' ho' => ?_) hv.1
      (by rw [hsl]; exact wc_of_accs hus)
    · rw [List.length_map] at hc; exact hc
    · obtain ⟨o2, rfl, -, -⟩ := hfin x hx
      obtain ⟨o3, rfl, -, -⟩ := hfin y hy
      omega
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho'
      obtain ⟨o2, rfl, -, hw⟩ := hfin x hx
      rw [Nat.add_sub_cancel_left]; exact hw

/-- **The unit count in memory**: memory's held part carries `wd n` at least
once per distinct initialised non-epoch word unit of region `n`. -/
theorem held_count {E : TEnv} {s : St} {H : Res} {n : Nat} {U : List Address} (hH : MemHeld E s H)
    (hnd : U.Nodup)
    (hu : ∀ A ∈ U, ∃ P, WordAt E A n P ∧ P.epoch = false ∧
      ∀ c, E.sto A.label = some c → IniAt E.ini c A (.word (.lit n) P)) :
    U.length ≤ H (.wd n) := by
  obtain ⟨L, Rl, hL, hcov, rfl, hent⟩ := hH
  rw [res_sum_apply]
  refine len_le_sum (fun A : Address => A.label) hL (fun A hA => ?_) (fun l hl => ?_)
  · obtain ⟨P, ⟨c, hs, -, -⟩, -, -⟩ := hu A hA
    exact hcov _ c hs
  · cases hc : E.sto l with
    | none =>
      have : U.filter (fun A => decide (A.label = l)) = [] := by
        refine List.eq_nil_iff_forall_not_mem.2 fun A hA => ?_
        obtain ⟨hm, hq⟩ := List.mem_filter.1 hA
        simp only [decide_eq_true_eq] at hq
        obtain ⟨P, ⟨c, hs, -, -⟩, -, -⟩ := hu A hm
        rw [hq, hc] at hs; cases hs
      rw [this]; exact Nat.zero_le _
    | some c =>
      obtain ⟨vals, -, hC⟩ := (hent l hl).2 c hc
      have hlab : ∀ A ∈ U.filter (fun A => decide (A.label = l)), A.label = l := fun A hA => by
        simpa using (List.mem_filter.1 hA).2
      have hcnt := cell_count (n := n) (os := (U.filter (fun A => decide (A.label = l))).map Address.offset) hC
        (nodup_map_on _ (fun A hA B hB e => ?_) (nodup_filter _ hnd)) (fun o ho => ?_)
      · rw [List.length_map] at hcnt; exact hcnt
      · have h1 := hlab A hA
        have h2 := hlab B hB
        cases A; cases B
        simp only at h1 h2 e
        subst h1 h2 e
        rfl
      · obtain ⟨A, hA, rfl⟩ := List.mem_map.1 ho
        have h1 := hlab A hA
        obtain ⟨P, ⟨c', hs, hat, hg⟩, hep, hini⟩ := hu A (List.mem_filter.1 hA).1
        rw [h1, hc] at hs; cases hs
        refine ⟨P, hat, hep, hg, ?_⟩
        have e : A = ⟨l, A.offset⟩ := by cases A; simp only at h1; subst h1; rfl
        rw [← e]
        exact hini c (by rw [h1]; exact hc)

/-! ## Debits at `wd n` -/

theorem db_wd_le1 {E : TEnv} {mem : Memory} {m : Msg} {tw : Ts} {R : Res} (n : Nat)
    (h : DbRes E mem m tw R)
    (hZ : DesigAt E mem m.loc tw → ∀ Z, BlkDb E mem m.loc Z → Z (.wd n) = 0) : R (.wd n) ≤ 1 := by
  rcases h with ⟨-, -, hI, hnI⟩ | ⟨-, rfl⟩
  · by_cases hin : InitAt mem m.loc tw
    · obtain ⟨R₁, Z, hF, hD, hND, rfl⟩ := hI hin
      have hz : Z (.wd n) = 0 := by
        by_cases hd : DesigAt E mem m.loc tw
        · exact hZ hd Z (hD hd)
        · rw [hND hd]; rfl
      simp only [Res.add_apply, hz, Nat.add_zero]
      rcases hF with ⟨n', P, -, rfl⟩ | ⟨-, rfl⟩
      · have hr : wr P n' (mw m).val (.wd n) = 0 := by
          unfold wr
          split <;> simp [Res.one]
        have hw := wdW_le P n' (.wd n)
        simp only [Res.add_apply, hr, Nat.zero_add]
        refine Nat.le_trans hw ?_
        simp only [Res.one]
        split <;> omega
      · simp
    · have := TermOnce.WRes_wd (hnI hin) n
      omega
  · simp

theorem sum_le_count {α : Type} (f : α → Res) (k : Key) : ∀ (L : List α), (∀ t ∈ L, f t k ≤ 1) →
    Res.sum (L.map f) k ≤ (L.filter fun t => decide (1 ≤ f t k)).length
  | [], _ => Nat.le_refl _
  | t :: L, h => by
    have ih := sum_le_count f k L fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    have ht := h t (List.mem_cons_self ..)
    simp only [List.map_cons, Res.sum_cons, Res.add_apply, List.filter_cons]
    by_cases h1 : 1 ≤ f t k
    · simp only [h1, decide_true, ↓reduceIte, List.length_cons]
      omega
    · simp only [h1, decide_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

/-- A visible cell of thread `j`'s cut is a shared cell, so it is in every
thread's cut. -/
theorem cutSto_vis {Eg : GEnv} {j i : Nat} {S S' : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (hs : (Cut Eg j S).sto l = some cl) (hv : Vis (Cut Eg j S) l) : (Cut Eg i S').sto l = some cl := by
  change cutSto Eg j l = some cl at hs
  change cutSto Eg i l = some cl
  unfold cutSto at hs ⊢
  by_cases hin : Eg.InCut j l
  · simp only [hin, ↓reduceIte] at hs
    have hsh : Eg.Shared l := by
      obtain ⟨c0, hc0, ho | hsh⟩ := hin
      · rw [hs] at hc0
        cases hc0
        cases hp : Eg.pfr l with
        | some f => exact ⟨f, hp⟩
        | none =>
          refine absurd ⟨⟨cl, ?_, ho⟩, hp⟩ hv
          change cutSto Eg j l = some cl
          unfold cutSto
          simp only [show Eg.InCut j l from ⟨cl, hs, Or.inl ho⟩, ↓reduceIte]
          exact hs
      · exact hsh
    have hin' : Eg.InCut i l := ⟨cl, hs, Or.inr hsh⟩
    simp only [hin', ↓reduceIte]
    exact hs
  · simp only [hin, ↓reduceIte] at hs
    cases hs

theorem nodup_flatMap_range {β : Type} {f : Nat → List β} (h1 : ∀ q, (f q).Nodup)
    (h2 : ∀ q1 q2 x, q1 ≠ q2 → x ∈ f q1 → x ∈ f q2 → False) : ∀ (N : Nat), ((List.range N).flatMap f).Nodup
  | 0 => List.nodup_nil
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine List.nodup_append.2 ⟨nodup_flatMap_range h1 h2 N, h1 N, fun x hx y hy hxy => ?_⟩
    subst hxy
    obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.1 hx
    rw [List.mem_range] at hq
    exact h2 q N x (by omega) hxq hy

/-! ## The holder units and the two distinctness facts -/

/-- Thread `q`'s holder units at `wd n`: the locations of its promises with a
nonzero `wd n` debit. -/
def holdU (c : Cfg) (db : Nat → Ts → Res) (n q : Nat) : List Address :=
  match c.ths[q]? with
  | some thq => (thq.promises.filter fun t => decide (1 ≤ db q t (.wd n))).map
      fun t => ((c.mem[t]?).map Msg.loc).getD default
  | none => []

theorem mem_holdU {c : Cfg} {db : Nat → Ts → Res} {n q : Nat} {A : Address} (h : A ∈ holdU c db n q) :
    ∃ thq t, c.ths[q]? = some thq ∧ t ∈ thq.promises ∧ 1 ≤ db q t (.wd n) ∧
      A = ((c.mem[t]?).map Msg.loc).getD default := by
  unfold holdU at h
  cases hq : c.ths[q]? with
  | none => rw [hq] at h; cases h
  | some thq =>
    rw [hq] at h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
    obtain ⟨ht1, ht2⟩ := List.mem_filter.1 ht
    simp only [decide_eq_true_eq] at ht2
    exact ⟨thq, t, rfl, ht1, ht2, rfl⟩

/-- **(R2a, named fact)** At most one outstanding promise per unit initialises
it: two `InitAt` promises at one unit would need an `.undef` message between
them (promises are not `.undef`). -/
def HolderUniq (c : Cfg) : Prop :=
  ∀ (j1 j2 : Nat) (th1 th2 : TTh) (t1 t2 : Ts) (m1 m2 : Msg), c.ths[j1]? = some th1 → c.ths[j2]? = some th2 →
    t1 ∈ th1.promises → t2 ∈ th2.promises → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 →
    m1.loc = m2.loc → InitAt c.mem m1.loc t1 → InitAt c.mem m2.loc t2 → t1 = t2

/-- `HolderUniq` along runs (the run-level form of R2a). -/
def HolderUniqR (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (c0 : Cfg) : Prop :=
  ∀ c, TermSpawnStep.StepsG p k arch Sp c0 c → HolderUniq c

/-- **(R2b, named fact)** At a plain non-protocol store of thread `i` (the
stores `StoreCrZ0` speaks of) over a unit where `i` has an outstanding promise
and which holds a non-epoch protocol word in `i`'s view `CE η`, no other thread has an outstanding promise initialising that unit (`StoreNI`
is the stepper's own half). -/
def StoreHolderFree (c : Cfg) (i : Nat) (th : TTh) (cx : Cx) (η : TEnv) : Prop :=
  ∀ x rel a v tok e u, th.term = .let_ x (.store rel a v tok) e →
    ((cx.peek a = .ok (.ptr .pub u) ∧ wordOf (.ptr .pub u) = none) ∨
      (cx.peek a = .ok (.loc .pub u) ∧ wordOf (.loc .pub u) = none)) →
    ∀ rt pw ad μ ru us j, evalAt th.env a = some (rt, [pw]) → addrOf pw = some ad →
      cellOf rt = some (μ, ru) → accs ru = some us → j < nWords us →
      (∃ t0 m0, t0 ∈ th.promises ∧ c.mem[t0]? = some m0 ∧ m0.loc = offs ad j) →
      (∃ n P, WordAt (CE η) (offs ad j) n P ∧ P.epoch = false) →
      ∀ q thq t m, q ≠ i → c.ths[q]? = some thq → t ∈ thq.promises → c.mem[t]? = some m →
        m.loc = offs ad j → ¬ InitAt c.mem (offs ad j) t

/-! ## `StoreCrZ` under (H)

The memory-count route (`storeCrZ_ofM`, `dwf_ofM`) does not survive (H): a designated
debit's block part `Z` (`BlkDb`) may carry `wd n` (planted fresh tokens), so `db_wd_pos` needs
`hZ`.  The (H) replacement is the pinned slot cover (TermWdCoverH §3/§4); until then
`StoreCrZ` is the temporary named field `storeCrZH` (TermMain). -/

#print axioms leaf_word
#print axioms one_at
#print axioms db_wd_pos
#print axioms db_wd_le1
#print axioms VRR_count_head
#print axioms VRR_count
#print axioms cell_count
#print axioms held_count
#print axioms cutSto_vis

end TermWdCover
