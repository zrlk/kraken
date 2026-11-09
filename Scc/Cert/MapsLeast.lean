import Scc.Cert.MapsCompute

/-!
# A least-fixpoint witness is the reference liveness (untrusted)

`leastOk body w r` (`Scc/Cert/MapsCompute.lean`) checks that `w` is a post-fixpoint of slot
liveness on `body` (`liveOk`) and that every slot of `w` is justified at its rank in `r`, the
ranks below `liveSlots`' fuel. `liveSlots_le` gives one inclusion (the reference liveness is
below every post-fixpoint); `leastOk_le` here gives the other (every justified slot is in the
`rank + 1`-th iterate of `liveSlots`' step, and `liveSlots` is above every iterate within its
fuel). So, as sets per instruction, a `leastOk` witness is `liveSlots body` (`leastOk_mem`).
-/

namespace Scc.Cert.Maps

/-! ## `liveSlots`' step and its iterates -/

/-- `liveSlots`' step on `body` (its `let step`). -/
def liveStep (body : List Item) (live : Array (List Int)) : Array (List Int) :=
  let is := insOf body
  let n := is.size
  let lix := labelIdx body
  let taken := is.toList.foldl (fun acc (_, _, i) => unionI acc i.takes) []
  (Array.range n).map fun k =>
    let i := (is[k]!).2.2
    let out := (succIdx lix n k i).foldl (fun acc j => unionI acc (live[j]!)) []
    unionI (unionI taken i.reads) (out.filter fun o => !i.writes.contains o)

theorem liveSlots_eq (body : List Item) :
    liveSlots body = liveSlots.go (liveStep body) (fuelOf body)
      (Array.replicate (insOf body).size []) := rfl

/-- The `i`-th iterate of `liveStep` from the empty array. -/
def liveIter (body : List Item) : Nat → Array (List Int)
  | 0 => Array.replicate (insOf body).size []
  | i + 1 => liveStep body (liveIter body i)

/-- Pointwise inclusion of liveness arrays. -/
def LeA (a b : Array (List Int)) : Prop := ∀ (k : Nat) (x : Int), x ∈ a[k]! → x ∈ b[k]!

theorem LeA.refl (a : Array (List Int)) : LeA a a := fun _ _ h => h

theorem LeA.trans {a b c : Array (List Int)} (h1 : LeA a b) (h2 : LeA b c) : LeA a c :=
  fun k x h => h2 k x (h1 k x h)

theorem liveStep_size (body : List Item) (m : Array (List Int)) :
    (liveStep body m).size = (insOf body).size := by
  simp [liveStep]

theorem liveIter_size (body : List Item) : ∀ i, (liveIter body i).size = (insOf body).size
  | 0 => by simp [liveIter]
  | i + 1 => liveStep_size body _

/-- Membership in a step's entry `k < n`. -/
theorem mem_liveStep {body : List Item} {m : Array (List Int)} {k : Nat}
    (hk : k < (insOf body).size) {x : Int} :
    x ∈ (liveStep body m)[k]! ↔
      (x ∈ (insOf body).toList.foldl (fun acc (_, _, i) => unionI acc i.takes) [] ∨
        x ∈ ((insOf body)[k]).2.2.reads) ∨
      ((∃ j ∈ succIdx (labelIdx body) (insOf body).size k ((insOf body)[k]).2.2, x ∈ m[j]!) ∧
        ¬ (((insOf body)[k]).2.2.writes.contains x = true)) := by
  rw [getElem!_pos (liveStep body m) k (by rw [liveStep_size]; exact hk)]
  simp only [liveStep, Array.getElem_map, Array.getElem_range]
  rw [getElem!_pos (insOf body) k hk]
  rw [mem_unionI, mem_unionI, List.mem_filter, mem_foldl_unionI (fun j => m[j]!)]
  simp

theorem liveStep_mono {body : List Item} {a b : Array (List Int)} (h : LeA a b) :
    LeA (liveStep body a) (liveStep body b) := by
  intro k x hx
  by_cases hk : k < (insOf body).size
  · rw [mem_liveStep hk] at hx ⊢
    rcases hx with h1 | ⟨⟨j, hj, hxj⟩, hw⟩
    · exact Or.inl h1
    · exact Or.inr ⟨⟨j, hj, h j x hxj⟩, hw⟩
  · rw [getElem!_none (by rw [liveStep_size]; exact hk)] at hx
    simp at hx

theorem liveIter_chain (body : List Item) : ∀ i, LeA (liveIter body i) (liveIter body (i + 1))
  | 0 => by
    intro k x hx
    by_cases hk : k < (liveIter body 0).size
    · simp [liveIter] at hx
      rw [getElem!_pos _ k (by simpa [liveIter] using hk)] at hx
      simp at hx
    · rw [getElem!_none hk] at hx; simp at hx
  | i + 1 => liveStep_mono (liveIter_chain body i)

theorem liveIter_le (body : List Item) {i j : Nat} (h : i ≤ j) :
    LeA (liveIter body i) (liveIter body j) := by
  induction h with
  | refl => exact LeA.refl _
  | step _ ih => exact ih.trans (liveIter_chain body _)

/-! ## Duplicate-free entries -/

theorem nodup_unionI : ∀ {a : List Int} (b : List Int), a.Nodup → (unionI a b).Nodup := by
  intro a b
  induction b generalizing a with
  | nil => intro h; simpa [unionI] using h
  | cons y ys ih =>
    intro h
    have e : unionI a (y :: ys) = unionI (if a.contains y then a else a ++ [y]) ys := rfl
    rw [e]
    apply ih
    by_cases hy : a.contains y
    · simp only [hy, ite_true]; exact h
    · simp only [hy, Bool.false_eq_true, ite_false]
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro u hu v hv
      simp only [List.mem_singleton] at hv
      subst hv
      intro e; subst e
      exact hy (List.contains_iff_mem.mpr hu)

theorem liveStep_nodup {body : List Item} (m : Array (List Int)) (k : Nat) :
    ((liveStep body m)[k]!).Nodup := by
  by_cases hk : k < (insOf body).size
  · rw [getElem!_pos (liveStep body m) k (by rw [liveStep_size]; exact hk)]
    simp only [liveStep, Array.getElem_map, Array.getElem_range]
    apply nodup_unionI
    apply nodup_unionI
    -- `taken` is a fold of `unionI` from `[]`
    have : ∀ (l : List (Nat × Nat × Ins)) (acc : List Int), acc.Nodup →
        (l.foldl (fun acc (p : Nat × Nat × Ins) => unionI acc p.2.2.takes) acc).Nodup := by
      intro l
      induction l with
      | nil => intro acc h; simpa using h
      | cons p ps ih => intro acc h; exact ih _ (nodup_unionI _ h)
    exact this _ [] List.nodup_nil
  · rw [getElem!_none (by rw [liveStep_size]; exact hk)]; exact List.nodup_nil

theorem liveIter_nodup (body : List Item) : ∀ (i k : Nat), ((liveIter body i)[k]!).Nodup
  | 0, k => by
    by_cases hk : k < (liveIter body 0).size
    · rw [getElem!_pos _ k hk]; simp [liveIter]
    · rw [getElem!_none hk]; exact List.nodup_nil
  | i + 1, _ => liveStep_nodup _ _

/-! ## `liveSlots` is above every iterate within its fuel -/

/-- A duplicate-free list included in another is at most as long. -/
theorem len_le_of_sub : ∀ {a c : List Int}, a.Nodup → (∀ x ∈ a, x ∈ c) → a.length ≤ c.length
  | [], _, _, _ => by simp
  | y :: a', c, h, hs => by
    have hy : y ∈ c := hs y (by simp)
    have hn := List.nodup_cons.mp h
    have ih := len_le_of_sub (c := c.erase y) hn.2 (fun x hx =>
      (List.mem_erase_of_ne (by intro e; subst e; exact hn.1 hx)).mpr (hs x (by simp [hx])))
    rw [List.length_erase_of_mem hy] at ih
    have : 0 < c.length := List.length_pos_of_mem hy
    simp only [List.length_cons]; omega

/-- A duplicate-free list included in a list at most as long contains it. -/
theorem sub_of_len {a b : List Int} (ha : a.Nodup) (hab : ∀ x ∈ a, x ∈ b)
    (hl : b.length ≤ a.length) : ∀ x ∈ b, x ∈ a := by
  intro x hx
  by_cases hxa : x ∈ a
  · exact hxa
  exfalso
  have h1 := len_le_of_sub (c := b.erase x) ha (fun y hy =>
    (List.mem_erase_of_ne (by intro e; subst e; exact hxa hy)).mpr (hab y hy))
  rw [List.length_erase_of_mem hx] at h1
  have : 0 < b.length := List.length_pos_of_mem hx
  omega

/-- Where the step leaves the entries' lengths unchanged, an iterate is a fixpoint (as sets). -/
theorem liveIter_fix {body : List Item} {i : Nat}
    (h : ((liveStep body (liveIter body i)).map List.length ==
      (liveIter body i).map List.length) = true) :
    LeA (liveIter body (i + 1)) (liveIter body i) := by
  have he : (liveStep body (liveIter body i)).map List.length = (liveIter body i).map List.length :=
    by simpa using h
  intro k x hx
  by_cases hk : k < (insOf body).size
  · have hk1 : k < (liveStep body (liveIter body i)).size := by rw [liveStep_size]; exact hk
    have hk0 : k < (liveIter body i).size := by rw [liveIter_size]; exact hk
    have hlen : ((liveStep body (liveIter body i))[k]).length = ((liveIter body i)[k]).length := by
      have := congrArg (fun a => a[k]!) he
      rw [getElem!_pos _ k (by simpa using hk1), getElem!_pos _ k (by simpa using hk0)] at this
      simpa using this
    have hsub := liveIter_chain body i
    simp only [liveIter] at hx hsub ⊢
    rw [getElem!_pos _ k hk1] at hx
    rw [getElem!_pos _ k hk0]
    have hn0 := liveIter_nodup body i k
    have hn1 := liveStep_nodup (body := body) (liveIter body i) k
    rw [getElem!_pos _ k hk0] at hn0
    rw [getElem!_pos _ k hk1] at hn1
    refine sub_of_len hn0 ?_ (by omega) x hx
    intro y hy
    have := hsub k y (by rw [getElem!_pos _ k hk0]; exact hy)
    rw [getElem!_pos _ k hk1] at this
    exact this
  · rw [getElem!_none (by rw [liveIter_size]; exact hk)] at hx; simp at hx

/-- A fixpoint (as sets) is above every later iterate. -/
theorem liveIter_fix_le {body : List Item} {i : Nat}
    (h : LeA (liveIter body (i + 1)) (liveIter body i)) : ∀ t, LeA (liveIter body (i + t)) (liveIter body i)
  | 0 => LeA.refl _
  | t + 1 => by
    have ih := liveIter_fix_le h t
    show LeA (liveStep body (liveIter body (i + t))) (liveIter body i)
    exact (liveStep_mono ih).trans h

/-- `liveSlots.go` from the `i`-th iterate with fuel `f` is above every iterate up to `i + f`. -/
theorem liveIter_go_le (body : List Item) : ∀ (f i j : Nat), j ≤ i + f →
    LeA (liveIter body j) (liveSlots.go (liveStep body) f (liveIter body i))
  | 0, i, j, hj => by
    simp only [liveSlots.go]
    exact liveIter_le body (by omega)
  | f + 1, i, j, hj => by
    simp only [liveSlots.go]
    split
    · rename_i h
      have hfix := liveIter_fix (body := body) (i := i) h
      by_cases hji : j ≤ i
      · exact liveIter_le body hji
      · have := liveIter_fix_le hfix (j - i)
        rw [show i + (j - i) = j by omega] at this
        exact this
    · exact liveIter_go_le body f (i + 1) j (by omega)

/-- **`liveSlots` is above every iterate within its fuel.** -/
theorem liveIter_le_liveSlots (body : List Item) {j : Nat} (hj : j ≤ fuelOf body) :
    LeA (liveIter body j) (liveSlots body) := by
  rw [liveSlots_eq]
  exact liveIter_go_le body (fuelOf body) 0 j (by omega)

/-! ## Every justified slot is in an iterate -/

theorem lowerIn_spec {o : Int} {r : Nat} : ∀ {ws : List Int} {rs : List Nat},
    lowerIn o r ws rs = true → ∃ r' < r, (o, r') ∈ ws.zip rs
  | [], _, h => by simp [lowerIn] at h
  | _ :: _, [], h => by simp [lowerIn] at h
  | o' :: os, r' :: rs, h => by
    simp only [lowerIn, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with ⟨rfl, hr⟩ | h
    · exact ⟨r', hr, by simp⟩
    · obtain ⟨r'', hr'', hm⟩ := lowerIn_spec h
      exact ⟨r'', hr'', by simp [hm]⟩

/-- **What `justGo` checks**, indexed (as `liveOkGo_spec`). -/
theorem justGo_spec (taken : List Int) (lix : List (String × Nat)) (n : Nat) (wl : List (List Int))
    (rl : List (List Nat)) :
    ∀ (is : List (Nat × Nat × Ins)) (ws : List (List Int)) (rs : List (List Nat)) (k : Nat),
      ws = wl.drop k → rs = rl.drop k → justGo taken lix n wl rl is ws rs k = true →
      ∀ m (hm : m < is.length),
        (wl.getD (k + m) []).length = (rl.getD (k + m) []).length ∧
        ∀ p ∈ (wl.getD (k + m) []).zip (rl.getD (k + m) []),
          taken.contains p.1 = true ∨ is[m].2.2.reads.contains p.1 = true ∨
          (is[m].2.2.writes.contains p.1 = false ∧
            ∃ j ∈ succIdx lix n (k + m) is[m].2.2, lowerIn p.1 p.2 (wl.getD j []) (rl.getD j []) = true)
  | [], _, _, _, _, _, _ => fun m hm => absurd hm (Nat.not_lt_zero _)
  | (a, z, i) :: is, wk :: ws, rk :: rs, k, hws, hrs, h => by
    have hwk : wk = wl.getD k [] := by
      have := congrArg (fun l => l.headD []) hws
      simpa [headD_drop] using this
    have hrk : rk = rl.getD k [] := by
      have := congrArg (fun l => l.headD []) hrs
      simpa [headD_drop] using this
    have hws' : ws = wl.drop (k + 1) := by
      have := congrArg List.tail hws
      simpa [List.tail_drop] using this
    have hrs' : rs = rl.drop (k + 1) := by
      have := congrArg List.tail hrs
      simpa [List.tail_drop] using this
    simp only [justGo, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hlen, hall⟩, hg⟩ := h
    have ih := justGo_spec taken lix n wl rl is ws rs (k + 1) hws' hrs' hg
    intro m hm
    cases m with
    | zero =>
      subst hwk hrk
      refine ⟨by simpa using Nat.eq_of_beq_eq_true hlen, ?_⟩
      intro p hp
      have := hall p (by simpa using hp)
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at this
      simp only [Nat.add_zero, List.getElem_cons_zero]
      rcases this with (h1 | h1) | ⟨h1, j, hj, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · refine Or.inr (Or.inr ⟨h1, j, hj, ?_⟩)
        by_cases hjk : j = k + 1
        · subst hjk
          simpa [hws', hrs', headD_drop] using h2
        · simpa [hjk] using h2
    | succ m =>
      have := ih m (by simpa using hm)
      simpa [Nat.add_assoc, Nat.add_comm 1 m] using this
  | (_ :: _), [], _, _, _, _, h => by simp [justGo] at h
  | (_ :: _), _ :: _, [], _, _, _, h => by simp [justGo] at h

theorem getD_of_size {w : Array (List Int)} {k : Nat} (h : ¬ k < w.size) : w.toList.getD k [] = [] := by
  rw [← getElem!_eq_getD_toList]; exact getElem!_none h

/-- **Every slot of a justified post-fixpoint, at rank `x`, is in the `x + 1`-th iterate.** -/
theorem justified_iter {body : List Item} {w : Array (List Int)} {r : List (List Nat)}
    (hl : liveOk body w = true) (hj : justified body w r = true) :
    ∀ (x k : Nat) (o : Int), (o, x) ∈ (w.toList.getD k []).zip (r.getD k []) →
      o ∈ (liveIter body (x + 1))[k]! := by
  obtain ⟨hsize, _⟩ := liveOk_spec hl
  have hspec := justGo_spec _ _ _ w.toList r (insOf body).toList w.toList r 0 (by simp) (by simp) hj
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro k o ho
    by_cases hk : k < (insOf body).size
    · obtain ⟨_, hall⟩ := hspec k (by simpa using hk)
      have := hall (o, x) (by simpa using ho)
      simp only [Nat.zero_add, Array.getElem_toList] at this
      show o ∈ (liveStep body (liveIter body x))[k]!
      rw [mem_liveStep hk]
      rcases this with h1 | h1 | ⟨h1, j, hj, h2⟩
      · exact Or.inl (Or.inl (List.contains_iff_mem.mp h1))
      · exact Or.inl (Or.inr (List.contains_iff_mem.mp h1))
      · obtain ⟨r', hr', hm⟩ := lowerIn_spec h2
        refine Or.inr ⟨⟨j, hj, ?_⟩, fun h => by rw [h1] at h; cases h⟩
        exact liveIter_le body (by omega) j o (ih r' hr' j o hm)
    · rw [getD_of_size (by rw [hsize]; exact hk)] at ho
      simp at ho

theorem mem_zip_of_len {a : List Int} {b : List Nat} :
    a.length = b.length → ∀ {o : Int}, o ∈ a → ∃ y ∈ b, (o, y) ∈ a.zip b := by
  induction a generalizing b with
  | nil => intro _ o h; simp at h
  | cons u us ih =>
    intro hl o ho
    cases b with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rcases List.mem_cons.mp ho with rfl | ho
      · exact ⟨v, by simp, by simp⟩
      · obtain ⟨y, hy, hz⟩ := ih hl ho
        exact ⟨y, by simp [hy], by simp [hz]⟩

theorem le_foldl_max : ∀ (l : List Nat) (m : Nat), m ≤ l.foldl max m
  | [], _ => Nat.le_refl _
  | y :: ys, m => Nat.le_trans (Nat.le_max_left m y) (le_foldl_max ys (max m y))

theorem mem_le_foldl_max : ∀ (l : List Nat) (m : Nat), ∀ y ∈ l, y ≤ l.foldl max m
  | [], _, _, h => by simp at h
  | z :: zs, m, y, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right m y) (le_foldl_max zs _)
    · exact mem_le_foldl_max zs _ y h

theorem le_maxRank_go : ∀ (r : List (List Nat)) (m : Nat), m ≤ r.foldl (fun m l => l.foldl max m) m
  | [], _ => Nat.le_refl _
  | l :: ls, m => Nat.le_trans (le_foldl_max l m) (le_maxRank_go ls _)

theorem mem_le_maxRank_go : ∀ (r : List (List Nat)) (m : Nat), ∀ l ∈ r, ∀ y ∈ l,
    y ≤ r.foldl (fun m l => l.foldl max m) m
  | [], _, _, h, _, _ => by simp at h
  | l' :: ls, m, l, h, y, hy => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (mem_le_foldl_max l m y hy) (le_maxRank_go ls _)
    · exact mem_le_maxRank_go ls _ l h y hy

theorem le_maxRank {r : List (List Nat)} {k y : Nat} (h : y ∈ r.getD k []) : y ≤ maxRank r := by
  unfold maxRank
  by_cases hk : k < r.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at h
    exact mem_le_maxRank_go r 0 _ (List.getElem_mem hk) y h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h; simp at h

/-- **A least-fixpoint witness is below the reference liveness**: with `leastOk body w r`, every
slot of `w[k]` is in `liveSlots body`'s entry `k`. -/
theorem leastOk_le {body : List Item} {w : Array (List Int)} {r : List (List Nat)}
    (h : leastOk body w r = true) : LeA w (liveSlots body) := by
  simp only [leastOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hj⟩, hf⟩ := h
  obtain ⟨hsize, _⟩ := liveOk_spec hl
  have hspec := justGo_spec _ _ _ w.toList r (insOf body).toList w.toList r 0 (by simp) (by simp) hj
  intro k o ho
  rw [getElem!_eq_getD_toList] at ho
  by_cases hk : k < (insOf body).size
  · obtain ⟨hlen, _⟩ := hspec k (by simpa using hk)
    simp only [Nat.zero_add] at hlen
    obtain ⟨y, hy, hz⟩ := mem_zip_of_len hlen ho
    have hit := justified_iter hl hj y k o hz
    have hy' : y + 1 ≤ fuelOf body := by have := le_maxRank hy; omega
    exact liveIter_le_liveSlots body hy' k o hit
  · rw [getD_of_size (by rw [hsize]; exact hk)] at ho
    simp at ho

/-- **A least-fixpoint witness is the reference liveness, as sets per instruction.** -/
theorem leastOk_mem {body : List Item} {w : Array (List Int)} {r : List (List Nat)}
    (h : leastOk body w r = true) : ∀ (k : Nat) (o : Int), o ∈ w[k]! ↔ o ∈ (liveSlots body)[k]! := by
  have hl : liveOk body w = true := by
    simp only [leastOk, Bool.and_eq_true] at h; exact h.1.1
  intro k o
  exact ⟨leastOk_le h k o, liveSlots_le hl k o⟩

/-! ## The tables from a least-fixpoint witness are the reference tables -/

/-- `liveRoots` depends on its liveness only through membership. -/
theorem liveRoots_congr (t : FnTags) {l l' : List Int} (h : ∀ o, o ∈ l ↔ o ∈ l') :
    liveRoots t l = liveRoots t l' := by
  have hc : ∀ o, l.contains o = l'.contains o := by
    intro o
    cases h1 : l.contains o <;> cases h2 : l'.contains o <;> try rfl
    · rw [← h1]; exact List.contains_iff_mem.mpr ((h o).mpr (List.contains_iff_mem.mp h2))
    · rw [← h2]; exact Eq.symm <| List.contains_iff_mem.mpr ((h o).mp (List.contains_iff_mem.mp h1))
  simp only [liveRoots, hc]

/-- **`fnMapsW` depends on its witness only through membership**, per instruction. -/
theorem fnMapsW_congr (t : FnTags) (items : List Item) {w w' : Array (List Int)}
    (h : ∀ (k : Nat) (o : Int), o ∈ w[k]! ↔ o ∈ w'[k]!) :
    fnMapsW t items w = fnMapsW t items w' := by
  have hr : ∀ k, liveRoots t (w[k]!) = liveRoots t (w'[k]!) := fun k => liveRoots_congr t (h k)
  simp only [fnMapsW, hr]

/-- With every witness its function's least fixpoint, the maps from the witnesses are the
reference maps (`fnMaps`), function by function. -/
theorem mapM_fnMapsW_least {items : List Item} : ∀ {fns : List FnTags} {gw : GcWit},
    gw.length = fns.length → (∀ p ∈ fns.zip gw, leastOk (bodyOf p.1 items) p.2.1 p.2.2 = true) →
    (fns.zip (gw.map (·.1))).mapM (fun (p : FnTags × Array (List Int)) => fnMapsW p.1 items p.2) =
      (fns.zip (witness fns items)).mapM
        (fun (p : FnTags × Array (List Int)) => fnMapsW p.1 items p.2)
  | [], [], _, _ => rfl
  | t :: ts, (w, r) :: gs, hl, h => by
    have h1 := h (t, w, r) (by simp)
    have ih := mapM_fnMapsW_least (fns := ts) (gw := gs) (by simpa using hl)
      (fun p hp => h p (List.mem_cons_of_mem _ hp))
    simp only [witness] at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons]
    rw [fnMapsW_congr t items (leastOk_mem h1), ih]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **With least-fixpoint witnesses, `computeW` is `compute`.** -/
theorem computeW_least {fns : List FnTags} {items : List Item} {gw : GcWit}
    (hl : gw.length = fns.length)
    (h : ∀ p ∈ fns.zip gw, leastOk (bodyOf p.1 items) p.2.1 p.2.2 = true) :
    computeW fns items (gw.map (·.1)) = compute fns items := by
  rw [← computeW_witness]
  have hm := mapM_fnMapsW_least hl h
  have hl' : (gw.map (·.1)).length = (witness fns items).length := by simp [witness, hl]
  simp only [computeW, hl']
  simp only [hm]

/-- **What `computeWR` accepts is `compute`'s result**: it refuses every witness that is not its
function's least fixpoint, and on least fixpoints it builds the reference tables. -/
theorem compute_of_computeWR {fns : List FnTags} {items : List Item} {gw : GcWit} {t : Tables}
    (h : computeWR fns items gw = .ok t) : compute fns items = .ok t := by
  by_cases hl : gw.length = fns.length
  · cases hf : (fns.zip gw).zipIdx.find? (fun ((t, (w, r)), _) => !leastOk (bodyOf t items) w r) with
    | some x =>
      obtain ⟨⟨t', _⟩, k⟩ := x
      simp [computeWR, hl, hf, throw, throwThe, MonadExceptOf.throw] at h
    | none =>
      have hall : ∀ p ∈ fns.zip gw, leastOk (bodyOf p.1 items) p.2.1 p.2.2 = true := by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
        have hmem : ((fns.zip gw)[i], i) ∈ (fns.zip gw).zipIdx :=
          List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
        have := List.find?_eq_none.mp hf _ hmem
        simpa using this
      rw [← computeW_least hl hall, ← h, computeWR_eq hl hall]
  · simp [computeWR, hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

end Scc.Cert.Maps
