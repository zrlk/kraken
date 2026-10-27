import WeakCore.TermSlotS
import WeakCore.TermPlantP
import WeakCore.TermPredOne

/-!
# TermPlantR1: the resourceful plant of an affine all-`.one` buffer (R1)

At a plant of a label whose element is affine (not a word buffer), every new slot's share in
memory's holding is paid, key by key, by the debits of the slot's own promises net of their
credits.  The pure parts: `slot_debitsW` (`TermSlotS.slot_debits` with protocol words read at any
message; the blocks stay on first writes) and `chain_tele` (the telescoping of a promise chain's
credits and debits at a word unit).
-/

namespace TermPlantR1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermBlkZ TermSlotS
open WeakMem (Msg Memory Address Ts AllocLabel)

/-- Two distinct members of a pairwise list are related one way or the other. -/
theorem pw_two {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l →
    a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hne
      · exact .inl (h.1 b hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact .inr (h.1 a ha')
      · exact pw_two h.2 ha' hb' hne

/-- **The telescoping of a chain**: the first element plus the rest equals every element but the
last (each one's successor's predecessor) plus the last. -/
theorem chain_tele {α : Type} (f : α → Res) : ∀ (x : α) (xs : List α),
    f x + Res.sum (xs.map f) = Res.sum ((x :: xs).dropLast.map f) + f ((x :: xs).getLast (List.cons_ne_nil x xs))
  | x, [] => by
    show f x + Res.sum [] = Res.sum [] + f x
    exact Res.add_comm _ _
  | x, y :: ys => by
    have ih := chain_tele f y ys
    show f x + Res.sum (f y :: ys.map f) = Res.sum (f x :: (y :: ys).dropLast.map f) + f ((y :: ys).getLast (List.cons_ne_nil y ys))
    rw [Res.sum_cons, Res.sum_cons]
    have ihk := fun k => congrFun ih k
    exact Res.ext fun k => by have := ihk k; simp only [Res.add_apply] at this ⊢; omega

section Debits
variable {E : TEnv} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc} {j : Nat}

/-- **`slot_debits` with protocol words at any message**: a slot value of a closed guarded
all-`.one` element type, read on words `ws` that are first writes at every unit which is not a
protocol word, splits over the slot's units as word parts (`FRes`, at the read words) plus
non-word parts (`BlkDb`, on first writes). -/
theorem slot_debitsW (mem : Memory) (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e)
    (hu : accs e = some us) (hone : ∀ u ∈ us, u = .one) (hpos : 0 < nWords us) (hj : j < N)
    (hCl : Clo e) (hm : mg e = true) {ws : List Word} {Rj : Res} (hl : ws.length = nWords us)
    (hws : ∀ o x, ws[o]? = some x → (∀ n P, ¬ WordAt E ⟨l, j * nWords us + o⟩ n P) →
      ∃ h m, FirstW mem ⟨l, j * nWords us + o⟩ h ∧ mem[h]? = some m ∧ x = mw m)
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
        · have hxo := getElem_take_drop hx
          have hon : o < n := by
            have := lt_of_getElem? hx
            rw [List.length_take] at this
            exact Nat.lt_of_lt_of_le this (Nat.min_le_left _ _)
          -- a unit inside the block is no protocol word: atoms are word-disjoint
          have hnw : ∀ n1 P1, ¬ WordAt E ⟨l, j * nWords us + (i + o)⟩ n1 P1 := by
            intro n1 P1 hW
            have hio : i + o < nWords us := by
              rw [← hl]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hon i) hle
            obtain ⟨hat1, hg1⟩ := (wordAt_iff hc hT hu hj hio).1 hW
            obtain ⟨g1, hg1m, e1⟩ := hinG hat1 ⟨fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩
            obtain ⟨uU, huU, hnU⟩ := wc_some hn
            have hw1 : accs (Ty.word (.lit n1) P1) = some [Acc.one] := by simp [accs, hg1]
            by_cases hge : g1.1 = (i, U)
            · rw [e1] at hge
              simp only [Prod.mk.injEq] at hge
              obtain ⟨-, hU⟩ := hge
              have := hgh _ _ hU.symm
              rw [hg1] at this; cases this
            · have hne : g1.1 ≠ (i, U) := hge
              have hm1 : g1.1 ∈ G.map Prod.fst := List.mem_map.2 ⟨g1, hg1m, rfl⟩
              have hm2 : (i, U) ∈ G.map Prod.fst := List.mem_map.2 ⟨_, hg, rfl⟩
              rw [e1] at hm1 hne
              have h1e : nWords [Acc.one] = 1 := by simp [nWords, Acc.size]
              have h1n : 0 < nWords [Acc.one] := by rw [h1e]; exact Nat.one_pos
              have hpU : 0 < nWords uU := by omega
              rcases pw_two hd hm1 hm2 hne with h | h
              · have := h [Acc.one] uU hw1 huU h1n hpU
                rw [h1e, hnU] at this; simp only at this
                rcases this with h2 | h2
                · exact Nat.not_lt.2 h2 (Nat.lt_succ_of_le (Nat.le_add_right i o))
                · exact Nat.not_le.2 hon (Nat.le_of_add_le_add_left h2)
              · have := h uU [Acc.one] huU hw1 hpU h1n
                rw [h1e, hnU] at this; simp only at this
                rcases this with h2 | h2
                · exact Nat.not_le.2 hon (Nat.le_of_add_le_add_left h2)
                · exact Nat.not_lt.2 h2 (Nat.lt_succ_of_le (Nat.le_add_right i o))
          obtain ⟨h, m, hf, hm1, hx1⟩ := hws (i + o) x hxo hnw
          exact ⟨h, m, by simpa [Nat.add_assoc] using hf, hm1, hx1⟩
    · by_cases hi0 : i = 0
      · subst hi0
        simp only [ite_true]
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

/-- `slot_debitsW` from a slot value (`ValOfR`) of an own-free element type. -/
theorem slot_debitsWV (mem : Memory) (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e)
    (hu : accs e = some us) (hone : ∀ u ∈ us, u = .one) (hpos : 0 < nWords us) (hj : j < N)
    (hCl : Clo e) (hm : mg e = true) (hno : Ty.noOwnIn [] e = true) {ws : List Word} {Rj : Res}
    (hl : ws.length = nWords us)
    (hws : ∀ o x, ws[o]? = some x → (∀ n P, ¬ WordAt E ⟨l, j * nWords us + o⟩ n P) →
      ∃ h m, FirstW mem ⟨l, j * nWords us + o⟩ h ∧ mem[h]? = some m ∧ x = mw m)
    (hv : ValOfR E e ws Rj) :
    ∃ F Z : Nat → Res, Rj = Res.sum ((List.range (nWords us)).map fun i => F i + Z i) ∧
      (∀ i w, ws[i]? = some w → FRes E ⟨l, j * nWords us + i⟩ w (F i)) ∧
      ∀ i, i < nWords us → BlkDb E mem ⟨l, j * nWords us + i⟩ (Z i) :=
  slot_debitsW mem hc hT hu hone hpos hj hCl hm hl hws hv.1 (noOwnR_valOfR hno hv)

end Debits

section RaiseW
open TermPlantR TermPlantS

/-- A bounded predicate that holds somewhere holds at a greatest point. -/
theorem exists_greatest {P : Nat → Prop} {B : Nat} (hb : ∀ n, P n → n < B) :
    ∀ d n, B - n ≤ d → P n → ∃ m, P m ∧ ∀ k, m < k → ¬ P k
  | 0, n, hd, hn => absurd (hb n hn) (by omega)
  | d + 1, n, hd, hn => by
    classical
    by_cases hm : ∃ k, n < k ∧ P k
    · obtain ⟨k, hk, hPk⟩ := hm
      exact exists_greatest hb d k (by omega) hPk
    · exact ⟨n, hn, fun k hk hPk => hm ⟨k, hk, hPk⟩⟩

/-- (R1) **The raise's reading of a new unit** `a`: the latest message at a protocol word unit, the
first write elsewhere. -/
def RdW (E : TEnv) (mem : Memory) (a : Address) (w : Word) : Prop :=
  ∃ h m, mem[h]? = some m ∧ m.loc = a ∧ w = mw m ∧ (¬ WordUnit E a → FirstW mem a h) ∧
    (WordUnit E a → ∀ t m', h < t → mem[t]? = some m' → m'.loc = a → False)

/-- (R1) **One label's entry at the raise, with protocol words**: `TermPlantS.HeldEntry_raiseUR`
for any element (not only word-free ones): a new unit that is a protocol word reads its latest
message (`PromAt` is empty at a visible word unit), every other new unit its first write. -/
theorem HeldEntry_raiseW {E E' : TEnv} {s : St} {l : AllocLabel} {R : Res} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} {Rf : Nat → Res}
    (he : HeldEntry E s l R) (hsl : E'.sto l = E.sto l) (htid : E'.tid = E.tid) (hpf : E'.pfr l = E.pfr l)
    (hfp : E'.fp = E.fp) (hri : E'.rini l = E.rini l)
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hil : E.ini l ≤ E'.ini l) (hN : E'.ini l ≤ N) (hrl : E.rini l ≤ E.ini l) (hpfl : E.pfr l ≠ none)
    (hR1 : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      ∃ h, FirstW s.mem ⟨l, o⟩ h ∧
        ∀ t m', h < t → s.mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ s.promises ++ E.fp)
    (hslot : ∀ j, E.ini l ≤ j → j < E'.ini l → ∀ ws : List Word, ws.length = nWords us →
      (∀ i w, ws[i]? = some w → RdW E' s.mem ⟨l, j * nWords us + i⟩ w) → ValOfR E' e ws (Rf j))
    (hz : ∀ j, nWords us = 0 → Rf j = .zero) :
    HeldEntry E' s l (R + Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf)) := by
  have hc' : E'.sto l = some c := by rw [hsl]; exact hc
  have hrc : E'.rc l = E.rc l := by
    unfold TEnv.rc; rw [hri]; omega
  have hrcE : E.rc l = E.rini l := by unfold TEnv.rc; omega
  have hvis : Vis E l := by
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hpfl; exact Vis_pfr hf
  have hvis' : Vis E' l := (Vis_congr hsl htid hpf).2 hvis
  have hpfl' : E'.pfr l ≠ none := by rw [hpf]; exact hpfl
  have hpa : ∀ o, ¬ (E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us) →
      PromAt E' s ⟨l, o⟩ = PromAt E s ⟨l, o⟩ := by
    intro o ho
    have h1 := Nat.mul_le_mul_right (nWords us) hil
    refine PromAt_congrE hsl htid hpf hfp ?_ ?_
    · rw [IniW_iff hc' hT hu, IniW_iff hc hT hu]; omega
    · rw [IniWr_iff hc' hT hu, IniWr_iff hc hT hu, hrc]
  -- every new unit reads its latest message (a word unit) or its first write (otherwise)
  have hex : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us → ∃ w,
      RdW E' s.mem ⟨l, o⟩ w ∧ LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ w := by
    intro o h1 h2
    obtain ⟨hh, hfw, habove⟩ := hR1 o h1 h2
    obtain ⟨⟨m, hm, hml, -⟩, -⟩ := id hfw
    by_cases hW : WordUnit E' ⟨l, o⟩
    · have hP0 : PromAt E' s ⟨l, o⟩ = [] := PromAt_word ⟨hW, hvis'⟩
      obtain ⟨t, ⟨mt, hmt, hlt⟩, hmax⟩ := exists_greatest
        (P := fun t => ∃ m', s.mem[t]? = some m' ∧ m'.loc = ⟨l, o⟩) (B := s.mem.size)
        (fun t ⟨_, h, _⟩ => TermMem.lt_of_get h) _ hh (Nat.le_refl _) ⟨m, hm, hml⟩
      refine ⟨mw mt, ⟨t, mt, hmt, hlt, rfl, fun h => absurd hW h,
        fun _ t' m' h3 h4 h5 => hmax t' h3 ⟨m', h4, h5⟩⟩, t, mt, ?_, hmt, hlt, rfl, fun t' m' h3 h4 h5 => ?_⟩
      · rw [hP0]; exact List.not_mem_nil
      · exact absurd ⟨m', h4, h5⟩ (hmax t' h3)
    · have hwu' : ¬ VisU E' ⟨l, o⟩ := fun hv' => hW hv'.1
      have hq : PredU E' ⟨l, o⟩ := by
        refine ⟨hpfl', (IniW_iff hc' hT hu).2 h2, fun hr => ?_⟩
        rw [IniWr_iff hc' hT hu, hrc, hrcE] at hr
        have := Nat.mul_le_mul_right (nWords us) hrl; omega
      refine ⟨mw m, ⟨hh, m, hm, hml, rfl, fun _ => hfw, fun h => absurd h hW⟩, hh, m, ?_, hm, hml, rfl,
        fun t' m' hlt hm' hl' => ?_⟩
      · rw [mem_PromAt_pred hwu' hq]
        rintro ⟨-, h', hf', hlt'⟩
        rw [FirstW_uniq hf' hfw] at hlt'; exact Nat.lt_irrefl _ hlt'
      · rw [mem_PromAt_pred hwu' hq, FpAt_vis hvis', hfp]
        exact ⟨habove t' m' hlt hm' hl', hh, hfw, hlt⟩
  let f : Nat → Word := fun o =>
    if hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us then
      Classical.choose (hex o hh.1 hh.2)
    else default
  have hf : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      RdW E' s.mem ⟨l, o⟩ (f o) ∧ LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (f o) := by
    intro o h1 h2
    have hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us := ⟨h1, h2⟩
    have a1 := Classical.choose_spec (hex o h1 h2)
    simp only [f, hh, and_self, dite_true]
    exact a1
  exact HeldEntry_raise (Rf := Rf) (f := f) he hc hc' hT hu hv hil hN hrc hpa
    (fun o h1 h2 => (hf o h1 h2).2)
    (fun j _ _ h0 => hz j h0)
    (fun j hj1 hj2 => by
      refine hslot j hj1 hj2 _ (by simp) (fun i w hw => ?_)
      rw [List.getElem?_map] at hw
      by_cases hi : i < nWords us
      · rw [List.getElem?_range hi, Option.map_some, Option.some.injEq] at hw
        subst hw
        have h1 : E.ini l * nWords us ≤ j * nWords us := Nat.mul_le_mul_right _ hj1
        have h2 : (j + 1) * nWords us ≤ E'.ini l * nWords us := Nat.mul_le_mul_right _ hj2
        rw [Nat.succ_mul] at h2
        exact (hf (j * nWords us + i) (Nat.le_trans h1 (Nat.le_add_right _ _))
          (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) h2)).1
      · have h0 : (List.range (nWords us))[i]? = none :=
          List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hi)
        rw [h0] at hw; cases hw)


/-- (R1, pins) `TermPlantR.BufOKR_raise` along the slot list: the new slots are appended. -/
theorem BufR_raise {E E' : TEnv} {n n' nr N : Nat} {e : Ty} {us : List Acc} {T : Ty}
    {vals vals' : List Word} {Rs : List Res} {Rf : Nat → Res}
    (h : BufR E n nr T vals Rs) (hT : T = .array (.lit N) e) (hu : accs e = some us)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hnn : n ≤ n') (hn' : n' ≤ N) (hlen : vals'.length = vals.length)
    (hpre : ∀ o, o < n * nWords us → vals'[o]? = vals[o]?)
    (hz : ∀ j, n ≤ j → j < n' → nWords us = 0 → Rf j = .zero)
    (hslot : ∀ j, n ≤ j → j < n' → ValOfR E' e (slotW vals' j (nWords us)) (Rf j)) :
    BufR E' n' nr T vals' (Rs ++ (List.range' n (n' - n)).map Rf) := by
  obtain ⟨N0, e0, us0, hT0, hu0, -, hl, hRs, hj⟩ := h
  rw [hT] at hT0; cases hT0
  rw [hu] at hu0; cases hu0
  refine ⟨N, e, us, hT, hu, hn', by rw [hlen]; exact hl,
    by simp only [List.length_append, List.length_map, List.length_range']; omega, fun j Rj hjn hRj => ?_⟩
  by_cases hjo : j < n
  · rw [List.getElem?_append_left (by omega)] at hRj
    have := hj j Rj hjo hRj
    refine slotR_imp this rfl (fun hb => ?_)
    rw [show (vals'.drop (j * nWords us)).take (nWords us) = slotW vals' j (nWords us) from rfl,
      slotW_congr hjo hpre]
    exact hv hb
  · rw [List.getElem?_append_right (by omega), List.getElem?_map, List.getElem?_range' (by omega)] at hRj
    simp only [Option.map_some, Option.some.injEq] at hRj
    subst hRj
    have e1 : n + 1 * (j - Rs.length) = j := by omega
    rw [e1]
    exact ⟨fun _ h0 => hz j (by omega) hjn h0, fun _ => hslot j (by omega) hjn⟩

/-- (R1, pins) `TermPlantR.HeldEntry_raise` along the slot list: the new slots' shares are
appended to label `l`'s list. -/
theorem HeldEntryL_raise {E E' : TEnv} {s : St} {l : AllocLabel} {Rs : List Res} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} {f : Nat → Word} {Rf : Nat → Res}
    (h : HeldEntryL E s l Rs) (hc : E.sto l = some c) (hc' : E'.sto l = some c)
    (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hini : E.ini l ≤ E'.ini l) (hN : E'.ini l ≤ N) (hrc : E'.rc l = E.rc l)
    (hpa : ∀ o, ¬ (E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us) →
      PromAt E' s ⟨l, o⟩ = PromAt E s ⟨l, o⟩)
    (hf : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (f o))
    (hz : ∀ j, E.ini l ≤ j → j < E'.ini l → nWords us = 0 → Rf j = .zero)
    (hslot : ∀ j, E.ini l ≤ j → j < E'.ini l →
      ValOfR E' e ((List.range (nWords us)).map fun i => f (j * nWords us + i)) (Rf j)) :
    HeldEntryL E' s l (Rs ++ (List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf) := by
  obtain ⟨-, hent⟩ := h
  obtain ⟨vals, hrd, hok⟩ := hent c hc
  have hb : BufR E (E.ini l) (E.rc l) c.ty vals Rs := by
    rcases hok with ⟨hw, -⟩ | hb
    · rw [hT] at hw; simp [wc, accs] at hw
    · exact hb
  have hl : vals.length = N * nWords us := by
    obtain ⟨N0, e0, us0, hT0, hu0, _, hl, _⟩ := hb
    rw [hT] at hT0; cases hT0; rw [hu] at hu0; cases hu0; exact hl
  have hiN' : E'.ini l * nWords us ≤ N * nWords us := Nat.mul_le_mul_right _ hN
  let g : Nat → Word := fun o =>
    if E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us then f o else vals.getD o (f o)
  have hg : ∀ o, o < N * nWords us → LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (g o) := by
    intro o ho
    by_cases hn : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us
    · simp only [g, hn, and_self, ite_true]; exact hf o hn.1 hn.2
    · simp only [g, hn, ite_false]
      have hlt : o < vals.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, hpa o hn]
      exact hrd o vals[o] (List.getElem?_eq_getElem hlt)
  refine ⟨fun h0 => (by rw [hc'] at h0; cases h0), fun c' hc'' => ?_⟩
  rw [hc'] at hc''; cases hc''
  refine ⟨(List.range (N * nWords us)).map g, fun o w hw => ?_, Or.inr ?_⟩
  · rw [List.getElem?_map] at hw
    by_cases ho : o < N * nWords us
    · rw [List.getElem?_range ho] at hw; cases hw; exact hg o ho
    · have h0 : (List.range (N * nWords us))[o]? = none :=
        List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt ho)
      rw [h0] at hw; cases hw
  · rw [hrc]
    refine BufR_raise (Rf := Rf) hb hT hu hv hini hN (by simp [hl]) (fun o ho => ?_) hz (fun j hj1 hj2 => ?_)
    · have hn : ¬ (E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us) := fun h => by omega
      have hlt : o < vals.length := by
        have := Nat.mul_le_mul_right (nWords us) hini; omega
      rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some, List.getElem?_eq_getElem hlt]
      simp only [g, hn, ite_false, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    · have hjk : (j + 1) * nWords us ≤ N * nWords us :=
        Nat.le_trans (Nat.mul_le_mul_right _ hj2) hiN'
      rw [slotW_map_range hjk]
      have e1 : (List.range (nWords us)).map (fun i => g (j * nWords us + i)) =
          (List.range (nWords us)).map (fun i => f (j * nWords us + i)) := by
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        have h1 : E.ini l * nWords us ≤ j * nWords us := Nat.mul_le_mul_right _ hj1
        have h2 : (j + 1) * nWords us ≤ E'.ini l * nWords us := Nat.mul_le_mul_right _ hj2
        rw [Nat.succ_mul] at h2
        have hn : E.ini l * nWords us ≤ j * nWords us + i ∧ j * nWords us + i < E'.ini l * nWords us :=
          ⟨by omega, by omega⟩
        simp only [g, hn, and_self, ite_true]
      rw [e1]; exact hslot j hj1 hj2

/-- (R1, pins) `HeldEntry_raiseW` along the slot list. -/
theorem HeldEntryL_raiseW {E E' : TEnv} {s : St} {l : AllocLabel} {Rs : List Res} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} {Rf : Nat → Res}
    (he : HeldEntryL E s l Rs) (hsl : E'.sto l = E.sto l) (htid : E'.tid = E.tid) (hpf : E'.pfr l = E.pfr l)
    (hfp : E'.fp = E.fp) (hri : E'.rini l = E.rini l)
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hil : E.ini l ≤ E'.ini l) (hN : E'.ini l ≤ N) (hrl : E.rini l ≤ E.ini l) (hpfl : E.pfr l ≠ none)
    (hR1 : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      ∃ h, FirstW s.mem ⟨l, o⟩ h ∧
        ∀ t m', h < t → s.mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ s.promises ++ E.fp)
    (hslot : ∀ j, E.ini l ≤ j → j < E'.ini l → ∀ ws : List Word, ws.length = nWords us →
      (∀ i w, ws[i]? = some w → RdW E' s.mem ⟨l, j * nWords us + i⟩ w) → ValOfR E' e ws (Rf j))
    (hz : ∀ j, nWords us = 0 → Rf j = .zero) :
    HeldEntryL E' s l (Rs ++ (List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf) := by
  have hc' : E'.sto l = some c := by rw [hsl]; exact hc
  have hrc : E'.rc l = E.rc l := by
    unfold TEnv.rc; rw [hri]; omega
  have hrcE : E.rc l = E.rini l := by unfold TEnv.rc; omega
  have hvis : Vis E l := by
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hpfl; exact Vis_pfr hf
  have hvis' : Vis E' l := (Vis_congr hsl htid hpf).2 hvis
  have hpfl' : E'.pfr l ≠ none := by rw [hpf]; exact hpfl
  have hpa : ∀ o, ¬ (E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us) →
      PromAt E' s ⟨l, o⟩ = PromAt E s ⟨l, o⟩ := by
    intro o ho
    have h1 := Nat.mul_le_mul_right (nWords us) hil
    refine PromAt_congrE hsl htid hpf hfp ?_ ?_
    · rw [IniW_iff hc' hT hu, IniW_iff hc hT hu]; omega
    · rw [IniWr_iff hc' hT hu, IniWr_iff hc hT hu, hrc]
  -- every new unit reads its latest message (a word unit) or its first write (otherwise)
  have hex : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us → ∃ w,
      RdW E' s.mem ⟨l, o⟩ w ∧ LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ w := by
    intro o h1 h2
    obtain ⟨hh, hfw, habove⟩ := hR1 o h1 h2
    obtain ⟨⟨m, hm, hml, -⟩, -⟩ := id hfw
    by_cases hW : WordUnit E' ⟨l, o⟩
    · have hP0 : PromAt E' s ⟨l, o⟩ = [] := PromAt_word ⟨hW, hvis'⟩
      obtain ⟨t, ⟨mt, hmt, hlt⟩, hmax⟩ := exists_greatest
        (P := fun t => ∃ m', s.mem[t]? = some m' ∧ m'.loc = ⟨l, o⟩) (B := s.mem.size)
        (fun t ⟨_, h, _⟩ => TermMem.lt_of_get h) _ hh (Nat.le_refl _) ⟨m, hm, hml⟩
      refine ⟨mw mt, ⟨t, mt, hmt, hlt, rfl, fun h => absurd hW h,
        fun _ t' m' h3 h4 h5 => hmax t' h3 ⟨m', h4, h5⟩⟩, t, mt, ?_, hmt, hlt, rfl, fun t' m' h3 h4 h5 => ?_⟩
      · rw [hP0]; exact List.not_mem_nil
      · exact absurd ⟨m', h4, h5⟩ (hmax t' h3)
    · have hwu' : ¬ VisU E' ⟨l, o⟩ := fun hv' => hW hv'.1
      have hq : PredU E' ⟨l, o⟩ := by
        refine ⟨hpfl', (IniW_iff hc' hT hu).2 h2, fun hr => ?_⟩
        rw [IniWr_iff hc' hT hu, hrc, hrcE] at hr
        have := Nat.mul_le_mul_right (nWords us) hrl; omega
      refine ⟨mw m, ⟨hh, m, hm, hml, rfl, fun _ => hfw, fun h => absurd h hW⟩, hh, m, ?_, hm, hml, rfl,
        fun t' m' hlt hm' hl' => ?_⟩
      · rw [mem_PromAt_pred hwu' hq]
        rintro ⟨-, h', hf', hlt'⟩
        rw [FirstW_uniq hf' hfw] at hlt'; exact Nat.lt_irrefl _ hlt'
      · rw [mem_PromAt_pred hwu' hq, FpAt_vis hvis', hfp]
        exact ⟨habove t' m' hlt hm' hl', hh, hfw, hlt⟩
  let f : Nat → Word := fun o =>
    if hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us then
      Classical.choose (hex o hh.1 hh.2)
    else default
  have hf : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      RdW E' s.mem ⟨l, o⟩ (f o) ∧ LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (f o) := by
    intro o h1 h2
    have hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us := ⟨h1, h2⟩
    have a1 := Classical.choose_spec (hex o h1 h2)
    simp only [f, hh, and_self, dite_true]
    exact a1
  exact HeldEntryL_raise (Rf := Rf) (f := f) he hc hc' hT hu hv hil hN hrc hpa
    (fun o h1 h2 => (hf o h1 h2).2)
    (fun j _ _ h0 => hz j h0)
    (fun j hj1 hj2 => by
      refine hslot j hj1 hj2 _ (by simp) (fun i w hw => ?_)
      rw [List.getElem?_map] at hw
      by_cases hi : i < nWords us
      · rw [List.getElem?_range hi, Option.map_some, Option.some.injEq] at hw
        subst hw
        have h1 : E.ini l * nWords us ≤ j * nWords us := Nat.mul_le_mul_right _ hj1
        have h2 : (j + 1) * nWords us ≤ E'.ini l * nWords us := Nat.mul_le_mul_right _ hj2
        rw [Nat.succ_mul] at h2
        exact (hf (j * nWords us + i) (Nat.le_trans h1 (Nat.le_add_right _ _))
          (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) h2)).1
      · have h0 : (List.range (nWords us))[i]? = none :=
          List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hi)
        rw [h0] at hw; cases hw)

end RaiseW

section Tele

/-- Message `t` of `mem` is at address `a`. -/
def AtB (mem : Memory) (a : Address) (t : Nat) : Bool := decide (∃ m, mem[t]? = some m ∧ m.loc = a)

theorem AtB_iff {mem : Memory} {a : Address} {t : Nat} : AtB mem a t = true ↔ ∃ m, mem[t]? = some m ∧ m.loc = a := by
  unfold AtB; exact decide_eq_true_iff

/-- A sum over the members below `B + 1` of a list without `B` is the sum below `B`. -/
theorem sum_filter_succN {f : Nat → Res} {B : Nat} : ∀ {L : List Nat}, B ∉ L →
    Res.sum ((L.filter fun t => decide (t < B + 1)).map f) = Res.sum ((L.filter fun t => decide (t < B)).map f)
  | [], _ => rfl
  | x :: L, hB => by
    have hxB : x ≠ B := fun e => hB (e ▸ List.mem_cons_self)
    have ih := sum_filter_succN (f := f) (fun h => hB (List.mem_cons_of_mem _ h))
    simp only [List.filter_cons]
    rcases Nat.lt_or_ge x B with hx | hx
    · rw [if_pos (decide_eq_true (Nat.lt_succ_of_lt hx)), if_pos (decide_eq_true hx), List.map_cons,
        List.map_cons, Res.sum_cons, Res.sum_cons, ih]
    · have h1 : ¬ x < B + 1 := fun h => hxB (Nat.le_antisymm (Nat.le_of_lt_succ h) hx)
      have h2 : ¬ x < B := Nat.not_lt.2 hx
      rw [if_neg (fun h => h1 (of_decide_eq_true h)), if_neg (fun h => h2 (of_decide_eq_true h)), ih]

/-- A sum over the members below `B + 1` of a duplicate-free list with `B` is the sum below `B`
and the `B` term. -/
theorem sum_filter_succM {f : Nat → Res} {B : Nat} : ∀ {L : List Nat}, L.Nodup → B ∈ L →
    Res.sum ((L.filter fun t => decide (t < B + 1)).map f) =
      Res.sum ((L.filter fun t => decide (t < B)).map f) + f B
  | [], _, hB => absurd hB List.not_mem_nil
  | x :: L, hnd, hB => by
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons]
    rcases Nat.lt_trichotomy x B with hx | hx | hx
    · have hBL : B ∈ L := (List.mem_cons.1 hB).resolve_left (fun e => Nat.lt_irrefl _ (e ▸ hx))
      rw [if_pos (decide_eq_true (Nat.lt_succ_of_lt hx)), if_pos (decide_eq_true hx), List.map_cons,
        List.map_cons, Res.sum_cons, Res.sum_cons, sum_filter_succM hnd.2 hBL, Res.add_assoc]
    · subst hx
      rw [if_pos (decide_eq_true (Nat.lt_succ_self x)), if_neg (fun h => Nat.lt_irrefl x (of_decide_eq_true h)),
        List.map_cons, Res.sum_cons, sum_filter_succN hnd.1, Res.add_comm]
    · have hBL : B ∈ L := (List.mem_cons.1 hB).resolve_left (fun e => Nat.lt_irrefl _ (e ▸ hx))
      have h1 : ¬ x < B + 1 := fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hx (Nat.le_of_lt_succ h))
      have h2 : ¬ x < B := fun h => Nat.lt_asymm h hx
      rw [if_neg (fun h => h1 (of_decide_eq_true h)), if_neg (fun h => h2 (of_decide_eq_true h)),
        sum_filter_succM hnd.2 hBL]

/-- **The telescoping of a unit's promise chain**: at an address holding one message `t0` (not a
promise) below promises only, the debits `d` (each promise's own term `φ`, plus `K` at the first
write `h1`) sum to the credits `c` (each promise's predecessor's term) plus the latest message's
term and `K`. -/
theorem unit_tele {mem : Memory} {a : Address} {P : List Nat} (hnd : P.Nodup) {t0 h1 : Nat}
    {φ d c : Nat → Res} {K : Res}
    (h0 : ∃ m, mem[t0]? = some m ∧ m.loc = a) (h0P : t0 ∉ P)
    (hall : ∀ t m, mem[t]? = some m → m.loc = a → t ≠ t0 → t0 < t ∧ t ∈ P)
    (hφ0 : φ t0 = .zero) (hh1 : ∃ m, mem[h1]? = some m ∧ m.loc = a) (hh1n : h1 ≠ t0)
    (hd : ∀ t, t ∈ P → (∃ m, mem[t]? = some m ∧ m.loc = a) → d t = φ t + (if t = h1 then K else .zero))
    (hc : ∀ t, t ∈ P → (∃ m, mem[t]? = some m ∧ m.loc = a) → ∀ t', t' < t →
      (∃ m, mem[t']? = some m ∧ m.loc = a) →
      (∀ t'', t' < t'' → t'' < t → ¬ ∃ m, mem[t'']? = some m ∧ m.loc = a) → c t = φ t') :
    ∃ top, (∃ m, mem[top]? = some m ∧ m.loc = a) ∧
      (∀ t m, top < t → mem[t]? = some m → m.loc = a → False) ∧
      Res.sum ((P.filter (AtB mem a)).map d) = Res.sum ((P.filter (AtB mem a)).map c) + φ top + K := by
  have hnd' : (P.filter (AtB mem a)).Nodup := hnd.filter _
  have hmemP : ∀ t, t ∈ P.filter (AtB mem a) ↔ t ∈ P ∧ ∃ m, mem[t]? = some m ∧ m.loc = a := fun t => by
    rw [List.mem_filter, AtB_iff]
  have ht0h1 : t0 < h1 := by
    obtain ⟨m, hm, hl⟩ := hh1; exact (hall h1 m hm hl hh1n).1
  have key : ∀ n, ∃ top, top < t0 + 1 + n ∧ (∃ m, mem[top]? = some m ∧ m.loc = a) ∧
      (∀ t'', top < t'' → t'' < t0 + 1 + n → ¬ ∃ m, mem[t'']? = some m ∧ m.loc = a) ∧
      Res.sum (((P.filter (AtB mem a)).filter fun t => decide (t < t0 + 1 + n)).map d) =
        Res.sum (((P.filter (AtB mem a)).filter fun t => decide (t < t0 + 1 + n)).map c) + φ top +
          (if h1 < t0 + 1 + n then K else .zero) := by
    intro n
    induction n with
    | zero =>
      have hnil : ((P.filter (AtB mem a)).filter fun t => decide (t < t0 + 1 + 0)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro t ht hlt
        obtain ⟨htP, m, hm, hl⟩ := (hmemP t).1 ht
        have hne : t ≠ t0 := fun e => h0P (e ▸ htP)
        have h3 : t0 < t := (hall t m hm hl hne).1
        have h4 : t < t0 + 1 + 0 := of_decide_eq_true hlt
        omega
      have hh : ¬ h1 < t0 + 1 + 0 := by omega
      refine ⟨t0, by omega, h0, fun t'' h1' h2' => absurd h2' (by omega), ?_⟩
      rw [hnil, if_neg hh, hφ0]; rfl
    | succ n ih =>
      obtain ⟨top, htop, hat, hgap, hsum⟩ := ih
      have e1 : t0 + 1 + (n + 1) = (t0 + 1 + n) + 1 := by omega
      rw [e1]
      by_cases hB : ∃ m, mem[t0 + 1 + n]? = some m ∧ m.loc = a
      · have hne : t0 + 1 + n ≠ t0 := by omega
        obtain ⟨m, hm, hl⟩ := hB
        have hBP : t0 + 1 + n ∈ P := (hall _ m hm hl hne).2
        have hBm : t0 + 1 + n ∈ P.filter (AtB mem a) := (hmemP _).2 ⟨hBP, m, hm, hl⟩
        rw [sum_filter_succM hnd' hBm, sum_filter_succM hnd' hBm, hd _ hBP ⟨m, hm, hl⟩,
          hc _ hBP ⟨m, hm, hl⟩ top htop hat hgap]
        refine ⟨t0 + 1 + n, by omega, ⟨m, hm, hl⟩, fun t'' a1 a2 => absurd a2 (by omega), ?_⟩
        rw [hsum]
        refine Res.ext fun k => ?_
        simp only [Res.add_apply]
        rcases Nat.lt_trichotomy h1 (t0 + 1 + n) with hl1 | hl1 | hl1
        · have q1 : h1 < t0 + 1 + n + 1 := Nat.lt_succ_of_lt hl1
          have q2 : t0 + 1 + n ≠ h1 := Nat.ne_of_gt hl1
          rw [if_pos hl1, if_pos q1, if_neg q2]
          simp only [Res.zero_apply]; omega
        · subst hl1
          rw [if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self _), if_pos rfl]
          simp only [Res.zero_apply]; omega
        · have q1 : ¬ h1 < t0 + 1 + n := Nat.not_lt_of_gt hl1
          have q2 : ¬ h1 < t0 + 1 + n + 1 := fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hl1 (Nat.le_of_lt_succ h))
          have q3 : t0 + 1 + n ≠ h1 := Nat.ne_of_lt hl1
          rw [if_neg q1, if_neg q2, if_neg q3]
          simp only [Res.zero_apply]; omega
      · have hBm : t0 + 1 + n ∉ P.filter (AtB mem a) := fun h => hB ((hmemP _).1 h).2
        have hh1B : h1 ≠ t0 + 1 + n := fun e => hB (e ▸ hh1)
        rw [sum_filter_succN hBm, sum_filter_succN hBm]
        refine ⟨top, by omega, hat, fun t'' a1 a2 => ?_, ?_⟩
        · rcases Nat.lt_or_ge t'' (t0 + 1 + n) with h | h
          · exact hgap t'' a1 h
          · have : t'' = t0 + 1 + n := Nat.le_antisymm (Nat.le_of_lt_succ a2) h
            subst this; exact hB
        · rw [hsum]
          by_cases hlt : h1 < t0 + 1 + n
          · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
          · have q : ¬ h1 < t0 + 1 + n + 1 := fun h => hlt (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hh1B)
            rw [if_neg hlt, if_neg q]
  obtain ⟨top, htop, hat, hgap, hsum⟩ := key mem.size
  have hall' : ((P.filter (AtB mem a)).filter fun t => decide (t < t0 + 1 + mem.size)) = P.filter (AtB mem a) := by
    rw [List.filter_eq_self]
    intro t ht
    obtain ⟨-, m, hm, -⟩ := (hmemP t).1 ht
    have h3 : t < mem.size := TermMem.lt_of_get hm
    exact decide_eq_true (by omega)
  have hh1s : h1 < t0 + 1 + mem.size := by
    obtain ⟨m, hm, -⟩ := hh1
    have h3 : h1 < mem.size := TermMem.lt_of_get hm
    omega
  rw [hall', if_pos hh1s] at hsum
  refine ⟨top, hat, fun t m h1' hm hl => ?_, hsum⟩
  have h3 : t < mem.size := TermMem.lt_of_get hm
  exact hgap t h1' (by omega) ⟨m, hm, hl⟩

end Tele

section UnitPay
open TermPlantR
attribute [local instance 10] Classical.propDecidable

/-- The protocol-word term of value `v` at unit `a` (nothing off protocol words). -/
noncomputable def wvE (E : TEnv) (a : Address) (v : WeakMem.Val) : Res :=
  if h : ∃ n P, WordAt E a n P then wr (Classical.choose (Classical.choose_spec h)) (Classical.choose h) v
  else .zero

/-- The word-debt term at unit `a` (nothing off protocol words). -/
noncomputable def wdE (E : TEnv) (a : Address) : Res :=
  if h : ∃ n P, WordAt E a n P then wdW (Classical.choose (Classical.choose_spec h)) (Classical.choose h)
  else .zero

theorem FRes_wv (E : TEnv) (a : Address) (w : Word) : FRes E a w (wvE E a w.val + wdE E a) := by
  by_cases h : ∃ n P, WordAt E a n P
  · refine Or.inl ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
      Classical.choose_spec (Classical.choose_spec h), ?_⟩
    rw [wvE, wdE, dif_pos h, dif_pos h]
  · refine Or.inr ⟨fun n P hw => h ⟨n, P, hw⟩, ?_⟩
    rw [wvE, wdE, dif_neg h, dif_neg h, Res.add_zero]

theorem FRes_eq_wv {E : TEnv} {a : Address} {w : Word} {R : Res} (h : FRes E a w R) :
    R = wvE E a w.val + wdE E a := by
  rcases h with ⟨n, P, hw, rfl⟩ | ⟨hn, rfl⟩
  · have hh : ∃ n P, WordAt E a n P := ⟨n, P, hw⟩
    have hw' := Classical.choose_spec (Classical.choose_spec hh)
    rw [wvE, wdE, dif_pos hh, dif_pos hh]
    generalize Classical.choose (Classical.choose_spec hh) = P' at hw' ⊢
    generalize Classical.choose hh = n' at hw' ⊢
    obtain ⟨rfl, rfl⟩ := WordAt_uniq hw hw'
    rfl
  · have hh : ¬ ∃ n P, WordAt E a n P := fun ⟨n, P, hw⟩ => hn n P hw
    rw [wvE, wdE, dif_neg hh, dif_neg hh, Res.add_zero]

theorem WRes_wv (E : TEnv) (a : Address) (w : Word) : WRes E a w (wvE E a w.val) := by
  by_cases h : ∃ n P, WordAt E a n P
  · rw [wvE, dif_pos h]; exact WRes_wr (Classical.choose_spec (Classical.choose_spec h)) w
  · rw [wvE, dif_neg h]; exact Or.inr ⟨fun n P hw => absurd ⟨n, P, hw⟩ h, rfl⟩

theorem wvE_undef (E : TEnv) (a : Address) : wvE E a .undef = .zero := by
  unfold wvE
  split
  · unfold wr
    rw [if_neg]
    rintro ⟨-, n, c, cl, k, hv, -⟩
    cases hv
  · rfl

/-- The debit of a promise at a new unit: its word term, plus (at the first write) the word debt and
(where it is designated) the unit's block debt `Zf`. -/
noncomputable def newDb (E : TEnv) (mem : Memory) (Zf : Address → Res) (t : Nat) : Res :=
  match mem[t]? with
  | some m => if InitAt mem m.loc t then
      wvE E m.loc m.val + (wdE E m.loc + if DesigAt E mem m.loc t then Zf m.loc else .zero)
    else wvE E m.loc m.val
  | none => .zero

/-- The credit of a promise at a new unit: its predecessor's word term. -/
noncomputable def newCr (E : TEnv) (mem : Memory) (t : Nat) : Res :=
  match mem[t]? with
  | some m => if h : ∃ w, PredAt mem m.loc t w then wvE E m.loc (Classical.choose h).val else .zero
  | none => .zero

theorem newDb_res {E : TEnv} {mem : Memory} {Zf : Address → Res} {t : Nat} {m : Msg} (hm : mem[t]? = some m)
    (hvi : Vis E m.loc.label ∧ IniW E m.loc) (hZ : DesigAt E mem m.loc t → BlkDb E mem m.loc (Zf m.loc)) :
    DbRes E mem m t (newDb E mem Zf t) := by
  refine Or.inl ⟨hvi.1, hvi.2, fun hI => ?_, fun hI => ?_⟩
  · refine ⟨_, if DesigAt E mem m.loc t then Zf m.loc else .zero, FRes_wv E m.loc (mw m),
      fun hD => by rw [if_pos hD]; exact hZ hD, fun hD => by rw [if_neg hD], ?_⟩
    simp only [newDb, hm, if_pos hI]
    exact (Res.add_assoc _ _ _).symm
  · simp only [newDb, hm, if_neg hI]
    exact WRes_wv E m.loc (mw m)

theorem newCr_res {E : TEnv} {mem : Memory} {t : Nat} {m : Msg} (hm : mem[t]? = some m)
    (hvi : Vis E m.loc.label ∧ IniW E m.loc) :
    (∃ w, PredAt mem m.loc t w ∧ VRes E m.loc w (newCr E mem t)) ∨
      ((∀ w, ¬ PredAt mem m.loc t w) ∧ newCr E mem t = .zero) := by
  by_cases h : ∃ w, PredAt mem m.loc t w
  · refine Or.inl ⟨Classical.choose h, Classical.choose_spec h, Or.inl ⟨hvi.1, hvi.2, ?_⟩⟩
    simp only [newCr, hm, dif_pos h]
    exact WRes_wv E m.loc _
  · refine Or.inr ⟨fun w hw => h ⟨w, hw⟩, ?_⟩
    simp only [newCr, hm, dif_neg h]

theorem wvE_noAt {E : TEnv} {a : Address} (h : ∀ n P, ¬ WordAt E a n P) (v : WeakMem.Val) : wvE E a v = .zero := by
  unfold wvE; rw [dif_neg (fun ⟨n, P, hw⟩ => h n P hw)]

theorem wdE_noAt {E : TEnv} {a : Address} (h : ∀ n P, ¬ WordAt E a n P) : wdE E a = .zero := by
  unfold wdE; rw [dif_neg (fun ⟨n, P, hw⟩ => h n P hw)]

/-- At a unit with no protocol word, a promise's new debit (with no block debt there) is nothing. -/
theorem newDb_zero {E : TEnv} {mem : Memory} {Zf : Address → Res} {t : Nat} {m : Msg} (hm : mem[t]? = some m)
    (h : ∀ n P, ¬ WordAt E m.loc n P) (hZ : Zf m.loc = .zero) : newDb E mem Zf t = .zero := by
  simp only [newDb, hm, wvE_noAt h, wdE_noAt h, hZ, ite_self, Res.add_zero]

/-- At a unit with no protocol word, a promise's new credit is nothing. -/
theorem newCr_zero {E : TEnv} {mem : Memory} {t : Nat} {m : Msg} (hm : mem[t]? = some m)
    (h : ∀ n P, ¬ WordAt E m.loc n P) : newCr E mem t = .zero := by
  simp only [newCr, hm, wvE_noAt h, dite_eq_ite, ite_self]

theorem noOwnR_zero : noOwnR (Res.zero + Res.zero) = Res.zero := by
  refine Res.ext fun k => ?_
  cases k <;> rfl

/-- Off a designated start (at an own cell) a block debt is nothing. -/
theorem blkDb_nstart {E : TEnv} {mem : Memory} {a : Address} {Z : Res} (h : BlkDb E mem a Z)
    (hn : ¬ ((∃ U, BlkStart E a U) ∨ SlotStart E a)) : Z = .zero := by
  obtain ⟨Zb, Zz, hb, hz, rfl⟩ := h
  rcases hb with ⟨U, -, -, hU, -⟩ | ⟨-, rfl⟩
  · exact absurd (Or.inl ⟨U, hU⟩) hn
  rcases hz with ⟨hS, -⟩ | ⟨-, rfl⟩
  · exact absurd (Or.inr hS) hn
  exact noOwnR_zero

/-- **A new unit's promises pay its share**: at a unit shaped by R1w (a placeholder below own
promises only), the new debits of its promises are its new credits plus the latest message's
`FRes` term and its block debt. -/
theorem unit_pay {E : TEnv} {mem : Memory} {P : List Nat} {a : Address} {Zf : Address → Res}
    (hnd : P.Nodup)
    (hR : ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = a ∧ m0.val = .undef ∧ t0 ∉ P ∧ (∃ t, AtA mem a t0 t = true) ∧
      ∀ t m, mem[t]? = some m → m.loc = a → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ P)
    (hq : PredU E a) (hown : ∃ c, E.sto a.label = some c ∧ c.owner = some E.tid)
    (hZ : BlkDb E mem a (Zf a)) :
    ∃ (top : Nat) (mt : Msg), mem[top]? = some mt ∧ mt.loc = a ∧
      (∀ (t : Nat) (m : Msg), top < t → mem[t]? = some m → m.loc = a → False) ∧
      Res.sum ((P.filter (AtB mem a)).map (newDb E mem Zf)) =
        Res.sum ((P.filter (AtB mem a)).map (newCr E mem)) + (wvE E a mt.val + wdE E a) + Zf a := by
  obtain ⟨h1, hfw, -, -⟩ := TermPlantS.firstW_of_R1w hR
  obtain ⟨t0, m0, hm0, hl0, hv0, h0P, -, hall⟩ := hR
  obtain ⟨⟨m1, hm1, hl1, hv1⟩, hbelow⟩ := id hfw
  have hh1n : h1 ≠ t0 := fun e => by rw [e, hm0] at hm1; cases hm1; exact hv1 hv0
  -- the first write is the least message above the placeholder
  have hmin : ∀ t m, mem[t]? = some m → m.loc = a → t ≠ t0 → h1 ≤ t := fun t m hm hl hne =>
    Nat.le_of_not_lt fun hlt => (hall t m hm hl hne).2.1 (hbelow t m hlt hm hl)
  let φ : Nat → Res := fun t => match mem[t]? with
    | some m => wvE E a m.val
    | none => .zero
  have hφ : ∀ t m, mem[t]? = some m → φ t = wvE E a m.val := fun t m hm => by
    simp only [φ, hm]
  have hDz : ¬ DesigAt E mem a h1 → Zf a = .zero := fun hD => by
    refine blkDb_nstart hZ fun hs => hD ⟨hq, ⟨hown, hs⟩, hfw⟩
  obtain ⟨top, ⟨mt, hmt, hlt⟩, hmax, hsum⟩ := unit_tele (P := P) (mem := mem) (a := a) (t0 := t0) (h1 := h1)
    (φ := φ) (d := newDb E mem Zf) (c := newCr E mem) (K := wdE E a + Zf a) hnd ⟨m0, hm0, hl0⟩ h0P
    (fun t m hm hl hne => ⟨(hall t m hm hl hne).1, (hall t m hm hl hne).2.2⟩)
    (by rw [hφ t0 m0 hm0, hv0]; exact wvE_undef E a) ⟨m1, hm1, hl1⟩ hh1n
    (fun t htP ⟨m, hm, hl⟩ => by
      rw [hφ t m hm]
      simp only [newDb, hm, hl]
      by_cases e : t = h1
      · subst e
        rw [if_pos (FirstW_initAt hfw), if_pos rfl]
        by_cases hD : DesigAt E mem a t
        · rw [if_pos hD]
        · rw [if_neg hD, hDz hD]
      · rw [if_neg e, Res.add_zero]
        have hne0 : t ≠ t0 := fun e0 => h0P (e0 ▸ htP)
        have hlt1 : h1 < t := Nat.lt_of_le_of_ne (hmin t m hm hl hne0) (Ne.symm e)
        rw [if_neg]
        intro hI
        -- the latest message below `t` is at or above the first write: not the placeholder
        obtain ⟨t', ⟨⟨m', hm', hl'⟩, hlt'⟩, hgap⟩ := exists_greatest
          (P := fun t' => (∃ m', mem[t']? = some m' ∧ m'.loc = a) ∧ t' < t) (B := t)
          (fun _ h => h.2) _ h1 (Nat.le_refl _) ⟨⟨m1, hm1, hl1⟩, hlt1⟩
        have hpa : PredAt mem a t (mw m') := ⟨t', m', hlt', hm', hl', rfl, fun t'' m'' a1 a2 a3 e4 =>
          hgap t'' a1 ⟨⟨m'', a3, e4⟩, a2⟩⟩
        have hu := hI _ hpa
        have hne' : t' ≠ t0 := by
          intro e0
          have h5 : h1 ≤ t' := Nat.le_of_not_lt fun h => hgap h1 h ⟨⟨m1, hm1, hl1⟩, hlt1⟩
          have h6 : t0 < h1 := (hall h1 m1 hm1 hl1 hh1n).1
          subst e0
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h6 h5)
        exact (hall t' m' hm' hl' hne').2.1 hu)
    (fun t htP ⟨m, hm, hl⟩ t' hlt' ⟨m', hm', hl'⟩ hgap => by
      rw [hφ t' m' hm']
      have hpa : PredAt mem a t (mw m') := ⟨t', m', hlt', hm', hl', rfl, fun t'' m'' a1 a2 a3 a4 =>
        hgap t'' a1 a2 ⟨m'', a3, a4⟩⟩
      have hex : ∃ w, PredAt mem m.loc t w := ⟨mw m', by rw [hl]; exact hpa⟩
      simp only [newCr, hm, dif_pos hex]
      have e := PredAt_uniq (Classical.choose_spec hex) (by rw [hl]; exact hpa)
      rw [e, hl]; rfl)
  refine ⟨top, mt, hmt, hlt, hmax, ?_⟩
  rw [hsum, hφ top mt hmt]
  exact Res.ext fun k => by simp only [Res.add_apply]; omega

end UnitPay

section Regroup

theorem sum_map_eq_zero {β : Type} {F : β → Res} : ∀ {U : List β}, (∀ u ∈ U, F u = .zero) →
    Res.sum (U.map F) = .zero
  | [], _ => rfl
  | u :: U, h => by
    rw [List.map_cons, Res.sum_cons, h u List.mem_cons_self,
      sum_map_eq_zero (fun v hv => h v (List.mem_cons_of_mem _ hv)), Res.zero_add]

theorem sum_map_add {β : Type} {A B : β → Res} : ∀ {U : List β},
    Res.sum (U.map fun u => A u + B u) = Res.sum (U.map A) + Res.sum (U.map B)
  | [] => (Res.add_zero _).symm
  | u :: U => by
    rw [List.map_cons, List.map_cons, List.map_cons, Res.sum_cons, Res.sum_cons, Res.sum_cons, sum_map_add]
    exact Res.ext fun k => by simp only [Res.add_apply]; omega

theorem sum_ind {β : Type} [DecidableEq β] (x : β) (r : Res) : ∀ {U : List β}, U.Nodup → x ∈ U →
    Res.sum (U.map fun u => if x = u then r else .zero) = r
  | [], _, h => absurd h List.not_mem_nil
  | u :: U, hnd, h => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, Res.sum_cons]
    by_cases e : x = u
    · subst e
      rw [if_pos rfl, sum_map_eq_zero (fun v hv => if_neg (fun (e : x = v) => hnd.1 (e ▸ hv))), Res.add_zero]
    · rw [if_neg e, Res.zero_add]
      exact sum_ind x r hnd.2 ((List.mem_cons.1 h).resolve_left e)

/-- **Regrouping a sum by a key**: a sum over a list whose keys lie in a duplicate-free list `U` is
the sum over `U` of the sums over each key's members. -/
theorem sum_part {β : Type} [DecidableEq β] (g : Nat → β) (f : Nat → Res) {U : List β} (hU : U.Nodup) :
    ∀ {P : List Nat}, (∀ t ∈ P, g t ∈ U) →
      Res.sum (P.map f) = Res.sum (U.map fun u => Res.sum ((P.filter fun t => decide (g t = u)).map f))
  | [], _ => by
    simp only [List.filter_nil, List.map_nil, Res.sum_nil]
    exact (sum_map_eq_zero (fun _ _ => rfl)).symm
  | x :: P, h => by
    have hpt : ∀ u, Res.sum (((x :: P).filter fun t => decide (g t = u)).map f) =
        (if g x = u then f x else .zero) + Res.sum ((P.filter fun t => decide (g t = u)).map f) := by
      intro u
      simp only [List.filter_cons]
      by_cases e : g x = u
      · rw [if_pos (decide_eq_true e), if_pos e, List.map_cons, Res.sum_cons]
      · rw [if_neg (fun h => e (of_decide_eq_true h)), if_neg e, Res.zero_add]
    rw [List.map_cons, Res.sum_cons, sum_part g f hU (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    simp only [hpt]
    rw [sum_map_add, sum_ind (g x) (f x) hU (h x List.mem_cons_self)]

/-- A sum of `f'` that agrees with `f` off the `new` members, where `f` is nothing: the `f` sum plus
the `f'` sum over the `new` members. -/
theorem sum_new {f f' : Nat → Res} {new : Nat → Bool} : ∀ {P : List Nat},
    (∀ t ∈ P, new t = false → f' t = f t) → (∀ t ∈ P, new t = true → f t = .zero) →
    Res.sum (P.map f') = Res.sum (P.map f) + Res.sum ((P.filter new).map f')
  | [], _, _ => (Res.add_zero _).symm
  | x :: P, h1, h2 => by
    have ih := sum_new (P := P) (fun t ht => h1 t (List.mem_cons_of_mem _ ht))
      (fun t ht => h2 t (List.mem_cons_of_mem _ ht))
    rw [List.map_cons, List.map_cons, Res.sum_cons, Res.sum_cons, ih, List.filter_cons]
    cases hx : new x
    · rw [if_neg (by simp), h1 x List.mem_cons_self hx]
      exact Res.ext fun k => by simp only [Res.add_apply]; omega
    · rw [if_pos rfl, List.map_cons, Res.sum_cons, h2 x List.mem_cons_self hx]
      exact Res.ext fun k => by simp only [Res.add_apply, Res.zero_apply]; omega

end Regroup

section SlotPay
open TermPlantR

theorem wvE_nword {E : TEnv} {a : Address} (h : ¬ WordUnit E a) (v : WeakMem.Val) : wvE E a v = .zero := by
  unfold wvE
  rw [dif_neg (fun ⟨n, P, hw⟩ => h (WordAt_unit hw))]

/-- **A new slot's promises pay its value**: over the units of slot `j` of `l` (each shaped by R1w,
predicted, at an own cell), the new debits are the new credits plus the slot's resources split as
`slot_debitsW` splits them (`F` at the raise's reading `ws`, `Z` the block debts, which are `Zf`). -/
theorem slot_pay {E : TEnv} {mem : Memory} {P : List Nat} {l : AllocLabel} {nW j : Nat} {Zf : Address → Res}
    (hnd : P.Nodup)
    (hR : ∀ i, i < nW → ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, j * nW + i⟩ ∧ m0.val = .undef ∧ t0 ∉ P ∧
      (∃ t, AtA mem ⟨l, j * nW + i⟩ t0 t = true) ∧
      ∀ t m, mem[t]? = some m → m.loc = ⟨l, j * nW + i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ P)
    (hq : ∀ i, i < nW → PredU E ⟨l, j * nW + i⟩) (hown : ∃ c, E.sto l = some c ∧ c.owner = some E.tid)
    {ws : List Word} (hl : ws.length = nW) (hrd : ∀ i w, ws[i]? = some w → RdW E mem ⟨l, j * nW + i⟩ w)
    {F Z : Nat → Res} (hF : ∀ i w, ws[i]? = some w → FRes E ⟨l, j * nW + i⟩ w (F i))
    (hZ : ∀ i, i < nW → Zf ⟨l, j * nW + i⟩ = Z i ∧ BlkDb E mem ⟨l, j * nW + i⟩ (Z i)) :
    Res.sum ((List.range nW).map fun i => Res.sum ((P.filter (AtB mem ⟨l, j * nW + i⟩)).map (newDb E mem Zf))) =
      Res.sum ((List.range nW).map fun i => Res.sum ((P.filter (AtB mem ⟨l, j * nW + i⟩)).map (newCr E mem))) +
        Res.sum ((List.range nW).map fun i => F i + Z i) := by
  have hpt : ∀ i ∈ List.range nW,
      Res.sum ((P.filter (AtB mem ⟨l, j * nW + i⟩)).map (newDb E mem Zf)) =
        Res.sum ((P.filter (AtB mem ⟨l, j * nW + i⟩)).map (newCr E mem)) + (F i + Z i) := by
    intro i hi
    have hi' : i < nW := List.mem_range.1 hi
    obtain ⟨hZe, hZb⟩ := hZ i hi'
    obtain ⟨top, mt, hmt, hlt, hmax, hsum⟩ := unit_pay (E := E) (mem := mem) (P := P) (a := ⟨l, j * nW + i⟩)
      (Zf := Zf) hnd (hR i hi') (hq i hi') hown (by rw [hZe]; exact hZb)
    rw [hsum, hZe]
    have hw : ∃ w, ws[i]? = some w := ⟨ws[i]'(by rw [hl]; exact hi'), List.getElem?_eq_getElem _⟩
    obtain ⟨w, hwi⟩ := hw
    rw [FRes_eq_wv (hF i w hwi)]
    have e : wvE E ⟨l, j * nW + i⟩ mt.val = wvE E ⟨l, j * nW + i⟩ w.val := by
      by_cases hW : WordUnit E ⟨l, j * nW + i⟩
      · obtain ⟨h, m, hm, hml, rfl, -, hlat⟩ := hrd i w hwi
        have e1 : h = top := by
          rcases Nat.lt_trichotomy h top with e | e | e
          · exact (hlat hW top mt e hmt hlt).elim
          · exact e
          · exact (hmax h m e hm hml).elim
        subst e1
        rw [hmt] at hm; cases hm; rfl
      · rw [wvE_nword hW, wvE_nword hW]
    rw [e]
    exact Res.ext fun k => by simp only [Res.add_apply]; omega
  rw [List.map_congr_left hpt, sum_map_add]

end SlotPay

section SlotTear
open TermPlantS

/-- (R1) **A new slot's reading is a value, with resources**: each word of the reading `ws` is (above)
the same word of some value of `e`, and `e` (all-`.one` units) tears at every boundary; so `ws` is a
value of `e` (`TermTear.assemble`, as `TermPlantS.unitFacts`), carrying some resources
(`VR_VRR`, `e` being `∀`-free). -/
theorem slotR_tear {E : TEnv} {e : Ty} {us : List Acc} (hu : accs e = some us) (hone : ∀ u ∈ us, u = .one)
    (hne : us ≠ []) (hTO : TearOK e) (hni : noIallV e = true) {ws : List Word} (hl : ws.length = nWords us)
    (hwd : ∀ i, i < nWords us → ∃ ws0 x, ValOf E e ws0 ∧ ws0.length = nWords us ∧ ws0[i]? = some x ∧
      ∀ y, ws[i]? = some y → WLe1 x y) :
    ∃ R, ValOfR E e ws R := by
  obtain ⟨vals, ⟨hvals, -⟩, hle⟩ :=
    TermTear.assemble (P := fun ws => ValOf E e ws ∧ ws.length = nWords us)
      (fun k ws1 ws2 hb h1 h2 => ⟨⟨hTO _ _ _ _ _ hu hb h1.1.1 h2.1.1 h1.2 h2.2,
          TermTear.Valid_tear hu hb h1.1.2 h2.1.2 h1.2 h2.2⟩,
        by rw [TermTear.splice_length (h1.2.trans h2.2.symm)]; exact h2.2⟩)
      (fun ws h => h.2) ws hl
      (fun i hi => by
        have hi' : i < nWords us := by rw [nWords_ones hone]; exact hi
        obtain ⟨ws0, x, hv0, hl0, hx, hle⟩ := hwd i hi'
        refine ⟨ws0, ⟨hv0, hl0⟩, fun jx x' y hj1 hj2 hx' hy => ?_⟩
        rw [nWords_take_ones hone, Nat.min_eq_left (Nat.le_of_lt hi)] at hj1
        rw [nWords_take_ones hone, Nat.min_eq_left hi] at hj2
        have e1 : jx = i := Nat.le_antisymm (Nat.le_of_lt_succ hj2) hj1
        subst e1
        rw [hx] at hx'; cases hx'; exact hle y hy)
      (by
        have h0 : 0 < nWords us := by
          rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
        obtain ⟨ws0, -, hv0, hl0, -⟩ := hwd 0 h0
        exact ⟨ws0, hv0, hl0⟩)
  have hv : ValOf E e ws := ⟨VR_up e _ vals ws hle hvals.1, Valid_vals e vals ws (WLe.vals hle) hvals.2⟩
  obtain ⟨R, hR⟩ := VR_VRR e hni (RInv_CE _) hv.1
  exact ⟨R, hR, hv.2⟩

end SlotTear

section Units

theorem nodup_map_some {α : Type} : ∀ {L : List α}, L.Nodup → (L.map some).Nodup
  | [], _ => List.nodup_nil
  | x :: L, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    exact ⟨fun hm => h.1 (by
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      cases e; exact hy), nodup_map_some h.2⟩

/-- A sum over offsets `[a·n, b·n)` is a sum over slots `[a, b)` of sums over their `n` units. -/
theorem sum_range_mul (h : Nat → Res) (n a : Nat) : ∀ b : Nat,
    Res.sum ((List.range' (a * n) (b * n)).map h) =
      Res.sum ((List.range' a b).map fun j => Res.sum ((List.range n).map fun i => h (j * n + i)))
  | 0 => by simp
  | b + 1 => by
    have e1 : (b + 1) * n = n + b * n := by rw [Nat.succ_mul, Nat.add_comm]
    have e2 : a * n + n = (a + 1) * n := (Nat.succ_mul a n).symm
    rw [e1, ← List.range'_append_1, List.map_append, Res.sum_append, e2, sum_range_mul h n (a + 1) b,
      List.range'_succ, List.map_cons, Res.sum_cons, List.range'_eq_map_range, List.map_map]
    rfl

/-- **Regrouping promises by unit**: a sum over messages each at a unit of a label of the
duplicate-free `L`, at an offset in `[lo l, hi l)`, is the sum over labels and offsets of the sums
over each unit's members. -/
theorem sum_units {mem : Memory} (f : Nat → Res) {L : List AllocLabel} (hL : L.Nodup)
    {lo hi : AllocLabel → Nat} : ∀ {P : List Nat},
    (∀ t ∈ P, ∃ m, mem[t]? = some m ∧ m.loc.label ∈ L ∧ lo m.loc.label ≤ m.loc.offset ∧
      m.loc.offset < hi m.loc.label) →
    Res.sum (P.map f) = Res.sum (L.map fun l => Res.sum ((List.range' (lo l) (hi l - lo l)).map fun o =>
      Res.sum ((P.filter (AtB mem ⟨l, o⟩)).map f))) := by
  intro P hin
  let g1 : Nat → Option AllocLabel := fun t => (mem[t]?).map fun m => m.loc.label
  let g2 : Nat → Option Nat := fun t => (mem[t]?).map fun m => m.loc.offset
  have hU1 : (L.map some).Nodup := nodup_map_some hL
  rw [sum_part g1 f hU1 (fun t ht => by
    obtain ⟨m, hm, hl, -⟩ := hin t ht
    exact List.mem_map.2 ⟨_, hl, by simp only [g1, hm, Option.map_some]⟩), List.map_map]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  show Res.sum (((P.filter fun t => decide (g1 t = some l))).map f) = _
  have hU2 : ((List.range' (lo l) (hi l - lo l)).map some).Nodup :=
    nodup_map_some List.nodup_range'
  rw [sum_part g2 f hU2 (fun t ht => by
    obtain ⟨htP, ht1⟩ := List.mem_filter.1 ht
    obtain ⟨m, hm, -, h1, h2⟩ := hin t htP
    have e : m.loc.label = l := by
      have := of_decide_eq_true ht1
      simp only [g1, hm, Option.map_some, Option.some.injEq] at this
      exact this
    refine List.mem_map.2 ⟨m.loc.offset, List.mem_range'_1.2 ⟨by rw [← e]; exact h1, ?_⟩,
      by simp only [g2, hm, Option.map_some]⟩
    rw [← e, Nat.add_sub_cancel' (Nat.le_of_lt (Nat.lt_of_le_of_lt h1 h2))]; exact h2), List.map_map]
  congr 1
  refine List.map_congr_left fun o _ => ?_
  simp only [Function.comp, List.filter_filter]
  congr 1
  congr 1
  refine List.filter_congr fun t _ => ?_
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, AtB_iff]
  constructor
  · rintro ⟨h2, h1⟩
    cases hm : mem[t]? with
    | none => simp only [g1, hm, Option.map_none] at h1; cases h1
    | some m =>
      simp only [g1, g2, hm, Option.map_some, Option.some.injEq] at h1 h2
      exact ⟨m, rfl, by cases e : m.loc; simp only [e] at h1 h2; rw [h1, h2]⟩
  · rintro ⟨m, hm, hl⟩
    simp only [g1, g2, hm, Option.map_some, hl]
    exact ⟨trivial, trivial⟩

end Units

section RaisePay
open TermPlantR TermPlantS
attribute [local instance 10] Classical.propDecidable

/-- The unit count of a label's buffer element (`0` off buffers with a layout). -/
def nWl (E : TEnv) (l : AllocLabel) : Nat :=
  match E.sto l with
  | some c => match c.ty with
    | .array _ e => match accs e with
      | some us => nWords us
      | none => 0
    | _ => 0
  | none => 0

theorem nWl_eq {E : TEnv} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc}
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us) : nWl E l = nWords us := by
  simp only [nWl, hc, hT, hu]

theorem RdW_uniq {E : TEnv} {mem : Memory} {a : Address} {w w' : Word} (h : RdW E mem a w)
    (h' : RdW E mem a w') : w = w' := by
  obtain ⟨h1, m1, hm1, hl1, rfl, hf1, hx1⟩ := h
  obtain ⟨h2, m2, hm2, hl2, rfl, hf2, hx2⟩ := h'
  have e : h1 = h2 := by
    by_cases hW : WordUnit E a
    · rcases Nat.lt_trichotomy h1 h2 with e | e | e
      · exact (hx1 hW h2 m2 e hm2 hl2).elim
      · exact e
      · exact (hx2 hW h1 m1 e hm1 hl1).elim
    · exact FirstW_uniq (hf1 hW) (hf2 hW)
  subst e
  rw [hm1] at hm2; cases hm2; rfl

theorem RdW_ex {E : TEnv} {mem : Memory} {a : Address} {h : Ts} (hf : FirstW mem a h) : ∃ w, RdW E mem a w := by
  obtain ⟨⟨m, hm, hml, -⟩, -⟩ := id hf
  by_cases hW : WordUnit E a
  · obtain ⟨t, ⟨mt, hmt, hlt⟩, hmax⟩ := exists_greatest
      (P := fun t => ∃ m', mem[t]? = some m' ∧ m'.loc = a) (B := mem.size)
      (fun t ⟨_, h, _⟩ => TermMem.lt_of_get h) _ h (Nat.le_refl _) ⟨m, hm, hml⟩
    exact ⟨mw mt, t, mt, hmt, hlt, rfl, fun h' => absurd hW h', fun _ t' m' h3 h4 h5 => hmax t' h3 ⟨m', h4, h5⟩⟩
  · exact ⟨mw m, h, m, hm, hml, rfl, fun _ => hf, fun h' => absurd h' hW⟩

theorem filter_sub {p q : Nat → Bool} : ∀ {P : List Nat}, (∀ t ∈ P, q t = true → p t = true) →
    (P.filter p).filter q = P.filter q
  | [], _ => rfl
  | x :: P, h => by
    have ih := filter_sub (P := P) (fun t ht => h t (List.mem_cons_of_mem _ ht))
    by_cases hq : q x = true
    · have hp := h x List.mem_cons_self hq
      simp [hp, hq, ih]
    · cases hp : p x <;> simp [hp, hq, ih]

theorem sum_congrB {β : Type} {f g : β → Res} {L : List β} (h : ∀ x ∈ L, f x = g x) :
    Res.sum (L.map f) = Res.sum (L.map g) := by
  rw [List.map_congr_left h]

theorem slot_in {a b j n i : Nat} (h1 : a ≤ j) (h2 : j < b) (hi : i < n) :
    a * n ≤ j * n + i ∧ j * n + i < b * n := by
  have q1 := Nat.mul_le_mul_right n h1
  have q2 := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h2)
  rw [Nat.succ_mul] at q2
  omega

theorem slot_divmod {n j i : Nat} (hi : i < n) : (j * n + i) / n = j ∧ (j * n + i) % n = i := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  rw [Nat.add_comm]
  constructor
  · rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hi, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem rdW_list_eq {E : TEnv} {mem : Memory} {f : Nat → Address} {n : Nat} {ws ws' : List Word}
    (hl : ws.length = n) (hl' : ws'.length = n) (h : ∀ i w, ws[i]? = some w → RdW E mem (f i) w)
    (h' : ∀ i w, ws'[i]? = some w → RdW E mem (f i) w) : ws = ws' := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · have hi1 : i < ws.length := by rw [hl]; exact hi
    have hi2 : i < ws'.length := by rw [hl']; exact hi
    rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2]
    exact congrArg some (RdW_uniq (h i _ (List.getElem?_eq_getElem hi1)) (h' i _ (List.getElem?_eq_getElem hi2)))
  · rw [List.getElem?_eq_none (by rw [hl]; omega), List.getElem?_eq_none (by rw [hl']; omega)]

/-- (R1) **The resourceful raise**: raising the counts of the labels `Q` (own affine all-`.one`
buffers whose new slots are a placeholder under own promises, R1w) keeps memory's holding and the
promise credits, the new slots' values (read at `RdW`) paid by their promises' new debits net of
their new credits (`slot_pay`).  The labels `Q0` are raised alongside, their entries by the
caller (`hQ0`), their new units carrying no protocol word and no block debt, so no new credit or
debit. -/
theorem raise_pay {E E' : TEnv} {s : St} {H : Res} {cr db : Ts → Res} {Q Q0 : AllocLabel → Prop}
    (hH : MemHeld E s H) (hC : PromCr E s cr db) (hnd : s.promises.Nodup)
    (hsto : ∀ l, E'.sto l = E.sto l) (htid : E'.tid = E.tid)
    (hpf : ∀ l, E'.pfr l = E.pfr l) (hfp : E'.fp = E.fp) (hri : ∀ l, E'.rini l = E.rini l)
    (hini : ∀ l, ¬ Q l → ¬ Q0 l → E'.ini l = E.ini l)
    (hQ0 : ∀ l, Q0 l → ¬ Q l ∧ ∃ c N e us, E.sto l = some c ∧ c.ty = .array (.lit N) e ∧ accs e = some us ∧
      E.ini l ≤ E'.ini l ∧ E.rini l ≤ E.ini l ∧ E.pfr l ≠ none ∧
      (∀ R, HeldEntry E s l R → HeldEntry E' s l R) ∧
      ∀ o, IniW E' ⟨l, o⟩ → ¬ IniW E ⟨l, o⟩ → (∀ n P, ¬ WordAt E' ⟨l, o⟩ n P) ∧
        ∀ tw, DesigAt E' s.mem ⟨l, o⟩ tw → BlkDb E' s.mem ⟨l, o⟩ .zero)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hbx : ∀ l B, E.box l = some B → E'.box l = some B)
    (hQ : ∀ l, Q l → ∃ c N e us, E.sto l = some c ∧ c.owner = some E.tid ∧ c.ty = .array (.lit N) e ∧
      accs e = some us ∧ (∀ u ∈ us, u = .one) ∧ us ≠ [] ∧ Clo e ∧ mg e = true ∧ Ty.noOwnIn [] e = true ∧
      E.ini l ≤ E'.ini l ∧ E'.ini l ≤ N ∧ E.rini l ≤ E.ini l ∧ E.pfr l ≠ none ∧
      (∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
        (∃ t0 m0, s.mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val = .undef ∧ t0 ∉ s.promises ∧
          (∃ t, AtA s.mem ⟨l, o⟩ t0 t = true) ∧
          ∀ t m, s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ s.promises) ∧
        (WordUnit E' ⟨l, o⟩ → ∃ n P, WordAt E' ⟨l, o⟩ n P)) ∧
      ∀ j, E.ini l ≤ j → j < E'.ini l → ∀ ws : List Word, ws.length = nWords us →
        (∀ i w, ws[i]? = some w → RdW E' s.mem ⟨l, j * nWords us + i⟩ w) → ∃ R, ValOfR E' e ws R) :
    ∃ H' cr' db', MemHeld E' s H' ∧ PromCr E' s cr' db' ∧
      (∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → ¬ Q m.loc.label → cr' tw = cr tw ∧ db' tw = db tw) ∧
      H' + pSum s cr' + pSum s db = H + pSum s cr + pSum s db' := by
  -- the slots' data: the reading, its value, and its split
  have hD : ∀ l j, ∃ d : List Word × Res × (Nat → Res) × (Nat → Res),
      Q l → E.ini l ≤ j → j < E'.ini l → ∀ c N e us, E.sto l = some c → c.ty = .array (.lit N) e →
        accs e = some us →
        d.1.length = nWords us ∧ (∀ i w, d.1[i]? = some w → RdW E' s.mem ⟨l, j * nWords us + i⟩ w) ∧
        ValOfR E' e d.1 d.2.1 ∧ d.2.1 = Res.sum ((List.range (nWords us)).map fun i => d.2.2.1 i + d.2.2.2 i) ∧
        (∀ i w, d.1[i]? = some w → FRes E' ⟨l, j * nWords us + i⟩ w (d.2.2.1 i)) ∧
        ∀ i, i < nWords us → BlkDb E' s.mem ⟨l, j * nWords us + i⟩ (d.2.2.2 i) := by
    intro l j
    by_cases hq : Q l ∧ E.ini l ≤ j ∧ j < E'.ini l
    · obtain ⟨c, N, e, us, hc, -, hT, hu, hone, hne, hCl, hmg, hno, -, hN, -, -, hU, hty⟩ := hQ l hq.1
      have hpos : 0 < nWords us := by rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
      have hc' : E'.sto l = some c := by rw [hsto]; exact hc
      have hrd : ∀ i, ∃ w : Word, i < nWords us → RdW E' s.mem ⟨l, j * nWords us + i⟩ w := fun i => by
        by_cases hi : i < nWords us
        · obtain ⟨b1, b2⟩ := slot_in hq.2.1 hq.2.2 hi
          obtain ⟨h, hf, -, -⟩ := firstW_of_R1w (hU _ b1 b2).1
          obtain ⟨w, hw⟩ := RdW_ex (E := E') hf
          exact ⟨w, fun _ => hw⟩
        · exact ⟨default, fun h => absurd h hi⟩
      obtain ⟨rd, hrdf⟩ := Classical.axiomOfChoice hrd
      obtain ⟨ws, hws⟩ : ∃ ws : List Word, ws = (List.range (nWords us)).map rd := ⟨_, rfl⟩
      have hwl : ws.length = nWords us := by rw [hws, List.length_map, List.length_range]
      have hwi : ∀ i w, ws[i]? = some w → i < nWords us ∧ RdW E' s.mem ⟨l, j * nWords us + i⟩ w := by
        intro i w hw
        rw [hws, List.getElem?_map] at hw
        by_cases hi : i < nWords us
        · rw [List.getElem?_range hi, Option.map_some, Option.some.injEq] at hw
          subst hw; exact ⟨hi, hrdf i hi⟩
        · have h0 : (List.range (nWords us))[i]? = none :=
            List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hi)
          rw [h0] at hw; cases hw
      obtain ⟨R, hR⟩ := hty j hq.2.1 hq.2.2 ws hwl (fun i w hw => (hwi i w hw).2)
      obtain ⟨F, Z, hRs, hF, hZ⟩ := slot_debitsWV (E := E') s.mem hc' hT hu hone hpos
        (Nat.lt_of_lt_of_le hq.2.2 hN) hCl hmg hno hwl
        (fun o x hx hnw => by
          obtain ⟨hi, h, m, hm, hml, hxe, hf, -⟩ := hwi o x hx
          obtain ⟨b1, b2⟩ := slot_in hq.2.1 hq.2.2 hi
          have hnW : ¬ WordUnit E' ⟨l, j * nWords us + o⟩ := fun hW => by
            obtain ⟨n, P, hw⟩ := (hU _ b1 b2).2 hW; exact hnw n P hw
          exact ⟨h, m, hf hnW, hm, hxe⟩) hR
      refine ⟨(ws, R, F, Z), fun _ _ _ c' N' e' us' hc2 hT2 hu2 => ?_⟩
      rw [hc] at hc2; cases hc2; rw [hT] at hT2; cases hT2; rw [hu] at hu2; cases hu2
      exact ⟨hwl, fun i w hw => (hwi i w hw).2, hR, hRs, hF, hZ⟩
    · exact ⟨([], .zero, fun _ => .zero, fun _ => .zero), fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hq⟩
  obtain ⟨dat, hdat⟩ := Classical.axiomOfChoice fun l => Classical.axiomOfChoice (hD l)
  obtain ⟨G, hG⟩ : ∃ G : AllocLabel → Res,
      ∀ l, G l = if Q l then Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map fun j => (dat l j).2.1)
        else .zero :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Zf, hZf⟩ : ∃ Zf : Address → Res,
      ∀ a, Zf a = if Q a.label then (dat a.label (a.offset / nWl E a.label)).2.2.2 (a.offset % nWl E a.label)
        else .zero :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cr', hcr'⟩ : ∃ f : Ts → Res,
      ∀ t, f t = if NewP E E' s t = true then newCr E' s.mem t else cr t := ⟨_, fun _ => rfl⟩
  obtain ⟨db', hdb'⟩ : ∃ f : Ts → Res,
      ∀ t, f t = if NewP E E' s t = true then newDb E' s.mem Zf t else db t := ⟨_, fun _ => rfl⟩
  have hile : ∀ l, E.ini l ≤ E'.ini l := fun l => by
    by_cases hq : Q l
    · obtain ⟨c, N, e, us, -, -, -, -, -, -, -, -, -, hil, -⟩ := hQ l hq; exact hil
    · by_cases hq0 : Q0 l
      · obtain ⟨-, c, N, e, us, -, -, -, hil, -⟩ := hQ0 l hq0; exact hil
      · rw [hini l hq hq0]; exact Nat.le_refl _
  have hmono : ∀ a, IniW E a → IniW E' a := fun a ha c N e us hc hT hu => by
    have := ha c N e us (by rw [← hsto]; exact hc) hT hu
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (hile a.label))
  have hrc : ∀ l, E'.rc l = E.rc l := fun l => by
    by_cases hq : Q l
    · obtain ⟨c, N, e, us, -, -, -, -, -, -, -, -, -, hil, -, hrl, -⟩ := hQ l hq
      unfold TEnv.rc; rw [hri]; omega
    · by_cases hq0 : Q0 l
      · obtain ⟨-, c, N, e, us, -, -, -, hil, hrl, -⟩ := hQ0 l hq0
        unfold TEnv.rc; rw [hri]; omega
      · exact TEnv.rc_congr (hini l hq hq0) (hri l)
  have hNew : ∀ a : Address, IniW E' a → ¬ IniW E a → Q a.label ∨ Q0 a.label := fun a h1 h2 =>
    Classical.byContradiction fun hq => h2 ((IniW_congrU (hsto _)
      (hini _ (fun h => hq (.inl h)) (fun h => hq (.inr h)))).1 h1)
  have hVis : ∀ a : Address, IniW E' a → ¬ IniW E a → Vis E' a.label := fun a h1 h2 => by
    have hpfl : E.pfr a.label ≠ none := by
      rcases hNew a h1 h2 with hq | hq0
      · obtain ⟨c, N, e, us, -, -, -, -, -, -, -, -, -, -, -, -, hpfl, -⟩ := hQ _ hq; exact hpfl
      · obtain ⟨-, c, N, e, us, -, -, -, -, -, hpfl, -⟩ := hQ0 _ hq0; exact hpfl
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hpfl
    exact Vis_pfr (by rw [hpf]; exact hf)
  have hBlk : ∀ (a : Address) tw, IniW E' a → ¬ IniW E a → DesigAt E' s.mem a tw → BlkDb E' s.mem a (Zf a) := by
    intro ⟨l, o⟩ tw h1 h2 hD
    rcases hNew _ h1 h2 with hq | hq0
    · obtain ⟨c, N, e, us, hc, -, hT, hu, hone, hne, -⟩ := hQ l hq
      have hpos : 0 < nWords us := by rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
      have hc' : E'.sto l = some c := by rw [hsto]; exact hc
      have b2 : o < E'.ini l * nWords us := (IniW_iff hc' hT hu).1 h1
      have b1 : E.ini l * nWords us ≤ o := Nat.le_of_not_lt fun h => h2 ((IniW_iff hc hT hu).2 h)
      have j1 : E.ini l ≤ o / nWords us := (Nat.le_div_iff_mul_le hpos).2 b1
      have j2 : o / nWords us < E'.ini l := (Nat.div_lt_iff_lt_mul hpos).2 b2
      obtain ⟨-, -, -, -, -, hZ⟩ := hdat l (o / nWords us) hq j1 j2 c N e us hc hT hu
      have hb := hZ (o % nWords us) (Nat.mod_lt _ hpos)
      rw [Nat.div_add_mod'] at hb
      rw [hZf]
      show BlkDb E' s.mem ⟨l, o⟩ (if Q l then (dat l (o / nWl E l)).2.2.2 (o % nWl E l) else .zero)
      rw [if_pos hq, nWl_eq hc hT hu]
      exact hb
    · obtain ⟨hnq, c, N, e, us, -, -, -, -, -, -, -, hU0⟩ := hQ0 l hq0
      rw [hZf]
      show BlkDb E' s.mem ⟨l, o⟩ (if Q l then (dat l (o / nWl E l)).2.2.2 (o % nWl E l) else .zero)
      rw [if_neg hnq]
      exact (hU0 o h1 h2).2 tw hD
  have hzero : ∀ t m, s.mem[t]? = some m → Q0 m.loc.label → IniW E' m.loc → ¬ IniW E m.loc →
      newDb E' s.mem Zf t = .zero ∧ newCr E' s.mem t = .zero := by
    intro t m hm hq0 h1 h2
    obtain ⟨hnq, c, N, e, us, -, -, -, -, -, -, -, hU0⟩ := hQ0 _ hq0
    have hna := (hU0 m.loc.offset h1 h2).1
    have hZ0 : Zf m.loc = .zero := by rw [hZf, if_neg hnq]
    exact ⟨newDb_zero hm hna hZ0, newCr_zero hm hna⟩
  have hNP : ∀ t, NewP E E' s t = true → ∃ m, s.mem[t]? = some m ∧ IniW E' m.loc ∧ ¬ IniW E m.loc :=
    fun t h => by simpa only [NewP, decide_eq_true_eq] using h
  obtain ⟨hC', hz⟩ := PromCr_raise (cr' := cr') (db' := db') hC hsto htid hpf hmono hrc hbx
    (fun tw m _ hm h1 h2 => by
      have hn : NewP E E' s tw = true := by
        simp only [NewP, decide_eq_true_eq]; exact ⟨m, hm, h1, h2⟩
      rw [hcr', hdb', if_pos hn, if_pos hn]
      exact ⟨newDb_res hm ⟨hVis _ h1 h2, h1⟩ (fun hD => hBlk _ tw h1 h2 hD), newCr_res hm ⟨hVis _ h1 h2, h1⟩⟩)
    (fun tw _ hn => by
      rw [hcr', hdb', if_neg (by simp [hn]), if_neg (by simp [hn])]; exact ⟨rfl, rfl⟩)
  obtain ⟨L, Rl, hndL, hcov, rfl, hent⟩ := hH
  -- the new debits and credits sit at new promises
  have eDb : pSum s db' = pSum s db + Res.sum ((s.promises.filter (NewP E E' s)).map (newDb E' s.mem Zf)) := by
    unfold pSum
    rw [sum_new (f := db) (new := NewP E E' s)
      (fun t _ hn => by rw [hdb', if_neg (by simp [hn])]) (fun t ht hn => (hz t ht hn).2)]
    congr 1
    exact sum_congrB fun t ht => by rw [List.mem_filter] at ht; rw [hdb', if_pos ht.2]
  have eCr : pSum s cr' = pSum s cr + Res.sum ((s.promises.filter (NewP E E' s)).map (newCr E' s.mem)) := by
    unfold pSum
    rw [sum_new (f := cr) (new := NewP E E' s)
      (fun t _ hn => by rw [hcr', if_neg (by simp [hn])]) (fun t ht hn => (hz t ht hn).1)]
    congr 1
    exact sum_congrB fun t ht => by rw [List.mem_filter] at ht; rw [hcr', if_pos ht.2]
  obtain ⟨lo, hlo⟩ : ∃ lo : AllocLabel → Nat, ∀ l, lo l = E.ini l * nWl E l := ⟨_, fun _ => rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi : AllocLabel → Nat, ∀ l, hi l = E'.ini l * nWl E l := ⟨_, fun _ => rfl⟩
  have hin : ∀ t ∈ s.promises.filter (NewP E E' s), ∃ m, s.mem[t]? = some m ∧ m.loc.label ∈ L ∧
      lo m.loc.label ≤ m.loc.offset ∧ m.loc.offset < hi m.loc.label := by
    intro t ht
    rw [List.mem_filter] at ht
    obtain ⟨m, hm, h1, h2⟩ := hNP t ht.2
    have hdat0 : ∃ c N e us, E.sto m.loc.label = some c ∧ c.ty = .array (.lit N) e ∧ accs e = some us := by
      rcases hNew _ h1 h2 with hq | hq0
      · obtain ⟨c, N, e, us, hc, -, hT, hu, -⟩ := hQ _ hq; exact ⟨c, N, e, us, hc, hT, hu⟩
      · obtain ⟨-, c, N, e, us, hc, hT, hu, -⟩ := hQ0 _ hq0; exact ⟨c, N, e, us, hc, hT, hu⟩
    obtain ⟨c, N, e, us, hc, hT, hu⟩ := hdat0
    have hc' : E'.sto m.loc.label = some c := by rw [hsto]; exact hc
    refine ⟨m, hm, hcov _ c hc, ?_, ?_⟩
    · rw [hlo, nWl_eq hc hT hu]; exact Nat.le_of_not_lt fun h => h2 ((IniW_iff hc hT hu).2 h)
    · rw [hhi, nWl_eq hc hT hu]; exact (IniW_iff hc' hT hu).1 h1
  -- the payment, label by label
  have hK : Res.sum ((s.promises.filter (NewP E E' s)).map (newDb E' s.mem Zf)) =
      Res.sum ((s.promises.filter (NewP E E' s)).map (newCr E' s.mem)) + Res.sum (L.map G) := by
    rw [sum_units (newDb E' s.mem Zf) hndL hin, sum_units (newCr E' s.mem) hndL hin, ← sum_map_add]
    refine sum_congrB fun l _ => ?_
    by_cases hq : Q l
    · obtain ⟨c, N, e, us, hc, ho, hT, hu, hone, hne, -, -, -, hil, -, hrl, hpfl, hU, -⟩ := hQ l hq
      have hpos : 0 < nWords us := by rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
      have hc' : E'.sto l = some c := by rw [hsto]; exact hc
      have hrcQ : E'.rc l = E.rini l := by unfold TEnv.rc; rw [hri]; omega
      have hlh := Nat.mul_le_mul_right (nWords us) hil
      have hfil : ∀ o ∈ List.range' (lo l) (hi l - lo l),
          (s.promises.filter (NewP E E' s)).filter (AtB s.mem ⟨l, o⟩) = s.promises.filter (AtB s.mem ⟨l, o⟩) := by
        intro o ho
        rw [List.mem_range'_1, hlo, hhi, nWl_eq hc hT hu] at ho
        have ho2 : o < E'.ini l * nWords us := by omega
        refine filter_sub fun t _ hat => ?_
        obtain ⟨m, hm, hml⟩ := AtB_iff.1 hat
        simp only [NewP, decide_eq_true_eq]
        refine ⟨m, hm, ?_, ?_⟩
        · rw [hml]; exact (IniW_iff hc' hT hu).2 ho2
        · rw [hml]; exact fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ((IniW_iff hc hT hu).1 h) ho.1)
      have eD : ∀ f : Nat → Res,
          Res.sum ((List.range' (lo l) (hi l - lo l)).map fun o =>
            Res.sum (((s.promises.filter (NewP E E' s)).filter (AtB s.mem ⟨l, o⟩)).map f)) =
          Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map fun j =>
            Res.sum ((List.range (nWords us)).map fun i =>
              Res.sum ((s.promises.filter (AtB s.mem ⟨l, j * nWords us + i⟩)).map f))) := by
        intro f
        have e1 := sum_range_mul (fun o => Res.sum ((s.promises.filter (AtB s.mem ⟨l, o⟩)).map f))
          (nWords us) (E.ini l) (E'.ini l - E.ini l)
        rw [Nat.sub_mul] at e1
        refine Eq.trans ?_ e1
        rw [← nWl_eq hc hT hu, ← hlo, ← hhi]
        exact sum_congrB fun o ho => by rw [hfil o ho]
      refine (eD _).trans (Eq.trans ?_ (congrArg (· + G l) (eD _).symm))
      show _ = _ + G l
      rw [hG l, if_pos hq, ← sum_map_add]
      refine sum_congrB fun j hj => ?_
      rw [List.mem_range'_1] at hj
      have hj1 : E.ini l ≤ j := hj.1
      have hj2 : j < E'.ini l := by
        have h3 := hj.2; rw [Nat.add_sub_cancel' hil] at h3; exact h3
      obtain ⟨hwl, hrd, -, hRs, hF, hZ⟩ := hdat l j hq hj1 hj2 c N e us hc hT hu
      rw [hRs]
      refine slot_pay hnd (fun i hi => (hU _ (slot_in hj1 hj2 hi).1 (slot_in hj1 hj2 hi).2).1)
        (fun i hi => ⟨by rw [hpf]; exact hpfl, (IniW_iff hc' hT hu).2 (slot_in hj1 hj2 hi).2, fun hr => by
          have h3 := (IniWr_iff hc' hT hu).1 hr
          rw [hrcQ] at h3
          have q := Nat.mul_le_mul_right (nWords us) hrl
          have q1 := (slot_in hj1 hj2 hi).1
          omega⟩)
        ⟨c, hc', by rw [htid]; exact ho⟩ hwl hrd hF (fun i hi => ⟨?_, hZ i hi⟩)
      rw [hZf]
      show (if Q l then (dat l ((j * nWords us + i) / nWl E l)).2.2.2 ((j * nWords us + i) % nWl E l)
        else .zero) = _
      rw [if_pos hq, nWl_eq hc hT hu, (slot_divmod hi).1, (slot_divmod hi).2]
    · by_cases hq0 : Q0 l
      · have hz0 : ∀ f : Nat → Res, (∀ t m, s.mem[t]? = some m → m.loc.label = l → NewP E E' s t = true →
            f t = .zero) →
            Res.sum ((List.range' (lo l) (hi l - lo l)).map fun o =>
              Res.sum (((s.promises.filter (NewP E E' s)).filter (AtB s.mem ⟨l, o⟩)).map f)) = .zero := by
          intro f hf
          refine sum_map_eq_zero fun o _ => sum_map_eq_zero fun t ht => ?_
          rw [List.mem_filter, List.mem_filter] at ht
          obtain ⟨m, hm, hml⟩ := AtB_iff.1 ht.2
          exact hf t m hm (by rw [hml]) ht.1.2
        have hzz : ∀ t m, s.mem[t]? = some m → m.loc.label = l → NewP E E' s t = true →
            newDb E' s.mem Zf t = .zero ∧ newCr E' s.mem t = .zero := fun t m hm hml hn => by
          obtain ⟨m', hm', h1, h2⟩ := hNP t hn
          have e : m' = m := Option.some.inj (hm'.symm.trans hm)
          have h1' : IniW E' m.loc := by rw [← e]; exact h1
          have h2' : ¬ IniW E m.loc := by rw [← e]; exact h2
          exact hzero t m hm (by rw [hml]; exact hq0) h1' h2'
        rw [hz0 _ (fun t m hm hml hn => (hzz t m hm hml hn).1),
          hz0 _ (fun t m hm hml hn => (hzz t m hm hml hn).2), hG l, if_neg hq]
        exact (Res.add_zero _).symm
      · have e0 : hi l - lo l = 0 := by rw [hlo, hhi, hini l hq hq0, Nat.sub_self]
        rw [e0, hG l, if_neg hq]
        exact (Res.add_zero _).symm
  refine ⟨Res.sum (L.map fun l => Rl l + G l), cr', db',
    ⟨L, fun l => Rl l + G l, hndL, fun l c hc => hcov l c (by rw [← hsto l]; exact hc), rfl, fun l hl => ?_⟩,
    hC', fun tw m htw hm hnq => ?_, ?_⟩
  · show HeldEntry E' s l (Rl l + G l)
    by_cases hq : Q l
    · obtain ⟨c, N, e, us, hc, -, hT, hu, hone, hne, -, -, -, hil, hN, hrl, hpfl, hU, -⟩ := hQ l hq
      have hpos : 0 < nWords us := by rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
      rw [hG l, if_pos hq]
      exact HeldEntry_raiseW (hent l hl) (hsto l) htid (hpf l) hfp (hri l) hc hT hu hv hil hN hrl hpfl
        (fun o h1 h2 => by
          obtain ⟨h, hf, -, hab⟩ := firstW_of_R1w (hU o h1 h2).1
          exact ⟨h, hf, fun t m' a1 a2 a3 => List.mem_append_left _ (hab t m' a1 a2 a3)⟩)
        (fun j hj1 hj2 ws hl hrd => by
          obtain ⟨hwl, hrd0, hR, -⟩ := hdat l j hq hj1 hj2 c N e us hc hT hu
          rw [rdW_list_eq hl hwl hrd hrd0]
          exact hR)
        (fun j h0 => absurd h0 (Nat.pos_iff_ne_zero.1 hpos))
    · rw [hG l, if_neg hq, Res.add_zero]
      by_cases hq0 : Q0 l
      · obtain ⟨-, c, N, e, us, -, -, -, -, -, -, hE0, -⟩ := hQ0 l hq0
        exact hE0 _ (hent l hl)
      · exact HeldEntry_tr (hent l hl) (hsto l) htid (hpf l) hfp (hini l hq hq0) (hri l) hv
  · by_cases hn : NewP E E' s tw = true
    · obtain ⟨m', hm', h1, h2⟩ := hNP tw hn
      have e : m' = m := Option.some.inj (hm'.symm.trans hm)
      have h1' : IniW E' m.loc := by rw [← e]; exact h1
      have h2' : ¬ IniW E m.loc := by rw [← e]; exact h2
      have hq0 : Q0 m.loc.label := (hNew _ h1' h2').resolve_left hnq
      obtain ⟨z1, z2⟩ := hzero tw m hm hq0 h1' h2'
      obtain ⟨y1, y2⟩ := hz tw htw hn
      rw [hcr', hdb', if_pos hn, if_pos hn, z1, z2, y1, y2]
      exact ⟨rfl, rfl⟩
    · rw [hcr', hdb', if_neg hn, if_neg hn]
      exact ⟨rfl, rfl⟩
  · rw [sum_map_add, eDb, eCr, hK]
    exact Res.ext fun k => by simp only [Res.add_apply]; omega


/-- (R1, pins) A buffer label's slot list has the label's count as length. -/
theorem HeldEntryL_len {E : TEnv} {s : St} {l : AllocLabel} {Rs : List Res} {c : Cell} {N : Nat} {e : Ty}
    (h : HeldEntryL E s l Rs) (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) : Rs.length = E.ini l := by
  obtain ⟨vals, -, hok⟩ := h.2 c hc
  rcases hok with ⟨hw, -⟩ | ⟨N0, e0, us0, -, -, -, -, hRs, -⟩
  · rw [hT] at hw; simp [wc, accs] at hw
  · exact hRs

/-- (R1, pins) **`raise_pay` along slot lists**: memory's holding as `MemHeldL`; the `Q` labels'
lists grow by their new slots (old slots unchanged), each new slot `j` the value of the raise's
reading, paid by its promises' debits net of their credits; labels off `Q`, `Q0` keep their lists. -/
theorem raise_payL {E E' : TEnv} {s : St} {H : Res} {S : AllocLabel → List Res} {cr db : Ts → Res}
    {Q Q0 : AllocLabel → Prop}
    (hH : MemHeldL E s H S) (hC : PromCr E s cr db) (hnd : s.promises.Nodup)
    (hsto : ∀ l, E'.sto l = E.sto l) (htid : E'.tid = E.tid)
    (hpf : ∀ l, E'.pfr l = E.pfr l) (hfp : E'.fp = E.fp) (hri : ∀ l, E'.rini l = E.rini l)
    (hini : ∀ l, ¬ Q l → ¬ Q0 l → E'.ini l = E.ini l)
    (hQ0 : ∀ l, Q0 l → ¬ Q l ∧ ∃ c N e us, E.sto l = some c ∧ c.ty = .array (.lit N) e ∧ accs e = some us ∧
      E.ini l ≤ E'.ini l ∧ E.rini l ≤ E.ini l ∧ E.pfr l ≠ none ∧
      (∀ R, HeldEntry E s l R → HeldEntry E' s l R) ∧
      ∀ o, IniW E' ⟨l, o⟩ → ¬ IniW E ⟨l, o⟩ → (∀ n P, ¬ WordAt E' ⟨l, o⟩ n P) ∧
        ∀ tw, DesigAt E' s.mem ⟨l, o⟩ tw → BlkDb E' s.mem ⟨l, o⟩ .zero)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hbx : ∀ l B, E.box l = some B → E'.box l = some B)
    (hQ : ∀ l, Q l → ∃ c N e us, E.sto l = some c ∧ c.owner = some E.tid ∧ c.ty = .array (.lit N) e ∧
      accs e = some us ∧ (∀ u ∈ us, u = .one) ∧ us ≠ [] ∧ Clo e ∧ mg e = true ∧ Ty.noOwnIn [] e = true ∧
      E.ini l ≤ E'.ini l ∧ E'.ini l ≤ N ∧ E.rini l ≤ E.ini l ∧ E.pfr l ≠ none ∧
      (∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
        (∃ t0 m0, s.mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val = .undef ∧ t0 ∉ s.promises ∧
          (∃ t, AtA s.mem ⟨l, o⟩ t0 t = true) ∧
          ∀ t m, s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ s.promises) ∧
        (WordUnit E' ⟨l, o⟩ → ∃ n P, WordAt E' ⟨l, o⟩ n P)) ∧
      ∀ j, E.ini l ≤ j → j < E'.ini l → ∀ ws : List Word, ws.length = nWords us →
        (∀ i w, ws[i]? = some w → RdW E' s.mem ⟨l, j * nWords us + i⟩ w) → ∃ R, ValOfR E' e ws R) :
    ∃ H' S' cr' db', MemHeldL E' s H' S' ∧ PromCr E' s cr' db' ∧
      (∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → ¬ Q m.loc.label → cr' tw = cr tw ∧ db' tw = db tw) ∧
      H' + pSum s cr' + pSum s db = H + pSum s cr + pSum s db' ∧
      (∀ l, ¬ Q l → ¬ Q0 l → S' l = S l) ∧
      (∀ l j, Q l → j < E.ini l → (S' l)[j]? = (S l)[j]?) ∧
      ∀ l j, Q l → E.ini l ≤ j → j < E'.ini l → ∀ c N e us, E.sto l = some c → c.ty = .array (.lit N) e →
        accs e = some us → ∃ ws Rj, (S' l)[j]? = some Rj ∧ ws.length = nWords us ∧
          (∀ i w, ws[i]? = some w → RdW E' s.mem ⟨l, j * nWords us + i⟩ w) ∧ ValOfR E' e ws Rj ∧
          (∃ F Z : Nat → Res, Rj = Res.sum ((List.range (nWords us)).map fun i => F i + Z i) ∧
            (∀ i w, ws[i]? = some w → FRes E' ⟨l, j * nWords us + i⟩ w (F i)) ∧
            ∀ i, i < nWords us → BlkDb E' s.mem ⟨l, j * nWords us + i⟩ (Z i)) ∧
          Res.sum ((List.range (nWords us)).map fun i =>
            Res.sum ((s.promises.filter (AtB s.mem ⟨l, j * nWords us + i⟩)).map db')) =
          Res.sum ((List.range (nWords us)).map fun i =>
            Res.sum ((s.promises.filter (AtB s.mem ⟨l, j * nWords us + i⟩)).map cr')) + Rj := by
  -- the slots' data: the reading, its value, and its split
  have hD : ∀ l j, ∃ d : List Word × Res × (Nat → Res) × (Nat → Res),
      Q l → E.ini l ≤ j → j < E'.ini l → ∀ c N e us, E.sto l = some c → c.ty = .array (.lit N) e →
        accs e = some us →
        d.1.length = nWords us ∧ (∀ i w, d.1[i]? = some w → RdW E' s.mem ⟨l, j * nWords us + i⟩ w) ∧
        ValOfR E' e d.1 d.2.1 ∧ d.2.1 = Res.sum ((List.range (nWords us)).map fun i => d.2.2.1 i + d.2.2.2 i) ∧
        (∀ i w, d.1[i]? = some w → FRes E' ⟨l, j * nWords us + i⟩ w (d.2.2.1 i)) ∧
        ∀ i, i < nWords us → BlkDb E' s.mem ⟨l, j * nWords us + i⟩ (d.2.2.2 i) := by
    intro l j
    by_cases hq : Q l ∧ E.ini l ≤ j ∧ j < E'.ini l
    · obtain ⟨c, N, e, us, hc, -, hT, hu, hone, hne, hCl, hmg, hno, -, hN, -, -, hU, hty⟩ := hQ l hq.1
      have hpos : 0 < nWords us := by rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
      have hc' : E'.sto l = some c := by rw [hsto]; exact hc
      have hrd : ∀ i, ∃ w : Word, i < nWords us → RdW E' s.mem ⟨l, j * nWords us + i⟩ w := fun i => by
        by_cases hi : i < nWords us
        · obtain ⟨b1, b2⟩ := slot_in hq.2.1 hq.2.2 hi
          obtain ⟨h, hf, -, -⟩ := firstW_of_R1w (hU _ b1 b2).1
          obtain ⟨w, hw⟩ := RdW_ex (E := E') hf
          exact ⟨w, fun _ => hw⟩
        · exact ⟨default, fun h => absurd h hi⟩
      obtain ⟨rd, hrdf⟩ := Classical.axiomOfChoice hrd
      obtain ⟨ws, hws⟩ : ∃ ws : List Word, ws = (List.range (nWords us)).map rd := ⟨_, rfl⟩
      have hwl : ws.length = nWords us := by rw [hws, List.length_map, List.length_range]
      have hwi : ∀ i w, ws[i]? = some w → i < nWords us ∧ RdW E' s.mem ⟨l, j * nWords us + i⟩ w := by
        intro i w hw
        rw [hws, List.getElem?_map] at hw
        by_cases hi : i < nWords us
        · rw [List.getElem?_range hi, Option.map_some, Option.some.injEq] at hw
          subst hw; exact ⟨hi, hrdf i hi⟩
        · have h0 : (List.range (nWords us))[i]? = none :=
            List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hi)
          rw [h0] at hw; cases hw
      obtain ⟨R, hR⟩ := hty j hq.2.1 hq.2.2 ws hwl (fun i w hw => (hwi i w hw).2)
      obtain ⟨F, Z, hRs, hF, hZ⟩ := slot_debitsWV (E := E') s.mem hc' hT hu hone hpos
        (Nat.lt_of_lt_of_le hq.2.2 hN) hCl hmg hno hwl
        (fun o x hx hnw => by
          obtain ⟨hi, h, m, hm, hml, hxe, hf, -⟩ := hwi o x hx
          obtain ⟨b1, b2⟩ := slot_in hq.2.1 hq.2.2 hi
          have hnW : ¬ WordUnit E' ⟨l, j * nWords us + o⟩ := fun hW => by
            obtain ⟨n, P, hw⟩ := (hU _ b1 b2).2 hW; exact hnw n P hw
          exact ⟨h, m, hf hnW, hm, hxe⟩) hR
      refine ⟨(ws, R, F, Z), fun _ _ _ c' N' e' us' hc2 hT2 hu2 => ?_⟩
      rw [hc] at hc2; cases hc2; rw [hT] at hT2; cases hT2; rw [hu] at hu2; cases hu2
      exact ⟨hwl, fun i w hw => (hwi i w hw).2, hR, hRs, hF, hZ⟩
    · exact ⟨([], .zero, fun _ => .zero, fun _ => .zero), fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hq⟩
  obtain ⟨dat, hdat⟩ := Classical.axiomOfChoice fun l => Classical.axiomOfChoice (hD l)
  obtain ⟨G, hG⟩ : ∃ G : AllocLabel → Res,
      ∀ l, G l = if Q l then Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map fun j => (dat l j).2.1)
        else .zero :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Zf, hZf⟩ : ∃ Zf : Address → Res,
      ∀ a, Zf a = if Q a.label then (dat a.label (a.offset / nWl E a.label)).2.2.2 (a.offset % nWl E a.label)
        else .zero :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cr', hcr'⟩ : ∃ f : Ts → Res,
      ∀ t, f t = if NewP E E' s t = true then newCr E' s.mem t else cr t := ⟨_, fun _ => rfl⟩
  obtain ⟨db', hdb'⟩ : ∃ f : Ts → Res,
      ∀ t, f t = if NewP E E' s t = true then newDb E' s.mem Zf t else db t := ⟨_, fun _ => rfl⟩
  have hile : ∀ l, E.ini l ≤ E'.ini l := fun l => by
    by_cases hq : Q l
    · obtain ⟨c, N, e, us, -, -, -, -, -, -, -, -, -, hil, -⟩ := hQ l hq; exact hil
    · by_cases hq0 : Q0 l
      · obtain ⟨-, c, N, e, us, -, -, -, hil, -⟩ := hQ0 l hq0; exact hil
      · rw [hini l hq hq0]; exact Nat.le_refl _
  have hmono : ∀ a, IniW E a → IniW E' a := fun a ha c N e us hc hT hu => by
    have := ha c N e us (by rw [← hsto]; exact hc) hT hu
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (hile a.label))
  have hrc : ∀ l, E'.rc l = E.rc l := fun l => by
    by_cases hq : Q l
    · obtain ⟨c, N, e, us, -, -, -, -, -, -, -, -, -, hil, -, hrl, -⟩ := hQ l hq
      unfold TEnv.rc; rw [hri]; omega
    · by_cases hq0 : Q0 l
      · obtain ⟨-, c, N, e, us, -, -, -, hil, hrl, -⟩ := hQ0 l hq0
        unfold TEnv.rc; rw [hri]; omega
      · exact TEnv.rc_congr (hini l hq hq0) (hri l)
  have hNew : ∀ a : Address, IniW E' a → ¬ IniW E a → Q a.label ∨ Q0 a.label := fun a h1 h2 =>
    Classical.byContradiction fun hq => h2 ((IniW_congrU (hsto _)
      (hini _ (fun h => hq (.inl h)) (fun h => hq (.inr h)))).1 h1)
  have hVis : ∀ a : Address, IniW E' a → ¬ IniW E a → Vis E' a.label := fun a h1 h2 => by
    have hpfl : E.pfr a.label ≠ none := by
      rcases hNew a h1 h2 with hq | hq0
      · obtain ⟨c, N, e, us, -, -, -, -, -, -, -, -, -, -, -, -, hpfl, -⟩ := hQ _ hq; exact hpfl
      · obtain ⟨-, c, N, e, us, -, -, -, -, -, hpfl, -⟩ := hQ0 _ hq0; exact hpfl
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hpfl
    exact Vis_pfr (by rw [hpf]; exact hf)
  have hBlk : ∀ (a : Address) tw, IniW E' a → ¬ IniW E a → DesigAt E' s.mem a tw → BlkDb E' s.mem a (Zf a) := by
    intro ⟨l, o⟩ tw h1 h2 hD
    rcases hNew _ h1 h2 with hq | hq0
    · obtain ⟨c, N, e, us, hc, -, hT, hu, hone, hne, -⟩ := hQ l hq
      have hpos : 0 < nWords us := by rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
      have hc' : E'.sto l = some c := by rw [hsto]; exact hc
      have b2 : o < E'.ini l * nWords us := (IniW_iff hc' hT hu).1 h1
      have b1 : E.ini l * nWords us ≤ o := Nat.le_of_not_lt fun h => h2 ((IniW_iff hc hT hu).2 h)
      have j1 : E.ini l ≤ o / nWords us := (Nat.le_div_iff_mul_le hpos).2 b1
      have j2 : o / nWords us < E'.ini l := (Nat.div_lt_iff_lt_mul hpos).2 b2
      obtain ⟨-, -, -, -, -, hZ⟩ := hdat l (o / nWords us) hq j1 j2 c N e us hc hT hu
      have hb := hZ (o % nWords us) (Nat.mod_lt _ hpos)
      rw [Nat.div_add_mod'] at hb
      rw [hZf]
      show BlkDb E' s.mem ⟨l, o⟩ (if Q l then (dat l (o / nWl E l)).2.2.2 (o % nWl E l) else .zero)
      rw [if_pos hq, nWl_eq hc hT hu]
      exact hb
    · obtain ⟨hnq, c, N, e, us, -, -, -, -, -, -, -, hU0⟩ := hQ0 l hq0
      rw [hZf]
      show BlkDb E' s.mem ⟨l, o⟩ (if Q l then (dat l (o / nWl E l)).2.2.2 (o % nWl E l) else .zero)
      rw [if_neg hnq]
      exact (hU0 o h1 h2).2 tw hD
  have hzero : ∀ t m, s.mem[t]? = some m → Q0 m.loc.label → IniW E' m.loc → ¬ IniW E m.loc →
      newDb E' s.mem Zf t = .zero ∧ newCr E' s.mem t = .zero := by
    intro t m hm hq0 h1 h2
    obtain ⟨hnq, c, N, e, us, -, -, -, -, -, -, -, hU0⟩ := hQ0 _ hq0
    have hna := (hU0 m.loc.offset h1 h2).1
    have hZ0 : Zf m.loc = .zero := by rw [hZf, if_neg hnq]
    exact ⟨newDb_zero hm hna hZ0, newCr_zero hm hna⟩
  have hNP : ∀ t, NewP E E' s t = true → ∃ m, s.mem[t]? = some m ∧ IniW E' m.loc ∧ ¬ IniW E m.loc :=
    fun t h => by simpa only [NewP, decide_eq_true_eq] using h
  obtain ⟨hC', hz⟩ := PromCr_raise (cr' := cr') (db' := db') hC hsto htid hpf hmono hrc hbx
    (fun tw m _ hm h1 h2 => by
      have hn : NewP E E' s tw = true := by
        simp only [NewP, decide_eq_true_eq]; exact ⟨m, hm, h1, h2⟩
      rw [hcr', hdb', if_pos hn, if_pos hn]
      exact ⟨newDb_res hm ⟨hVis _ h1 h2, h1⟩ (fun hD => hBlk _ tw h1 h2 hD), newCr_res hm ⟨hVis _ h1 h2, h1⟩⟩)
    (fun tw _ hn => by
      rw [hcr', hdb', if_neg (by simp [hn]), if_neg (by simp [hn])]; exact ⟨rfl, rfl⟩)
  obtain ⟨L, hndL, hcov, hoff, rfl, hent⟩ := hH
  -- the new debits and credits sit at new promises
  have eDb : pSum s db' = pSum s db + Res.sum ((s.promises.filter (NewP E E' s)).map (newDb E' s.mem Zf)) := by
    unfold pSum
    rw [sum_new (f := db) (new := NewP E E' s)
      (fun t _ hn => by rw [hdb', if_neg (by simp [hn])]) (fun t ht hn => (hz t ht hn).2)]
    congr 1
    exact sum_congrB fun t ht => by rw [List.mem_filter] at ht; rw [hdb', if_pos ht.2]
  have eCr : pSum s cr' = pSum s cr + Res.sum ((s.promises.filter (NewP E E' s)).map (newCr E' s.mem)) := by
    unfold pSum
    rw [sum_new (f := cr) (new := NewP E E' s)
      (fun t _ hn => by rw [hcr', if_neg (by simp [hn])]) (fun t ht hn => (hz t ht hn).1)]
    congr 1
    exact sum_congrB fun t ht => by rw [List.mem_filter] at ht; rw [hcr', if_pos ht.2]
  obtain ⟨lo, hlo⟩ : ∃ lo : AllocLabel → Nat, ∀ l, lo l = E.ini l * nWl E l := ⟨_, fun _ => rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi : AllocLabel → Nat, ∀ l, hi l = E'.ini l * nWl E l := ⟨_, fun _ => rfl⟩
  have hin : ∀ t ∈ s.promises.filter (NewP E E' s), ∃ m, s.mem[t]? = some m ∧ m.loc.label ∈ L ∧
      lo m.loc.label ≤ m.loc.offset ∧ m.loc.offset < hi m.loc.label := by
    intro t ht
    rw [List.mem_filter] at ht
    obtain ⟨m, hm, h1, h2⟩ := hNP t ht.2
    have hdat0 : ∃ c N e us, E.sto m.loc.label = some c ∧ c.ty = .array (.lit N) e ∧ accs e = some us := by
      rcases hNew _ h1 h2 with hq | hq0
      · obtain ⟨c, N, e, us, hc, -, hT, hu, -⟩ := hQ _ hq; exact ⟨c, N, e, us, hc, hT, hu⟩
      · obtain ⟨-, c, N, e, us, hc, hT, hu, -⟩ := hQ0 _ hq0; exact ⟨c, N, e, us, hc, hT, hu⟩
    obtain ⟨c, N, e, us, hc, hT, hu⟩ := hdat0
    have hc' : E'.sto m.loc.label = some c := by rw [hsto]; exact hc
    refine ⟨m, hm, hcov _ c hc, ?_, ?_⟩
    · rw [hlo, nWl_eq hc hT hu]; exact Nat.le_of_not_lt fun h => h2 ((IniW_iff hc hT hu).2 h)
    · rw [hhi, nWl_eq hc hT hu]; exact (IniW_iff hc' hT hu).1 h1
  -- the payment, label by label
  have hK : Res.sum ((s.promises.filter (NewP E E' s)).map (newDb E' s.mem Zf)) =
      Res.sum ((s.promises.filter (NewP E E' s)).map (newCr E' s.mem)) + Res.sum (L.map G) := by
    rw [sum_units (newDb E' s.mem Zf) hndL hin, sum_units (newCr E' s.mem) hndL hin, ← sum_map_add]
    refine sum_congrB fun l _ => ?_
    by_cases hq : Q l
    · obtain ⟨c, N, e, us, hc, ho, hT, hu, hone, hne, -, -, -, hil, -, hrl, hpfl, hU, -⟩ := hQ l hq
      have hpos : 0 < nWords us := by rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
      have hc' : E'.sto l = some c := by rw [hsto]; exact hc
      have hrcQ : E'.rc l = E.rini l := by unfold TEnv.rc; rw [hri]; omega
      have hlh := Nat.mul_le_mul_right (nWords us) hil
      have hfil : ∀ o ∈ List.range' (lo l) (hi l - lo l),
          (s.promises.filter (NewP E E' s)).filter (AtB s.mem ⟨l, o⟩) = s.promises.filter (AtB s.mem ⟨l, o⟩) := by
        intro o ho
        rw [List.mem_range'_1, hlo, hhi, nWl_eq hc hT hu] at ho
        have ho2 : o < E'.ini l * nWords us := by omega
        refine filter_sub fun t _ hat => ?_
        obtain ⟨m, hm, hml⟩ := AtB_iff.1 hat
        simp only [NewP, decide_eq_true_eq]
        refine ⟨m, hm, ?_, ?_⟩
        · rw [hml]; exact (IniW_iff hc' hT hu).2 ho2
        · rw [hml]; exact fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ((IniW_iff hc hT hu).1 h) ho.1)
      have eD : ∀ f : Nat → Res,
          Res.sum ((List.range' (lo l) (hi l - lo l)).map fun o =>
            Res.sum (((s.promises.filter (NewP E E' s)).filter (AtB s.mem ⟨l, o⟩)).map f)) =
          Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map fun j =>
            Res.sum ((List.range (nWords us)).map fun i =>
              Res.sum ((s.promises.filter (AtB s.mem ⟨l, j * nWords us + i⟩)).map f))) := by
        intro f
        have e1 := sum_range_mul (fun o => Res.sum ((s.promises.filter (AtB s.mem ⟨l, o⟩)).map f))
          (nWords us) (E.ini l) (E'.ini l - E.ini l)
        rw [Nat.sub_mul] at e1
        refine Eq.trans ?_ e1
        rw [← nWl_eq hc hT hu, ← hlo, ← hhi]
        exact sum_congrB fun o ho => by rw [hfil o ho]
      refine (eD _).trans (Eq.trans ?_ (congrArg (· + G l) (eD _).symm))
      show _ = _ + G l
      rw [hG l, if_pos hq, ← sum_map_add]
      refine sum_congrB fun j hj => ?_
      rw [List.mem_range'_1] at hj
      have hj1 : E.ini l ≤ j := hj.1
      have hj2 : j < E'.ini l := by
        have h3 := hj.2; rw [Nat.add_sub_cancel' hil] at h3; exact h3
      obtain ⟨hwl, hrd, -, hRs, hF, hZ⟩ := hdat l j hq hj1 hj2 c N e us hc hT hu
      rw [hRs]
      refine slot_pay hnd (fun i hi => (hU _ (slot_in hj1 hj2 hi).1 (slot_in hj1 hj2 hi).2).1)
        (fun i hi => ⟨by rw [hpf]; exact hpfl, (IniW_iff hc' hT hu).2 (slot_in hj1 hj2 hi).2, fun hr => by
          have h3 := (IniWr_iff hc' hT hu).1 hr
          rw [hrcQ] at h3
          have q := Nat.mul_le_mul_right (nWords us) hrl
          have q1 := (slot_in hj1 hj2 hi).1
          omega⟩)
        ⟨c, hc', by rw [htid]; exact ho⟩ hwl hrd hF (fun i hi => ⟨?_, hZ i hi⟩)
      rw [hZf]
      show (if Q l then (dat l ((j * nWords us + i) / nWl E l)).2.2.2 ((j * nWords us + i) % nWl E l)
        else .zero) = _
      rw [if_pos hq, nWl_eq hc hT hu, (slot_divmod hi).1, (slot_divmod hi).2]
    · by_cases hq0 : Q0 l
      · have hz0 : ∀ f : Nat → Res, (∀ t m, s.mem[t]? = some m → m.loc.label = l → NewP E E' s t = true →
            f t = .zero) →
            Res.sum ((List.range' (lo l) (hi l - lo l)).map fun o =>
              Res.sum (((s.promises.filter (NewP E E' s)).filter (AtB s.mem ⟨l, o⟩)).map f)) = .zero := by
          intro f hf
          refine sum_map_eq_zero fun o _ => sum_map_eq_zero fun t ht => ?_
          rw [List.mem_filter, List.mem_filter] at ht
          obtain ⟨m, hm, hml⟩ := AtB_iff.1 ht.2
          exact hf t m hm (by rw [hml]) ht.1.2
        have hzz : ∀ t m, s.mem[t]? = some m → m.loc.label = l → NewP E E' s t = true →
            newDb E' s.mem Zf t = .zero ∧ newCr E' s.mem t = .zero := fun t m hm hml hn => by
          obtain ⟨m', hm', h1, h2⟩ := hNP t hn
          have e : m' = m := Option.some.inj (hm'.symm.trans hm)
          have h1' : IniW E' m.loc := by rw [← e]; exact h1
          have h2' : ¬ IniW E m.loc := by rw [← e]; exact h2
          exact hzero t m hm (by rw [hml]; exact hq0) h1' h2'
        rw [hz0 _ (fun t m hm hml hn => (hzz t m hm hml hn).1),
          hz0 _ (fun t m hm hml hn => (hzz t m hm hml hn).2), hG l, if_neg hq]
        exact (Res.add_zero _).symm
      · have e0 : hi l - lo l = 0 := by rw [hlo, hhi, hini l hq hq0, Nat.sub_self]
        rw [e0, hG l, if_neg hq]
        exact (Res.add_zero _).symm
  -- the lists: `Q` labels append their new slots, `Q0` labels re-chosen, the rest kept
  have hx : ∀ l, ∃ Rs : List Res, Q0 l → l ∈ L → HeldEntryL E' s l Rs ∧ Res.sum Rs = Res.sum (S l) := by
    intro l
    by_cases h : Q0 l ∧ l ∈ L
    · obtain ⟨-, c, N, e, us, -, -, -, -, -, -, hE0, -⟩ := hQ0 l h.1
      obtain ⟨Rs, h1, h2⟩ := HeldEntry.toS (hE0 _ (hent l h.2).entry)
      exact ⟨Rs, fun _ _ => ⟨h1, h2.symm⟩⟩
    · exact ⟨[], fun a b => absurd ⟨a, b⟩ h⟩
  obtain ⟨T0, hT0⟩ := Classical.axiomOfChoice hx
  obtain ⟨S', hS'⟩ : ∃ S' : AllocLabel → List Res, ∀ l, S' l =
      if Q l then S l ++ (List.range' (E.ini l) (E'.ini l - E.ini l)).map (fun j => (dat l j).2.1)
      else if Q0 l then T0 l else S l := ⟨_, fun _ => rfl⟩
  have hent' : ∀ l, l ∈ L → HeldEntryL E' s l (S' l) := by
    intro l hl
    rw [hS' l]
    by_cases hq : Q l
    · obtain ⟨c, N, e, us, hc, -, hT, hu, hone, hne, -, -, -, hil, hN, hrl, hpfl, hU, -⟩ := hQ l hq
      have hpos : 0 < nWords us := by rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
      rw [if_pos hq]
      exact HeldEntryL_raiseW (hent l hl) (hsto l) htid (hpf l) hfp (hri l) hc hT hu hv hil hN hrl hpfl
        (fun o h1 h2 => by
          obtain ⟨h, hf, -, hab⟩ := firstW_of_R1w (hU o h1 h2).1
          exact ⟨h, hf, fun t m' a1 a2 a3 => List.mem_append_left _ (hab t m' a1 a2 a3)⟩)
        (fun j hj1 hj2 ws hl hrd => by
          obtain ⟨hwl, hrd0, hR, -⟩ := hdat l j hq hj1 hj2 c N e us hc hT hu
          rw [rdW_list_eq hl hwl hrd hrd0]
          exact hR)
        (fun j h0 => absurd h0 (Nat.pos_iff_ne_zero.1 hpos))
    · rw [if_neg hq]
      by_cases hq0 : Q0 l
      · rw [if_pos hq0]; exact (hT0 l hq0 hl).1
      · rw [if_neg hq0]
        exact HeldEntryL_tr (hent l hl) (hsto l) (hini l hq hq0) (hri l)
          (fun o w hw => by
            rw [PromAt_congr (a := ⟨l, o⟩) (hsto l) htid (hpf l) hfp (hini l hq hq0) (hrc l)]
            exact hw) hv
  have eS : ∀ l ∈ L, Res.sum (S' l) = Res.sum (S l) + G l := by
    intro l hl
    rw [hS' l, hG l]
    by_cases hq : Q l
    · rw [if_pos hq, if_pos hq, Res.sum_append]
    · rw [if_neg hq, if_neg hq, Res.add_zero]
      by_cases hq0 : Q0 l
      · rw [if_pos hq0]; exact (hT0 l hq0 hl).2
      · rw [if_neg hq0]
  refine ⟨Res.sum (L.map fun l => Res.sum (S' l)), S', cr', db',
    ⟨L, hndL, fun l c hc => hcov l c (by rw [← hsto l]; exact hc), fun l hl => ?_, rfl, hent'⟩,
    hC', fun tw m htw hm hnq => ?_, ?_, fun l hq hq0 => by rw [hS' l, if_neg hq, if_neg hq0],
    fun l j hq hj => ?_, fun l j hq hj1 hj2 c N e us hc hT hu => ?_⟩
  · rw [hS' l]
    by_cases hq : Q l
    · obtain ⟨c, -, -, -, hc, -⟩ := hQ l hq; exact absurd (hcov l c hc) hl
    · rw [if_neg hq]
      by_cases hq0 : Q0 l
      · obtain ⟨-, c, -, -, -, hc, -⟩ := hQ0 l hq0; exact absurd (hcov l c hc) hl
      · rw [if_neg hq0]; exact hoff l hl
  · by_cases hn : NewP E E' s tw = true
    · obtain ⟨m', hm', h1, h2⟩ := hNP tw hn
      have e : m' = m := Option.some.inj (hm'.symm.trans hm)
      have h1' : IniW E' m.loc := by rw [← e]; exact h1
      have h2' : ¬ IniW E m.loc := by rw [← e]; exact h2
      have hq0 : Q0 m.loc.label := (hNew _ h1' h2').resolve_left hnq
      obtain ⟨z1, z2⟩ := hzero tw m hm hq0 h1' h2'
      obtain ⟨y1, y2⟩ := hz tw htw hn
      rw [hcr', hdb', if_pos hn, if_pos hn, z1, z2, y1, y2]
      exact ⟨rfl, rfl⟩
    · rw [hcr', hdb', if_neg hn, if_neg hn]
      exact ⟨rfl, rfl⟩
  · rw [sum_congrB eS, sum_map_add, eDb, eCr, hK]
    exact Res.ext fun k => by simp only [Res.add_apply]; omega
  · obtain ⟨c, N, e, us, hc, -, hT, -⟩ := hQ l hq
    have hlen := HeldEntryL_len (hent l (hcov l c hc)) hc hT
    rw [hS' l, if_pos hq, List.getElem?_append_left (by omega)]
  · obtain ⟨c0, N0, e0, us0, hc0, ho, hT0', hu0, hone, hne, -, -, -, hil, -, hrl, hpfl, hU, -⟩ := hQ l hq
    rw [hc] at hc0; cases hc0
    rw [hT] at hT0'; cases hT0'
    rw [hu] at hu0; cases hu0
    have hc' : E'.sto l = some c := by rw [hsto]; exact hc
    have hrcQ : E'.rc l = E.rini l := by unfold TEnv.rc; rw [hri]; omega
    have hlen := HeldEntryL_len (hent l (hcov l c hc)) hc hT
    have e1 : E.ini l + 1 * (j - (S l).length) = j := by omega
    have hget : (S' l)[j]? = some (dat l j).2.1 := by
      rw [hS' l, if_pos hq, List.getElem?_append_right (by omega), List.getElem?_map,
        List.getElem?_range' (by omega), e1]
      try rfl
    obtain ⟨hwl, hrd, hR, hRs, hF, hZ⟩ := hdat l j hq hj1 hj2 c N e us hc hT hu
    refine ⟨(dat l j).1, (dat l j).2.1, hget, hwl, hrd, hR, ⟨_, _, hRs, hF, hZ⟩, ?_⟩
    have hpay := slot_pay (Zf := Zf) hnd (fun i hi => (hU _ (slot_in hj1 hj2 hi).1 (slot_in hj1 hj2 hi).2).1)
      (fun i hi => ⟨by rw [hpf]; exact hpfl, (IniW_iff hc' hT hu).2 (slot_in hj1 hj2 hi).2, fun hr => by
        have h3 := (IniWr_iff hc' hT hu).1 hr
        rw [hrcQ] at h3
        have q := Nat.mul_le_mul_right (nWords us) hrl
        have q1 := (slot_in hj1 hj2 hi).1
        omega⟩)
      ⟨c, hc', by rw [htid]; exact ho⟩ hwl hrd hF (fun i hi => ⟨by
        rw [hZf]
        show (if Q l then (dat l ((j * nWords us + i) / nWl E l)).2.2.2 ((j * nWords us + i) % nWl E l)
          else .zero) = _
        rw [if_pos hq, nWl_eq hc hT hu, (slot_divmod hi).1, (slot_divmod hi).2], hZ i hi⟩)
    have hconv : ∀ i ∈ List.range (nWords us), ∀ t ∈ s.promises.filter (AtB s.mem ⟨l, j * nWords us + i⟩),
        NewP E E' s t = true := by
      intro i hi t ht
      rw [List.mem_range] at hi
      rw [List.mem_filter] at ht
      obtain ⟨m, hm, hml⟩ := AtB_iff.1 ht.2
      obtain ⟨b1, b2⟩ := slot_in hj1 hj2 hi
      simp only [NewP, decide_eq_true_eq]
      refine ⟨m, hm, ?_, ?_⟩
      · rw [hml]; exact (IniW_iff hc' hT hu).2 b2
      · rw [hml]; exact fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ((IniW_iff hc hT hu).1 h) b1)
    have eD : Res.sum ((List.range (nWords us)).map fun i =>
          Res.sum ((s.promises.filter (AtB s.mem ⟨l, j * nWords us + i⟩)).map db')) =
        Res.sum ((List.range (nWords us)).map fun i =>
          Res.sum ((s.promises.filter (AtB s.mem ⟨l, j * nWords us + i⟩)).map (newDb E' s.mem Zf))) :=
      sum_congrB fun i hi => sum_congrB fun t ht => by rw [hdb', if_pos (hconv i hi t ht)]
    have eC : Res.sum ((List.range (nWords us)).map fun i =>
          Res.sum ((s.promises.filter (AtB s.mem ⟨l, j * nWords us + i⟩)).map cr')) =
        Res.sum ((List.range (nWords us)).map fun i =>
          Res.sum ((s.promises.filter (AtB s.mem ⟨l, j * nWords us + i⟩)).map (newCr E' s.mem))) :=
      sum_congrB fun i hi => sum_congrB fun t ht => by rw [hcr', if_pos (hconv i hi t ht)]
    rw [eD, eC, hRs]
    exact hpay

end RaisePay




section PlantQ
open TermCut TermSys TermMain TermPlantR TermPlantW TermPlantL TermPlantE TermPlantS

/-- (dedup) master of `ThSysAt_plantQ`: also exports `KeepNW` (old non-word credits kept). -/
theorem ThSysAt_plantQK {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Sp : TermRun.Cfg → TermRun.Cfg → Prop} {c0 : TermRun.Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {Q R : AllocLabel → Prop}
    {F : AllocLabel → Ts} {Np : AllocLabel → Nat}
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hRQ : ∀ l, R l → Q l)
    (hQ : ∀ l, Q l → ∃ c N e us, Eg.sto l = some c ∧ c.owner = some g.i ∧ Eg.pfr l = none ∧
      c.ty = .array (.lit N) e ∧ accs e = some us ∧ Eg.rini l ≤ Eg.ini l ∧
      Eg.ini l ≤ Np l ∧ Np l ≤ N ∧ FlipOK (Cut Eg g.i S) (stOf mem pairs th) l ∧
      (∀ o, Eg.ini l * nWords us ≤ o → o < Np l * nWords us →
        ∃ h, FirstW mem ⟨l, o⟩ h ∧
          ∀ t m', h < t → mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ th.promises ++ Eg.fpOf g.i) ∧
      ((¬ R l ∧
        (us = [] ∨ (dwf e = true ∧
        (∀ j, Eg.ini l ≤ j → j < Np l → ∀ ws : List Word, ws.length = nWords us →
          (∀ i w, ws[i]? = some w → ∃ h m, FirstW mem ⟨l, j * nWords us + i⟩ h ∧ mem[h]? = some m ∧ w = mw m) →
          ValOfR (Cut (plantS Eg Q F Np) g.i S) e ws .zero) ∧
          (TermBlkZ.SkFree e = true ∨ (Clo e ∧ TermTv.mg e = true))))) ∨
      (R l ∧ (∀ u ∈ us, u = .one) ∧ us ≠ [] ∧ Clo e ∧ mg e = true ∧ Ty.noOwnIn [] e = true ∧
        (∀ o, Eg.ini l * nWords us ≤ o → o < Np l * nWords us →
          (∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val = .undef ∧ t0 ∉ th.promises ∧
            (∃ t, AtA mem ⟨l, o⟩ t0 t = true) ∧
            ∀ t m, mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ th.promises) ∧
          (WordUnit (Cut (plantS Eg Q F Np) g.i S) ⟨l, o⟩ →
            ∃ n P, WordAt (Cut (plantS Eg Q F Np) g.i S) ⟨l, o⟩ n P)) ∧
        ∀ j, Eg.ini l ≤ j → j < Np l → ∀ ws : List Word, ws.length = nWords us →
          (∀ i w, ws[i]? = some w → RdW (Cut (plantS Eg Q F Np) g.i S) mem ⟨l, j * nWords us + i⟩ w) →
          ∃ Rv, ValOfR (Cut (plantS Eg Q F Np) g.i S) e ws Rv)))
    (hfo : FpOK (Cut Eg g.i S) (stOf mem pairs th))
    (hMI : MemInv g (Cut (plantS Eg Q F Np) g.i S) (stOf mem pairs th)) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plantS Eg Q F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' ∧
      KeepNW (Cut Eg g.i S) mem th.promises cr cr' := by
  classical
  obtain ⟨hRE, hTE, hm, hHP, hHS, hC⟩ := h
  have hH : MemHeld (Cut Eg g.i S) (stOf mem pairs th) (HP + HS) :=
    MemHeld_join (fun _ _ h1 h2 => Cut_cov h1 h2) hHP hHS
  obtain ⟨ρ, η, cx, Rf, Rs, hE0, hE, hTy, htv, hFI, hsum⟩ := hRE
  have hQo : ∀ l, Q l → ∃ c, Eg.sto l = some c ∧ c.owner = some g.i := fun l hl => by
    obtain ⟨c, -, -, -, hc, ho, -⟩ := hQ l hl; exact ⟨c, hc, ho⟩
  have e2 := CE_withSto_CutS (F := F) (Np := Np) hE0 hQo
  rw [← hE0] at hm hH hC hfo
  have htid : η.tid = g.i := congrArg TEnv.tid hE0
  have hini : η.ini = Eg.ini := congrArg TEnv.ini hE0
  have hrini : η.rini = Eg.rini := congrArg TEnv.rini hE0
  have hpfr : η.pfr = Eg.pfr := congrArg TEnv.pfr hE0
  have hfpE : η.fp = Eg.fpOf g.i := congrArg TEnv.fp hE0
  have hstoQ : ∀ l c, Eg.sto l = some c → c.owner = some g.i → η.sto l = some c := fun l c hc ho => by
    show (CE η).sto l = some c
    rw [hE0]; exact cutSto_own hc ho
  let P1 : AllocLabel → Option Ts := fun l' => if Q l' then some (F l') else η.pfr l'
  let I2 : AllocLabel → Nat := fun l' => if Q l' then Np l' else η.ini l'
  have hP1 : ∀ l' f, η.pfr l' = some f → P1 l' = some f := fun l' f h => by
    by_cases he : Q l'
    · obtain ⟨c, -, -, -, -, -, hn, -⟩ := hQ l' he
      rw [hpfr, hn] at h; cases h
    · simp [P1, he, h]
  have hI2 : ∀ l', η.ini l' ≤ I2 l' := fun l' => by
    by_cases he : Q l'
    · obtain ⟨c, N, e, -, -, -, -, -, -, -, hNp, -⟩ := hQ l' he
      simp only [I2, he, ite_true]; rw [hini]; exact hNp
    · simp [I2, he]
  have hx : Ext η (η.withSto η.sto I2 P1 η.seen) :=
    Ext_withSto hE.2.1 (fun _ _ h => h) hI2 hP1
  have hE' : EnvOK p (η.withSto η.sto I2 P1 η.seen) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
  -- the flipped (`Ef`) and raised (`E2`) code views
  have hVf : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR (CE η) T vs R →
      ValOfR (CE (η.withSto η.sto η.ini P1 η.seen)) T vs R := fun h =>
    ValOfR_mono (η₁ := CE η) (η₂ := CE (η.withSto η.sto η.ini P1 η.seen)) rfl rfl
      (fun _ _ h => h) (fun _ => Nat.le_refl _) h hP1 (fun _ _ h => h) (fun _ => Nat.le_refl _)
  have hV2 : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR (CE (η.withSto η.sto η.ini P1 η.seen)) T vs R →
      ValOfR (CE (η.withSto η.sto I2 P1 η.seen)) T vs R := fun h =>
    ValOfR_mono (η₁ := CE (η.withSto η.sto η.ini P1 η.seen)) (η₂ := CE (η.withSto η.sto I2 P1 η.seen)) rfl rfl
      (fun _ _ h => h) hI2 h (fun _ _ h => h) (fun _ _ h => h) (fun _ => Nat.le_refl _)
  have hV02 : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR (CE η) T vs R →
      ValOfR (CE (η.withSto η.sto I2 P1 η.seen)) T vs R := fun h => hV2 (hVf h)
  have hvisl : ∀ l', ¬ Q l' → Vis (CE (η.withSto η.sto I2 P1 η.seen)) l' → Vis (CE η) l' :=
    fun l' hne hv hpr => hv ⟨hpr.1, by simpa [CE, TEnv.withSto, P1, hne] using hpr.2⟩
  have e2' : CE (η.withSto η.sto I2 P1 η.seen) = Cut (plantS Eg Q F Np) g.i S := e2
  obtain ⟨H', cr', db', hH', hC', heq, hKN⟩ := PromCrK_liftQK (hsto := fun _ => rfl) (E2 := CE (η.withSto η.sto I2 P1 η.seen)) (Ql := Q) hC
    (fun tw m R hm' hp hla => by
      obtain ⟨-, -, -, -, -, -, -, -, -, hpf, -⟩ := hp
      obtain ⟨c, -, -, -, -, -, hn, -⟩ := hQ _ hla
      exact hpf (by show η.pfr m.loc.label = none; rw [hpfr]; exact hn))
    (fun tw m R hm' hla hp => TermPlant.PlantCr_mono (E := CE η) (E' := CE (η.withSto η.sto I2 P1 η.seen))
      (s := stOf mem pairs th) (s' := stOf mem pairs th)
      (fun _ _ => rfl) (Nat.le_refl _) rfl (MemInv_promLt hm) rfl rfl
      (fun h => by
        show P1 m.loc.label ≠ none
        simp only [P1, hla, ite_false]; exact h)
      (fun h => (WordUnit_congr rfl).1 h)
      (fun _ _ h => by
        have hvq : Vis (CE (η.withSto η.sto I2 P1 η.seen)) m.loc.label ↔ Vis (CE η) m.loc.label :=
          Vis_congr rfl rfl (by show P1 m.loc.label = η.pfr m.loc.label; simp [P1, hla])
        unfold FpAt at h ⊢; rw [hvq] at h; exact h)
      (fun S ws R0 h => hV02 h) hp)
    (fun cr0 hC0 => by
      obtain ⟨H1, cr1, db1, hH1, hC1, hk, e⟩ := MemHeld_flipQ (E := CE η)
        (E' := CE (η.withSto η.sto η.ini P1 η.seen)) (Q := Q)
        hm hH hC0 hpa (fun _ => rfl) (fun _ => rfl)
        (fun l' hv hpr => hv ⟨hpr.1, by
          by_cases he : Q l'
          · have := hpr.2; simp [CE, TEnv.withSto, P1, he] at this
          · have := hpr.2; simpa [CE, TEnv.withSto, P1, he] using this⟩)
        (fun l' hne hv hpr => hv ⟨hpr.1, by simpa [CE, TEnv.withSto, P1, hne] using hpr.2⟩)
        hVf (fun l hl => by
          obtain ⟨c, N, e, -, -, -, -, -, -, -, -, -, hfl, -⟩ := hQ l hl
          rw [← hE0] at hfl; exact hfl) hfo
        (fun l hl => by
          obtain ⟨c, -, -, -, hc, ho, -⟩ := hQ l hl
          exact ⟨c, hstoQ l c hc ho, by show c.owner = some η.tid; rw [htid]; exact ho⟩)
        (fun l' hne => by
          by_cases he : Q l'
          · simp [CE, TEnv.withSto, P1, he]
          · simpa [CE, TEnv.withSto, P1, he] using hne)
        (fun l' hne h1 => by simpa [CE, TEnv.withSto, P1, hne] using h1)
        rfl (fun _ => rfl) rfl (fun _ _ h => h)
      have hil : ∀ l, (CE (η.withSto η.sto η.ini P1 η.seen)).ini l = Eg.ini l := fun l => by
        show η.ini l = Eg.ini l; rw [hini]
      have hil2 : ∀ l, Q l → (CE (η.withSto η.sto I2 P1 η.seen)).ini l = Np l := fun l hl => by
        show I2 l = Np l; simp [I2, hl]
      obtain ⟨H2, cr2, db2, hH2, hC2, hk2, e2⟩ := raise_pay (Q := R) (Q0 := fun l => Q l ∧ ¬ R l)
        (E' := CE (η.withSto η.sto I2 P1 η.seen)) hH1 hC1
        (hm.2.2.2.2.2.2.2.2.2.2.1 : (stOf mem pairs th).promises.Nodup)
        (fun _ => rfl) rfl (fun _ => rfl) rfl (fun _ => rfl)
        (fun l hr hq0 => by
          have hq : ¬ Q l := fun hq => hq0 ⟨hq, hr⟩
          simp [CE, TEnv.withSto, I2, hq])
        (fun l hq0 => by
          obtain ⟨c, N, e, us, hc, ho, -, hT, hu, hrl, hNp, hNN, -, hR1, hZZ⟩ := hQ l hq0.1
          obtain ⟨-, hZ⟩ := hZZ.resolve_right (fun h => hq0.2 h.1)
          have hc2 : (CE (η.withSto η.sto I2 P1 η.seen)).sto l = some c := hstoQ l c hc ho
          have hcE : (CE (η.withSto η.sto η.ini P1 η.seen)).sto l = some c := hstoQ l c hc ho
          have hrl' : (CE (η.withSto η.sto η.ini P1 η.seen)).rini l ≤
              (CE (η.withSto η.sto η.ini P1 η.seen)).ini l := by
            show η.rini l ≤ η.ini l; rw [hini, hrini]; exact hrl
          have hil' : (CE (η.withSto η.sto η.ini P1 η.seen)).ini l ≤
              (CE (η.withSto η.sto I2 P1 η.seen)).ini l := by
            rw [hil, hil2 l hq0.1]; exact hNp
          have hN' : (CE (η.withSto η.sto I2 P1 η.seen)).ini l ≤ N := by rw [hil2 l hq0.1]; exact hNN
          have hpfl : (CE (η.withSto η.sto η.ini P1 η.seen)).pfr l ≠ none := by
            show P1 l ≠ none; simp [P1, hq0.1]
          refine ⟨hq0.2, c, N, e, us, hcE, hT, hu, hil', hrl', hpfl, fun R0 he => ?_, fun o h1 h2 => ?_⟩
          · rcases hZ with rfl | ⟨hd, hslot, -⟩
            · exact HeldEntry_raiseZ he rfl rfl hcE hT hu hV2 hil' hN' hrl'
            · exact HeldEntry_raiseU he rfl rfl rfl rfl rfl hcE hT hu hd hV2 hil' hN' hrl' hpfl
                (fun o h1 h2 => by
                  rw [hil] at h1; rw [hil2 l hq0.1] at h2
                  obtain ⟨hh, hfw, hab⟩ := hR1 o h1 h2
                  refine ⟨hh, hfw, fun t m' a1 a2 a3 => ?_⟩
                  have := hab t m' a1 a2 a3
                  show t ∈ th.promises ++ η.fp
                  rw [hfpE]; exact this)
                (fun j h1 h2 ws hl hw => by
                  rw [hil] at h1; rw [hil2 l hq0.1] at h2
                  rw [e2']; exact hslot j h1 h2 ws hl hw)
          · have hup : o < Np l * nWords us := by
              have := (IniW_iff hc2 hT hu).1 h1
              rw [hil2 l hq0.1] at this; exact this
            have hlo : Eg.ini l * nWords us ≤ o := by
              apply Nat.le_of_not_lt; intro hlt; apply h2
              exact (IniW_iff hcE hT hu).2 (by rw [hil]; exact hlt)
            rcases hZ with rfl | ⟨hd, hsl, hsk⟩
            · exfalso; simp [nWords] at hup
            refine ⟨noWordAt_dwf (o := o) hc2 (by rw [hT]; exact hd), fun tw hD => ?_⟩
            have hjr : ∀ jj, jj * nWords us ≤ o → o < jj * nWords us + nWords us →
                Eg.ini l ≤ jj ∧ jj < Np l := fun jj hj1 hj2 => by
              have hj2' : jj * nWords us + nWords us > o := hj2
              have hup' : Np l * nWords us > o := hup
              constructor
              · apply Nat.le_of_not_lt; intro hlt
                have := Nat.mul_le_mul_right (nWords us) (Nat.succ_le_of_lt hlt)
                rw [Nat.succ_mul] at this; omega
              · apply Nat.lt_of_not_le; intro hle
                have := Nat.mul_le_mul_right (nWords us) hle; omega
            rw [e2'] at hD ⊢
            refine TermBlkZ.blkDb_zero (c := c) (N := N) (e := e) (us := us) ?_ hT hu hsk
              (Nat.lt_of_lt_of_le hup (Nat.mul_le_mul_right _ hNN))
              (fun jj _ hj1 hj2 i hi => ?_)
              (fun jj _ hj1 hj2 ws hl hw => hsl jj (hjr jj hj1 hj2).1 (hjr jj hj1 hj2).2 ws hl hw)
            · rw [← e2']; exact hc2
            · obtain ⟨r1, r2⟩ := hjr jj hj1 hj2
              have q1 := Nat.mul_le_mul_right (nWords us) r1
              have q2 := Nat.mul_le_mul_right (nWords us) (Nat.succ_le_of_lt r2)
              rw [Nat.succ_mul] at q2
              obtain ⟨hh, hF, -⟩ := hR1 (jj * nWords us + i) (by omega) (by omega)
              exact ⟨hh, hF⟩)
        hV2 (fun _ _ h => h)
        (fun l hr => by
          obtain ⟨c, N, e, us, hc, ho, -, hT, hu, hrl, hNp, hNN, -, -, hZZ⟩ := hQ l (hRQ l hr)
          obtain ⟨-, hone, hne, hCl, hmg, hno, hU, hty⟩ := hZZ.resolve_left (fun h => h.1 hr)
          refine ⟨c, N, e, us, hstoQ l c hc ho, by show c.owner = some η.tid; rw [htid]; exact ho,
            hT, hu, hone, hne, hCl, hmg, hno, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hil, hil2 l (hRQ l hr)]; exact hNp
          · rw [hil2 l (hRQ l hr)]; exact hNN
          · show η.rini l ≤ η.ini l; rw [hini, hrini]; exact hrl
          · show P1 l ≠ none; simp [P1, hRQ l hr]
          · intro o h1 h2
            rw [hil] at h1; rw [hil2 l (hRQ l hr)] at h2
            obtain ⟨hR, hW⟩ := hU o h1 h2
            refine ⟨hR, ?_⟩
            rw [e2']; exact hW
          · intro j h1 h2 ws hl hw
            rw [hil] at h1; rw [hil2 l (hRQ l hr)] at h2
            rw [e2'] at hw ⊢
            exact hty j h1 h2 ws hl hw)
      refine ⟨H2, cr2, db2, hH2, hC2, fun tw m htw hm' hla => ?_, ?_⟩
      · obtain ⟨a1, a2⟩ := hk2 tw m htw hm' (fun hr => hla (hRQ _ hr))
        obtain ⟨b1, b2⟩ := hk tw m htw hm' (by
          rintro ⟨h1, h2⟩
          exact h2 ⟨(WordUnit_congr rfl).1 h1.1, fun hpr => h1.2 ⟨hpr.1, by
            simpa [CE, TEnv.withSto, P1, hla] using hpr.2⟩⟩)
        exact ⟨a1.trans b1, a2.trans b2⟩
      · show _ = (HP + HS) + _ + _
        exact Res.ext fun k => by
          have q1 := congrFun e k
          have q2 := congrFun e2 k
          simp only [Res.add_apply] at q1 q2 ⊢
          omega)
  -- the plain invariant at the raised environment
  have hTE' : ThInvE p (CE (η.withSto η.sto I2 P1 η.seen)) th := by
    obtain ⟨ρe, ηe, cxe, hEe0, hEe, hTye, htve, hFIe⟩ := hTE
    have hce : CE ηe = CE η := hEe0.trans hE0.symm
    have q1 : ηe.sto = η.sto := (congrArg TEnv.sto hce : (CE ηe).sto = (CE η).sto)
    have q2 : ηe.ini = η.ini := (congrArg TEnv.ini hce : (CE ηe).ini = (CE η).ini)
    have q3 : ηe.pfr = η.pfr := (congrArg TEnv.pfr hce : (CE ηe).pfr = (CE η).pfr)
    have q4 : ηe.seen = η.seen := (congrArg TEnv.seen hce : (CE ηe).seen = (CE η).seen)
    have hxe : Ext ηe (ηe.withSto ηe.sto I2 P1 ηe.seen) :=
      Ext_withSto hEe.2.1 (fun _ _ h => h) (fun l' => by rw [q2]; exact hI2 l')
        (fun l' f h => hP1 l' f (by rw [← q3]; exact h))
    refine ⟨ρe, ηe.withSto ηe.sto I2 P1 ηe.seen, cxe, ?_, ⟨hEe.1, hxe.1, hxe.2.2.2.2.2.2.2.2.2.2.1⟩, hTye, htve, FInv_ext hEe.2.1 hxe hFIe.1, hFIe.2⟩
    have q5 : ηe.prog = η.prog := (congrArg TEnv.prog hce : (CE ηe).prog = (CE η).prog)
    have q6 : ηe.tid = η.tid := (congrArg TEnv.tid hce : (CE ηe).tid = (CE η).tid)
    have q7 : ηe.rini = η.rini := (congrArg TEnv.rini hce : (CE ηe).rini = (CE η).rini)
    have q8 : ηe.box = η.box := (congrArg TEnv.box hce : (CE ηe).box = (CE η).box)
    have q9 : ηe.fp = η.fp := (congrArg TEnv.fp hce : (CE ηe).fp = (CE η).fp)
    simp only [CE, TEnv.withSto, q1, q4, q5, q6, q7, q8, q9]
  have hRE' : ThInvRE p (CE (η.withSto η.sto I2 P1 η.seen)) th Tot :=
    ⟨ρ, _, cx, Rf, Rs, rfl, hE', hTy, htv, FInvR_ext hE.2.1 hE.2.2 hx hFI, hsum⟩
  rw [e2'] at hRE' hTE' hH' hC'
  obtain ⟨HP', HS', rfl, hP', hS'⟩ := MemHeld_split (fun _ _ h1 h2 => Cut_cov h1 h2) hH'
  exact ⟨HP', HS', cr', db', ⟨hRE', hTE', hMI, hP', hS', hC'⟩, heq, by rw [hE0] at hKN; exact hKN⟩

/-- (R1) **`TermPlantS.ThSysAt_plantS` with resourceful labels**: planting the own labels `Q` at
once keeps the thread's system invariant.  Each label is either as for `ThSysAt_plantS` (a
word-free buffer whose new slots carry nothing), or, in `R`, a buffer of an own-free closed
guarded all-`.one` element whose new slots are a placeholder under own promises (R1w), their
values paid by their promises' new debits (`raise_pay`). -/
theorem ThSysAt_plantQ {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Sp : TermRun.Cfg → TermRun.Cfg → Prop} {c0 : TermRun.Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {Q R : AllocLabel → Prop}
    {F : AllocLabel → Ts} {Np : AllocLabel → Nat}
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hRQ : ∀ l, R l → Q l)
    (hQ : ∀ l, Q l → ∃ c N e us, Eg.sto l = some c ∧ c.owner = some g.i ∧ Eg.pfr l = none ∧
      c.ty = .array (.lit N) e ∧ accs e = some us ∧ Eg.rini l ≤ Eg.ini l ∧
      Eg.ini l ≤ Np l ∧ Np l ≤ N ∧ FlipOK (Cut Eg g.i S) (stOf mem pairs th) l ∧
      (∀ o, Eg.ini l * nWords us ≤ o → o < Np l * nWords us →
        ∃ h, FirstW mem ⟨l, o⟩ h ∧
          ∀ t m', h < t → mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ th.promises ++ Eg.fpOf g.i) ∧
      ((¬ R l ∧
        (us = [] ∨ (dwf e = true ∧
        (∀ j, Eg.ini l ≤ j → j < Np l → ∀ ws : List Word, ws.length = nWords us →
          (∀ i w, ws[i]? = some w → ∃ h m, FirstW mem ⟨l, j * nWords us + i⟩ h ∧ mem[h]? = some m ∧ w = mw m) →
          ValOfR (Cut (plantS Eg Q F Np) g.i S) e ws .zero) ∧
          (TermBlkZ.SkFree e = true ∨ (Clo e ∧ TermTv.mg e = true))))) ∨
      (R l ∧ (∀ u ∈ us, u = .one) ∧ us ≠ [] ∧ Clo e ∧ mg e = true ∧ Ty.noOwnIn [] e = true ∧
        (∀ o, Eg.ini l * nWords us ≤ o → o < Np l * nWords us →
          (∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val = .undef ∧ t0 ∉ th.promises ∧
            (∃ t, AtA mem ⟨l, o⟩ t0 t = true) ∧
            ∀ t m, mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ th.promises) ∧
          (WordUnit (Cut (plantS Eg Q F Np) g.i S) ⟨l, o⟩ →
            ∃ n P, WordAt (Cut (plantS Eg Q F Np) g.i S) ⟨l, o⟩ n P)) ∧
        ∀ j, Eg.ini l ≤ j → j < Np l → ∀ ws : List Word, ws.length = nWords us →
          (∀ i w, ws[i]? = some w → RdW (Cut (plantS Eg Q F Np) g.i S) mem ⟨l, j * nWords us + i⟩ w) →
          ∃ Rv, ValOfR (Cut (plantS Eg Q F Np) g.i S) e ws Rv)))
    (hfo : FpOK (Cut Eg g.i S) (stOf mem pairs th))
    (hMI : MemInv g (Cut (plantS Eg Q F Np) g.i S) (stOf mem pairs th)) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plantS Eg Q F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
    obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := ThSysAt_plantQK (hV0 := hV0) h hpa hRQ hQ hfo hMI
    exact ⟨x0, x1, x2, x3, h0, h1⟩

end PlantQ


section R1Facts
open TermCut TermSys TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open TermPlantR TermPlantW TermPlantL TermPlantE TermPlantS TermPlantP
open WeakMem (Val VState Arch)
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (R1) A buffer type of an all-`.one` element with units, `∀`-free at value positions. -/
def R1T (T : Ty) : Prop :=
  ∃ N e us, T = .array (.lit N) e ∧ accs e = some us ∧ (∀ u ∈ us, u = Acc.one) ∧ us ≠ [] ∧ noIallV e = true

/-- (R1) At a closed buffer of an all-`.one` element every protocol word unit is a literal word. -/
theorem wordAt_of_unit {E : TEnv} {l : AllocLabel} {o : Nat} {cl : Cell} {N : Nat} {e : Ty} {us : List Acc}
    (hc : E.sto l = some cl) (hT : cl.ty = .array (.lit N) e) (hu : accs e = some us)
    (hone : ∀ u ∈ us, u = Acc.one) (hCl : Clo cl.ty) (hW : WordUnit E ⟨l, o⟩) : ∃ n P, WordAt E ⟨l, o⟩ n P := by
  obtain ⟨c', hc', h⟩ := hW
  rw [hc] at hc'; cases hc'
  have hno2 : ∀ o' r P, ¬ AtOff cl.ty o' (.word2 r P) := fun o' r P ha => by
    rw [hT] at ha
    rcases AtOff_arr_elem ha rfl with h0 | ⟨us', j', o'', hu', -, -, ha'⟩
    · cases h0
    · rw [hu] at hu'; cases hu'
      exact TermPlant.no_word2_of_ones hu hone ha'
  rcases h with ⟨r, P, hg, ha⟩ | ⟨r, P, ha⟩ | ⟨r, P, -, ha⟩
  · obtain ⟨n, rfl⟩ := AtOff_word_lit ha hCl r P rfl
    exact ⟨n, P, cl, hc, ha, hg⟩
  · exact (hno2 _ r P ha).elim
  · exact (hno2 _ r P ha).elim

/-- (R1) **The facts at a new-slot R1 label `l`** (`unitFacts` for an all-`.one` element that is not
a copyable word-free one): the plant facts, and the R1 data — the new units are a placeholder under
own promises (`hR1w`), the protocol word units literal, and every reading (`RdW`) of a new slot is
a value of the element type, carrying some resources (`slotR_tear`). -/
theorem r1Facts (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop} {l : AllocLabel}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hS : ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hm0 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf c.mem c.pairs th))
    (hH0 : MemHeldP (Cut Eg j S) (stOf c.mem c.pairs th) (HP j))
    (hTE1 : ThInvE p (Cut Eg j S) (thP th c.mem.size))
    (hm1 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)))
    (hpl0 : TermPlantF.plantOf c Eg j a v w l ≠ none)
    (hU : ∀ cl, Eg.sto l = some cl → R1T cl.ty)
    (hR1w : ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e → accs e = some us →
      ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises)
    {Eg1 EgF : GEnv} (A : PAgree Eg Eg1 j l)
    (hF : Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S =
      Cut EgF j S)
    (hFi : EgF.ini l = max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l))
    (hFs : ∀ cl, Eg.sto l = some cl → (Cut EgF j S).sto l = some cl) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ cl N e us, Eg1.sto l = some cl ∧ cl.owner = some j ∧ Eg1.pfr l = none ∧
      cl.ty = .array (.lit N) e ∧ accs e = some us ∧ Eg1.rini l ≤ Eg1.ini l ∧
      Eg1.ini l ≤ max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ∧
      max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ≤ N ∧
      FlipOK (Cut Eg1 j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) l ∧
      (∀ o, Eg1.ini l * nWords us ≤ o → o < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
        ∃ h, FirstW (c.mem.push ⟨a, v, w⟩) ⟨l, o⟩ h ∧
          ∀ t m', h < t → (c.mem.push ⟨a, v, w⟩)[t]? = some m' → m'.loc = ⟨l, o⟩ →
            t ∈ (thP th c.mem.size).promises ++ Eg1.fpOf j) ∧
      ((∀ u ∈ us, u = .one) ∧ us ≠ [] ∧ Clo e ∧ mg e = true ∧ Ty.noOwnIn [] e = true ∧
        (∀ o, Eg1.ini l * nWords us ≤ o → o < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
          (∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val = .undef ∧
            t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, o⟩ t0 t = true) ∧
            ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, o⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
              t ∈ (thP th c.mem.size).promises) ∧
          (WordUnit (Cut EgF j S) ⟨l, o⟩ → ∃ n P, WordAt (Cut EgF j S) ⟨l, o⟩ n P)) ∧
        ∀ jj, Eg1.ini l ≤ jj → jj < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
          ∀ ws : List Word, ws.length = nWords us →
          (∀ i w', ws[i]? = some w' → RdW (Cut EgF j S) (c.mem.push ⟨a, v, w⟩) ⟨l, jj * nWords us + i⟩ w') →
          ∃ Rv, ValOfR (Cut EgF j S) e ws Rv) ∧
      (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l ≤
          (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)).vs.vWr ∨
        HoldW (Cut Eg1 j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) l
          (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)) ∧
      (∀ o, InitR (Cut EgF j S) cl l o → ¬ InitR (Cut Eg1 j S) cl l o →
        ∀ (t : Nat) (m : Msg), t ∉ (thP th c.mem.size).promises → (c.mem.push ⟨a, v, w⟩)[t]? = some m →
          m.loc = ⟨l, o⟩ → ∃ (t' : Nat) (m' : Msg), t < t' ∧
            t' ≤ plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l ∧
            (c.mem.push ⟨a, v, w⟩)[t']? = some m' ∧ m'.loc = ⟨l, o⟩) ∧
      (∀ b S' us', SegOf cl.ty b S' → accs S' = some us' → IniSeg (Cut EgF j S) cl l b →
        ¬ IniSeg (Cut Eg1 j S) cl l b → ∃ ws, ValOf (Cut EgF j S) S' ws ∧ ws.length = nWords us') ∧
      (∀ b S', SegOf cl.ty b S' → accs S' ≠ none → TearOK S') ∧ Ty.coupledOKIn [] cl.ty = true ∧
      Ty.noOwnIn [] cl.ty = true ∧ rgnFree cl.ty = true := by
  obtain ⟨f, hpl⟩ := Option.ne_none_iff_exists'.mp hpl0
  have hi1 : Eg1.ini l = Eg.ini l := A.ini
  refine slotFacts (hV0 := hV0) hP hrun X hS hInh hm0 hH0 hTE1 hm1 hpl0
    (fun cl hcl => by obtain ⟨N, e, us, hTc, hu, -⟩ := hU cl hcl; exact ⟨N, e, us, hTc, hu⟩) hR1w A hF hFi
    hPS hSub hSig ?_
  intro cl N e us hcl hTc hu hNl hcpl hnT hCe htb
  obtain ⟨N', e', us', hTc', hu', hone, hne, hni⟩ := hU cl hcl
  rw [hTc] at hTc'
  simp only [Ty.array.injEq, Idx.lit.injEq] at hTc'
  obtain ⟨rfl, rfl⟩ := hTc'
  obtain rfl : us = us' := Option.some.inj (hu.symm.trans hu')
  have hty := promTyL X hPO hNO hpl hcl
  have hclo : Clo cl.ty := X.inv.clo l cl hcl
  have hmg : mg e = true := X.inv.cmg.elem hcl hTc
  have hnoE : Ty.noOwnIn [] e = true := by
    have := hnT; rw [hTc] at this; simpa [Ty.noOwnIn] using this
  have hFsl : (Cut EgF j S).sto l = some cl := hFs cl hcl
  have hsl : ∀ jj, Eg1.ini l ≤ jj → jj < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
      ∀ ws : List Word, ws.length = nWords us →
      (∀ i w', ws[i]? = some w' → RdW (Cut EgF j S) (c.mem.push ⟨a, v, w⟩) ⟨l, jj * nWords us + i⟩ w') →
      ∃ Rv, ValOfR (Cut EgF j S) e ws Rv := by
    intro jj h1 h2 ws hl hw
    rw [hi1] at h1
    have hjN : jj < N := Nat.lt_of_lt_of_le h2 hNl
    have hTO : TearOK e := hcpl _ e (Or.inr ⟨N, us, jj, hTc, hu, hjN, rfl⟩) (by rw [hu]; exact Option.some_ne_none _)
    refine slotR_tear hu hone hne hTO hni hl fun i hi => ?_
    have hwi : ∃ y, ws[i]? = some y := ⟨ws[i]'(by rw [hl]; exact hi), List.getElem?_eq_getElem _⟩
    obtain ⟨y, hy⟩ := hwi
    obtain ⟨hh, m, hm, hml, rfl, hfw, hlat⟩ := hw i y hy
    have r1 : Eg.ini l * nWords us ≤ jj * nWords us + i :=
      Nat.le_trans (Nat.mul_le_mul_right _ h1) (Nat.le_add_right _ _)
    have r2 : jj * nWords us + i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us := by
      have := Nat.mul_le_mul_right (nWords us) (Nat.succ_le_of_lt h2)
      rw [Nat.succ_mul] at this; omega
    have hRw := hR1w cl N e us hcl hTc hu _ r1 r2
    obtain ⟨h1w, hfw1, -, -⟩ := firstW_of_R1w hRw
    obtain ⟨t0, m0, hm0, -, hv0, -, -, hall⟩ := hRw
    have hne0 : hh ≠ t0 := by
      intro e0
      rw [← e0] at hm0
      by_cases hW : WordUnit (Cut EgF j S) ⟨l, jj * nWords us + i⟩
      · obtain ⟨⟨m1, hm1, hml1, hv1⟩, -⟩ := hfw1
        have hne1 : h1w ≠ t0 := fun e1 => by
          rw [e1, ← e0, hm0] at hm1; cases hm1; exact hv1 hv0
        have hlt := (hall h1w m1 hm1 hml1 hne1).1
        rw [← e0] at hlt
        exact hlat hW h1w m1 hlt hm1 hml1
      · obtain ⟨⟨m1, hm1, -, hv1⟩, -⟩ := hfw hW
        rw [hm0] at hm1; cases hm1; exact hv1 hv0
    have hpr := (hall hh m hm hml hne0).2.2
    have hok := hty hh m hpr hm (by rw [hml])
    have hok2 := WordOK_transfer (Incl_pub_cut _ j S) hnT hok
    rw [hF, hTc, hml] at hok2
    obtain ⟨ws0, x, hvx, hlx, hx, hle⟩ := WordOK_slot hu hi rfl hok2
    exact ⟨ws0, x, hvx, hlx, hx, fun y2 hy2 => by rw [hy] at hy2; cases hy2; exact hle⟩
  exact ⟨hone, hne, hCe, hmg, hnoE, fun o h1 h2 => ⟨hR1w cl N e us hcl hTc hu o (by rw [hi1] at h1; exact h1) h2,
      fun hW => wordAt_of_unit hFsl hTc hu hone hclo hW⟩, hsl⟩

end R1Facts

section PrivAny
open TermCut TermSys TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open TermPlantR TermPlantW TermPlantL TermPlantE TermPlantS TermPlantP
open WeakMem (Val VState Arch)
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (R1) `TermPlantS.PrivSlotF` at every own label, whatever its element (the `WordBufT ∨ UnitT`
guard dropped): the new slots of a plant are a placeholder under own promises. -/
def PrivSlotA (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ l f, TermPlantF.plantOf c Eg j a v w l = some f → ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l →
      ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e →
      accs e = some us → ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises

theorem PrivSlotA.toF {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (h : PrivSlotA p k arch Sp Init MintOK c0) : TermPlantS.PrivSlotF p k arch Sp Init MintOK c0 :=
  fun X l f hf hno cl N e us hcl _ hT hu i h1 h2 => h X l f hf hno cl N e us hcl hT hu i h1 h2

/-- (R1) **`PrivSlotA` from `PrivCoh`**: `TermPlantP.privSlot_of`, whose proof never used the
element guard. -/
theorem privSlot_any (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    (hPC : ∀ {g : G} {E : TEnv} {s : St}, MemInv g E s → PrivCoh E s) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PrivSlotA p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X l f hf hno cl N e us hcl hT hu i h1 h2
  obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X hf
  obtain ⟨cl', hcl', ho, hnone, -⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  rw [hcl] at hcl'; cases hcl'
  obtain ⟨S0, hS0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hS0
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hb : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => X.inv.plt j th t X.hth ht
  have hm1 : MemInv (gOf p k arch c j) (Cut Eg j S0)
      (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) := MemInv_promSt hm
  have hpa1 : PromAbove (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) := by
    have h1 := TermTyped.certified_promAboveSt X.cert hpi.2.1
    rw [hpi.2.2] at h1
    exact h1
  -- certification: no promise is `.undef`
  have hSC : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, -, -, -, hIH0⟩ := InvAtXF_of (p := p) (k := k) (arch := arch)
    hpi.2.1 hTE (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
  have hX : InvAtX p k arch j (Cut Eg j S0) _ _ (promise c j a v w) :=
    ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  have hsc := fun c1 h1 h2 => (hrun X S0 hS0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hS0 c1 h1 h2).2
  have hnu : ∀ t m, t ∈ (thP th c.mem.size).promises → (c.mem.push ⟨a, v, w⟩)[t]? = some m →
      m.loc = ⟨l, i⟩ → m.val ≠ .undef := fun t m ht hm _ => by
    have ht' : t ∈ TermFul.promsOf (promise c j a v w) j := by
      rw [TermFul.promsOf_some hpi.2.1]; exact ht
    have hmt : (promise c j a v w).mem[t]? = some m := by rw [hpi.1]; exact hm
    exact (certified_promNotUndefX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX (TermMain.tidAt_cutP X.inv j S0) X.cert ht' hmt).1
  -- the word is below the planted count, hence in the buffer and held by a promise
  have hPsto : (TermPlantF.cutP Eg j).sto l = some cl := cutSto_own hcl ho
  have hNp : i < NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l * nWords us := by
    rw [← plantN_eq l X]
    rcases Nat.le_total (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) with hle | hle
    · rw [Nat.max_eq_right hle] at h2; exact h2
    · rw [Nat.max_eq_left hle] at h2; omega
  have hkN : NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l ≤ N := NpZ_le hPsto hT
  have hin : i < N * nWords us :=
    Nat.lt_of_lt_of_le hNp (Nat.mul_le_mul_right _ hkN)
  have hex : ∃ t m, t ∈ (thP th c.mem.size).promises ∧ (c.mem.push ⟨a, v, w⟩)[t]? = some m ∧
      m.loc = ⟨l, i⟩ := by
    rcases PrefixHeld_NpZ hPsto N e us hT hu i hNp with hI | ⟨u, hu', m, hm, hl⟩
    · have := hI N e us hT hu
      have e1 : (TermPlantF.cutP Eg j).ini l = Eg.ini l := rfl
      rw [e1] at this; omega
    · refine ⟨u, m, List.mem_append_left _ hu', ?_, hl⟩
      rw [getElem_push_lt (hb u hu')]; exact hm
  have hU : PrivU (Cut Eg j S0) ⟨l, i⟩ := by
    refine ⟨cl, N, e, us, cutSto_own hcl ho, ho, hnone, hT, hu, ?_, hin⟩
    have e1 : (Cut Eg j S0).ini l = Eg.ini l := rfl
    have := (Cut Eg j S0).rc_le_ini l
    rw [e1] at this
    exact Nat.le_trans (Nat.mul_le_mul_right _ this) h1
  exact privR1w (hPC hm1) hm1.2.1 hpa1 hU hnu hex


end PrivAny

section PlantR
open TermCut TermSys TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open TermPlantR TermPlantW TermPlantL TermPlantE TermPlantS TermPlantP
open WeakMem (Val VState Arch)
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (R1) The planted labels with new slots whose cell is a copyable buffer of single-word units
(`UnitT`) or an `R1T` buffer. -/
def QA (c : Cfg) (Eg : GEnv) (j : Nat) (a : Address) (v : WeakMem.Val) (w : Ts) (l : AllocLabel) : Prop :=
  TermPlantF.plantOf c Eg j a v w l ≠ none ∧ ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l ∧
    ∃ cl, Eg.sto l = some cl ∧ (UnitT cl.ty ∨ R1T cl.ty)

/-- (R1) The `QA` labels whose cell is not `UnitT` (hence `R1T`). -/
def RA (c : Cfg) (Eg : GEnv) (j : Nat) (a : Address) (v : WeakMem.Val) (w : Ts) (l : AllocLabel) : Prop :=
  QA c Eg j a v w l ∧ ∃ cl, Eg.sto l = some cl ∧ ¬ UnitT cl.ty

theorem qSplit {c : Cfg} {Eg : GEnv} {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel}
    (hq : QA c Eg j a v w l) :
    (¬ RA c Eg j a v w l ∧ ∀ cl, Eg.sto l = some cl → UnitT cl.ty) ∨
      (RA c Eg j a v w l ∧ ∀ cl, Eg.sto l = some cl → R1T cl.ty) := by
  by_cases hr : RA c Eg j a v w l
  · refine .inr ⟨hr, fun cl hcl => ?_⟩
    obtain ⟨cl', hcl', hu⟩ := hq.2.2
    rw [hcl] at hcl'; cases hcl'
    obtain ⟨-, cl2, hcl2, hnu⟩ := hr
    rw [hcl] at hcl2; cases hcl2
    rcases hu with hu | hu
    · exact absurd hu hnu
    · exact hu
  · refine .inl ⟨hr, fun cl hcl => ?_⟩
    obtain ⟨cl', hcl', hu⟩ := hq.2.2
    rw [hcl] at hcl'; cases hcl'
    rcases hu with hu | hu
    · exact hu
    · exact Classical.byContradiction fun hnu => hr ⟨hq, cl, hcl, hnu⟩

/-- (R1) **The facts at a new-slot label of `ThSys_plantR`**: `unitFacts` off `Rl`, `r1Facts` on it,
in the per-label shape of `ThSysAt_plantQ`. -/
theorem qFacts (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop} {l : AllocLabel}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hS : ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hm0 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf c.mem c.pairs th))
    (hH0 : MemHeldP (Cut Eg j S) (stOf c.mem c.pairs th) (HP j))
    (hTE1 : ThInvE p (Cut Eg j S) (thP th c.mem.size))
    (hm1 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)))
    (hpl0 : TermPlantF.plantOf c Eg j a v w l ≠ none)
    {Rl : Prop} (hq : (¬ Rl ∧ ∀ cl, Eg.sto l = some cl → UnitT cl.ty) ∨ (Rl ∧ ∀ cl, Eg.sto l = some cl → R1T cl.ty))
    (hR1w : ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e → accs e = some us →
      ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises)
    {Eg1 EgF : GEnv} (A : PAgree Eg Eg1 j l)
    (hF : Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S =
      Cut EgF j S)
    (hFi : EgF.ini l = max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l))
    (hFs : ∀ cl, Eg.sto l = some cl → (Cut EgF j S).sto l = some cl) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ cl N e us, Eg1.sto l = some cl ∧ cl.owner = some j ∧ Eg1.pfr l = none ∧
      cl.ty = .array (.lit N) e ∧ accs e = some us ∧ Eg1.rini l ≤ Eg1.ini l ∧
      Eg1.ini l ≤ max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ∧
      max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ≤ N ∧
      FlipOK (Cut Eg1 j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) l ∧
      (∀ o, Eg1.ini l * nWords us ≤ o → o < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
        ∃ h, FirstW (c.mem.push ⟨a, v, w⟩) ⟨l, o⟩ h ∧
          ∀ t m', h < t → (c.mem.push ⟨a, v, w⟩)[t]? = some m' → m'.loc = ⟨l, o⟩ →
            t ∈ (thP th c.mem.size).promises ++ Eg1.fpOf j) ∧
      ((¬ Rl ∧ (us = [] ∨ (dwf e = true ∧
          (∀ jj, Eg1.ini l ≤ jj → jj < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
            ∀ ws : List Word, ws.length = nWords us →
            (∀ i w', ws[i]? = some w' → ∃ h m, FirstW (c.mem.push ⟨a, v, w⟩) ⟨l, jj * nWords us + i⟩ h ∧
              (c.mem.push ⟨a, v, w⟩)[h]? = some m ∧ w' = mw m) →
              ValOfR (Cut EgF j S) e ws .zero) ∧
          (TermBlkZ.SkFree e = true ∨ (Clo e ∧ TermTv.mg e = true))))) ∨
       (Rl ∧ (∀ u ∈ us, u = .one) ∧ us ≠ [] ∧ Clo e ∧ mg e = true ∧ Ty.noOwnIn [] e = true ∧
        (∀ o, Eg1.ini l * nWords us ≤ o → o < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
          (∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val = .undef ∧
            t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, o⟩ t0 t = true) ∧
            ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, o⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
              t ∈ (thP th c.mem.size).promises) ∧
          (WordUnit (Cut EgF j S) ⟨l, o⟩ → ∃ n P, WordAt (Cut EgF j S) ⟨l, o⟩ n P)) ∧
        ∀ jj, Eg1.ini l ≤ jj → jj < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
          ∀ ws : List Word, ws.length = nWords us →
          (∀ i w', ws[i]? = some w' → RdW (Cut EgF j S) (c.mem.push ⟨a, v, w⟩) ⟨l, jj * nWords us + i⟩ w') →
          ∃ Rv, ValOfR (Cut EgF j S) e ws Rv)) ∧
      (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l ≤
          (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)).vs.vWr ∨
        HoldW (Cut Eg1 j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) l
          (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)) ∧
      (∀ o, InitR (Cut EgF j S) cl l o → ¬ InitR (Cut Eg1 j S) cl l o →
        ∀ (t : Nat) (m : Msg), t ∉ (thP th c.mem.size).promises → (c.mem.push ⟨a, v, w⟩)[t]? = some m →
          m.loc = ⟨l, o⟩ → ∃ (t' : Nat) (m' : Msg), t < t' ∧
            t' ≤ plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l ∧
            (c.mem.push ⟨a, v, w⟩)[t']? = some m' ∧ m'.loc = ⟨l, o⟩) ∧
      (∀ b S' us', SegOf cl.ty b S' → accs S' = some us' → IniSeg (Cut EgF j S) cl l b →
        ¬ IniSeg (Cut Eg1 j S) cl l b → ∃ ws, ValOf (Cut EgF j S) S' ws ∧ ws.length = nWords us') ∧
      (∀ b S', SegOf cl.ty b S' → accs S' ≠ none → TearOK S') ∧ Ty.coupledOKIn [] cl.ty = true ∧
      Ty.noOwnIn [] cl.ty = true ∧ rgnFree cl.ty = true := by
  rcases hq with ⟨hr, hU⟩ | ⟨hr, hU⟩
  · obtain ⟨cl, N, e, us, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ :=
      unitFacts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hS hPO hNO hInh hm0 hH0 hTE1 hm1 hpl0 hU hR1w A hF hFi
    exact ⟨cl, N, e, us, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, .inl ⟨hr, a11⟩, a12, a13, a14, a15, a16,
      a17, a18⟩
  · obtain ⟨cl, N, e, us, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ :=
      r1Facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hS hPO hNO hInh hm0 hH0 hTE1 hm1 hpl0 hU hR1w A hF hFi hFs
    exact ⟨cl, N, e, us, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, .inr ⟨hr, a11⟩, a12, a13, a14, a15, a16,
      a17, a18⟩

/-- (dedup) master of `ThSys_plantR`: also exports `KeepNW` (old non-word credits kept). -/
theorem ThSys_plantRK (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S))
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hWU : ∀ l f cl, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → Eg.sto l = some cl → WordBufT cl.ty ∨ UnitT cl.ty ∨ R1T cl.ty)
    (hR1w : ∀ l f, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e →
      accs e = some us → ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' ∧
      (∀ t m, t ∈ th.promises → c.mem[t]? = some m → ∀ S : AllocLabel → Prop,
        ¬ WordUnit (Cut Eg j S) m.loc → cr' t = cr j t) := by
  classical
  obtain ⟨S, HP1, HS1, cr1, db1, hacct, hT, hm0, hH0, hk0, hS0⟩ := ThSysAt_promK X hwu hfw
  have hsome : ∀ l, TermPlantF.plantOf c Eg j a v w l ≠ none → ∃ f, TermPlantF.plantOf c Eg j a v w l = some f :=
    fun l h => Option.ne_none_iff_exists'.mp h
  -- the labels planted one at a time, as a duplicate-free list
  obtain ⟨Ls, hnd, hLs⟩ := exists_nodup_filter
    (fun l => TermPlantF.plantOf c Eg j a v w l ≠ none ∧ ¬ QA c Eg j a v w l)
    ((th.promises ++ [c.mem.size]).filterMap fun t => locLab (c.mem.push ⟨a, v, w⟩)[t]?)
  have hmem : ∀ l, l ∈ Ls ↔ TermPlantF.plantOf c Eg j a v w l ≠ none ∧ ¬ QA c Eg j a v w l := fun l => by
    refine ⟨fun h => ((hLs l).1 h).2, fun h => (hLs l).2 ⟨?_, h⟩⟩
    obtain ⟨f, hf⟩ := hsome l h.1
    obtain ⟨⟨l', -, t, ht, m, hm, -, -, a', g, hv, hal, -⟩, -⟩ := plantOf_some X hf
    refine List.mem_filterMap.2 ⟨t, ht, ?_⟩
    simp only [locLab, hm, Option.bind_some, hv, hal]
  have hownP : ∀ l, TermPlantF.plantOf c Eg j a v w l ≠ none →
      ∃ cl, Eg.sto l = some cl ∧ cl.owner = some (gOf p k arch c j).i := fun l h => by
    obtain ⟨f, hf⟩ := hsome l h
    obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X hf
    obtain ⟨cl, hcl, ho, -⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
    exact ⟨cl, hcl, ho⟩
  have hown : ∀ l ∈ Ls, ∃ cl, Eg.sto l = some cl ∧ cl.owner = some (gOf p k arch c j).i :=
    fun l hl => hownP l ((hmem l).1 hl).1
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hpa1 : PromAbove (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) := by
    have h1 := TermTyped.certified_promAboveSt X.cert hpi.2.1
    rw [hpi.2.2] at h1
    exact h1
  -- phase 1: word buffers and no-new-slot labels, one at a time
  obtain ⟨HP2, HS2, cr2, db2, hT1, e1, hk1⟩ := ThSysAt_plantLK
    (Fm := fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
    (Nm := fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) hnd hown
    (fun l hl => by
      obtain ⟨hpl0, hnq⟩ := (hmem l).1 hl
      obtain ⟨f, hf⟩ := hsome l hpl0
      by_cases hno : TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l
      · exact flipStepK (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hS0 hm0 hH0 hT.2.1 hT.2.2.1 hf hno
      · obtain ⟨cl, hcl, -⟩ := hownP l hpl0
        have hwb : WordBufT cl.ty := by
          rcases hWU l f cl hf hno hcl with hb | hu | hu
          · exact hb
          · exact absurd ⟨hpl0, hno, cl, hcl, .inl hu⟩ hnq
          · exact absurd ⟨hpl0, hno, cl, hcl, .inr hu⟩ hnq
        refine plantStepK (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hPO hNO hInh hm0 hH0 hf
          (fun cl' hcl' => by rw [hcl] at hcl'; cases hcl'; exact hwb) ?_
        obtain ⟨N, n, P, hTy, hg⟩ := hwb
        have h1w : nWords [Acc.one] = 1 := by simp [nWords, Acc.size]
        intro i h1 h2
        exact hR1w l f hf hno cl N _ [Acc.one] hcl hTy (by simp [accs, hg]) i
          (by rw [h1w, Nat.mul_one]; exact h1) (by rw [h1w, Nat.mul_one]; exact h2)) hT
  -- the final environment
  have hQo : ∀ l, QA c Eg j a v w l → ∃ cl,
      (plantL Eg (fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
        (fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) Ls).sto l = some cl ∧
      cl.owner = some (gOf p k arch c j).i := fun l hq => by
    rw [plantL_sto]; exact hownP l hq.1
  have hG : plantS (plantL Eg (fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
        (fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) Ls) (QA c Eg j a v w)
        (fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
        (fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) =
      plantG Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) :=
    plantS_plantL_eq hmem (fun l hq => hq.1) (fun l f hf => ((plantOf_some X hf).2).symm) (fun _ _ => rfl)
  have hcut : Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
      (gOf p k arch c j).i S = Cut (plantG Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w))
        (gOf p k arch c j).i S :=
    TermStepper.Cut_withFp _ _ _ _ (by show TermStepper.fpProm Eg j c.mem.size j = Eg.fpOf j; simp [TermStepper.fpProm])
  have hFcut : Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S =
      Cut (plantS (plantL Eg (fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
        (fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) Ls) (QA c Eg j a v w)
        (fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
        (fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l))) j S := by
    rw [hG]; exact hcut
  -- the per-label facts at the unit buffers
  have hR1w' : ∀ l, TermPlantF.plantOf c Eg j a v w l ≠ none →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e →
      accs e = some us → ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises := fun l h hno => by
    obtain ⟨f, hf⟩ := hsome l h
    exact hR1w l f hf hno
  have hUF := fun l (hq : QA c Eg j a v w l) =>
    qFacts (hV0 := hV0) (Rl := RA c Eg j a v w l) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hS0 hPO hNO hInh hm0 hH0 hT.2.1 hT.2.2.1 hq.1
      (qSplit hq)
      (hR1w' l hq.1 hq.2.1)
      (PAgree_plantL (Fm := fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
        (Nm := fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) hown (fun h => ((hmem l).1 h).2 hq))
      hFcut (by simp [plantS, hq]) (fun cl hcl => by
        obtain ⟨cl', hcl', ho⟩ := hownP l hq.1
        rw [hcl] at hcl'; cases hcl'
        exact cutSto_own (by show (plantL Eg _ _ Ls).sto l = some cl; rw [plantL_sto]; exact hcl) ho)
  -- `FpOK` at the partial plant
  have hfo1 : FpOK (Cut (plantL Eg (fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
      (fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) Ls) j S)
      (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) := by
    have h0 := X.inv.fpok j th S X.hth
    refine FpOK_agreeW (plantL_csto hown) (plantL_fp _ _ _ Ls) (fun l' => ?_)
      ⟨fun t ht => ?_, fun t m ht hm => h0.2 t m ht ?_⟩
    · by_cases h : l' ∈ Ls
      · exact .inr ⟨_, plantL_in h⟩
      · exact .inl (plantL_out h).2
    · have := h0.1 t ht
      show t < (c.mem.push ⟨a, v, w⟩).size
      rw [Array.size_push]; exact Nat.lt_succ_of_lt this
    · have hm' : (c.mem.push ⟨a, v, w⟩)[t]? = some m := hm
      rw [getElem_push_lt (mem := c.mem) (h0.1 t ht)] at hm'; exact hm'
  -- `MemInv` at the final environment (`MemInv_plantSet` at the unit buffers)
  have hMI := MemInv_plantSet (Lp := QA c Eg j a v w)
    (F := fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
    (N := fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l))
    (E' := Cut (plantS (plantL Eg (fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
        (fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) Ls) (QA c Eg j a v w)
        (fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
        (fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l))) j S)
    hT1.2.2.1
    (fun l hq => by
      obtain ⟨cl, N, e, us, hcl, ho, -⟩ := hUF l hq
      exact ⟨cl, cutSto_own hcl ho, ho⟩)
    (fun l hq => by obtain ⟨cl, N, e, us, -, -, hn, -⟩ := hUF l hq; exact hn)
    rfl rfl (cutSto_plantS hQo)
    (fun l hq => by simp [Cut, plantS, hq]) (fun l hq => by simp [Cut, plantS, hq])
    (fun l hq => by obtain ⟨cl, N, e, us, -, -, -, -, -, -, h1, -⟩ := hUF l hq; exact h1)
    (fun l hq => by obtain ⟨cl, N, e, us, -, -, -, -, -, h1, -⟩ := hUF l hq; exact h1)
    (fun l hq => by simp [Cut, plantS, hq]) (fun l hq => by simp [Cut, plantS, hq]) rfl rfl
    (fun l hq => by obtain ⟨cl, N, e, us, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := hUF l hq; exact h1)
    (fun l _ _ => Nat.le_max_left _ _)
    (fun l c' hq hc' => by
      obtain ⟨cl, N, e, us, hcl, ho, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := hUF l hq
      obtain rfl : c' = cl := Option.some.inj (hc'.symm.trans (cutSto_own hcl ho)); exact h1)
    (fun l c' hq hc' => by
      obtain ⟨cl, N, e, us, hcl, ho, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := hUF l hq
      obtain rfl : c' = cl := Option.some.inj (hc'.symm.trans (cutSto_own hcl ho)); exact h1)
    (fun l c' hq hc' => by
      obtain ⟨cl, N, e, us, hcl, ho, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := hUF l hq
      obtain rfl : c' = cl := Option.some.inj (hc'.symm.trans (cutSto_own hcl ho)); exact h1)
    (fun l c' hq hc' => by
      obtain ⟨cl, N, e, us, hcl, ho, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := hUF l hq
      obtain rfl : c' = cl := Option.some.inj (hc'.symm.trans (cutSto_own hcl ho)); exact h1)
    (fun l c' hq hc' => by
      obtain ⟨cl, N, e, us, hcl, ho, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := hUF l hq
      obtain rfl : c' = cl := Option.some.inj (hc'.symm.trans (cutSto_own hcl ho)); exact h1)
    (fun l c' hq hc' => by
      obtain ⟨cl, N, e, us, hcl, ho, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := hUF l hq
      obtain rfl : c' = cl := Option.some.inj (hc'.symm.trans (cutSto_own hcl ho)); exact h1)
    (fun _ _ h => h) rfl
  -- phase 2: the unit buffers at once
  obtain ⟨HP', HS', cr', db', hT2, e2, hk2⟩ := ThSysAt_plantQK (hV0 := hV0) (Q := QA c Eg j a v w) (R := RA c Eg j a v w) hT1 hpa1 (fun l h => h.1)
    (fun l hq => by
      obtain ⟨cl, N, e, us, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -⟩ :=
        hUF l hq
      exact ⟨cl, N, e, us, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩) hfo1 hMI
  have hk2' : KeepNW (Cut Eg j S) (c.mem.push ⟨a, v, w⟩) (thP th c.mem.size).promises cr2 cr' :=
    KeepNW_of_sto hk2 (plantL_csto hown)
  rw [hG] at hT2
  refine ⟨HP', HS', cr', db', acct_trans hacct (acct_trans e1 e2), ⟨S, ?_⟩, ?_⟩
  · rw [hcut]
    exact hT2
  · intro t m ht hm S' hnw
    have htl : t < c.mem.size := X.inv.plt j th t X.hth ht
    have hm' : (c.mem.push ⟨a, v, w⟩)[t]? = some m := by rw [push_lt htl]; exact hm
    have ht' : t ∈ (thP th c.mem.size).promises := List.mem_append_left _ ht
    have hw0 : ¬ WordUnit (Cut Eg j S) m.loc := fun h => hnw ((WordUnit_congr rfl).1 h)
    rw [hk2' t m ht' hm' hw0, hk1 t m ht' hm' hw0, hk0 t m ht hm hw0]

/-- (R1) **`ThSys_plantR`**: `TermPlantS.ThSys_plantS` whose new-slot labels may also be `R1T`
buffers (paid by `raise_pay` through `ThSysAt_plantQ`), modulo PrivSlot (`hR1w`). -/
theorem ThSys_plantR (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S))
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hWU : ∀ l f cl, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → Eg.sto l = some cl → WordBufT cl.ty ∨ UnitT cl.ty ∨ R1T cl.ty)
    (hR1w : ∀ l f, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e →
      accs e = some us → ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' := by
    obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := ThSys_plantRK (hV0 := hV0) hP hrun X hwu hfw hPO hNO hInh hWU hR1w hPS hSub hSig
    exact ⟨x0, x1, x2, x3, h0, h1⟩

/-- (residual, **selfPlantRest** after R1) `selfPlant` at events planting a label with new slots
that is neither a single-word protocol buffer, nor a copyable buffer of single-word units, nor an
`R1T` buffer. -/
def SelfPlantRestR (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    (∃ l f cl, TermPlantF.plantOf c Eg j a v w l = some f ∧ ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l ∧
      Eg.sto l = some cl ∧ ¬ WordBufT cl.ty ∧ ¬ UnitT cl.ty ∧ ¬ R1T cl.ty) →
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db'

/-- (R1) **`selfPlant`** from `ThSys_plantR` and `SelfPlantRestR`, with PrivSlot from `PrivCoh`
(`privSlot_any`). -/
theorem selfPlant_ofR (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hPC : ∀ {g : G} {E : TEnv} {s : St}, MemInv g E s → PrivCoh E s)
    (hRest : SelfPlantRestR p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' := by
  by_cases hW : ∀ l f cl, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → Eg.sto l = some cl → WordBufT cl.ty ∨ UnitT cl.ty ∨ R1T cl.ty
  · exact ThSys_plantR (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hwu hfw hPO hNO hInh hW (privSlot_any (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun hPC X)
  · apply hRest X
    apply Classical.byContradiction; intro hn
    exact hW fun l f cl hf hno hcl => Classical.byContradiction fun hb =>
      hn ⟨l, f, cl, hf, hno, hcl, fun h => hb (.inl h), fun h => hb (.inr (.inl h)), fun h => hb (.inr (.inr h))⟩

end PlantR

section PlantN
open TermCut TermSys TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open TermPlantR TermPlantW TermPlantL TermPlantE TermPlantS TermPlantP
open WeakMem (Val VState Arch)
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- A cell that is not a buffer has no held prefix (`slotCnt = 0`). -/
theorem Np_nonarr {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} (hc : E.sto l = some c)
    (hT : ∀ N e, c.ty ≠ .array (.lit N) e) : Np E s l = 0 := by
  classical
  have h0 : slotCnt c = 0 := by
    unfold slotCnt; split
    next Na e' h => exact absurd h (hT Na e')
    next => rfl
  rw [Np_of hc]
  rcases foldr_max_mem ((List.range (slotCnt c + 1)).filter fun n =>
      @decide (PrefixHeld E s l c n) (Classical.propDecidable _)) with h | h
  · exact h
  · have := List.mem_range.1 (List.mem_filter.1 h).1
    rw [h0] at this ⊢; omega

/-- (R1) **A label planted with new slots is a buffer whose element has a layout, and it is
`R1T` as soon as it is not `UnitT` and its element is `∀`-free at value positions** (all-`.one`
from `TermPredOne.plantNew_allOne`). -/
theorem plantNew_shape (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {l : AllocLabel} {f : Ts} {cl : Cell}
    (hpl : TermPlantF.plantOf c Eg j a v w l = some f)
    (hgt : ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l) (hcl : Eg.sto l = some cl) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ N e us, cl.ty = .array (.lit N) e ∧ accs e = some us ∧
      (¬ UnitT cl.ty → noIallV e = true → R1T cl.ty) := by
  obtain ⟨hPL, -⟩ := TermPlantE.plantOf_some X hpl
  have hcP : (TermPlantF.cutP Eg j).sto l = some cl := by
    obtain ⟨-, -, t1, -, m1, -, -, -, a1, g1, -, hal, cl1, hc1, -, -⟩ := hPL
    subst hal
    have e1 : cl1 = cl := by rw [cutSto_sub hc1] at hcl; cases hcl; rfl
    subst e1; exact hc1
  have hN : TermPlantF.plantN c Eg j a v w l = NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l := by
    simp only [TermPlantF.plantN, X.hth]
  have harr : ∃ N e, cl.ty = .array (.lit N) e := by
    refine Classical.byContradiction fun hn => hgt ?_
    have hT : ∀ N e, cl.ty ≠ .array (.lit N) e := fun N e h => hn ⟨N, e, h⟩
    rw [hN]
    by_cases hz : EmptyZ (TermPlantF.cutP Eg j) l
    · rw [NpZ_of_empty hz]; exact Nat.zero_le _
    · rw [NpZ_of_not hz, Np_nonarr hcP hT]; exact Nat.zero_le _
  obtain ⟨N, e, hT⟩ := harr
  obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X hpl
  obtain ⟨cl2, hcl2, -, -, hLay, -⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  rw [hcl] at hcl2; cases hcl2
  have hacc : accs e ≠ none := by
    rcases hLay with h | ⟨n, e2, h2, h3⟩
    · rw [hT] at h; exact absurd rfl h
    · rw [hT] at h2; cases h2; exact h3
  obtain ⟨us, hu⟩ := Option.ne_none_iff_exists'.mp hacc
  refine ⟨N, e, us, hT, hu, fun hnu hni => ⟨N, e, us, hT, hu,
    TermPredOne.plantNew_allOne X hpl hgt hcl hT hu, fun h0 => hnu ?_, hni⟩⟩
  subst h0
  exact ⟨N, e, [], hT, hu, fun u hu' => absurd hu' (List.not_mem_nil), .inl rfl⟩

/-- (residual, **selfPlantRest** after R1 and the `.two` vacuity) `selfPlant` at events planting,
with new slots, a buffer that is neither a single-word protocol buffer nor a copyable buffer of
single-word units and whose element has a `∀` at a value position. -/
def SelfPlantRestN (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    (∃ l f cl N e, TermPlantF.plantOf c Eg j a v w l = some f ∧ ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l ∧
      Eg.sto l = some cl ∧ ¬ WordBufT cl.ty ∧ ¬ UnitT cl.ty ∧ cl.ty = .array (.lit N) e ∧ noIallV e = false) →
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db'

theorem SelfPlantRestN.toR (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    (h : SelfPlantRestN p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : SelfPlantRestR p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X ⟨l, f, cl, hf, hno, hcl, hnw, hnu, hnr⟩
  obtain ⟨N, e, us, hT, hu, hR⟩ := plantNew_shape (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hf hno hcl
  refine h X ⟨l, f, cl, N, e, hf, hno, hcl, hnw, hnu, hT, ?_⟩
  cases hni : noIallV e
  · rfl
  · exact absurd (hR hnu hni) hnr

/-- (R1) **`selfPlant`** from `ThSys_plantR`, `PrivCoh` and `SelfPlantRestN`. -/
theorem selfPlant_ofN (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hPC : ∀ {g : G} {E : TEnv} {s : St}, MemInv g E s → PrivCoh E s)
    (hRest : SelfPlantRestN p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' :=
  selfPlant_ofR (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun hPO hNO hInh hPC (hRest.toR (hV0 := hV0) hP hrun hPS hSub hSig) X hwu hfw

/-- (R1, StoNI) **`SelfPlantRestN` is vacuous**: every cell type is `∀`-free at value positions
(`SysInvN.stoNI`), so a planted buffer's element is. -/
theorem selfPlantRestN_of : SelfPlantRestN p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X hex
  obtain ⟨l, f, cl, N, e, -, -, hcl, -, -, hT, hni⟩ := hex
  have h := X.inv.stoNI l cl hcl
  rw [hT] at h
  simp only [noIallV] at h
  rw [h] at hni
  exact absurd hni (by decide)

end PlantN

section Swap
open TermSlotS

/-- The weighted word sum `Σ_i f i ws[i]`. -/
def wsum (f : Nat → Word → Res) : List Word → Res
  | [] => .zero
  | w :: ws => f 0 w + wsum (fun i => f (i + 1)) ws

/-- `wsum` splits at any index. -/
theorem wsum_split : ∀ (f : Nat → Word → Res) (ws : List Word) (n : Nat),
    wsum f ws = wsum f (ws.take n) + wsum (fun i => f (n + i)) (ws.drop n)
  | f, [], n => by
    rw [List.take_nil, List.drop_nil]
    show Res.zero = Res.zero + Res.zero
    exact (Res.add_zero _).symm
  | f, w :: ws, 0 => by
    have e : (fun i => f (0 + i)) = f := funext fun i => by rw [Nat.zero_add]
    rw [e]
    show wsum f (w :: ws) = Res.zero + wsum f (w :: ws)
    exact Res.ext fun k => by simp only [Res.add_apply, Res.zero_apply]; omega
  | f, w :: ws, n + 1 => by
    have ih := wsum_split (fun i => f (i + 1)) ws n
    have e : (fun i => (fun i => f (i + 1)) (n + i)) = (fun i => f (n + 1 + i)) :=
      funext fun i => by show f (n + i + 1) = f (n + 1 + i); rw [Nat.add_right_comm]
    rw [e] at ih
    show f 0 w + wsum (fun i => f (i + 1)) ws =
      (f 0 w + wsum (fun i => f (i + 1)) (ws.take n)) + wsum (fun i => f (n + 1 + i)) (ws.drop n)
    rw [ih, Res.add_assoc]

/-- A closed guarded `μ` is valid like its unfolding. -/
theorem mu_unfold_valid {s : Ty} (hc : Clo (.mu s)) (hg : s.unguarded 0 = false) (ws : List Word) :
    Valid (.mu s) ws ↔ Valid (unfold1 (.mu s)) ws := by
  have hW : ∀ k : Nat, Clo ((fun _ : Nat => Ty.void) k) := fun _ => Clo_void
  have hU : cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (unfold1 (.mu s)) = unfold1 (.mu s) := by
    rw [TermStep.cl_unfold1 hW, hc.2]
  have hsig := TermStep.sig_cl_unfold (ρ := fun _ : Nat => 0) (W := fun _ : Nat => Ty.void) hg
  rw [hU] at hsig
  have hM : cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (.mu s) = .mu s := hc.2 _ _ _ _
  rw [cl_mu_eq] at hM
  have e : Valid (.mu s) ws ↔ Valid (cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 1 0 s) ws := by
    rw [← hM]; exact Iff.rfl
  rw [e]
  exact ⟨fun h => Valid_of_sig hsig.symm h, fun h => Valid_of_sig hsig h⟩

/-- (R1) **The word swap**: a value read on words `ws`, re-read on words `wq` that agree with `ws`
off its (non-ghost, literal) protocol word atoms and are numbers in the protocols there, is again a
value; its resources change by the word terms (`f`, which is `wr` at the word atoms):
`R' + Σ f ws = R + Σ f wq`. -/
theorem VRR_swap (E : TEnv) {ρ : Nat → Nat} {T : Ty} {L : List (Nat × Ty)} (h : AtL T L) :
    Clo T → mg T = true → ∀ {ws wq : List Word} {R : Res} (f : Nat → Word → Res),
      VRR ρ (CE E) T (shp T) ws R → Valid T ws → wc T = some ws.length → wq.length = ws.length →
      (∀ i, i < ws.length → (∀ n P, (i, Ty.word (.lit n) P) ∈ L → P.ghost = false → False) →
        wq[i]? = ws[i]?) →
      (∀ i n P x, (i, Ty.word (.lit n) P) ∈ L → P.ghost = false → wq[i]? = some x →
        ∃ m, x.val = .num m ∧ InP P m) →
      (∀ i n P w, (i, Ty.word (.lit n) P) ∈ L → P.ghost = false → f i w = wr P n w.val) →
      ∃ R', VRR ρ (CE E) T (shp T) wq R' ∧ Valid T wq ∧ R' + wsum f ws = R + wsum f wq := by
  induction h with
  | @atom t hA hne =>
    intro hc hm ws wq R f hv hV hwc hlq hK hW hf
    by_cases hw : ∃ n P, t = .word (.lit n) P ∧ P.ghost = false
    · obtain ⟨n, P, rfl, hg⟩ := hw
      have hmem : ((0 : Nat), Ty.word (.lit n) P) ∈ [((0 : Nat), Ty.word (.lit n) P)] :=
        List.mem_singleton_self _
      have h1 : ws.length = 1 := by simp [wc, accs, hg, nWords, Acc.size] at hwc; omega
      obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
        match ws, h1 with
        | [w], _ => exact ⟨w, rfl⟩
      obtain ⟨x, rfl⟩ : ∃ x, wq = [x] := by
        match wq, hlq with
        | [x], _ => exact ⟨x, rfl⟩
      obtain ⟨m, hxm, hxi⟩ := hW 0 n P x hmem hg rfl
      have ev0 : ev ρ (.lit n) = n := rfl
      simp only [VRR, ev0, List.map_cons, List.map_nil] at hv
      obtain ⟨⟨hpwf, -⟩, hR⟩ := hv
      have hR' : R = wr P n w.val + wdW P n := by
        rcases hR with ⟨hh, rfl⟩ | ⟨hh, rfl⟩
        · unfold wr; rw [if_pos hh]
        · unfold wr; rw [if_neg hh]
          exact Res.ext fun k => by simp only [Res.add_apply, Res.zero_apply]; omega
      refine ⟨wr P n x.val + wdW P n, ?_, by simp [Valid], ?_⟩
      · simp only [VRR, ev0, List.map_cons, List.map_nil]
        refine ⟨⟨hpwf, fun _ => ⟨m, by rw [hxm], hxi⟩⟩, ?_⟩
        by_cases hh : WordHolds P [x.val]
        · left; refine ⟨hh, ?_⟩; unfold wr; rw [if_pos hh]
        · right; refine ⟨hh, ?_⟩; unfold wr; rw [if_neg hh]
          exact Res.ext fun k => by simp only [Res.add_apply, Res.zero_apply]; omega
      · rw [hR']
        show wr P n x.val + wdW P n + (f 0 w + Res.zero) = wr P n w.val + wdW P n + (f 0 x + Res.zero)
        rw [hf 0 n P w hmem hg, hf 0 n P x hmem hg]
        exact Res.ext fun k => by simp only [Res.add_apply, Res.zero_apply]; omega
    · have hall : ∀ i : Nat, wq[i]? = ws[i]? := by
        intro i
        by_cases hi : i < ws.length
        · refine hK i hi fun n P hm hg => hw ⟨n, P, ?_, hg⟩
          have := List.mem_singleton.1 hm
          simp only [Prod.mk.injEq] at this
          exact this.2.symm
        · have h1 : ws.length ≤ i := by omega
          have h2 : wq.length ≤ i := by omega
          rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]
      have e : wq = ws := List.ext_getElem? hall
      subst e
      exact ⟨R, hv, hV, rfl⟩
  | @prod a b A B us hus hA hB ihA ihB =>
    intro hc hm ws wq R f hv hV hwc hlq hK hW hf
    simp only [mg, Bool.and_eq_true] at hm
    obtain ⟨hca, hcb⟩ := Clo_prod hc
    cases hb' : accs b with
    | none => simp [wc, accs, hus, hb'] at hwc
    | some ub =>
    have hwa : wc a = some (nWords us) := wc_of_accs hus
    have hwb : wc b = some (nWords ub) := wc_of_accs hb'
    have hlen : ws.length = nWords us + nWords ub := by
      simp [wc, accs, hus, hb', TermSound.nWords_append] at hwc; omega
    simp only [VRR] at hv
    obtain ⟨ra, rb, e, Ra, Rb, hR, -, hsplit⟩ := hv
    simp only [shp, Shp.prod.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨-, hva, hvb⟩ := hsplit _ (by rw [shp_wc]; exact hwa)
    obtain ⟨hVa, hVb⟩ := hV _ hwa
    have hla : (ws.take (nWords us)).length = nWords us := by simp; omega
    have hlb : (ws.drop (nWords us)).length = nWords ub := by simp; omega
    have hAb := atl_bound hA hca hm.1 hus
    obtain ⟨Ra', hva', hVa', ha⟩ := ihA (ws := ws.take (nWords us)) (wq := wq.take (nWords us)) hca hm.1 f hva hVa (by rw [hla]; exact hwa) (by simp [hlq])
      (fun i hi hno => by
        have hi' : i < nWords us := by rw [hla] at hi; exact hi
        rw [List.getElem?_take, List.getElem?_take, if_pos hi', if_pos hi']
        refine hK i (by omega) fun n P hm hg => ?_
        rcases List.mem_append.1 hm with hm | hm
        · exact hno n P hm hg
        · obtain ⟨⟨i', U⟩, -, he⟩ := List.mem_map.1 hm
          simp only [shO, Prod.mk.injEq] at he
          omega)
      (fun i n P x hm hg hx => by
        rw [List.getElem?_take] at hx
        split at hx
        · exact hW i n P x (List.mem_append_left _ hm) hg hx
        · cases hx)
      (fun i n P w hm hg => hf i n P w (List.mem_append_left _ hm) hg)
    obtain ⟨Rb', hvb', hVb', hb⟩ := ihB (ws := ws.drop (nWords us)) (wq := wq.drop (nWords us)) hcb hm.2 (fun i => f (nWords us + i)) hvb hVb
      (by rw [hlb]; exact hwb) (by simp [hlq])
      (fun i hi hno => by
        rw [hlb] at hi
        rw [List.getElem?_drop, List.getElem?_drop]
        refine hK (nWords us + i) (by omega) fun n P hm hg => ?_
        rcases List.mem_append.1 hm with hm | hm
        · obtain ⟨up, hup, hle⟩ := hAb _ hm
          have e1 : accs (Ty.word (.lit n) P) = some [Acc.one] := by simp [accs, hg]
          rw [e1] at hup
          cases hup
          have e2 : nWords [Acc.one] = 1 := by simp [nWords, Acc.size]
          rw [e2] at hle
          simp only at hle
          omega
        · obtain ⟨⟨i', U⟩, hp, he⟩ := List.mem_map.1 hm
          simp only [shO, Prod.mk.injEq] at he
          obtain ⟨h1, rfl⟩ := he
          have : i' = i := by omega
          subst this
          exact hno n P hp hg)
      (fun i n P x hm hg hx => by
        rw [List.getElem?_drop] at hx
        exact hW (nWords us + i) n P x (List.mem_append_right _ (List.mem_map.2 ⟨(i, _), hm, rfl⟩)) hg hx)
      (fun i n P w hm hg => hf (nWords us + i) n P w
        (List.mem_append_right _ (List.mem_map.2 ⟨(i, _), hm, rfl⟩)) hg)
    have hlq' : wq.length = nWords us + nWords ub := by omega
    have hsa : (shp a).wc = some (nWords us) := by rw [shp_wc]; exact hwa
    refine ⟨Ra' + Rb', ?_, ?_, ?_⟩
    · show ∃ ra rb, Shp.prod (shp a) (shp b) = Shp.prod ra rb ∧ ∃ Ra Rb, Ra' + Rb' = Ra + Rb ∧
        (ra.wc = none → Ra' + Rb' = Res.zero) ∧ ∀ n, ra.wc = some n →
        n ≤ wq.length ∧ VRR ρ (CE E) a ra (wq.take n) Ra ∧ VRR ρ (CE E) b rb (wq.drop n) Rb
      refine ⟨shp a, shp b, rfl, Ra', Rb', rfl, fun h => ?_, fun n hn => ?_⟩
      · rw [hsa] at h; cases h
      · rw [hsa] at hn; cases hn
        exact ⟨by omega, hva', hvb'⟩
    · show ∀ n, wc a = some n → Valid a (wq.take n) ∧ Valid b (wq.drop n)
      intro n hn
      rw [hwa] at hn; cases hn
      exact ⟨hVa', hVb'⟩
    · rw [wsum_split f ws (nWords us), wsum_split f wq (nWords us), hR]
      exact Res.ext fun k => by
        have e1 := congrFun ha k
        have e2 := congrFun hb k
        simp only [Res.add_apply] at e1 e2 ⊢
        omega
  | @mu s L0 hL ih =>
    intro hc hm ws wq R f hv hV hwc hlq hK hW hf
    have hm0 := hm
    simp only [mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
    obtain ⟨hcU, -, -⟩ := mu_unfold_facts hc hm.1
    obtain ⟨hshp, hwcU, hvr⟩ := mu_unfold_vrr hc hm.1
    have hv' := (hvr ρ E _ ws R).2 hv
    rw [← hshp] at hv'
    obtain ⟨R', h1, h2, h3⟩ := ih hcU (mg_unfold1 hm0) f hv' ((mu_unfold_valid hc hm.1 ws).1 hV)
      (by rw [hwcU]; exact hwc) hlq hK hW hf
    rw [hshp] at h1
    exact ⟨R', (hvr ρ E _ wq R').1 h1, (mu_unfold_valid hc hm.1 wq).2 h2, h3⟩

/-- `wvE` at a protocol word unit is its `wr`. -/
theorem wvE_at {E : TEnv} {a : Address} {n : Nat} {P : Proto} (hw : WordAt E a n P) (v : WeakMem.Val) :
    wvE E a v = wr P n v := by
  have hh : ∃ n P, WordAt E a n P := ⟨n, P, hw⟩
  have hw' := Classical.choose_spec (Classical.choose_spec hh)
  rw [wvE, dif_pos hh]
  generalize Classical.choose (Classical.choose_spec hh) = P' at hw' ⊢
  generalize Classical.choose hh = n' at hw' ⊢
  obtain ⟨rfl, rfl⟩ := WordAt_uniq hw hw'
  rfl

/-- (R1) **The slot swap** (`VRR_swap` at slot `j` of a buffer `l`): a slot value on `ws`, re-read on
`wq` agreeing with `ws` off the slot's protocol word units and in protocol there, is a slot value
whose resources change by the protocol-word terms `wvE`. -/
theorem slot_swap {E : TEnv} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc} {j : Nat}
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us) (hj : j < N)
    (hCl : Clo e) (hm : mg e = true) {ws wq : List Word} {R : Res} (hv : ValOfR E e ws R)
    (hl : ws.length = nWords us) (hlq : wq.length = nWords us)
    (hK : ∀ i, i < nWords us → (∀ n P, ¬ WordAt E ⟨l, j * nWords us + i⟩ n P) → wq[i]? = ws[i]?)
    (hW : ∀ i n P x, WordAt E ⟨l, j * nWords us + i⟩ n P → wq[i]? = some x → ∃ m, x.val = .num m ∧ InP P m) :
    ∃ R', ValOfR E e wq R' ∧
      R' + wsum (fun i w => wvE E ⟨l, j * nWords us + i⟩ w.val) ws =
        R + wsum (fun i w => wvE E ⟨l, j * nWords us + i⟩ w.val) wq := by
  obtain ⟨L, hL, hLo⟩ := atl_exists hCl hm (by rw [hu]; simp)
  have hWL : ∀ i n P, (i, Ty.word (.lit n) P) ∈ L → P.ghost = false →
      WordAt E ⟨l, j * nWords us + i⟩ n P := by
    intro i n P hmem hg
    obtain ⟨up, hup, hle⟩ := atl_bound hL hCl hm hu _ hmem
    have e1 : accs (Ty.word (.lit n) P) = some [Acc.one] := by simp [accs, hg]
    rw [e1] at hup
    cases hup
    have e2 : nWords [Acc.one] = 1 := by simp [nWords, Acc.size]
    rw [e2] at hle
    simp only at hle
    have hi : i < nWords us := by omega
    exact (wordAt_iff hc hT hu hj hi).2 ⟨hLo _ hmem, hg⟩
  obtain ⟨R', h1, h2, h3⟩ := VRR_swap E.unsee hL hCl hm (fun i w => wvE E ⟨l, j * nWords us + i⟩ w.val)
    hv.1 hv.2 (by rw [wc_of_accs hu, hl]) (by rw [hlq, hl])
    (fun i hi hno => hK i (by omega) fun n P hw => by
      obtain ⟨hat, hg⟩ := (wordAt_iff hc hT hu hj (by omega)).1 hw
      exact hno n P (atl_complete hat hL ⟨fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩) hg)
    (fun i n P x hmem hg hx => hW i n P x (hWL i n P hmem hg) hx)
    (fun i n P w hmem hg => wvE_at (hWL i n P hmem hg) w.val)
  exact ⟨R', ⟨h1, h2⟩, h3⟩

end Swap

#print axioms ThSysAt_plantQK
#print axioms ThSys_plantRK

end TermPlantR1

/-! ## `TermPlantS` plant corollaries of the R1 masters -/

namespace TermPlantS
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open TermPlantR TermPlantW TermPlantL TermPlantE TermPlantP TermPlantR1
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (S4) **`ThSysAt_plantS`**: planting a set `Q` of own private word-free buffers at
once (frontiers `F`, counts `Np`) keeps the thread's system invariant at the same `seen` set.
Memory's holding is kept (the new slots are values carrying nothing, `hslot`, read at their first
writes, `hR1`); the credits move by an equality of totals (the flip).  `MemInv` at the planted
environment is a premise (`MemInv_plantSet`). -/
theorem ThSysAt_plantS (hV0 : TermViewInv.ViewInvR p k arch Sp c0) {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {Q : AllocLabel → Prop}
    {F : AllocLabel → Ts} {Np : AllocLabel → Nat}
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hQ : ∀ l, Q l → ∃ c N e us, Eg.sto l = some c ∧ c.owner = some g.i ∧ Eg.pfr l = none ∧
      c.ty = .array (.lit N) e ∧ accs e = some us ∧ Eg.rini l ≤ Eg.ini l ∧
      Eg.ini l ≤ Np l ∧ Np l ≤ N ∧ FlipOK (Cut Eg g.i S) (stOf mem pairs th) l ∧
      (∀ o, Eg.ini l * nWords us ≤ o → o < Np l * nWords us →
        ∃ h, FirstW mem ⟨l, o⟩ h ∧
          ∀ t m', h < t → mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ th.promises ++ Eg.fpOf g.i) ∧
      (us = [] ∨ (dwf e = true ∧
      (∀ j, Eg.ini l ≤ j → j < Np l → ∀ ws : List Word, ws.length = nWords us →
        (∀ i w, ws[i]? = some w → ∃ h m, FirstW mem ⟨l, j * nWords us + i⟩ h ∧ mem[h]? = some m ∧ w = mw m) →
        ValOfR (Cut (plantS Eg Q F Np) g.i S) e ws .zero) ∧
        (TermBlkZ.SkFree e = true ∨ (Clo e ∧ TermTv.mg e = true)))))
    (hfo : FpOK (Cut Eg g.i S) (stOf mem pairs th))
    (hMI : MemInv g (Cut (plantS Eg Q F Np) g.i S) (stOf mem pairs th)) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plantS Eg Q F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
  obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := ThSysAt_plantQK (hV0 := hV0) (R := fun _ => False) h hpa (fun _ h => h.elim)
    (fun l hl => by
      obtain ⟨c, N, e, us, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hQ l hl
      exact ⟨c, N, e, us, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, .inl ⟨fun h => h, h10⟩⟩) hfo hMI
  exact ⟨x0, x1, x2, x3, h0, h1⟩

/-- (S7) **`ThSys_plantS`**: the promiser's part of a planting promise step for events whose
planted labels with new slots are single-word protocol buffers or copyable word-free
buffers of single-word units, modulo PrivSlotFresh (`hR1w`, at those labels) and the obligations `hwu`,
`hfw`, `plantPromOK`, `promNewOK`, `plantInh`. -/
theorem ThSys_plantS (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S))
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hWU : ∀ l f cl, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → Eg.sto l = some cl → WordBufT cl.ty ∨ UnitT cl.ty)
    (hR1w : ∀ l f, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e →
      accs e = some us → ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' := by
  obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := ThSys_plantRK (hV0 := hV0) hP hrun X hwu hfw hPO hNO hInh
    (fun l f cl hf hno hcl => (hWU l f cl hf hno hcl).elim .inl fun h => .inr (.inl h)) hR1w hPS hSub hSig
  exact ⟨x0, x1, x2, x3, h0, h1⟩

/-- (S8) **`selfPlant`** from `ThSys_plantS` (word-buffer and unit-buffer events) and
`selfPlantRest` (the others). -/
theorem selfPlant_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hPS : PrivSlotF p k arch Sp Init MintOK c0) (hRest : SelfPlantRestF p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S)) (hPSk : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' := by
  by_cases hW : ∀ l f cl, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → Eg.sto l = some cl → WordBufT cl.ty ∨ UnitT cl.ty
  · exact ThSys_plantS (hV0 := hV0) (hPS := hPSk) (hSub := hSub) (hSig := hSig) hP hrun X hwu hfw hPO hNO hInh hW
      (fun l f hf hno cl N e us hcl hT hu => hPS X l f hf hno cl N e us hcl (hW l f cl hf hno hcl) hT hu)
  · apply hRest X
    apply Classical.byContradiction; intro hn
    exact hW fun l f cl hf hno hcl => Classical.byContradiction fun hb =>
      hn ⟨l, f, cl, hf, hno, hcl, fun h => hb (.inl h), fun h => hb (.inr h)⟩

end
end TermPlantS

#print axioms TermPlantR1.pw_two
#print axioms TermPlantR1.chain_tele
#print axioms TermPlantR1.slot_debitsW
#print axioms TermPlantR1.slot_debitsWV
#print axioms TermPlantR1.PrivSlotA.toF
#print axioms TermPlantR1.privSlot_any
#print axioms TermPlantR1.exists_greatest
#print axioms TermPlantR1.HeldEntry_raiseW
#print axioms TermPlantR1.AtB_iff
#print axioms TermPlantR1.sum_filter_succN
#print axioms TermPlantR1.sum_filter_succM
#print axioms TermPlantR1.unit_tele
#print axioms TermPlantR1.FRes_wv
#print axioms TermPlantR1.FRes_eq_wv
#print axioms TermPlantR1.WRes_wv
#print axioms TermPlantR1.wvE_undef
#print axioms TermPlantR1.newDb_res
#print axioms TermPlantR1.newCr_res
#print axioms TermPlantR1.noOwnR_zero
#print axioms TermPlantR1.blkDb_nstart
#print axioms TermPlantR1.unit_pay
#print axioms TermPlantR1.sum_map_eq_zero
#print axioms TermPlantR1.sum_map_add
#print axioms TermPlantR1.sum_ind
#print axioms TermPlantR1.sum_part
#print axioms TermPlantR1.sum_new
#print axioms TermPlantR1.wvE_nword
#print axioms TermPlantR1.slot_pay
#print axioms TermPlantR1.slotR_tear
#print axioms TermPlantR1.nodup_map_some
#print axioms TermPlantR1.sum_range_mul
#print axioms TermPlantR1.sum_units
#print axioms TermPlantR1.nWl_eq
#print axioms TermPlantR1.RdW_uniq
#print axioms TermPlantR1.RdW_ex
#print axioms TermPlantR1.filter_sub
#print axioms TermPlantR1.sum_congrB
#print axioms TermPlantR1.slot_in
#print axioms TermPlantR1.slot_divmod
#print axioms TermPlantR1.rdW_list_eq
#print axioms TermPlantR1.raise_pay
#print axioms TermPlantR1.BufR_raise
#print axioms TermPlantR1.HeldEntryL_raise
#print axioms TermPlantR1.HeldEntryL_raiseW
#print axioms TermPlantR1.HeldEntryL_len
#print axioms TermPlantR1.raise_payL
#print axioms TermPlantR1.ThSysAt_plantQ
#print axioms TermPlantR1.wvE_noAt
#print axioms TermPlantR1.wdE_noAt
#print axioms TermPlantR1.newDb_zero
#print axioms TermPlantR1.newCr_zero
#print axioms TermPlantR1.wordAt_of_unit
#print axioms TermPlantR1.r1Facts
#print axioms TermPlantR1.qSplit
#print axioms TermPlantR1.qFacts
#print axioms TermPlantR1.ThSys_plantR
#print axioms TermPlantR1.selfPlant_ofR
#print axioms TermPlantR1.Np_nonarr
#print axioms TermPlantR1.plantNew_shape
#print axioms TermPlantR1.SelfPlantRestN.toR
#print axioms TermPlantR1.selfPlant_ofN
#print axioms TermPlantR1.selfPlantRestN_of
#print axioms TermPlantR1.wsum
#print axioms TermPlantR1.wsum_split
#print axioms TermPlantR1.mu_unfold_valid
#print axioms TermPlantR1.VRR_swap
#print axioms TermPlantR1.wvE_at
#print axioms TermPlantR1.slot_swap
#print axioms TermPlantS.ThSysAt_plantS
#print axioms TermPlantS.ThSys_plantS
#print axioms TermPlantS.selfPlant_of
