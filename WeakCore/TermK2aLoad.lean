import WeakCore.TermCntEmb
import WeakCore.TermK2a
import WeakCore.TermPubPos

/-!
# TermK2aLoad: what a typed load reads, with read timestamps (K-2a load cases)

`loadUnits_readsR`: each word a load returns carries the value of the message it read and that
message's index as its `rts`; the message is no outstanding promise of the reader (`P`), and a
two-word unit's messages straddle no pair store.
-/

namespace TermK2aLoad
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- What a load of one unit at offset `o` read, with read timestamps. -/
def UnitReadR (mem : Memory) (pairs : List Ts) (a : Address) (P : List Ts) : Acc → Nat → List Word → Prop
  | .one, o, [w] => ∃ (t : Nat) (m : Msg), mem[t]? = some m ∧ m.loc = offs a o ∧ w.val = m.val ∧
      (w.rts : Nat) = t ∧ t ∉ P
  | .two, o, [w0, w1] => ∃ (t0 t1 : Nat) (m0 m1 : Msg), mem[t0]? = some m0 ∧ mem[t1]? = some m1 ∧
      m0.loc = offs a o ∧ m1.loc = offs a (o + 1) ∧
      WeakMem.pairStraddles mem pairs (offs a o) t0 t1 = false ∧
      w0.val = m0.val ∧ (w0.rts : Nat) = t0 ∧ w1.val = m1.val ∧ (w1.rts : Nat) = t1 ∧ t0 ∉ P ∧ t1 ∉ P
  | _, _, _ => False

/-- What a load read, unit by unit, with read timestamps. -/
def ReadsR (mem : Memory) (pairs : List Ts) (a : Address) (P : List Ts) : List Acc → Nat → List Word → Prop
  | [], _, ws => ws = []
  | u :: us, k, ws => UnitReadR mem pairs a P u k (ws.take u.size) ∧
      ReadsR mem pairs a P us (k + u.size) (ws.drop u.size)

/-- **What a load reads, with read timestamps** (`loadUnits_reads` recording `rts`). -/
theorem loadUnits_readsR {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      ∀ P : List Ts, (∀ (t : Nat) (m : Msg), t ∈ P → s.mem[t]? = some m → r.1.vs.coh m.loc < t) →
      ReadsR s.mem s.pairs a P us k r.2
  | [], k, s, r, hr, P, _ => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; rfl
  | .one :: us, k, s, r, hr, P, hP => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have ih := loadUnits_readsR us (k + 1) _ (s', ws) hmem P hP
      have hcm := loadUnits_cohMono us (k + 1) _ (s', ws) hmem
      simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at hth
      obtain ⟨t, ⟨_, hrd⟩, rfl⟩ := hth
      obtain ⟨m, hm, hloc, -⟩ := readable_get hrd
      have e : s.mem[t]! = m := by simp [getElem!_def, hm]
      refine ⟨?_, ih⟩
      refine ⟨t, m, hm, hloc, by simp [e], by simp, fun htp => ?_⟩
      have h1 := hP t m htp hm
      rw [hloc] at h1
      have h2 := Nat.le_trans (by
        show t ≤ (if offs a k = offs a k then max (s.vs.coh (offs a k)) t else s.vs.coh (offs a k))
        split
        · exact Nat.le_max_right _ _
        · rename_i hne; exact absurd rfl hne) (hcm (offs a k))
      exact absurd (Nat.lt_of_le_of_lt h2 h1) (Nat.lt_irrefl _)
  | .two :: us, k, s, r, hr, P, hP => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have ih := loadUnits_readsR us (k + 2) _ (s', ws) hmem P hP
      have hcm := loadUnits_cohMono us (k + 2) _ (s', ws) hmem
      simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
        List.mem_range] at hth
      obtain ⟨t0, ⟨_, hr0⟩, t1, ⟨_, hr1⟩, hs⟩ := hth
      split at hs
      · exact absurd hs (by simp)
      · rename_i hns
        simp only [Option.some.injEq] at hs
        subst hs
        obtain ⟨m0, hm0, hl0, -⟩ := readable_get hr0
        obtain ⟨m1, hm1, hl1, -⟩ := readable_get hr1
        have e0 : s.mem[t0]! = m0 := by simp [getElem!_def, hm0]
        have e1 : s.mem[t1]! = m1 := by simp [getElem!_def, hm1]
        have hnx : (offs a k).next = offs a (k + 1) := by simp [offs, WeakMem.Address.next, Nat.add_assoc]
        refine ⟨?_, ih⟩
        refine ⟨t0, t1, m0, m1, hm0, hm1, hl0, by rw [hl1, hnx], by simpa using hns,
          by simp [e0], by simp, by simp [e1], by simp, fun htp => ?_, fun htp => ?_⟩
        · have h1 := hP t0 m0 htp hm0
          rw [hl0] at h1
          have h2 := Nat.le_trans (by
            show t0 ≤ (if offs a k = offs a k then max (s.vs.coh (offs a k)) t0
              else if offs a k = (offs a k).next then max (s.vs.coh (offs a k).next) t1 else s.vs.coh (offs a k))
            split
            · exact Nat.le_max_right _ _
            · rename_i hne; exact absurd rfl hne) (hcm (offs a k))
          exact absurd (Nat.lt_of_le_of_lt h2 h1) (Nat.lt_irrefl _)
        · have h1 := hP t1 m1 htp hm1
          rw [hl1] at h1
          have h2 := Nat.le_trans (by
            show t1 ≤ (if (offs a k).next = offs a k then max (s.vs.coh (offs a k)) t0
              else if (offs a k).next = (offs a k).next then max (s.vs.coh (offs a k).next) t1
              else s.vs.coh (offs a k).next)
            split
            · rename_i heq; exact absurd (congrArg WeakMem.Address.offset heq) (Nat.succ_ne_self _)
            · split
              · exact Nat.le_max_right _ _
              · rename_i hne; exact absurd rfl hne) (hcm (offs a k).next)
          exact absurd (Nat.lt_of_le_of_lt h2 h1) (Nat.lt_irrefl _)

/-! ## Positions of a read -/

theorem unitReadR_len {mem : Memory} {pairs : List Ts} {a : Address} {P : List Ts} {u : Acc} {o : Nat}
    {ws : List Word} (h : UnitReadR mem pairs a P u o ws) : ws.length = u.size := by
  cases u with
  | one =>
    match ws, h with
    | [_], _ => rfl
    | [], h => simp [UnitReadR] at h
    | _ :: _ :: _, h => simp [UnitReadR] at h
  | two =>
    match ws, h with
    | [_, _], _ => rfl
    | [], h => simp [UnitReadR] at h
    | [_], h => simp [UnitReadR] at h
    | _ :: _ :: _ :: _, h => simp [UnitReadR] at h

theorem readsR_len {mem : Memory} {pairs : List Ts} {a : Address} {P : List Ts} :
    ∀ (us : List Acc) (k : Nat) (ws : List Word), ReadsR mem pairs a P us k ws → ws.length = nWords us
  | [], _, ws, h => by simp only [ReadsR] at h; subst h; rfl
  | u :: us, k, ws, h => by
      have h1 := unitReadR_len h.1
      have h2 := readsR_len us _ _ h.2
      rw [List.length_take] at h1
      rw [List.length_drop] at h2
      rw [TermCntLoc.nWords_cons]
      omega

theorem readsR_at {mem : Memory} {pairs : List Ts} {a : Address} {P : List Ts} :
    ∀ (us : List Acc) (k : Nat) (ws : List Word), ReadsR mem pairs a P us k ws →
      ∀ i u d, UnitAt us i = some (u, d) → UnitReadR mem pairs a P u (k + (i - d)) ((ws.drop (i - d)).take u.size)
  | [], _, _, _, i, u, d, hu => by simp [UnitAt] at hu
  | v :: us, k, ws, h, i, u, d, hu => by
      simp only [UnitAt] at hu
      split at hu
      · cases hu
        simpa using h.1
      · rename_i hlt
        have hb := TermCntLoc.unitAt_bound us _ hu
        have ih := readsR_at us _ _ h.2 _ _ _ hu
        rw [List.drop_drop] at ih
        rw [show k + (i - d) = k + v.size + (i - v.size - d) by omega,
          show i - d = v.size + (i - v.size - d) by omega]
        exact ih

/-- A unit's place in an embedded layout. -/
theorem unitAt_embed {pre us post : List Acc} {i : Nat} (hi : i < nWords us) :
    UnitAt (pre ++ us ++ post) (nWords pre + i) = UnitAt us i := by
  rw [TermCntLoc.unitAt_append, ite_eq_left_iff.mpr (fun h => absurd (by rw [TermCntLoc.nWords_append]; omega) h)]
  rw [TermCntLoc.unitAt_append, ite_eq_right_iff.mpr (fun h => absurd h (by omega)), Nat.add_sub_cancel_left]

theorem unitAt_one {us : List Acc} {i d : Nat} (h : UnitAt us i = some (.one, d)) : d = 0 := by
  have := TermCntLoc.unitAt_bound us i h
  simp [Acc.size] at this; omega

/-- A two-word unit's start. -/
theorem twoAt_of_unitAt : ∀ (us : List Acc) (i d : Nat), UnitAt us i = some (.two, d) → TwoAt us (i - d)
  | [], _, _, h => by simp [UnitAt] at h
  | v :: us, i, d, h => by
      simp only [UnitAt] at h
      split at h
      · cases h
        exact ⟨0, rfl, by simp [nWords]⟩
      · rename_i hlt
        have hb := TermCntLoc.unitAt_bound us _ h
        obtain ⟨j, hj, e⟩ := twoAt_of_unitAt us _ _ h
        refine ⟨j + 1, by simpa using hj, ?_⟩
        rw [List.take_succ_cons, TermCntLoc.nWords_cons]
        omega

/-- **A unit start of a component is no granule's second word of the cell.** -/
theorem notSnd_of_comp {T S U : Ty} {b o : Nat} {L us : List Acc} (hseg : SegOf T b S) (hL : accs S = some L)
    (hat : AtOff S o U) (hu : accs U = some us) {i : Nat} {u : Acc} (hui : UnitAt us i = some (u, 0)) :
    NotSnd T (b + o + i) := by
  intro b' S' L' oo u' d' hs' hL' he hu'
  obtain ⟨pre, post, e, hn⟩ := AtOff_embed hat hL hu
  have hb := TermCntLoc.unitAt_bound us i hui
  have hb' := TermCntLoc.unitAt_bound L' oo hu'
  have hlt : o + i < nWords L := by rw [e, TermCntLoc.nWords_append, TermCntLoc.nWords_append]; omega
  have hoo' : oo < nWords L' := by omega
  obtain ⟨rfl, rfl⟩ := SegOf_unique2 (o := o + i) (o' := oo) hseg hL hlt hs' hL' hoo' (by omega)
  rw [hL] at hL'; cases hL'
  have hoo : oo = nWords pre + i := by omega
  subst hoo
  rw [e, unitAt_embed (by omega), hui] at hu'
  cases hu'; rfl

theorem veq_set {ws : List Word} {i : Nat} {w0 x : Word} (h : ws[i]? = some w0) (hv : w0.val = x.val) :
    VEq ws (ws.set i x) := by
  show ws.map (·.val) = (ws.set i x).map (·.val)
  rw [List.map_set]
  have hi : i < ws.length := (List.getElem?_eq_some_iff.1 h).1
  have e : ws[i] = w0 := by rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  by_cases hj : i = j
  · subst hj; simp [hi, e, hv]
  · simp [hj]

theorem names_unique {l x : AllocLabel} {w : Word} (h1 : Names l w) (h2 : Names x w) : l = x := by
  obtain ⟨a1, g1, e1, rfl⟩ := h1
  obtain ⟨a2, g2, e2, rfl⟩ := h2
  rw [e1] at e2
  simp only [WeakMem.Val.loc.injEq] at e2
  rw [e2.1]

theorem names_val {x : AllocLabel} {w : Word} {m : Msg} (h : Names x w) (hv : w.val = m.val) : Names x (mw m) := by
  obtain ⟨a', g, e, hl⟩ := h
  exact ⟨a', g, by rw [show (mw m).val = m.val from rfl, ← hv]; exact e, hl⟩

/-- **A loaded counted word is `LoadW`**: the word at a counted position of a component value read
from a cell of `sto` (a one-word unit, or a granule's first word: the read message's own slot; a
granule's second word: by clause 4 a pair store's second half, whose first half the read is by the
load lemma). -/
theorem loadW_of_reads {sto : Sto} {mem : Memory} {pairs P : List Ts} {a : Address} {us : List Acc}
    {ws : List Word} (hR : ReadsR mem pairs a P us 0 ws) {cl : Cell} (hc : sto a.label = some cl)
    {S U : Ty} {b o : Nat} {L : List Acc} (hseg : SegOf cl.ty b S) (hL : accs S = some L) (hat : AtOff S o U)
    (hu : accs U = some us) (hbo : b + o = a.offset) (hG : GranuleWP sto mem pairs P)
    {w : Word} (hw : w ∈ pubWords U ws) {x : AllocLabel} (hn : Names x w) :
    TermK2a.LoadW sto mem pairs P w := by
  obtain ⟨i, w0, hi, hw0, hn0, hr0⟩ := TermPubPos.pubWords_pos hw hn
  have hlen := readsR_len us 0 ws hR
  have hil : i < nWords us := by have := (List.getElem?_eq_some_iff.1 hw0).1; omega
  obtain ⟨u, d, hud⟩ := TermCntLoc.unitAt_some us i hil
  have hb := TermCntLoc.unitAt_bound us i hud
  have hU := readsR_at us 0 ws hR i u d hud
  have hnm : ∀ (m : Msg), w0.val = m.val → ∀ l, Names l w → Names l (mw m) := fun m hv l hl => by
    rw [names_unique hl hn]; exact names_val hn0 hv
  -- the one-slot case (a one-word unit, or a granule's first word)
  have hfirst : ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc = offs a i → w0.val = m.val →
      (w0.rts : Nat) = t → t ∉ P → UnitAt us i = some (u, 0) → TermK2a.LoadW sto mem pairs P w := by
    intro t m hm hl hv hrt hP hu0
    have hlab : m.loc.label = a.label := by rw [hl]; rfl
    have hoff : m.loc.offset = b + o + i := by rw [hl]; show a.offset + i = b + o + i; rw [← hbo]
    refine ⟨t, m, cl, hm, hP, by rw [hlab]; exact hc, hnm m hv, Nat.le_of_eq (hrt.symm.trans hr0), .inl ⟨?_, ?_⟩⟩
    · rw [hoff]; exact notSnd_of_comp hseg hL hat hu hu0
    · rw [hoff]
      have hve := veq_set (x := mw m) hw0 hv
      exact TermCntEmb.cntOK_of_comp hseg hL hat hu (wsU := ws.set i (mw m)) (by simp [hlen])
        (by rw [TermCntLoc.cntIdx_eq, ← TermCntLoc.cntK_of_veq U 0 hve, ← TermCntLoc.cntIdx_eq]; exact hi)
        (by rw [List.getElem?_set_self (by omega)])
  cases u with
  | one =>
    obtain rfl := unitAt_one hud
    change UnitReadR mem pairs a P .one (0 + (i - 0)) ((ws.drop (i - 0)).take 1) at hU
    rw [Nat.sub_zero, TermCntLoc.take_drop_one hw0] at hU
    obtain ⟨t, m, hm, hl, hv, hrt, hP⟩ := hU
    exact hfirst t m hm (by rw [hl, Nat.zero_add]) hv hrt hP hud
  | two =>
    have hd : d = 0 ∨ d = 1 := by simp [Acc.size] at hb; omega
    rcases hd with rfl | rfl
    · obtain ⟨w1, hw1⟩ : ∃ w1, ws[i + 1]? = some w1 :=
        ⟨ws[i + 1]'(by simp [Acc.size] at hb; omega), List.getElem?_eq_getElem _⟩
      change UnitReadR mem pairs a P .two (0 + (i - 0)) ((ws.drop (i - 0)).take 2) at hU
      rw [Nat.sub_zero, TermCntLoc.take_drop_two hw0 hw1] at hU
      obtain ⟨t0, t1, m0, m1, hm0, hm1, hl0, hl1, hs, hv0, hr0', hv1, hr1, hP0, hP1⟩ := hU
      exact hfirst t0 m0 hm0 (by rw [hl0, Nat.zero_add]) hv0 hr0' hP0 hud
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      obtain ⟨wj, hwj⟩ : ∃ wj, ws[j]? = some wj := ⟨ws[j]'(by omega), List.getElem?_eq_getElem _⟩
      change UnitReadR mem pairs a P .two (0 + (j + 1 - 1)) ((ws.drop (j + 1 - 1)).take 2) at hU
      rw [show j + 1 - 1 = j from rfl, TermCntLoc.take_drop_two hwj hw0] at hU
      obtain ⟨t0, t1, m0, m1, hm0, hm1, hl0, hl1, hs, hv0, hr0', hv1, hr1, hP0, hP1⟩ := hU
      have hlab1 : m1.loc.label = a.label := by rw [hl1]; rfl
      have hT : TwoAtT cl.ty (a.offset + j) := by
        obtain ⟨pre, post, e, hnp⟩ := AtOff_embed hat hL hu
        have h2 := twoAt_of_unitAt us (j + 1) 1 hud
        rw [show j + 1 - 1 = j from rfl] at h2
        exact ⟨b, S, L, nWords pre + j, hseg, hL, by rw [e]; exact TwoAt_embed h2, by omega⟩
      have hloc : ∃ a' g, m1.val = .loc a' g := by
        obtain ⟨a', g, e, -⟩ := hn0
        exact ⟨a', g, by rw [← hv1]; exact e⟩
      rcases hG.2.2.2 t1 m1 cl (a.offset + j) hm1 hP1 (by rw [hlab1]; exact hc)
          (by rw [hl1]; show a.offset + (0 + j + 1) = a.offset + j + 1; rw [Nat.zero_add, Nat.add_assoc]) hT with
        hnl | ⟨q, hq, rfl⟩
      · obtain ⟨a', g, e⟩ := hloc
        exact absurd e (hnl a' g)
      · have hnx : (offs a (0 + j)).next = offs a (0 + j + 1) := by
          simp [offs, WeakMem.Address.next, Nat.add_assoc]
        have hq0 := TermGranW.granuleWP_partner hG hm0 hl0 hP0 hq hm1 (by rw [hl1, hnx]) hs
        subst hq0
        refine ⟨t0 + 1, m1, cl, hm1, hP1, by rw [hlab1]; exact hc, hnm m1 hv1, Nat.le_of_eq (hr1.symm.trans hr0),
          .inr ⟨t0, m0, rfl, hq, hm0, by rw [hl0, hl1]; rfl, ?_⟩⟩
        have hoff : m0.loc.offset = b + o + j := by
          rw [hl0]; show a.offset + (0 + j) = b + o + j; rw [← hbo, Nat.zero_add]
        rw [hoff]
        have hve1 := veq_set (x := mw m0) hwj hv0
        have hw0' : (ws.set j (mw m0))[j + 1]? = some w0 := by
          rw [List.getElem?_set_ne (by omega)]; exact hw0
        have hve2 := veq_set (x := mw m1) hw0' hv1
        have hve : VEq ws ((ws.set j (mw m0)).set (j + 1) (mw m1)) := hve1.trans hve2
        exact TermCntEmb.cntPairOK_of_comp hseg hL hat hu (wsU := (ws.set j (mw m0)).set (j + 1) (mw m1)) (by rw [List.length_set, List.length_set, hlen])
          (by rw [TermCntLoc.cntIdx_eq, ← TermCntLoc.cntK_of_veq U 0 hve, ← TermCntLoc.cntIdx_eq]; exact hi)
          (by rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)])
          (by rw [List.getElem?_set_self (by rw [List.length_set]; omega)])

/-- **The contract at a load's result**: every counted word of the read component value is new-fine
(naming nothing, or loaded). -/
theorem valB_of_reads {sto : Sto} {s : St} {a : Address} {us : List Acc} {ws : List Word} {th : TTh}
    (hR : ReadsR s.mem s.pairs a th.promises us 0 ws) {cl : Cell} (hc : sto a.label = some cl)
    {S U : Ty} {b o : Nat} {L : List Acc} (hseg : SegOf cl.ty b S) (hL : accs S = some L) (hat : AtOff S o U)
    (hu : accs U = some us) (hbo : b + o = a.offset) (hG : GranuleWP sto s.mem s.pairs th.promises)
    (ga : AllocLabel) (N : AllocLabel → Prop) : TermK2a.ValB sto s ga N th U ws := by
  intro w hw
  by_cases hn : ∃ x, Names x w
  · obtain ⟨x, hx⟩ := hn
    have hL' := loadW_of_reads hR hc hseg hL hat hu hbo hG hw hx
    exact ⟨.inr hL', .inr (.inl hL')⟩
  · exact TermK2a.newW_of_noName fun l hl => hn ⟨l, hl⟩

end TermK2aLoad

#print axioms TermK2aLoad.loadUnits_readsR
#print axioms TermK2aLoad.readsR_len
#print axioms TermK2aLoad.readsR_at
#print axioms TermK2aLoad.notSnd_of_comp
#print axioms TermK2aLoad.loadW_of_reads
#print axioms TermK2aLoad.valB_of_reads
