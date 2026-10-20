import WeakCore.TermOwnX2

/-!
# TermOwnHeldQ (own-key layer, shared; owner): holdings on a label set, and the dispatcher

Copy-free helpers for K2–K4 (no full holding):
* `MemHeldOn Q`: `heldEntry_eqs/tr`, `memHeldOn_eqs/split/move/focus/unfocus/off/tr/store`.
* Thread-local obligation `OwnXLeS`/`OwnXStepL` and the dispatcher `ownXStepPkg_of_local` (any package `q`).
-/

namespace TermOwnHeldQ
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Private holding helpers -/

/-- A held entry depends on the state only through memory and the promises. -/
theorem heldEntry_eqs {E : TEnv} {s s' : St} {l : AllocLabel} {R : Res} (h : HeldEntry E s l R)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) : HeldEntry E s' l R := by
  refine ⟨h.1, fun c hc => ?_⟩
  obtain ⟨vals, hL, hC⟩ := h.2 c hc
  refine ⟨vals, fun o w hw => ?_, hC⟩
  rw [PromAt_eqp e2 e1, e1]
  exact hL o w hw

/-- `MemHeldOn` moves along a state with the same memory and promises. -/
theorem memHeldOn_eqs {Q : AllocLabel → Prop} {E : TEnv} {s s' : St} {H : Res} (h : MemHeldOn Q E s H)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) : MemHeldOn Q E s' H := by
  obtain ⟨L, Rl, hn, hc, hq, hH, he⟩ := h
  exact ⟨L, Rl, hn, hc, hq, hH, fun l hl => heldEntry_eqs (he l hl) e1 e2⟩

/-- **Split** a holding on `Q` along `Q'`. -/
theorem memHeldOn_split {Q : AllocLabel → Prop} (Q' : AllocLabel → Prop) {E : TEnv} {s : St} {H : Res}
    (h : MemHeldOn Q E s H) :
    ∃ H₁ H₂, H = H₁ + H₂ ∧ MemHeldOn (fun l => Q l ∧ Q' l) E s H₁ ∧ MemHeldOn (fun l => Q l ∧ ¬ Q' l) E s H₂ := by
  classical
  obtain ⟨L, Rl, hn, hc, hq, rfl, he⟩ := h
  refine ⟨Res.sum ((L.filter (fun l => decide (Q' l))).map Rl),
    Res.sum ((L.filter (fun l => !decide (Q' l))).map Rl), ?_,
    ⟨_, Rl, hn.filter _, fun l c hq' hs => List.mem_filter.2 ⟨hc l c hq'.1 hs, by simpa using hq'.2⟩,
      fun l hl => ⟨hq l (List.mem_filter.1 hl).1, by simpa using (List.mem_filter.1 hl).2⟩, rfl,
      fun l hl => he l (List.mem_filter.1 hl).1⟩,
    ⟨_, Rl, hn.filter _, fun l c hq' hs => List.mem_filter.2 ⟨hc l c hq'.1 hs, by simpa using hq'.2⟩,
      fun l hl => ⟨hq l (List.mem_filter.1 hl).1, by simpa using (List.mem_filter.1 hl).2⟩, rfl,
      fun l hl => he l (List.mem_filter.1 hl).1⟩⟩
  rw [← Res.sum_append, ← List.map_append]
  exact Res.sum_perm (List.filter_append_perm _ L).symm

/-- **Move** a holding to a new environment, state and label set: the new labels with a cell were
labels with a cell, and their entries move.  The new holding is at most the old one at every key. -/
theorem memHeldOn_move {Q Q' : AllocLabel → Prop} {E E' : TEnv} {s s' : St} {H : Res} (h : MemHeldOn Q E s H)
    (hcov : ∀ l c, Q' l → E'.sto l = some c → Q l ∧ ∃ c', E.sto l = some c')
    (hent : ∀ l R, Q l → Q' l → HeldEntry E s l R → HeldEntry E' s' l R) :
    ∃ H', MemHeldOn Q' E' s' H' ∧ ∀ key, H' key ≤ H key := by
  obtain ⟨H₁, H₂, rfl, ⟨L, Rl, hn, hc, hq, rfl, he⟩, -⟩ := memHeldOn_split Q' h
  refine ⟨_, ⟨L, Rl, hn, fun l c hq' hs => ?_, fun l hl => (hq l hl).2, rfl,
    fun l hl => hent l _ (hq l hl).1 (hq l hl).2 (he l hl)⟩, fun key => by simp only [Res.add_apply]; omega⟩
  obtain ⟨hql, c', hc'⟩ := hcov l c hq' hs
  exact hc l c' ⟨hql, hq'⟩ hc'

/-- **Focus** on a label `l ∈ Q` of a holding. -/
theorem memHeldOn_focus {Q : AllocLabel → Prop} {E : TEnv} {s : St} {H : Res} (h : MemHeldOn Q E s H)
    {l : AllocLabel} (hql : Q l) :
    ∃ R0 H0, H = R0 + H0 ∧ HeldEntry E s l R0 ∧ MemHeldOn (fun l' => Q l' ∧ l' ≠ l) E s H0 := by
  obtain ⟨L, Rl, hnd, hcov, hq, rfl, hent⟩ := h
  by_cases hl : l ∈ L
  · obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hl
    have hnd' : (L1 ++ L2).Nodup := List.Nodup.sublist (by simp) hnd
    have hnl : l ∉ L1 ++ L2 := by
      intro hm
      rw [List.nodup_append] at hnd
      rcases List.mem_append.1 hm with h1 | h2
      · exact hnd.2.2 l h1 l (by simp) rfl
      · exact (List.nodup_cons.1 hnd.2.1).1 h2
    have hsub : ∀ l', l' ∈ L1 ++ L2 → l' ∈ L1 ++ l :: L2 := fun l' hl' => by
      simp only [List.mem_append, List.mem_cons] at hl' ⊢
      rcases hl' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    refine ⟨Rl l, Res.sum ((L1 ++ L2).map Rl), Res.sum_map_cons_mid Rl l L1 L2, hent l hl,
      L1 ++ L2, Rl, hnd', fun l' c hq' hc => ?_, fun l' hl' => ⟨hq l' (hsub l' hl'), fun e => hnl (e ▸ hl')⟩,
      rfl, fun l' hl' => hent l' (hsub l' hl')⟩
    have := hcov l' c hq'.1 hc
    simp only [List.mem_append, List.mem_cons] at this ⊢
    rcases this with h | h | h
    · exact Or.inl h
    · exact absurd h hq'.2
    · exact Or.inr h
  · have hnone : E.sto l = none := by
      cases hc : E.sto l with
      | none => rfl
      | some c => exact absurd (hcov l c hql hc) hl
    refine ⟨.zero, Res.sum (L.map Rl), (Res.zero_add _).symm, ⟨fun _ => rfl, fun c hc => ?_⟩,
      L, Rl, hnd, fun l' c hq' hc => hcov l' c hq'.1 hc, fun l' hl' => ⟨hq l' hl', fun e => hl (e ▸ hl')⟩,
      rfl, hent⟩
    rw [hnone] at hc; cases hc

/-- **Unfocus**: put the entry of a label `l ∈ Q` back. -/
theorem memHeldOn_unfocus {Q : AllocLabel → Prop} {E : TEnv} {s : St} {l : AllocLabel} {R H0 : Res}
    (hX : MemHeldOn (fun l' => Q l' ∧ l' ≠ l) E s H0) (he : HeldEntry E s l R) (hql : Q l) :
    MemHeldOn Q E s (R + H0) := by
  classical
  obtain ⟨L, Rl, hnd, hcov, hq, rfl, hent⟩ := hX
  have hnl : l ∉ L := fun h => (hq l h).2 rfl
  have hmap : L.map (fun l' => if l' = l then R else Rl l') = L.map Rl :=
    List.map_congr_left fun l' hl' => by simp only [(hq l' hl').2, ↓reduceIte]
  refine ⟨l :: L, fun l' => if l' = l then R else Rl l', List.nodup_cons.2 ⟨hnl, hnd⟩,
    fun l' c hq' hc => ?_, fun l' hl' => ?_, ?_, fun l' hl' => ?_⟩
  · by_cases e : l' = l
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hcov l' c ⟨hq', e⟩ hc)
  · rcases List.mem_cons.1 hl' with e | h
    · exact e ▸ hql
    · exact (hq l' h).1
  · rw [List.map_cons, Res.sum_cons, hmap]; simp only [↓reduceIte]
  · by_cases e : l' = l
    · simp only [e, ↓reduceIte]; exact e ▸ he
    · simp only [e, ↓reduceIte]
      exact hent l' ((List.mem_cons.1 hl').resolve_left e)

/-- A holding on `Q` is one on `Q ∧ · ≠ l` when `l ∉ Q`. -/
theorem memHeldOn_off {Q : AllocLabel → Prop} {E : TEnv} {s : St} {l : AllocLabel} {H : Res}
    (h : MemHeldOn Q E s H) (hql : ¬ Q l) : MemHeldOn (fun l' => Q l' ∧ l' ≠ l) E s H := by
  obtain ⟨L, Rl, hnd, hcov, hq, rfl, hent⟩ := h
  exact ⟨L, Rl, hnd, fun l' c hq' hc => hcov l' c hq'.1 hc,
    fun l' hl' => ⟨hq l' hl', fun e => hql (e ▸ hq l' hl')⟩, rfl, hent⟩

/-- A held entry under a transport that keeps the cell, `ini`, `rini` and the latest words. -/
theorem heldEntry_tr {E E' : TEnv} {s s' : St} {l : AllocLabel} {R : Res} (h : HeldEntry E s l R)
    (hsto : E'.sto l = E.sto l) (hini : E'.ini l = E.ini l) (hri : E'.rini l = E.rini l)
    (hlat : ∀ o w, LatestNP s.mem (PromAt E s ⟨l, o⟩) ⟨l, o⟩ w → LatestNP s'.mem (PromAt E' s' ⟨l, o⟩) ⟨l, o⟩ w)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R) :
    HeldEntry E' s' l R := by
  obtain ⟨Rs, hL, rfl⟩ := h.toS
  exact (HeldEntryL_tr hL hsto hini hri hlat hv).entry

/-- **`MemHeldOn` transport** (cf. `MemHeldL_tr`): on `Q` the cell, `ini`, `rini`, `pfr` are kept and
the latest words move; the label set is the same at both environments. -/
theorem memHeldOn_tr {Q Q' : AllocLabel → Prop} {E E' : TEnv} {s s' : St} {H : Res} (h : MemHeldOn Q E s H)
    (hQ : ∀ l, Q' l ↔ Q l)
    (hsto : ∀ l, Q l → E'.sto l = E.sto l) (hini : ∀ l, Q l → E'.ini l = E.ini l)
    (hri : ∀ l, Q l → E'.rini l = E.rini l) (hpf : ∀ l, Q l → E'.pfr l = E.pfr l)
    (htid : E'.tid = E.tid) (hfp : E'.fp = E.fp)
    (hlat : ∀ l, Q l → ∀ o w, LatestNP s.mem (PromAt E s ⟨l, o⟩) ⟨l, o⟩ w →
      LatestNP s'.mem (PromAt E s' ⟨l, o⟩) ⟨l, o⟩ w)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R) :
    MemHeldOn Q' E' s' H := by
  obtain ⟨L, Rl, hnd, hcov, hq, rfl, hent⟩ := h
  refine ⟨L, Rl, hnd, fun l c hq' hc => hcov l c ((hQ l).1 hq') (by rw [← hsto l ((hQ l).1 hq')]; exact hc),
    fun l hl => (hQ l).2 (hq l hl), rfl, fun l hl => heldEntry_tr (hent l hl) (hsto l (hq l hl))
      (hini l (hq l hl)) (hri l (hq l hl)) (fun o w hw => ?_) hv⟩
  rw [PromAt_congr (a := ⟨l, o⟩) (hsto l (hq l hl)) htid (hpf l (hq l hl)) hfp (hini l (hq l hl))
    (TEnv.rc_congr (hini l (hq l hl)) (hri l (hq l hl)))]
  exact hlat l (hq l hl) o w hw

/-- **A store at `a` keeps a holding off `a.label`** (cf. `MemHeldX_store`). -/
theorem memHeldOn_store {Q : AllocLabel → Prop} {E : TEnv} {s s' : St} {H : Res} {k : Promises.Knobs}
    {arch : Arch} {pw : Word} {a : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (h : MemHeldOn Q E s H) (hoff : ∀ l, Q l → l ≠ a.label) (hpl : PromLt s)
    (hs : s' ∈ storeUnits k arch pw a rel us ws 0 s) : MemHeldOn Q E s' H :=
  memHeldOn_tr h (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
    (fun l hq _ _ hl => LatestNP_growsAtF (storeUnits_growsF us ws 0 s s' hs).1
      (storeUnits_growsF us ws 0 s s' hs).2.1 (storeUnits_fulL hpl hs) (hoff l hq) hl) id

-- copied from TermStep.heldStoreAt; holding on `Q` at `a.label ∈ Q`
theorem heldStoreAtP {Q : AllocLabel → Prop} {g : G} {E : TEnv} {s : St} {H : Res} {a : Address} {c : Cell} {us : List Acc}
    {ws : List Word} {U : Ty} {Rv : Res} (hm : MemInv g E s) (hH : MemHeldOn Q E s H) (hq : Q a.label)
    (hsto : E.sto a.label = some c) (hown : c.owner = some E.tid)
    (hnv : NVP E s a.label)
    (hcP : ∃ vals, CellOK E (E.rc a.label) c.ty vals ∧
      ∀ o v, vals[o]? = some v → LatestP s.mem s.promises s.vs.coh ⟨a.label, o⟩ v)
    (hat : AtOff c.ty a.offset U)
    (hini : IniAt E.rc c a U) (hna : ∀ N e, U ≠ .array (.lit N) e)
    (hU : EnvValR E U ws Rv) (hwU : wc U = some (nWords us)) (hlen : ws.length = nWords us) :
    ∃ vq Rq R2 H0, R2 + Rq + H0 = Rv + H ∧ vq.length = nWords us ∧
      (∀ j v, vq[j]? = some v → LatestP s.mem s.promises s.vs.coh (offs a (0 + j)) v) ∧
      VRR (fun _ => 0) (CE E.unsee) U (shp U) vq Rq ∧
      ∀ (k : Promises.Knobs) (arch : Arch) (pw : Word) (rel : Bool) (s1 : St), s1.mem = s.mem →
        s1.promises = s.promises → LoadCoh E s s1 → (∀ b, s.vs.coh b ≤ s1.vs.coh b) →
        SeenLE E s1.vs.vRelSt →
        ∀ s', s' ∈ storeUnits k arch pw a rel us ws 0 s1 → MemHeldOn Q E s' (R2 + H0) := by
  obtain ⟨vals, hcell, hlat⟩ := hcP
  obtain ⟨valsm, hW, hP⟩ := own_msgWordsN (E := E) hnv vals hlat
  obtain ⟨R0, H0, rfl, hent0, hX⟩ := memHeldOn_focus hH hq
  have hcR : CellOKR E (E.ini a.label) (E.rc a.label) c.ty valsm R0 :=
    HeldEntry_cell hent0 hsto hcell hW.length.symm (fun o w h => (hP o w h).2)
  rcases own_segR hcR hat (IniAt_mono E.rc_le_ini hini) hna with
    ⟨b, oS, S, wS, Rs, Rr, -, hbo, hatS, hwS, hbw, hR0, ⟨hvs, hVs⟩, hput⟩ | ⟨N0, e0, -, hT0, -, -, hr0, -⟩
  rotate_left
  · rcases hini N0 e0 hT0 with ⟨hUc, -⟩ | ⟨-, j0, -, -, hj0, -, -⟩
    · exact absurd (hUc.trans hT0) (hna N0 e0)
    · have hj1 : j0 < E.rc a.label := hj0
      omega
  have hsl : ((valsm.drop b).take wS).length = wS := by
    simp only [List.length_take, List.length_drop]; omega
  obtain ⟨n, Rq, Rr2, hwn, hle, hRs, hvq, hput2⟩ := VRR_at E.unsee hatS hvs (by rw [hsl]; exact hwS)
  rw [hwU] at hwn
  obtain rfl : nWords us = n := Option.some.inj hwn
  rw [hsl] at hle
  have hlenv : a.offset + nWords us ≤ valsm.length := by
    rw [← hbo, Nat.add_assoc]; exact Nat.le_trans (Nat.add_le_add_left hle b) hbw
  have hvqe : (((valsm.drop b).take wS).drop oS).take (nWords us) = (valsm.drop a.offset).take (nWords us) := by
    rw [take_drop_take hle, drop_drop', hbo]
  rw [hvqe] at hvq
  refine ⟨(valsm.drop a.offset).take (nWords us), Rq, Rv + Rr2 + Rr, H0, ?_, by simp; omega,
    fun j v hj => ?_, hvq, fun k arch pw rel s1 e1 e2 e3 hmono hsn1 s' hs' => ?_⟩
  · subst hR0; subst hRs; exact Res.ext fun k => by simp only [Res.add_apply]; omega
  · have hj' : valsm[a.offset + j]? = some v := by
      by_cases hjn : j < nWords us
      · rw [List.getElem?_take_of_lt hjn, List.getElem?_drop] at hj; exact hj
      · rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
    have e : offs a (0 + j) = ⟨a.label, a.offset + j⟩ := by simp [offs]
    rw [e]; exact (hP _ v hj').1
  -- the store
  have hpl1 : PromLt s1 := fun t ht => by
    rw [e1]; rw [e2] at ht; exact hm.2.2.1 t ht
  have hnd1 : s1.promises.Nodup := by rw [e2]; exact hm.2.2.2.2.2.2.2.2.2.2.1
  have e3' : ∀ o, o < vals.length → s1.vs.coh ⟨a.label, o⟩ = s.vs.coh ⟨a.label, o⟩ := by
    obtain ⟨valsB, hcB, hlatB, -⟩ := e3.1 a.label c hsto hown
    have hlB : valsB.length = vals.length := (CellOKR_len hcR hcB).symm.trans hW.length.symm
    intro o ho
    have hA := hlat o (vals[o]'ho) (List.getElem?_eq_getElem ho)
    obtain ⟨⟨m1, hm1, hl1, -⟩, hn1, -⟩ := hlatB o (valsB[o]'(hlB ▸ ho)) (List.getElem?_eq_getElem _)
    rcases Nat.lt_or_ge (s.vs.coh ⟨a.label, o⟩) (s1.vs.coh ⟨a.label, o⟩) with hlt | hge
    · exact absurd (hA.2.2 _ m1 hlt hm1 hl1) hn1
    · exact Nat.le_antisymm hge (hmono _)
  have htail : ∀ j : Nat, j < nWords us → TailP s1 (offs a (0 + j)) := fun j hj => by
    have hlt : a.offset + j < vals.length := by
      have h1 : vals.length = valsm.length := hW.length
      rw [h1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hlenv
    have hv := hlat (a.offset + j) (vals[a.offset + j]'hlt) (List.getElem?_eq_getElem hlt)
    have e : offs a (0 + j) = ⟨a.label, a.offset + j⟩ := by simp [offs]
    unfold TailP; rw [e1, e2, e, e3' _ hlt]
    exact fun t m ht hm hl => hv.2.2 t m ht hm hl
  obtain ⟨g2, g3⟩ := storeUnits_latP (a := a) us ws 0 s1 s1.vs.vRelSt hpl1 hnd1 (Nat.le_refl _) s' hs'
  replace g2 := g2 htail
  have hst := hU.store hsn1
  generalize hws' : ws.map (bumpW s1.vs.vRelSt) = ws' at hst
  have hlen' : ws'.length = nWords us := by rw [← hws', List.length_map]; exact hlen
  have hget : ∀ j w, ws[j]? = some w → ws'[j]? = some (bumpW s1.vs.vRelSt w) := fun j w hw => by
    rw [← hws', List.getElem?_map, hw]; rfl
  have hQ := hput2 ws' Rv hst.1 hlen'
  have hQV := (VR_put E.unsee hatS (VRR_VR S (RLink_of (Coh_CE _) (CohR_CE _)) hvs) hVs (by rw [hsl]; exact hwS)
    (VRR_VR U (RLink_of (Coh_CE _) (CohR_CE _)) hst.1) hst.2 (by rw [hlen']; exact hwU)).2.2
  rw [hlen'] at hQV
  have hQl : (((valsm.drop b).take wS).take oS ++ ws' ++ ((valsm.drop b).take wS).drop (oS + nWords us)).length = wS := by
    simp only [List.length_append, List.length_take, List.length_drop, hlen']; omega
  have hcell' := hput _ _ ⟨hQ, hQV⟩ hQl
  have hsp := splice_seg valsm ws' b wS oS (by rw [hlen']; exact hle)
  rw [hlen'] at hsp
  rw [hsp, hbo] at hcell'
  have hlat' : ∀ o v, (valsm.take a.offset ++ ws' ++ valsm.drop (a.offset + nWords us))[o]? = some v →
      LatestP s'.mem s'.promises s'.vs.coh ⟨a.label, o⟩ v := by
    intro o v hov
    rw [splice_get valsm ws' a.offset (nWords us) o hlen' hlenv] at hov
    by_cases hr : a.offset ≤ o ∧ o < a.offset + nWords us
    · rw [iteT hr] at hov
      obtain ⟨hr1, hr2⟩ := hr
      have hj : o - a.offset < ws.length := by rw [hlen]; exact Nat.sub_lt_left_of_lt_add hr1 hr2
      obtain ⟨w, hw⟩ : ∃ w, ws[o - a.offset]? = some w := ⟨ws[o - a.offset], List.getElem?_eq_getElem hj⟩
      rw [hget _ _ hw] at hov
      cases hov
      have := g2 (o - a.offset) w (by rw [← hlen]; exact hj) hw
      have e2 : offs a (0 + (o - a.offset)) = ⟨a.label, o⟩ := by
        simp only [offs, Nat.zero_add]; congr 1; exact Nat.add_sub_of_le hr1
      rw [e2] at this; exact this
    · rw [iteF hr] at hov
      have hold := (hP o v hov).1
      have hov' : o < vals.length := by rw [hW.length]; exact (List.getElem?_eq_some_iff.1 hov).1
      rw [← e1, ← e2] at hold
      replace hold := LatestS_coh_congr (e3' o hov') hold
      refine g3 _ _ (fun j hj e => ?_) hold
      have h' : o = a.offset + j := by simpa [offs] using congrArg WeakMem.Address.offset e
      subst h'
      exact hr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩
  have hent : HeldEntry E s' a.label (Rv + Rr2 + Rr) :=
    HeldEntry_ownN hsto (NVP_store (NVP_eqs hnv e1 e2) hpl1 hs') hlat' hcell'
  exact memHeldOn_unfocus (memHeldOn_store (memHeldOn_eqs hX e1 e2) (fun _ h => h.2) hpl1 hs') hent hq

/-! ## The thread-local obligation and the dispatcher -/

/-- `OwnXLe`'s body at a thread state (`g`, `mem`, `pairs`, `th`). -/
def OwnXLeS (p : Prog) (g : G) (E0 : TEnv) (x : AllocLabel) (n : Nat) (mem : Memory) (pairs : List Ts)
    (th : TTh) : Prop :=
  ∃ E Tot HP, ThInvRE p E th Tot ∧ MemInv g E (stOf mem pairs th) ∧ MemHeldP E (stOf mem pairs th) HP ∧
    g.boxFence = true ∧ StoNIE E ∧ E.sto x ≠ none ∧ Tot (.own x) + HP (.own x) ≤ n ∧
    Ext E0 E ∧ AnchR E0 E0 E (stOf mem pairs th)

/-- **The thread-local step obligation** at the terms `T`: one `tstep` result meeting `PromAbove`, from
a source meeting `PAx`, `ScopeOK` and `PubWinS3` (any `g`, hence any knobs). -/
def OwnXStepL (p : Prog) (x : AllocLabel) (n : Nat) (T : Expr → Prop) : Prop :=
  ∀ (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (r : Memory × List Ts × TTh), g.p = p → 0 < g.n →
    T th.term → ∀ E0 : TEnv, ScopeOK p th → PubWinSA p g mem pairs th E0 E0 →
    (∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts) → OwnXLeS p g E0 x n mem pairs th →
    r ∈ tstep g mem pairs th → PromAbove (stOf r.1 r.2.1 r.2.2) → PAx g mem pairs th →
    OwnXLeS p g E0 x n r.1 r.2.1 r.2.2

/-- **Dispatcher**: the package deliverable from the thread-local obligation at its terms. -/
theorem ownXStepPkg_of_local {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {n q : Nat}
    (h : OwnXStepL p x n (fun t => exprPkg t = q)) : OwnXStepPkg p k arch i x n q := by
  intro E0 c0 c0' th hth hq hsc hw hvI hI hs hc
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  obtain ⟨th1, E, Tot, HP, hth1, hT, hm, hP, hb, hni, hsx, hle, hx0, hA⟩ := hI
  rw [hth] at hth1
  cases hth1
  have hS := h (gOf p k arch c0 i) c0.mem c0.pairs th r rfl
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth))) hq E0 (hsc th hth (TermTyped.not_spawnT_of_steps hth hs)) (hw th hth) (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth)
    ⟨E, Tot, HP, hT, hm, hP, hb, hni, hsx, hle, hx0, hA⟩ hr hpa (PAx_of_step hs hc hth)
  obtain ⟨E', Tot', HP', hT', hm', hP', hb', hni', hsx', hle', hx', hA'⟩ := hS
  refine ⟨r.2.2, E', Tot', HP', e3, hT', ?_, ?_, ?_, hni', hsx', hle', hx', ?_⟩
  · rw [gOf_thread hs, e1, e2]; exact hm'
  · rw [e1, e2]; exact hP'
  · rw [gOf_thread hs]; exact hb'
  · rw [e1, e2]; exact hA'

/-- **A per-op step conclusion**: the result has the own-key data at some `E'` keeping `x` allocated,
with the key total at most the source's frame `Tot0` plus private holding `HP0`. -/
def StepC (p : Prog) (g : G) (x : AllocLabel) (E : TEnv) (s : St) (th : TTh) (Tot0 HP0 : Res)
    (r : Memory × List Ts × TTh) : Prop :=
  ∃ E' Tot' HP', ThInvRE p E' r.2.2 Tot' ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧
    MemHeldP E' (stOf r.1 r.2.1 r.2.2) HP' ∧ StoNIE E' ∧ E'.sto x ≠ none ∧
    Tot' (.own x) + HP' (.own x) ≤ Tot0 (.own x) + HP0 (.own x) ∧
    AnchStep g th E E' s (stOf r.1 r.2.1 r.2.2)

/-- `OwnXStepL` from per-op conclusions at the unpacked source frame (the `tstepMR_*` shape). -/
theorem ownXStepL_of [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} {T : Expr → Prop}
    (h : ∀ (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (r : Memory × List Ts × TTh) (ρ : Nat → Nat)
      (η : TEnv) (cx : Cx) (Rf Rs HP : Res), g.p = p → 0 < g.n → T th.term → ScopeOK p th →
      (∃ E0, PubWinSA p g mem pairs th E0 E0) → EnvOK p η → TypedK p η cx th.term → TvOK cx →
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf → RetPw th.σs th.stack cx.ret → MemInv g (CE η) (stOf mem pairs th) →
      MemHeldP (CE η) (stOf mem pairs th) HP → g.boxFence = true → StoNIE (CE η) → (CE η).sto x ≠ none →
      r ∈ tstep g mem pairs th → PromAbove (stOf r.1 r.2.1 r.2.2) → PAx g mem pairs th →
      StepC p g x (CE η) (stOf mem pairs th) th (Rf + Rs) HP r) :
    OwnXStepL p x n T := by
  intro g mem pairs th r hp hn ht E0 hsc hw hvr hS hr hpa hpx
  obtain ⟨E, Tot, HP, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hT, htv, hi, rfl, hRP⟩, hm, hP, hb, hni, hx, hle, hx0, hA⟩ := hS
  obtain ⟨E', Tot', HP', h1, h2, h3, h0, h4, h5, h6⟩ :=
    h g mem pairs th r ρ η cx Rf Rs HP hp hn ht hsc ⟨E0, hw⟩ hE hT htv hi hRP hm hP hb hni hx hr hpa hpx
  have hFp := finv_of htv hi
  obtain ⟨hx', hA'⟩ := h6 E0 hx0 hA hm.2.2.2.1 h2 (wrHyp hE hT.1 htv hFp hm (hsc ρ η cx hE hT.1 htv hFp) hvr hr)
  exact ⟨E', Tot', HP', h1, h2, h3, hb, h0, h4, by omega, hx', hA'⟩

end TermOwnHeldQ

#print axioms TermOwnHeldQ.heldEntry_eqs
#print axioms TermOwnHeldQ.memHeldOn_eqs
#print axioms TermOwnHeldQ.memHeldOn_split
#print axioms TermOwnHeldQ.memHeldOn_move
#print axioms TermOwnHeldQ.memHeldOn_focus
#print axioms TermOwnHeldQ.memHeldOn_unfocus
#print axioms TermOwnHeldQ.memHeldOn_off
#print axioms TermOwnHeldQ.heldEntry_tr
#print axioms TermOwnHeldQ.memHeldOn_tr
#print axioms TermOwnHeldQ.memHeldOn_store
#print axioms TermOwnHeldQ.ownXStepPkg_of_local
#print axioms TermOwnHeldQ.ownXStepL_of
#print axioms TermOwnHeldQ.heldStoreAtP
