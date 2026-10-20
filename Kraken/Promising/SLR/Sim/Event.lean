/-
Simulation library, part 2: the per-event simulations (promoted from the
simulation prototype). Read (`readSuccs_sim`), fence (`fenceStep_sim`), the RMW / exclusive
atomic check (`atomic_sim`), write (`writeSuccs_sim`) and the `PromisePure`
break event (`writeSuccs_break`), plus the discharge of the event side
conditions `GapFree` / `AtomGap` from `NoForeign` and `FgnSep`.
-/
import Kraken.Promising.SLR.Sim.Rel

namespace Kraken.Promising

namespace Sim

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Event simulations: read (proved) -/

section Read

variable (A : Arch)

theorem readView_le {ρ : TMap} {k : LoadKind} {f g : Option FwdItem} {t : Time} (ht : ρ.dom t)
    (hfg : FwdLe ρ f g) : readView A k g (ρ.f t) ≤ ρ.fv (readView A k f t) := by
  cases f with
  | none =>
    cases g with
    | none => simp only [readView]; rw [ρ.fv_dom t ht]; exact Nat.le_refl _
    | some b => exact hfg.elim
  | some a =>
    cases g with
    | none => exact hfg.elim
    | some b =>
      obtain ⟨hd, h1, h2, h3, h4⟩ := hfg
      simp only [readView]
      rw [h1, h3]
      by_cases ha : a.time = t
      · subst ha
        by_cases hc : (!a.xcl || (!A.fwdXclOnlyPlain || k == .plain)) = true
        · simp only [decide_true, hc, Bool.and_self, ↓reduceIte]
          split
          · rw [ρ.fv_max]
            refine Nat.max_le.mpr ⟨Nat.le_trans h2 (Nat.le_max_left _ _), Nat.le_trans ?_ (Nat.le_max_right _ _)⟩
            rw [h1] at h4; exact h4
          · exact h2
        · simp only [decide_true, Bool.true_and, hc, Bool.false_eq_true, ↓reduceIte]
          rw [ρ.fv_dom _ hd]; exact Nat.le_refl _
      · have hb : ¬ ρ.f a.time = ρ.f t := fun h => ha (ρ.f_inj hd ht h)
        simp only [ha, hb, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [ρ.fv_dom t ht]; exact Nat.le_refl _

theorem readPre_le {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hiv : IVLe ρ iv' iv)
    (hv : ViewsLe ρ c'.views c.views) (k : LoadKind) : readPre A iv' c' k ≤ ρ.fv (readPre A iv c k) := by
  unfold readPre
  rw [ρ.fv_max, ρ.fv_max]
  have h3 : (if (A.loadKind k == .acq) = true then c'.views.vRel else 0) ≤
      ρ.fv (if (A.loadKind k == .acq) = true then c.views.vRel else 0) := by
    split
    · exact hv.vRel
    · exact Nat.zero_le _
  exact max_le_max' hiv.addrR (max_le_max' hv.vrNew h3)


/-- **Read simulation.** A source read of `l` from `t ∈ dom ρ` is matched by
the target read of `l` from `ρ.f t`, with the same value and related
successor contexts, provided no foreign target message to `l` lies in
`(ρ.f t, ρ.fv bound]` (`bound` the source read's `max νpre (coh l)`). -/
theorem readSuccs_sim {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hc : CtxRel ρ c c')
    (hiv : IVLe ρ iv' iv) {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {t : Time} {v : Val}
    {c₁ : Ctx} (hx : (t, v, c₁) ∈ readSuccs A iv c k xcl l noRet) (ht : ρ.dom t)
    (hgap : GapFree ρ c'.mem l (ρ.f t) (ρ.fv (max (readPre A iv c k) (c.views.getCoh l)))) :
    ∃ c₁', (ρ.f t, v, c₁') ∈ readSuccs A iv' c' k xcl l noRet ∧ CtxRel ρ c₁ c₁' := by
  obtain ⟨t0, v0, he, htl, hv, hw, hp⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hpre := readPre_le A hiv hc.views k
  have hB : max (readPre A iv' c' k) (c'.views.getCoh l) ≤ ρ.fv (max (readPre A iv c k) (c.views.getCoh l)) :=
    le_fv_max hpre (hc.views.coh l)
  refine ⟨readNext A iv' c' k xcl l noRet (ρ.f t) v, (mem_readSuccs A).mpr ⟨_, _, rfl, hc.mem.f_le t ht, ?_, ?_, ?_⟩, ?_⟩
  · -- the value
    unfold Memory.read? at hv ⊢
    by_cases h0 : t = 0
    · subst h0; rw [ρ.f0]; simp only [↓reduceIte] at hv ⊢; rw [Memory.initVal, hc.mem.init]; exact hv
    · have h0' : ρ.f t ≠ 0 := by
        intro h; have := ρ.strict 0 t ρ.dom0 ht (by omega_t); omega_t
      simp only [h0, h0', ↓reduceIte] at hv ⊢
      rw [hc.mem.get t ht]; exact hv
  · -- no overwrite in the window
    cases hw' : c'.mem.writeIn l (ρ.f t) (max (readPre A iv' c' k) (c'.views.getCoh l))
    · rfl
    · exfalso
      obtain ⟨u, w, h1, h2, h3, h4⟩ := (Memory.writeIn_iff _ _ _ _).mp hw'
      by_cases hfor : Foreign ρ u
      · exact hgap u w h1 (Nat.le_trans h2 hB) hfor h3 h4
      · obtain ⟨s, hs, rfl⟩ := Classical.not_not.mp hfor
        have hts : t < s := (ρ.f_lt_iff ht hs).mp h1
        have hsb := ρ.le_of_f_le_fv hs (Nat.le_trans h2 hB)
        rw [hc.mem.get s hs] at h3
        have : c.mem.writeIn l t (max (readPre A iv c k) (c.views.getCoh l)) = true :=
          (Memory.writeIn_iff _ _ _ _).mpr ⟨s, w, hts, hsb, h3, h4⟩
        rw [this] at hw; cases hw
  · -- not an own promise
    cases hp' : c'.prom.contains (ρ.f t)
    · rfl
    · exfalso
      obtain ⟨s, hs, hsd, hst⟩ := (hc.prom.mem _).mp (List.contains_iff_mem.mp hp')
      rw [ρ.f_inj hsd ht hst] at hs
      rw [List.contains_iff_mem.mpr hs] at hp; cases hp
  · -- the successor contexts
    have hν : max (readPre A iv' c' k) (readView A (A.loadKind k) (c'.views.getFwd l) (ρ.f t)) ≤
        ρ.fv (max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) t)) :=
      le_fv_max hpre (readView_le A ht (hc.views.fwd l))
    have hv := hc.views
    refine ⟨hc.mem, ?_, hc.prom, ?_, hc.succView, hc.rmwWrote, hc.stores⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hv.vwOldNT, ?_, hv.vRel, ?_, ?_⟩
      · intro l'
        simp only [readNext]
        change (Views.setCoh _ l _).getCoh l' ≤ ρ.fv ((Views.setCoh _ l _).getCoh l')
        rw [Views.getCoh_setCoh, Views.getCoh_setCoh]
        split
        · exact le_fv_max (hv.coh l) hν
        · exact hv.coh l'
      · simp only [readNext]; split
        · exact le_fv_max hv.vrNew hν
        · exact hv.vrNew
      · simp only [readNext]; split
        · exact hv.vrOld
        · exact le_fv_max hv.vrOld hν
      · simp only [readNext]; split
        · exact le_fv_max hv.vrOldNR hν
        · exact hv.vrOldNR
      · simp only [readNext]; split
        · exact le_fv_max hv.vwNew hν
        · exact hv.vwNew
      · exact hv.vwOld
      · simp only [readNext]; exact le_fv_max hv.vCAP hiv.addrW
      · intro l'; exact hv.fwd l'
      · simp only [readNext]; split
        · exact ⟨ht, rfl, hν, rfl⟩
        · exact hv.xclb
    · simp only [readNext]
      exact Rel2.append hc.loadViews (Rel2.cons hν Rel2.nil)

end Read

/-! ## Event simulations: fence (proved) -/

theorem fenceStep_sim {ρ : TMap} {c c' : Ctx} (hc : CtxRel ρ c c') (k : FenceKind) :
    CtxRel ρ (fenceStep c k) (fenceStep c' k) := by
  have hv := hc.views
  have m2 : ∀ {a' a b' b : View}, a' ≤ ρ.fv a → b' ≤ ρ.fv b → max a' b' ≤ ρ.fv (max a b) :=
    fun ha hb => le_fv_max ha hb
  cases k <;> refine ⟨hc.mem, ?_, hc.prom, hc.loadViews, hc.succView, hc.rmwWrote, hc.stores⟩ <;>
    simp only [fenceStep]
  · exact ⟨hv.coh, m2 hv.vrNew (m2 (m2 hv.vrOld hv.vrOldNR) (m2 hv.vwOld hv.vwOldNT)), hv.vrOld, hv.vrOldNR,
      m2 hv.vwNew (m2 (m2 hv.vrOld hv.vrOldNR) (m2 hv.vwOld hv.vwOldNT)), hv.vwOld, hv.vwOldNT, hv.vCAP, hv.vRel,
      hv.fwd, hv.xclb⟩
  · exact ⟨hv.coh, m2 hv.vrNew hv.vrOld, hv.vrOld, hv.vrOldNR, m2 hv.vwNew hv.vrOld, hv.vwOld, hv.vwOldNT,
      hv.vCAP, hv.vRel, hv.fwd, hv.xclb⟩
  · exact ⟨hv.coh, hv.vrNew, hv.vrOld, hv.vrOldNR, m2 hv.vwNew (m2 hv.vwOld hv.vwOldNT), hv.vwOld, hv.vwOldNT,
      hv.vCAP, hv.vRel, hv.fwd, hv.xclb⟩
  · exact ⟨hv.coh, m2 hv.vrNew (m2 hv.vwOld hv.vwOldNT), hv.vrOld, hv.vrOldNR,
      m2 hv.vwNew (m2 hv.vwOld hv.vwOldNT), hv.vwOld, hv.vwOldNT, hv.vCAP, hv.vRel, hv.fwd, hv.xclb⟩
  · exact ⟨hv.coh, m2 hv.vrNew hv.vCAP, hv.vrOld, hv.vrOldNR, hv.vwNew, hv.vwOld, hv.vwOldNT, hv.vCAP, hv.vRel,
      hv.fwd, hv.xclb⟩

/-! ## Event simulations: write (proved) -/

section Write

variable (A : Arch) (tid : Nat)

theorem read?_rel {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') {s : Time} (hs : ρ.dom s) (l : Loc) :
    M'.read? l (ρ.f s) = M.read? l s := by
  unfold Memory.read?
  by_cases h0 : s = 0
  · subst h0; rw [ρ.f0]; simp only [↓reduceIte]; rw [Memory.initVal, hm.init]; rfl
  · have h0' : ρ.f s ≠ 0 := by
      intro h; have := ρ.strict 0 s ρ.dom0 hs (by omega_t); omega_t
    simp only [h0, h0', ↓reduceIte]
    rw [hm.get s hs]

theorem atomic_intro {mem : Memory} {l : Loc} {tid : Nat} {tr tw : Time}
    (h : ∀ v, mem.read? l tr = some v → ∀ u w, tr < u → u < tw → mem.get? u = some w → w.loc = l → w.tid = tid) :
    mem.atomic l tid tr tw = true := by
  unfold Memory.atomic
  cases hv : mem.read? l tr with
  | none => rfl
  | some v =>
    simp only [List.all_eq_true, List.mem_range]
    intro i hi
    cases hw : mem.get? (tr + i + 1) with
    | none => rfl
    | some w =>
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      by_cases hl : w.loc = l
      · exact .inr (h v hv _ w (by omega_t) (by omega_t) hw hl)
      · exact .inl hl

theorem atomic_sim {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') {l : Loc} {a t t' : Time} (ha : ρ.dom a)
    (hat : M.atomic l tid a t = true) (htt : ∀ s, ρ.dom s → ρ.f s < t' → s < t)
    (hgap : AtomGap ρ M' l tid (ρ.f a) t') : M'.atomic l tid (ρ.f a) t' = true := by
  apply atomic_intro
  intro v hv u w h1 h2 hw hl
  rw [read?_rel hm ha] at hv
  by_cases hfor : Foreign ρ u
  · exact hgap u w h1 h2 hfor hw hl
  · obtain ⟨s, hs, rfl⟩ := Classical.not_not.mp hfor
    rw [hm.get s hs] at hw
    exact Memory.atomic_elim hat hv s w ((ρ.f_lt_iff ha hs).mp h1) (htt s hs h2) hw hl

theorem fv_lt_f {ρ : TMap} {b t : Time} (ht : ρ.dom t) (h : b < t) : ρ.fv b < ρ.f t := by
  obtain ⟨s0, hs0, hle, he⟩ := ρ.fv_floor b
  rw [he]; exact ρ.strict s0 t hs0 ht (by omega_t)

theorem fv_le_last {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') (b : View) : ρ.fv b ≤ M'.last := by
  obtain ⟨s0, hs0, -, he⟩ := ρ.fv_floor b
  rw [he]; exact hm.f_le s0 hs0

theorem writePre_le {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hiv : IVLe ρ iv' iv)
    (hv : ViewsLe ρ c'.views c.views) (k : StoreKind) {extra extra' : View} (hex : extra' ≤ ρ.fv extra) :
    writePre A iv' c' k extra' ≤ ρ.fv (writePre A iv c k extra) := by
  unfold writePre
  refine le_fv_max (le_fv_max hiv.addrW (le_fv_max hiv.dataW (le_fv_max hiv.condW hex)))
    (le_fv_max (le_fv_max hv.vwNew hv.vCAP) ?_)
  split
  · exact le_fv_max (le_fv_max hv.vrOld hv.vrOldNR) hv.vwOld
  · split
    · exact le_fv_max hv.vrOld hv.vrOldNR
    · exact Nat.zero_le _

/-- `afterWrite` on related contexts, the write's timestamp in the domain. -/
theorem afterWrite_rel {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hc : CtxRel ρ c c')
    (hiv : iv'.addrW ≤ ρ.fv iv.addrW) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) {t : Time} (ht : ρ.dom t)
    {νfwd νfwd' : View} (hν : νfwd' ≤ ρ.fv νfwd) (ful ful' : Bool) {xr xr' : View} (hxr : xr' ≤ ρ.fv xr) :
    CtxRel ρ (afterWrite A iv c k xcl l v t νfwd ful xr) (afterWrite A iv' c' k xcl l v (ρ.f t) νfwd' ful' xr') := by
  have hv := hc.views
  have hft : ρ.f t ≤ ρ.fv t := by rw [ρ.fv_dom t ht]; exact Nat.le_refl _
  refine ⟨hc.mem, ⟨fun l' => ?_, hv.vrNew, hv.vrOld, hv.vrOldNR, hv.vwNew, ?_, ?_, le_fv_max hv.vCAP hiv, ?_,
    fun l' => ?_, ?_⟩, hc.prom.erase ht, hc.loadViews, ?_, hc.rmwWrote, congrArg (· + 1) hc.stores⟩
  · rw [afterWrite_getCoh, afterWrite_getCoh]
    split
    · exact le_fv_max (hv.coh l) hft
    · exact hv.coh l'
  · show (if k == .nt then _ else _) ≤ ρ.fv (if k == .nt then _ else _)
    split
    · exact hv.vwOld
    · exact le_fv_max hv.vwOld hft
  · show (if k == .nt then _ else _) ≤ ρ.fv (if k == .nt then _ else _)
    split
    · exact le_fv_max hv.vwOldNT hft
    · exact hv.vwOldNT
  · show (if k == .rel then _ else _) ≤ ρ.fv (if k == .rel then _ else _)
    split
    · exact le_fv_max hv.vRel hft
    · exact hv.vRel
  · rw [afterWrite_getFwd, afterWrite_getFwd]
    split
    · refine ⟨ht, rfl, hν, rfl, ?_⟩
      rcases Nat.le_total xr t with h | h
      · rw [Nat.min_eq_left h]; exact Nat.le_trans (Nat.min_le_left _ _) hxr
      · rw [Nat.min_eq_right h, ρ.fv_dom t ht]; exact Nat.min_le_right _ _
    · exact hv.fwd l'
  · show XclLe ρ (if xcl then none else c.views.xclb) (if xcl then none else c'.views.xclb)
    cases xcl
    · exact hv.xclb
    · trivial
  · show (if A.succViewBot then 0 else ρ.f t) ≤ ρ.fv (if A.succViewBot then 0 else t)
    split
    · exact Nat.zero_le _
    · exact hft

/-- **Write simulation.** A source write (fulfilling a promise in the domain,
or fresh at the end of memory) is matched by the target write at the mapped
timestamp; a fresh write extends the map (`freshMap`). Side conditions: the
source context is bounded (`Ctx.Bnd`), its promises are in the domain, and,
for an exclusive/RMW write, no foreign message to `l` by another thread lies
between the read and the end of the target memory (`AtomGap`). This is the
general form, with foreign messages separated at a set of thresholds
(`FgnSepAt`); `writeSuccs_sim` is the single-threshold form. -/
theorem writeSuccs_simAt {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hc : CtxRel ρ c c') (hb : c.Bnd)
    (hpd : ∀ s ∈ c.prom, ρ.dom s) (hiv : IVLe ρ iv' iv) (hivb : iv.Le c.mem.last) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : TrRel ρ tr tr') {extra extra' : View} (hex : extra' ≤ ρ.fv extra)
    (hexb : extra ≤ c.mem.last) {xr xr' : View} (hxr : xr' ≤ ρ.fv xr) (hxrb : xr ≤ c.mem.last)
    (hgap : ∀ a, tr' = some a → AtomGap ρ c'.mem l tid a (c'.mem.last + 1))
    {c₂ : Ctx} (h : c₂ ∈ writeSuccs A tid iv c k xcl l v tr extra xr) :
    ∃ ρ' : TMap, ∃ c₂', c₂' ∈ writeSuccs A tid iv' c' k xcl l v tr' extra' xr' ∧ CtxRel ρ' c₂ c₂' ∧
      (∀ s, ρ.dom s → ρ'.dom s ∧ ρ'.f s = ρ.f s) ∧ (∀ x ≤ c.mem.last, ρ'.fv x = ρ.fv x) ∧
      (∀ s ∈ c₂.prom, ρ'.dom s) ∧ (NoForeign ρ c'.mem → NoForeign ρ' c₂'.mem) ∧
      ((∀ s ≤ c.mem.last, ρ.dom s) → ∀ s ≤ c₂.mem.last, ρ'.dom s) ∧
      (∀ N L, (∀ n, N n → n ≤ c.mem.last) → FgnSepAt ρ c'.mem N L → FgnSepAt ρ' c₂'.mem N L) := by
  have hpre := writePre_le A hiv hc.views k hex
  have hB : max (writePre A iv' c' k extra') (c'.views.getCoh l) ≤
      ρ.fv (max (writePre A iv c k extra) (c.views.getCoh l)) := le_fv_max hpre (hc.views.coh l)
  have hfwd : max iv'.addrR (max iv'.dataR extra') ≤ ρ.fv (max iv.addrR (max iv.dataR extra)) :=
    le_fv_max hiv.addrR (le_fv_max hiv.dataR hex)
  -- the exclusive part of `WriteOk`, transported
  have hatom : ∀ (t t' : Time), (∀ s, ρ.dom s → ρ.f s < t' → s < t) → t' ≤ c'.mem.last + 1 →
      (∀ a, ρ.dom a → a < t → ρ.f a < t') →
      (∀ a, tr = some a → a < t ∧ c.mem.atomic l tid a t = true) →
      ∀ a', tr' = some a' → a' < t' ∧ c'.mem.atomic l tid a' t' = true := by
    intro t t' htt ht' hlt hok a' ha'
    cases tr with
    | none => cases tr' with
      | none => cases ha'
      | some _ => exact htr.elim
    | some a =>
      cases tr' with
      | none => cases ha'
      | some b =>
        cases ha'
        obtain ⟨hd, rfl⟩ := htr
        obtain ⟨h1, h2⟩ := hok a rfl
        refine ⟨hlt a hd h1, atomic_sim tid hc.mem hd h2 htt ?_⟩
        intro s' w x y z u
        exact hgap _ rfl s' w x (Nat.lt_of_lt_of_le y ht') z u
  rcases (mem_writeSuccs A tid).mp h with ⟨t, htp, w, hw, hl, hv, htid, ⟨hok1, hok2⟩, rfl⟩ | ⟨⟨hok1, hok2⟩, rfl⟩
  · -- fulfil a promise in the domain
    have ht := hpd t htp
    refine ⟨ρ, _, (mem_writeSuccs A tid).mpr (.inl ⟨ρ.f t, (hc.prom.mem _).mpr ⟨t, htp, ht, rfl⟩, w,
      by rw [hc.mem.get t ht]; exact hw, hl, hv, htid, ⟨Nat.lt_of_le_of_lt hB (fv_lt_f ht hok1), ?_⟩, rfl⟩),
      afterWrite_rel A hc hiv.addrW _ xcl l v ht hfwd true true hxr, fun s hs => ⟨hs, rfl⟩, fun _ _ => rfl,
      fun s hs => hpd s (List.mem_of_mem_erase hs), fun h => h, fun h => h, fun _ _ _ h => h⟩
    exact hatom t (ρ.f t) (fun s hs h => (ρ.f_lt_iff hs ht).mp h)
      (Nat.le_succ_of_le (hc.mem.f_le t ht)) (fun a ha h => ρ.strict a t ha ht h) hok2
  · -- a fresh write at the end of both memories
    have hc2 := CtxRel.fresh hc hb hpd { loc := l, val := v, tid }
      (pn := c.promisedNow ++ [({ loc := l, val := v, tid }, max (writePre A iv c k extra) (c.views.getCoh l))])
      (pn' := c'.promisedNow ++ [({ loc := l, val := v, tid }, max (writePre A iv' c' k extra') (c'.views.getCoh l))])
    have hn := freshMap_new hc.mem
    have hlast := Memory.last_append c.mem { loc := l, val := v, tid }
    have hiv2 : iv'.addrW ≤ (freshMap ρ hc.mem).fv iv.addrW := by
      rw [freshMap_fv hc.mem hivb.addrW]; exact hiv.addrW
    have hfwd2 : max iv'.addrR (max iv'.dataR extra') ≤ (freshMap ρ hc.mem).fv (max iv.addrR (max iv.dataR extra)) := by
      rw [freshMap_fv hc.mem (by have := hivb.addrR; have := hivb.dataR; omega_t)]; exact hfwd
    have hr := afterWrite_rel A hc2 hiv2 (A.storeKind k) xcl l v hn.1 hfwd2 false false
      (xr := xr) (xr' := xr') (by rw [freshMap_fv hc.mem hxrb]; exact hxr)
    rw [hn.2] at hr
    refine ⟨freshMap ρ hc.mem, _, (mem_writeSuccs A tid).mpr (.inr ⟨⟨?_, ?_⟩, rfl⟩), hr,
      freshMap_agree hc.mem, fun x hx => freshMap_fv hc.mem hx, ?_, ?_, ?_, ?_⟩
    rotate_left 2
    · intro s hs
      have hs' := List.mem_of_mem_erase hs
      rcases List.mem_append.mp hs' with hs' | hs'
      · exact (freshMap_agree hc.mem s (hpd s hs')).1
      · rw [List.mem_singleton.mp hs']; exact hn.1
    · intro hnf s' h1 h2
      show ∃ s, (freshMap ρ hc.mem).dom s ∧ (freshMap ρ hc.mem).f s = s'
      change s' ≤ (c'.mem.append _).1.last at h2
      rw [Memory.last_append] at h2
      rcases Nat.lt_or_eq_of_le h2 with h2 | rfl
      · obtain ⟨s, hs, rfl⟩ := hnf s' h1 (Nat.le_of_lt_succ h2)
        exact ⟨s, (freshMap_agree hc.mem s hs).1, (freshMap_agree hc.mem s hs).2⟩
      · exact ⟨_, hn.1, hn.2⟩
    · intro hall s hs
      change s ≤ (c.mem.append _).1.last at hs
      rw [Memory.last_append] at hs
      rcases Nat.lt_or_eq_of_le hs with hs | rfl
      · exact (freshMap_agree hc.mem s (hall s (Nat.le_of_lt_succ hs))).1
      · exact hn.1
    · intro N L hN hfs s' w hfor hw
      have hfor0 : Foreign ρ s' := fun ⟨s, hs, he⟩ => hfor ⟨s, (freshMap_agree hc.mem s hs).1,
        by rw [(freshMap_agree hc.mem s hs).2]; exact he⟩
      have hne : s' ≠ c'.mem.last + 1 := fun he => hfor ⟨_, hn.1, by rw [hn.2, he]⟩
      have hle := (get?_some_le' hw).2
      change s' ≤ (c'.mem.append _).1.last at hle
      rw [Memory.last_append] at hle
      have hle' : s' ≤ c'.mem.last := by omega_t
      change (c'.mem.append _).1.get? s' = some w at hw
      rw [Memory.get?_append_of_le _ _ _ hle'] at hw
      obtain ⟨h1, n, hnN, h2, h3⟩ := hfs s' w hfor0 hw
      refine ⟨h1, n, hnN, by rw [freshMap_fv hc.mem (hN n hnN)]; exact h2, fun s hs hns => ?_⟩
      rcases hs with hs | rfl
      · rw [(freshMap_agree hc.mem s hs).2]; exact h3 s hs hns
      · rw [hn.2]; omega_t
    · exact Nat.lt_succ_of_le (Nat.le_trans hB (fv_le_last hc.mem _))
    · refine hatom (c.mem.last + 1) (c'.mem.last + 1) (fun s hs _ => Nat.lt_succ_of_le (hc.mem.dom_le s hs))
        (Nat.le_refl _) (fun a ha _ => Nat.lt_succ_of_le (hc.mem.f_le a ha)) hok2

/-- **Write simulation**, foreign messages separated at one threshold `n`
(`FgnSep`). The corollary of `writeSuccs_simAt` at `N = {n}`. -/
theorem writeSuccs_sim {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hc : CtxRel ρ c c') (hb : c.Bnd)
    (hpd : ∀ s ∈ c.prom, ρ.dom s) (hiv : IVLe ρ iv' iv) (hivb : iv.Le c.mem.last) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : TrRel ρ tr tr') {extra extra' : View} (hex : extra' ≤ ρ.fv extra)
    (hexb : extra ≤ c.mem.last) {xr xr' : View} (hxr : xr' ≤ ρ.fv xr) (hxrb : xr ≤ c.mem.last)
    (hgap : ∀ a, tr' = some a → AtomGap ρ c'.mem l tid a (c'.mem.last + 1))
    {c₂ : Ctx} (h : c₂ ∈ writeSuccs A tid iv c k xcl l v tr extra xr) :
    ∃ ρ' : TMap, ∃ c₂', c₂' ∈ writeSuccs A tid iv' c' k xcl l v tr' extra' xr' ∧ CtxRel ρ' c₂ c₂' ∧
      (∀ s, ρ.dom s → ρ'.dom s ∧ ρ'.f s = ρ.f s) ∧ (∀ x ≤ c.mem.last, ρ'.fv x = ρ.fv x) ∧
      (∀ s ∈ c₂.prom, ρ'.dom s) ∧ (NoForeign ρ c'.mem → NoForeign ρ' c₂'.mem) ∧
      ((∀ s ≤ c.mem.last, ρ.dom s) → ∀ s ≤ c₂.mem.last, ρ'.dom s) ∧
      (∀ n L, n ≤ c.mem.last → FgnSep ρ c'.mem n L → FgnSep ρ' c₂'.mem n L) := by
  obtain ⟨ρ', c₂', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    writeSuccs_simAt A tid hc hb hpd hiv hivb htr hex hexb hxr hxrb hgap h
  exact ⟨ρ', c₂', h1, h2, h3, h4, h5, h6, h7, fun n L hn hf =>
    (h8 (· = n) L (fun m hm => hm ▸ hn) hf.toAt).toSep⟩

/-- **The break event** (`PromisePure` instance). When the source write
fulfils an outstanding promise *outside* the domain (the promise whose message
the target memory does not have), the target performs the same write — same
location, value and kind — *fresh*, at the end of its memory. The target's
fresh write is always enabled under the relation (its bound is at most
`|M'|`); the one side condition is the exclusive check `Memory.atomic` up to
the end of the target memory: vacuous for a plain store (`tr = none`), and for
an RMW or a store exclusive false when another thread wrote `l` after the read
(in the source those writes come after the promise). After this event the map
would send the promise's timestamp to the end of the target memory, above the
images of larger source timestamps: not monotone, so the relation does not
continue. The instance stops here, which is all `PromisePure` needs (the value
written by the fulfilling instruction, from an erased configuration). -/
theorem writeSuccs_break {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hc : CtxRel ρ c c')
    (hiv : IVLe ρ iv' iv) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) {tr tr' : Option Time}
    (htr : TrRel ρ tr tr') {extra extra' : View} (hex : extra' ≤ ρ.fv extra) {xr' : View}
    (hatom : ∀ a, tr' = some a → c'.mem.atomic l tid a (c'.mem.last + 1) = true) :
    afterWrite A iv'
        { c' with mem := (c'.mem.append { loc := l, val := v, tid }).1,
                  prom := c'.prom ++ [c'.mem.last + 1],
                  promisedNow := c'.promisedNow ++
                    [({ loc := l, val := v, tid }, max (writePre A iv' c' k extra') (c'.views.getCoh l))] }
        (A.storeKind k) xcl l v (c'.mem.last + 1) (max iv'.addrR (max iv'.dataR extra')) false xr' ∈
      writeSuccs A tid iv' c' k xcl l v tr' extra' xr' := by
  refine (mem_writeSuccs A tid).mpr (.inr ⟨⟨?_, ?_⟩, rfl⟩)
  · exact Nat.lt_succ_of_le (Nat.le_trans (le_fv_max (writePre_le A hiv hc.views k hex) (hc.views.coh l))
      (fv_le_last hc.mem _))
  · intro a ha
    refine ⟨?_, hatom a ha⟩
    cases tr with
    | none => cases tr' with
      | none => cases ha
      | some _ => exact htr.elim
    | some b =>
      cases tr' with
      | none => cases ha
      | some b' =>
        cases ha
        obtain ⟨hd, rfl⟩ := htr
        exact Nat.lt_succ_of_le (hc.mem.f_le b hd)

end Write

/-! ## Event side conditions from the placement of foreign messages -/

theorem NoForeign.gap {ρ : TMap} {M' : Memory} (h : NoForeign ρ M') (l : Loc) (lo hi : Time) :
    GapFree ρ M' l lo hi := by
  intro s' w _ _ hfor hw _
  obtain ⟨h1, h2⟩ := get?_some_le hw
  exact hfor (h s' h1 h2)

theorem NoForeign.atom {ρ : TMap} {M' : Memory} (h : NoForeign ρ M') (l : Loc) (tid : Nat) (lo hi : Time) :
    AtomGap ρ M' l tid lo hi := by
  intro s' w _ _ hfor hw _
  obtain ⟨h1, h2⟩ := get?_some_le hw
  exact absurd (h s' h1 h2) hfor

theorem FgnSep.gap {ρ : TMap} {M' : Memory} {n : Nat} {L : Loc → Prop} (h : FgnSep ρ M' n L) {l : Loc}
    {t b : Time} (ht : ρ.dom t) (hst : L l → t ≤ n → b ≤ n) : GapFree ρ M' l (ρ.f t) (ρ.fv b) := by
  intro s' w h1 h2 hfor hw hl
  obtain ⟨hL, hlo, hhi⟩ := h s' w hfor hw
  by_cases htn : t ≤ n
  · have hb := hst (hl ▸ hL) htn
    have := ρ.fv_mono _ _ hb; omega_t
  · have := hhi t ht (by omega_t); omega_t

theorem FgnSep.atom {ρ : TMap} {M' : Memory} {n : Nat} {L : Loc → Prop} (h : FgnSep ρ M' n L) {l : Loc}
    (tid : Nat) {a : Time} (ha : ρ.dom a) (hst : L l → n < a) (hi : Time) :
    AtomGap ρ M' l tid (ρ.f a) hi := by
  intro s' w h1 _ hfor hw hl
  obtain ⟨hL, -, hhi⟩ := h s' w hfor hw
  have := hhi a ha (hst (hl ▸ hL)); omega_t

theorem NoForeign.fgnSep {ρ : TMap} {M' : Memory} (h : NoForeign ρ M') (n : Nat) (L : Loc → Prop) :
    FgnSep ρ M' n L := by
  intro s' w hfor hw
  obtain ⟨h1, h2⟩ := get?_some_le hw
  exact absurd (h s' h1 h2) hfor

/-- `FgnSep.gap` at several thresholds: the read's `StaleFree` clause at every
threshold in `N`. -/
theorem FgnSepAt.gap {ρ : TMap} {M' : Memory} {N : Nat → Prop} {L : Loc → Prop} (h : FgnSepAt ρ M' N L)
    {l : Loc} {t b : Time} (ht : ρ.dom t) (hst : ∀ n, N n → L l → t ≤ n → b ≤ n) :
    GapFree ρ M' l (ρ.f t) (ρ.fv b) := by
  intro s' w h1 h2 hfor hw hl
  obtain ⟨hL, n, hn, hlo, hhi⟩ := h s' w hfor hw
  by_cases htn : t ≤ n
  · have hb := hst n hn (hl ▸ hL) htn
    have := ρ.fv_mono _ _ hb; omega_t
  · have := hhi t ht (by omega_t); omega_t

/-- `FgnSep.atom` at several thresholds. -/
theorem FgnSepAt.atom {ρ : TMap} {M' : Memory} {N : Nat → Prop} {L : Loc → Prop} (h : FgnSepAt ρ M' N L)
    {l : Loc} (tid : Nat) {a : Time} (ha : ρ.dom a) (hst : ∀ n, N n → L l → n < a) (hi : Time) :
    AtomGap ρ M' l tid (ρ.f a) hi := by
  intro s' w h1 _ hfor hw hl
  obtain ⟨hL, n, hn, -, hhi⟩ := h s' w hfor hw
  have := hhi a ha (hst n hn (hl ▸ hL)); omega_t

end Sim

end Kraken.Promising
