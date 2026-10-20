import WeakCore.TermOverCrPoolG

/-! # TermOverCrRepin: the δ-funded re-pinned drop items (hWbR B2)

At an hWbR unit (a footprint promise `t ≤ tw` lost, ¬ pre-`WinG`) the drop item's word is the
stepper's pre-state `LatestNP`, which skips `t`: the wrong pin.  B2: when the post word keeps the
resources (same region / holding: the named `ValOfR` premise), the drop item is **re-pinned** — same
holder `tw`, piece and resources `R` (so still funded by `δ = plantD1`), words `W y` carrying the memory's
`PredAt` word at the new units `K y` — and covers the unit in the post cover.

* `rpOf`, `crItemQ_repin`: the re-pinned item is a credited item, given the `PredAt` words at the new units
  and the old words at the drop's own units.
* `predAt_lost`: at an hWbR unit the memory's `PredAt` word below `tw` exists (the lost `t` is below `tw`).
* `foreign_overCrPZOR`: `foreign_overCrPZOG` with the drop list re-pinned and a fourth cover disjunct.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (B2) The re-pinned item: holder, offset, piece and resources of `y`, words `W y`, units `K y`. -/
def rpOf (W : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → List Word) (K : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → Nat → Bool)
    (y : (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :=
  (y.1, y.2.1, y.2.2.1, W y, y.2.2.2.2.1, K y)

/-- (B2) **A re-pinned credited item is credited**: the new words keep the length and the resources
(`hV`, the same-region / same-holding premise), and at every unit of `K'` each word is either the old
one at an old unit, or the memory's `PredAt` word below the unit's lowest own promise. -/
theorem crItemQ_repin {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : (Ts × Nat × Ty × List Word × Res × (Nat → Bool))} {W' : List Word} {K' : Nat → Bool}
    (h : TermOverCr.CrItemQ E s cr l c x) (hlen : W'.length = x.2.2.2.1.length)
    (hV : ValOfR E x.2.2.1 W' x.2.2.2.2.1)
    (hP : ∀ usS, accs x.2.2.1 = some usS → ∀ i o w tw', K' i = true → InAcc usS i o → W'[o]? = some w →
      TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ tw' →
      (x.2.2.2.2.2 i = true ∧ W'[o]? = x.2.2.2.1[o]?) ∨ PredAt s.mem ⟨l, x.2.1 + o⟩ tw' w) :
    TermOverCr.CrItemQ E s cr l c (x.1, x.2.1, x.2.2.1, W', x.2.2.2.2.1, K') := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -, a12, hq⟩ := h
  refine ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, hlen.trans a10, hV, a12,
    fun i o w tw' hK hio hw hlo => ?_⟩
  rcases hP usS a7 i o w tw' hK hio hw hlo with ⟨hk, he⟩ | hp
  · exact hq i o w tw' hk hio (he ▸ hw) hlo
  · exact .inl hp

/-- (B2) At a unit losing a footprint message `t` below `tw`, the memory's `PredAt` word below `tw`
exists (the latest message below `tw` at the unit; `predAt_above`). -/
theorem predAt_lost {mem : Memory} {a : Address} {tw t : Ts} {m : Msg} (hlt : t < tw) (hm : mem[t]? = some m)
    (hloc : m.loc = a) : ∃ t1 m1, t ≤ t1 ∧ t1 < tw ∧ mem[t1]? = some m1 ∧ m1.loc = a ∧ PredAt mem a tw (mw m1) := by
  obtain ⟨t1, m1, h1, hp, h2, h3, h4⟩ := predAt_above (tw - t) t m rfl hlt hm hloc
  exact ⟨t1, m1, h1, h2, h3, h4, hp⟩

/-- (hWbR B2) `foreign_overCrPZOG` with the drop items **re-pinned**: the new items are
`rpOf W K y` for the drop items `y` (same holder, piece and resources, words `W y`, units `K y ⊇` the
drop's own), so a re-pinned item's `K` bit may cover a unit (`hWbO`, `hent`); the resources stay
`δ`-funded (`plantD1`). -/
theorem foreign_overCrPZOR {E E' : TEnv} {s s' : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    {Fz Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    {W : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → List Word} {K : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → Nat → Bool}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto0 : E.sto l = some c) (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hrc : E'.rc l ≤ E.rc l) (hini : E'.ini l ≤ E.ini l) (hpf : E.pfr l ≠ none)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hnu : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.val ≠ .undef)
    (hWbO : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw ∨
      (∃ x ∈ Fz, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∨
      (∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∨
      ∃ y ∈ dnOf l tg (kfOf E s l) Gd, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧
        InAcc usS i (o - y.2.1) ∧ K y i = true)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hL : TermOverCr.OverCrL E s cr l c (TermOverCr.WinG E s l) Gs) (hHL : TermOverCr.HolderLow s l Gs)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    (hT : ∀ g ∈ Gd, ∀ t, tg g = some t → ∃ m us, s'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ s'.promises → s'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece c.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, ∀ t, tg g = some t → t ∈ s.promises)
    (hTl : ∀ g ∈ Gd, ∀ t, tg g = some t → g.l = l)
    (hD : ∀ y ∈ dnOf l tg (kfOf E s l) Gd,
      TermOverCr.CrItemQ E s (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c (rpOf W K y))
    (hwaD : ∀ y ∈ dnOf l tg (kfOf E s l) Gd, ∀ usS i o, accs y.2.2.1 = some usS → K y i = true →
      InAcc usS i o → ∃ t0, TermPlant.LowOwn s ⟨l, y.2.1 + o⟩ t0)
    (hKm : ∀ y ∈ dnOf l tg (kfOf E s l) Gd, ∀ i, y.2.2.2.2.2 i = true → K y i = true)
    (hFi : ∀ x ∈ Fz, TermOverCr.CrItemQ E s (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c x)
    (hFR : ∀ x ∈ Fz, x.2.2.2.2.1 = .zero)
    (hFwa : ∀ x ∈ Fz, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hFHL : TermOverCr.HolderLow s l Fz)
    (hent : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ((∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) ∧
        TermOverCr.WinG E s l o tw) ∨
      (∃ x ∈ Fz, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∨
      (∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∨
      ∃ y ∈ dnOf l tg (kfOf E s l) Gd, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧
        InAcc usS i (o - y.2.1) ∧ K y i = true) :
    TermOverCr.OverCrE E' s' (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c := by
  have hpm : ∀ g ∈ Gd, ∀ t m, tg g = some t → s'.mem[t]? = some m → s.mem[t]? = some m := by
    intro g hg t m ht hm
    rw [← hpre t (hP t (hTp g hg t ht))]
    exact hm
  have hinj := tg_inj (E := E) (s := s) (tg := tg) (Gd := Gd) (fun g hg t ht => by
    obtain ⟨m, us, hm, hml, -, hpc, hus, h1, h2⟩ := hT g hg t ht
    exact ⟨m, us, c, hpm g hg t m ht hm, hml, by rw [hTl g hg t ht]; exact hsto0, hpc, hus, h1, h2⟩) hnd
  have hlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → s.mem[t]? = some m → m.loc.label = g.l := by
    intro g hg t m ht hm
    obtain ⟨m', us, hm', hml, -⟩ := hT g hg t ht
    rw [hpm g hg t m' ht hm'] at hm
    cases hm
    exact hml
  obtain ⟨hDR, hDnd, hδD⟩ := dnOf_facts (s := s) (l := l) (Kf := kfOf E s l) hinj hlab hnd
  have hHLD : TermOverCr.HolderLow s l (dnOf l tg (kfOf E s l) Gd) := by
    refine holderLow_dnOfL (fun g hg hgl t ht us hus => ?_)
    obtain ⟨m, us1, hm, hml, hpl, hpc, hus1, h1, h2⟩ := hT g hg t ht
    rw [hus] at hus1
    cases hus1
    intro t' m' ht' hm' hl' h1' h2'
    exact hpl t' m' (by rw [hpr]; exact ht') (by rw [hpre t' (hP t' ht')]; exact hm') (by rw [hl', hml, hgl])
      h1' h2'
  -- the re-pinned items keep holders, pieces and resources
  have hDR' : ∀ y ∈ (dnOf l tg (kfOf E s l) Gd).map (rpOf W K),
      y.2.2.2.2.1 ≤ TermPlant.plantD1 Gd TermPiece.GdE.R tg y.1 := by
    intro y hy
    obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 hy
    exact hDR y0 hy0
  have hmap1 : ((dnOf l tg (kfOf E s l) Gd).map (rpOf W K)).map (·.1) = (dnOf l tg (kfOf E s l) Gd).map (·.1) := by
    rw [List.map_map]
    rfl
  have hHLD' : TermOverCr.HolderLow s l ((dnOf l tg (kfOf E s l) Gd).map (rpOf W K)) := by
    intro y hy
    obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 hy
    exact hHLD y0 hy0
  have hRP : ∀ o, (∃ y ∈ dnOf l tg (kfOf E s l) Gd, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧
        InAcc usS i (o - y.2.1) ∧ K y i = true) →
      ∃ x ∈ (dnOf l tg (kfOf E s l) Gd).map (rpOf W K) ++ Fz, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
        InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true :=
    fun o ⟨y, hy, usS, i, h1, h2, h3, h4⟩ =>
      ⟨rpOf W K y, List.mem_append_left _ (List.mem_map_of_mem hy), usS, i, h1, h2, h3, h4⟩
  refine overCr_foreignMOG (Dn := (dnOf l tg (kfOf E s l) Gd).map (rpOf W K) ++ Fz) hpre hpr hP hsto hV
    (covU_back hsto0 hsto hpf hini hrc) hVU hPU
    (fun o tw hi hv hl hg hov hold => (hWbO o tw hi hv hl hg hov hold).imp id (fun h2 => by
      rcases h2 with ⟨x, hx, hr⟩ | hgs | hrp
      · exact .inl ⟨x, List.mem_append_right _ hx, hr⟩
      · exact .inr hgs
      · exact .inl (hRP o hrp))) hcpl hni hL hHL
    (fun y hy => (List.mem_append.1 hy).elim (fun h1 => by
      obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 h1
      exact hD y0 hy0) (hFi y)) (fun t => ?_)
    (fun y hy => (List.mem_append.1 hy).elim (fun h1 => by
      obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 h1
      exact hwaD y0 hy0) (hFwa y))
    (fun y hy => (List.mem_append.1 hy).elim (fun h1 => hHLD' y h1) (fun h1 => hFHL y h1))
    (fun o tw hI hv hl hw hov => ?_)
    (fun t m ht hm hl hnz => List.map_append ▸ List.mem_append_left _ (hmap1 ▸ hδD t m hm hl hnz))
  · rw [sumH_append, sumH_zero hFR, Res.add_zero]
    exact sumH_le_of_nodup (hmap1 ▸ hDnd) hDR' t
  · by_cases hold : TermPlant.OverT E s ⟨l, o⟩ tw
    · exact .inl hold
    · right
      rcases hent o tw hI hv hl hw hov hold with ⟨hg, hw0⟩ | ⟨x, hx, hr⟩ | hgs | hrp
      · obtain ⟨y, hy, usS, i, h1, h2, h3, h4⟩ := hcovD_unitO hVU hnu hv hl hw0 hold hg
        exact .inl ⟨rpOf W K y, List.mem_append_left _ (List.mem_map_of_mem hy), usS, i, h1, h2, h3,
          hKm y hy i h4⟩
      · exact .inl ⟨x, List.mem_append_right _ hx, hr⟩
      · exact .inr hgs
      · exact .inl (hRP o hrp)

end TermOverCrW

#print axioms TermOverCrW.crItemQ_repin
#print axioms TermOverCrW.predAt_lost
#print axioms TermOverCrW.foreign_overCrPZOR
