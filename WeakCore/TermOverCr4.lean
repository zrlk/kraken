import WeakCore.TermOverCr

/-! # TermOverCr4: step-4 facts for the `gd_fund` cover emission (draft)

At a foreign store creating overtaken units at the owner's frontier cell, the store's drop
entries carry the words of `LatestNP` in the storing thread's cut.  The owner's `CrItem` pins
the predecessor of its lowest own promise (`PredAt`).  (F3) The two agree under the per-unit
`F2bW` fact (no promise below the lowest own promise at the unit) and non-overtakenness before
the store (every message above it is skipped).
-/

namespace TermOverCr4
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (F3, memory level) **The latest unskipped word is the lowest skipped promise's
predecessor**: if `tw` is skipped, every later message at `a` is skipped, and no earlier one
is, then `LatestNP`'s word is `PredAt … tw`. -/
theorem predAt_of_latestNP {mem : Memory} {P : List Ts} {a : Address} {tw : Ts} {w : Word}
    (hL : LatestNP mem P a w) (htw : tw ∈ P)
    (hab : ∀ t m, tw < t → mem[t]? = some m → m.loc = a → t ∈ P)
    (hbe : ∀ t m, t < tw → mem[t]? = some m → m.loc = a → t ∉ P) : PredAt mem a tw w := by
  obtain ⟨t, m, htP, hm, hl, hw, hlat⟩ := hL
  have hlt : t < tw := by
    rcases Nat.lt_trichotomy t tw with h | h | h
    · exact h
    · subst h; exact absurd htw htP
    · exact absurd (hab t m h hm hl) htP
  refine ⟨t, m, hlt, hm, hl, hw, fun t' m' h1 h2 hm' hl' => ?_⟩
  exact hbe t' m' h2 hm' hl' (hlat t' m' h1 hm' hl')

#print axioms predAt_of_latestNP

/-- (F3) **Converse direction**: `PredAt … tw` is the `LatestNP` word under the same
hypotheses (so the drop entry's word and the pin coincide either way). -/
theorem latestNP_of_predAt {mem : Memory} {P : List Ts} {a : Address} {tw : Ts} {w : Word}
    (hp : PredAt mem a tw w) (htw : tw ∈ P)
    (hab : ∀ t m, tw < t → mem[t]? = some m → m.loc = a → t ∈ P)
    (hbe : ∀ t m, t < tw → mem[t]? = some m → m.loc = a → t ∉ P) : LatestNP mem P a w := by
  obtain ⟨t0, m, hlt, hm, hl, hw, hn⟩ := hp
  refine ⟨t0, m, hbe t0 m hlt hm hl, hm, hl, hw, fun t' m' h1 hm' hl' => ?_⟩
  rcases Nat.lt_trichotomy t' tw with h | h | h
  · exact absurd hl' (hn t' m' h1 h hm')
  · rw [h]; exact htw
  · exact hab t' m' h hm' hl'

#print axioms latestNP_of_predAt

/-! ## gd_fund skeleton: a drop entry's words give a `CrItem` -/

/-- (gd_fund, memory level) **A credited item from latest-unskipped words**: a piece at `b`
(layout `us`) of the owner's cell containing the unit of `tw` (the unit's lowest own promise),
words `ws` of value resources `R ≤ cr tw`, and at each `K`-unit with a lowest own promise `tw'`
the word is `LatestNP` for a skip list `Pu` containing `tw'`, skipping everything above it and
nothing below it (`LowOwn` minimality and the window guard give the latter). -/
theorem crItem_of_latest {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {tw : Ts} {mh : Msg} {b : Nat} {S : Ty} {us : List Acc} {ws : List Word} {R : Res} {K : Nat → Bool}
    (Pu : Nat → List Ts)
    (hm : s.mem[tw]? = some mh) (hlab : mh.loc.label = l) (hlow : TermPlant.LowOwn s mh.loc tw)
    (hnw : ¬ WordUnit E mh.loc) (hpc : TermPiece.Piece c.ty b S) (hus : accs S = some us)
    (h1 : b ≤ mh.loc.offset) (h2 : mh.loc.offset < b + nWords us)
    (hlen : ws.length = nWords us) (hv : ValOfR E S ws R) (hR : R ≤ cr tw)
    (hlat : ∀ i o w tw', K i = true → InAcc us i o → ws[o]? = some w → TermPlant.LowOwn s ⟨l, b + o⟩ tw' →
      LatestNP s.mem (Pu o) ⟨l, b + o⟩ w ∧ tw' ∈ Pu o ∧
      (∀ t m, tw' < t → s.mem[t]? = some m → m.loc = ⟨l, b + o⟩ → t ∈ Pu o) ∧
      (∀ t m, t < tw' → s.mem[t]? = some m → m.loc = ⟨l, b + o⟩ → t ∉ Pu o)) :
    TermPlant.CrItem E s cr l c (tw, b, S, ws, R, K) := by
  refine ⟨mh, us, hm, hlab, hlow, hnw, hpc.1, hpc.2.1, hus, h1, h2, hlen, hv, hR,
    fun i o w tw' hK hio hw hl => ?_⟩
  obtain ⟨hL, hin, hab, hbe⟩ := hlat i o w tw' hK hio hw hl
  exact predAt_of_latestNP hL hin hab hbe

#print axioms crItem_of_latest

/-- (gd_fund, "nothing below is skipped") **Below the owner's lowest own promise at a unit, no
message is outstanding for anyone**: in particular not in another thread `k`'s skip list
(`k`'s promises and foreign promises, `PromsOK`).  From `LowOwn` minimality (own promises) and
the per-unit, per-event fact `hf` (everyone else's; F2bS at a newly overtaking store). -/
theorem below_unskipped {Eg : GEnv} {c : Cfg} {j k : Nat} {thj thk : TTh}
    {l : AllocLabel} {o : Nat} {tw : Ts} (hP : PromsOK Eg c) (hj : c.ths[j]? = some thj)
    (hk : c.ths[k]? = some thk)
    (hf : ∀ t m, t ∈ Eg.fpOf j → c.mem[t]? = some m → m.loc = ⟨l, o⟩ → tw < t)
    (hlow : TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw) :
    ∀ t m, t < tw → c.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ∉ thk.promises ++ Eg.fpOf k := by
  intro t m hlt hm hl hin
  have hall := (hP k thk hk t).1 hin
  rcases List.mem_append.1 ((hP j thj hj t).2 hall) with h | h
  · exact absurd (hlow.2.2 t m h hm hl) (Nat.not_le.2 hlt)
  · exact absurd (hf t m h hm hl) (Nat.lt_asymm hlt)

#print axioms below_unskipped

/-! ## gd_fund: extending the cover by new items -/

/-- (gd_fund, combination) **The cover extended by new items**: the old items are kept
(`hold`), the new items `Gn` are credited, holders stay distinct, every overtaken unit is
covered by an old item (kept) or a new one, and the access-window fact holds for all. -/
theorem overCr_extend {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {Gs Gn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hnd : ((Gs ++ Gn).map (·.1)).Nodup)
    (hold : ∀ x ∈ Gs, TermOverCr.CrItemQ E s cr l c x) (hnew : ∀ x ∈ Gn, TermOverCr.CrItemQ E s cr l c x)
    (hcov : ∀ o tw, TermOverCr.CovU E c l o → ¬ VisU E ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw → TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ x ∈ Gs ++ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hwa : ∀ x ∈ Gs ++ Gn, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hz : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr t ≠ .zero → t ∈ (Gs ++ Gn).map (·.1))
    (hHL : TermOverCr.HolderLow s l (Gs ++ Gn)) :
    TermOverCr.OverCrE E s cr l c := by
  refine ⟨Gs ++ Gn, ⟨hnd, fun x hx => ?_, hcov, hwa, hz⟩, hHL⟩
  rcases List.mem_append.1 hx with h | h
  · exact hold x h
  · exact hnew x h

#print axioms overCr_extend

/-- (gd_fund, holders) **Distinct units give distinct lowest own promises** (a promise is a
single message): the holders of per-unit items at distinct units are distinct. -/
theorem lowOwn_ne {s : St} {a a2 : Address} {t t2 : Ts} (h : TermPlant.LowOwn s a t)
    (h2 : TermPlant.LowOwn s a2 t2) (hne : a ≠ a2) : t ≠ t2 := by
  intro e
  subst e
  obtain ⟨m, hm, hl⟩ := h.2.1
  obtain ⟨m2, hm2, hl2⟩ := h2.2.1
  rw [hm] at hm2
  cases hm2
  exact hne (hl.symm.trans hl2)

#print axioms lowOwn_ne

/-- (F5) **A new holder is not an old holder**: an old item's holder unit lies in its own `K`
(`OverCrE`'s holder clause), so a unit `o` of `l` that the old item does not cover has a
different lowest own promise. -/
theorem holder_ne {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} {o : Nat} {ty : Ts}
    (hx : TermPlant.CrItem E s cr l c x)
    (hhk : ∀ mh, s.mem[x.1]? = some mh → ∀ usS, accs x.2.2.1 = some usS →
      ∃ i, x.2.2.2.2.2 i = true ∧ InAcc usS i (mh.loc.offset - x.2.1))
    (hnc : ¬ ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true)
    (hy : TermPlant.LowOwn s ⟨l, o⟩ ty) : ty ≠ x.1 := by
  intro e
  obtain ⟨mh, usS, hmh, hlab, -, -, -, -, hus, h1, -⟩ := hx
  obtain ⟨my, hmy, hly⟩ := hy.2.1
  rw [e, hmh] at hmy
  cases hmy
  obtain ⟨i, hK, hin⟩ := hhk _ hmh usS hus
  rw [hly] at h1 hin
  exact hnc ⟨usS, i, hus, h1, hin, hK⟩

#print axioms holder_ne

/-! ## Skip lists agree across cuts at a shared label -/

theorem cutSto_sh {Eg : GEnv} {i : Nat} {l : AllocLabel} (hsh : Eg.Shared l) : cutSto Eg i l = Eg.sto l := by
  cases e : Eg.sto l with
  | none =>
    cases e2 : cutSto Eg i l with
    | none => rfl
    | some c => rw [cutSto_sub e2] at e; cases e
  | some c => exact cutSto_shared e hsh

theorem vis_sh {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {l : AllocLabel} (hsh : Eg.Shared l) :
    Vis (Cut Eg i S) l := fun hp => by
  obtain ⟨f, hf⟩ := hsh
  have : (Cut Eg i S).pfr l = some f := hf
  rw [hp.2] at this; cases this

/-- **At a shared label, every thread's skip list is the same set**: `PromAt` in thread `j`'s
cut and in thread `k`'s cut have the same members (`PromsOK`; the word-unit, predicted-unit
and visibility tests read only global data at a shared label). -/
theorem promAt_sh_iff {Eg : GEnv} {c : Cfg} {j k : Nat} {thj thk : TTh} {Sj Sk : AllocLabel → Prop}
    {l : AllocLabel} {o : Nat} (hP : PromsOK Eg c) (hj : c.ths[j]? = some thj) (hk : c.ths[k]? = some thk)
    (hsh : Eg.Shared l) (t : Ts) :
    t ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, o⟩ ↔
      t ∈ PromAt (Cut Eg k Sk) (stOf c.mem c.pairs thk) ⟨l, o⟩ := by
  have hsj : (Cut Eg j Sj).sto l = Eg.sto l := cutSto_sh hsh
  have hsk : (Cut Eg k Sk).sto l = Eg.sto l := cutSto_sh hsh
  have hWU : WordUnit (Cut Eg j Sj) ⟨l, o⟩ ↔ WordUnit (Cut Eg k Sk) ⟨l, o⟩ := by
    unfold WordUnit; simp only [hsj, hsk]
  have hVU : VisU (Cut Eg j Sj) ⟨l, o⟩ ↔ VisU (Cut Eg k Sk) ⟨l, o⟩ := by
    unfold VisU
    exact ⟨fun h => ⟨hWU.1 h.1, vis_sh hsh⟩, fun h => ⟨hWU.2 h.1, vis_sh hsh⟩⟩
  have hPU : PredU (Cut Eg j Sj) ⟨l, o⟩ ↔ PredU (Cut Eg k Sk) ⟨l, o⟩ := by
    unfold PredU IniW IniWr; simp only [hsj, hsk]; rfl
  have hfj : FpAt (Cut Eg j Sj) ⟨l, o⟩ = Eg.fpOf j := by
    unfold FpAt; simp only [vis_sh hsh, ↓reduceIte]; rfl
  have hfk : FpAt (Cut Eg k Sk) ⟨l, o⟩ = Eg.fpOf k := by
    unfold FpAt; simp only [vis_sh hsh, ↓reduceIte]; rfl
  have hall : t ∈ thj.promises ++ Eg.fpOf j ↔ t ∈ thk.promises ++ Eg.fpOf k :=
    (hP j thj hj t).trans (hP k thk hk t).symm
  by_cases hv : VisU (Cut Eg j Sj) ⟨l, o⟩
  · have hv' := hVU.1 hv
    simp only [PromAt, hv, hv', ↓reduceIte]
  · have hv' : ¬ VisU (Cut Eg k Sk) ⟨l, o⟩ := fun h => hv (hVU.2 h)
    by_cases hq : PredU (Cut Eg j Sj) ⟨l, o⟩
    · have hq' := hPU.1 hq
      simp only [PromAt, hv, hv', hq, hq', ↓reduceIte, hfj, hfk, List.mem_filter]
      exact ⟨fun h => ⟨hall.1 h.1, h.2⟩, fun h => ⟨hall.2 h.1, h.2⟩⟩
    · have hq' : ¬ PredU (Cut Eg k Sk) ⟨l, o⟩ := fun h => hq (hPU.2 h)
      simp only [PromAt, hv, hv', hq, hq', ↓reduceIte, hfj, hfk]
      exact hall

#print axioms promAt_sh_iff

/-! ## PromCrK check: at a non-word unit an `OldCr` credit is zero -/

/-- (OldCr at a non-word unit) **The `OldCr` credit is nothing**: `VRes`/`WRes` credit only a
`WordAt` unit, which is a word unit. -/
theorem oldCr_nword_zero {E : TEnv} {s : St} {m : Msg} {tw : Ts} {R : Res} (hw : ¬ WordUnit E m.loc)
    (h : OldCr E s m tw R) : R = .zero := by
  rcases h with ⟨w, -, hv⟩ | ⟨-, hz⟩
  · rcases hv with ⟨-, -, hW⟩ | ⟨-, hz⟩
    · rcases hW with ⟨n, P, hA, -, -⟩ | ⟨-, hz⟩
      · exact absurd (WordUnit_of_WordAt hA) hw
      · exact hz
    · exact hz
  · exact hz

#print axioms oldCr_nword_zero

/-- (holder side condition) **A nonzero credit at an own non-word promise is a plant credit**
(`PromCrK`): what makes "nonzero credit ⇒ holder" an invariant about δ targets only. -/
theorem plantCr_of_nz {E : TEnv} {s : St} {cr db : Ts → Res} {tw : Ts} {m : Msg}
    (hC : TermPlant.PromCrK E s cr db) (htw : tw ∈ s.promises) (hm : s.mem[tw]? = some m)
    (hw : ¬ WordUnit E m.loc) (hnz : cr tw ≠ .zero) : PlantCr E s m tw (cr tw) := by
  obtain ⟨m', hm', -, hc⟩ := hC tw htw
  rw [hm] at hm'
  cases hm'
  rcases hc with h | h
  · exact absurd (oldCr_nword_zero hw h) hnz
  · exact h.1

#print axioms plantCr_of_nz

/-- (F2bS, the storer's own low promise) **A step of `k` whose coherence at the unit passes a
`k` promise kills it**: with `PromAbove` after the step (certification, `hpa`), no outstanding
`k` promise at the unit lies below a message `k` now has coherence over.  At a store or fulfil
of `k` newly overtaking `u` above `LowOwn_j(u)`, `k`'s coherence at `u` reaches the new
message, so `k` has no outstanding promise below `LowOwn_j(u)` there (a `k` promise fulfilled
by the step itself is at its own index, below `LowOwn`, so it does not overtake). -/
theorem f2bS_self {s' : St} {tk tn : Ts} {m : Msg} (hpa : PromAbove s') (htk : tk ∈ s'.promises)
    (hm : s'.mem[tk]? = some m) (hcoh : tn ≤ s'.vs.coh m.loc) (hlt : tk < tn) : False := by
  exact Nat.lt_irrefl tk (Nat.lt_trans (Nat.lt_of_lt_of_le hlt hcoh) (hpa tk htk m hm))

#print axioms f2bS_self

/-! ## gd_fund: the per-piece item from a drop entry -/

/-- `PromAt` only skips own and foreign promises. -/
theorem promAt_sub {E : TEnv} {s : St} {a : Address} {t : Ts} (h : t ∈ PromAt E s a) :
    t ∈ s.promises ++ E.fp := by
  unfold PromAt at h
  have hF : ∀ t, t ∈ FpAt E a → t ∈ E.fp := fun t ht => by
    unfold FpAt at ht
    by_cases hv : Vis E a.label
    · simp only [hv, ↓reduceIte] at ht; exact ht
    · simp only [hv, ↓reduceIte] at ht; exact absurd ht (List.not_mem_nil (a := t))
  by_cases hv : VisU E a
  · simp only [hv, ↓reduceIte] at h; exact absurd h (List.not_mem_nil (a := t))
  · by_cases hq : PredU E a
    · simp only [hv, hq, ↓reduceIte, List.mem_filter] at h
      rcases List.mem_append.1 h.1 with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (hF t h1)
    · simp only [hv, hq, ↓reduceIte] at h
      rcases List.mem_append.1 h with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (hF t h1)

#print axioms promAt_sub

/-- (gd_fund, per piece) **The owner's credited item from a foreign store's drop entry.**
Thread `k`'s drop entry `g` (OK in `k`'s cut) names a piece of `j`'s shared frontier cell
`l`; the holder `tP` (lowest own promise at its unit, inside the piece, funded `g.R ≤ cr tP`)
and the access units `K` (recorded by `g.L`; at each unit with a lowest own promise `tw'`:
`tw'` and everything above it skipped by `j`, i.e. not overtaken, and no `j`-foreign promise
below it (F2bS)) give a `CrItem` in `j`'s cut. -/
theorem gd_item {Eg : GEnv} {c : Cfg} {j k : Nat} {thj thk : TTh} {Sj Sk : AllocLabel → Prop}
    {cr : Ts → Res} {l : AllocLabel} {cl : Cell} {g : TermPiece.GdE} {tP : Ts} {mh : Msg}
    {us : List Acc} {K : Nat → Bool}
    (hP : PromsOK Eg c) (hj : c.ths[j]? = some thj) (hk : c.ths[k]? = some thk) (hsh : Eg.Shared l)
    (hc : (Cut Eg j Sj).sto l = some cl) (hgl : g.l = l)
    (hg : TermPiece.GdOK (Cut Eg k Sk) (stOf c.mem c.pairs thk) g) (hnr : noOR g.S = true)
    (hus : accs g.S = some us)
    (hm : c.mem[tP]? = some mh) (hlab : mh.loc.label = l)
    (hlow : TermPlant.LowOwn (stOf c.mem c.pairs thj) mh.loc tP)
    (hnw : ¬ WordUnit (Cut Eg j Sj) mh.loc) (h1 : g.b ≤ mh.loc.offset) (h2 : mh.loc.offset < g.b + nWords us)
    (hR : g.R ≤ cr tP)
    (hK : ∀ i o tw', K i = true → InAcc us i o → TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩ tw' →
      g.L o = true ∧ tw' ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩ ∧
      (∀ t m, tw' < t → c.mem[t]? = some m → m.loc = ⟨l, g.b + o⟩ →
        t ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩) ∧
      (∀ t m, t ∈ Eg.fpOf j → c.mem[t]? = some m → m.loc = ⟨l, g.b + o⟩ → tw' < t)) :
    TermPlant.CrItem (Cut Eg j Sj) (stOf c.mem c.pairs thj) cr l cl (tP, g.b, g.S, g.ws, g.R, K) := by
  obtain ⟨c1, hc1, -, -, hpc, hwc, hlat, hv⟩ := hg
  have e1 : (Cut Eg k Sk).sto l = Eg.sto l := cutSto_sh hsh
  have e2 : (Cut Eg j Sj).sto l = Eg.sto l := cutSto_sh hsh
  rw [hgl, e1, ← e2, hc] at hc1
  cases hc1
  have hlen : g.ws.length = nWords us := Option.some.inj (hwc.symm.trans (wc_of_accs hus))
  refine crItem_of_latest (fun o => PromAt (Cut Eg k Sk) (stOf c.mem c.pairs thk) ⟨l, g.b + o⟩)
    hm hlab hlow hnw hpc hus h1 h2 hlen (ValOfR_transferS (InclS_cut Eg k j Sk Sj) hnr hv) hR ?_
  intro i o w tw' hKi hio hw hl
  obtain ⟨hL, hin, hab, hf⟩ := hK i o tw' hKi hio hl
  have hiff := fun t => promAt_sh_iff (o := g.b + o) (Sj := Sj) (Sk := Sk) hP hj hk hsh t
  refine ⟨?_, (hiff tw').1 hin, fun t m a b c' => (hiff t).1 (hab t m a b c'), fun t m a b c' hk' => ?_⟩
  · have := hlat o w hL hw
    rw [hgl] at this
    exact this
  · exact below_unskipped hP hj hk hf hl t m a b c' (promAt_sub hk')

#print axioms gd_item

/-- (PredCov) **`gd_item` with the pin relaxed**: at a `K` unit whose lowest own promise `tw'` is
the first write of a predicted unit (not skipped), the drop entry's word is `tw'`'s own word. -/
theorem gd_itemQ {Eg : GEnv} {c : Cfg} {j k : Nat} {thj thk : TTh} {Sj Sk : AllocLabel → Prop}
    {cr : Ts → Res} {l : AllocLabel} {cl : Cell} {g : TermPiece.GdE} {tP : Ts} {mh : Msg}
    {us : List Acc} {K : Nat → Bool}
    (hP : PromsOK Eg c) (hj : c.ths[j]? = some thj) (hk : c.ths[k]? = some thk) (hsh : Eg.Shared l)
    (hc : (Cut Eg j Sj).sto l = some cl) (hgl : g.l = l)
    (hg : TermPiece.GdOK (Cut Eg k Sk) (stOf c.mem c.pairs thk) g) (hnr : noOR g.S = true)
    (hus : accs g.S = some us)
    (hm : c.mem[tP]? = some mh) (hlab : mh.loc.label = l)
    (hlow : TermPlant.LowOwn (stOf c.mem c.pairs thj) mh.loc tP)
    (hnw : ¬ WordUnit (Cut Eg j Sj) mh.loc) (h1 : g.b ≤ mh.loc.offset) (h2 : mh.loc.offset < g.b + nWords us)
    (hR : g.R ≤ cr tP)
    (hK : ∀ i o tw', K i = true → InAcc us i o → TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩ tw' →
      g.L o = true ∧ (tw' ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩ ∨
        (PredU (Cut Eg j Sj) ⟨l, g.b + o⟩ ∧ FirstW c.mem ⟨l, g.b + o⟩ tw')) ∧
      (∀ t m, tw' < t → c.mem[t]? = some m → m.loc = ⟨l, g.b + o⟩ →
        t ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩) ∧
      (∀ t m, t ∈ Eg.fpOf j → c.mem[t]? = some m → m.loc = ⟨l, g.b + o⟩ → tw' < t)) :
    TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj) cr l cl (tP, g.b, g.S, g.ws, g.R, K) := by
  obtain ⟨c1, hc1, -, -, hpc, hwc, hlat, hv⟩ := hg
  have e1 : (Cut Eg k Sk).sto l = Eg.sto l := cutSto_sh hsh
  have e2 : (Cut Eg j Sj).sto l = Eg.sto l := cutSto_sh hsh
  rw [hgl, e1, ← e2, hc] at hc1
  cases hc1
  have hlen : g.ws.length = nWords us := Option.some.inj (hwc.symm.trans (wc_of_accs hus))
  refine ⟨mh, us, hm, hlab, hlow, hnw, hpc.1, hpc.2.1, hus, h1, h2, hlen,
    ValOfR_transferS (InclS_cut Eg k j Sk Sj) hnr hv, hR, fun i o w tw' hKi hio hw hl => ?_⟩
  obtain ⟨hL, hin, hab, hf⟩ := hK i o tw' hKi hio hl
  have hiff := fun t => promAt_sh_iff (o := g.b + o) (Sj := Sj) (Sk := Sk) hP hj hk hsh t
  have hLat : LatestNP c.mem (PromAt (Cut Eg k Sk) (stOf c.mem c.pairs thk) ⟨l, g.b + o⟩) ⟨l, g.b + o⟩ w := by
    have := hlat o w hL hw
    rw [hgl] at this
    exact this
  have habk : ∀ t m, tw' < t → c.mem[t]? = some m → m.loc = ⟨l, g.b + o⟩ →
      t ∈ PromAt (Cut Eg k Sk) (stOf c.mem c.pairs thk) ⟨l, g.b + o⟩ :=
    fun t m a b c' => (hiff t).1 (hab t m a b c')
  rcases hin with hin | ⟨hpu, hfw⟩
  · refine .inl (predAt_of_latestNP hLat ((hiff tw').1 hin) habk fun t m a b c' hk' => ?_)
    exact below_unskipped hP hj hk hf hl t m a b c' (promAt_sub hk')
  · refine .inr ⟨hpu, hfw, ?_⟩
    obtain ⟨⟨m0, hm0, hl0, -⟩, -⟩ := id hfw
    have hnot : tw' ∉ PromAt (Cut Eg k Sk) (stOf c.mem c.pairs thk) ⟨l, g.b + o⟩ := fun h => by
      have h' := (hiff tw').2 h
      unfold PromAt at h'
      by_cases hvu : VisU (Cut Eg j Sj) ⟨l, g.b + o⟩
      · simp only [hvu, ↓reduceIte] at h'
        exact absurd h' (List.not_mem_nil (a := tw'))
      · simp only [hvu, hpu, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at h'
        obtain ⟨h0, hf0, hlt⟩ := h'.2
        have e := FirstW_uniq hf0 hfw
        subst e
        exact Nat.lt_irrefl _ hlt
    exact ⟨m0, hm0, LatestNP_uniq ⟨tw', m0, hnot, hm0, hl0, rfl, habk⟩ hLat⟩

#print axioms gd_itemQ

/-! ## (b) A whole-piece store overtakes every owned unit of the piece -/

/-- (b) **A store writing every unit of a piece overtakes each unit with an own promise**:
the store's message at the unit lies above the old memory (so above the lowest own promise)
and is neither an own promise nor a foreign one of the owner's post cut. -/
theorem piece_newOver {E' : TEnv} {s s' : St} {l : AllocLabel} {b n : Nat}
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size) (hpr : s'.promises = s.promises)
    (hw : ∀ o, o < n → ∃ t m, s.mem.size ≤ t ∧ s'.mem[t]? = some m ∧ m.loc = ⟨l, b + o⟩ ∧ t ∉ E'.fp) :
    ∀ o tw, o < n → TermPlant.LowOwn s ⟨l, b + o⟩ tw → TermPlant.OverT E' s' ⟨l, b + o⟩ tw := by
  intro o tw ho hl
  obtain ⟨t, m, ht, hm, hloc, hnf⟩ := hw o ho
  have hlt : tw < t := Nat.lt_of_lt_of_le (hP tw hl.1) ht
  refine ⟨t, m, hlt, hm, hloc, fun hin => ?_⟩
  rcases List.mem_append.1 (promAt_sub hin) with h1 | h1
  · rw [hpr] at h1
    exact absurd (hP t h1) (Nat.not_lt.2 ht)
  · exact hnf h1

#print axioms piece_newOver

end TermOverCr4
