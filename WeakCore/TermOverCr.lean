import WeakCore.TermPlantOpG
import WeakCore.TermOverCrDefs

/-! # TermOverCr: the overtaken-unit credit invariant (plantOpG discharge, draft)

`OverCrE E s cr l c`: at the own frontier cell `l`, a duplicate-free list of credited items
(`TermPlant.CrItem`, per item) covers every overtaken unit of the real count,
whatever its lowest own promise (no window bound).  `PlantOpG`'s `CoverAt` at any `wB` is its
restriction (`coverAt_of_overCr`).  The invariant (`OverCrG`, per thread and own frontier cell)
is to be maintained at the plant (nothing overtaken), foreign stores (`gd_fund`), and the
owner's fulfils (2a re-key).
-/

namespace TermOverCr
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- Word counts of prefixes are bounded by the whole. -/
theorem nWords_take_le (us : List Acc) (k : Nat) : nWords (us.take k) ≤ nWords us := by
  have e := congrArg nWords (List.take_append_drop k us)
  rw [TermSound.nWords_append] at e
  omega

/-- The first write survives memory growth keeping the prefix. -/
theorem firstW_pre {M M' : Memory} {a : Address} {h : Ts} (hpre : ∀ t, t < M.size → M'[t]? = M[t]?)
    (hf : FirstW M a h) : FirstW M' a h := by
  obtain ⟨⟨m, hm, hl, hv⟩, hb⟩ := hf
  have hh := lt_of_get hm
  exact ⟨⟨m, by rw [hpre h hh]; exact hm, hl, hv⟩, fun t m' hlt hm' hl' =>
    hb t m' hlt (by rw [← hpre t (Nat.lt_trans hlt hh)]; exact hm') hl'⟩

/-- **The predicted-unit pin disjunct is kept** along memory growth keeping the prefix and the
predicted units. -/
theorem pinQ_pre {E E' : TEnv} {M M' : Memory} {a : Address} {tw : Ts} {w : Word}
    (hpre : ∀ t, t < M.size → M'[t]? = M[t]?) (hPU : PredU E a → PredU E' a)
    (h : PredU E a ∧ FirstW M a tw ∧ ∃ m, M[tw]? = some m ∧ mw m = w) :
    PredU E' a ∧ FirstW M' a tw ∧ ∃ m, M'[tw]? = some m ∧ mw m = w := by
  obtain ⟨hp, hf, m, hm, hw⟩ := h
  exact ⟨hPU hp, firstW_pre hpre hf, m, by rw [hpre tw (lt_of_get hm)]; exact hm, hw⟩

/-- **A solid component of a buffer lies in one slot.** -/
theorem piece_slot {N : Nat} {e S : Ty} {b : Nat} {us vs : List Acc} (h : AtOff (.array (.lit N) e) b S)
    (hS : Solid S) (hus : accs e = some us) (hvs : accs S = some vs) :
    ∃ j, j * nWords us ≤ b ∧ b + nWords vs ≤ (j + 1) * nWords us := by
  cases h with
  | here _ => exact absurd rfl (hS.2.1 _ _)
  | @elem _ _ _ j o us' hus' _ hat =>
      rw [hus] at hus'
      cases hus'
      have hb := AtOff_bound hat hus hvs
      exact ⟨j, by omega, by rw [Nat.succ_mul]; omega⟩
  | fold _ _ _ _ => exact absurd (cl_mu_eq _ _ _) (hS.2.2 _)

/-- **No word of a piece meeting a real-count unit is predicted.** -/
theorem not_predU_piece {E : TEnv} {c : Cell} {l : AllocLabel} {b o o' : Nat} {S : Ty} {vs : List Acc}
    (hsto : E.sto l = some c) (hat : AtOff c.ty b S) (hS : Solid S) (hvs : accs S = some vs)
    (h1 : b ≤ o) (h2' : o' < b + nWords vs)
    (hI : InitRr E c l o) : ¬ PredU E ⟨l, o'⟩ := by
  intro hp
  apply hp.2.2
  intro c1 N e us hc1 hty hus
  have e1 : c1 = c := Option.some.inj (hc1.symm.trans hsto)
  subst e1
  have hlt := hI N e us hty hus
  rw [hty] at hat
  obtain ⟨j, hj1, hj2⟩ := piece_slot hat hS hus hvs
  have hj : j < E.rc l := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt (Nat.le_trans hj1 h1) hlt)
  have := Nat.mul_le_mul_right (nWords us) (show j + 1 ≤ E.rc l from hj)
  show o' < E.rc l * nWords us
  omega

open Classical in
/-- The unit mask restricted to items with no predicted word. -/
noncomputable def kQ (E : TEnv) (l : AllocLabel) (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :
    Nat → Bool :=
  if ∃ usS o', accs x.2.2.1 = some usS ∧ x.2.1 ≤ o' ∧ o' < x.2.1 + nWords usS ∧ PredU E ⟨l, o'⟩ then
    fun _ => false else x.2.2.2.2.2

/-- The item with its mask restricted. -/
noncomputable def xQ (E : TEnv) (l : AllocLabel) (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :
    Ts × Nat × Ty × List Word × Res × (Nat → Bool) :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, kQ E l x)

/-- **A predicted-unit item, restricted, is a plain credited item.** -/
theorem crItem_of_Q {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (h : CrItemQ E s cr l c x) :
    TermPlant.CrItem E s cr l c (xQ E l x) := by
  classical
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hp⟩ := h
  refine ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, fun i o w tw' hk hi hw hl => ?_⟩
  by_cases hc : ∃ usS o', accs x.2.2.1 = some usS ∧ x.2.1 ≤ o' ∧ o' < x.2.1 + nWords usS ∧ PredU E ⟨l, o'⟩
  · have hk' : kQ E l x i = true := hk
    unfold kQ at hk'
    simp only [hc, ↓reduceIte] at hk'
    exact absurd hk' (by simp)
  · have hk' : kQ E l x i = true := hk
    unfold kQ at hk'
    simp only [hc, ↓reduceIte] at hk'
    rcases hp i o w tw' hk' hi hw hl with h0 | ⟨hpu, -⟩
    · exact h0
    · have ho : o < nWords usS := Nat.lt_of_lt_of_le hi.2 (nWords_take_le usS (i + 1))
      exact absurd ⟨usS, x.2.1 + o, a7, Nat.le_add_right _ _, by omega, hpu⟩ hc

#print axioms crItem_of_Q

/-- At an item meeting a real-count unit the restriction keeps the mask. -/
theorem kQ_eq {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hsto : E.sto l = some c) (h : CrItemQ E s cr l c x)
    {usS : List Acc} {o : Nat} (hus : accs x.2.2.1 = some usS) (h1 : x.2.1 ≤ o)
    (hI : InitRr E c l o) : kQ E l x = x.2.2.2.2.2 := by
  classical
  obtain ⟨-, -, -, -, -, -, hat, hS, -⟩ := h
  have hc : ¬ ∃ usS o', accs x.2.2.1 = some usS ∧ x.2.1 ≤ o' ∧ o' < x.2.1 + nWords usS ∧ PredU E ⟨l, o'⟩ := by
    rintro ⟨us2, o', hus2, h1', h2', hp⟩
    rw [hus] at hus2
    cases hus2
    exact not_predU_piece hsto hat hS hus h1 h2' hI hp
  unfold kQ
  simp only [hc, ↓reduceIte]

/-- The window-free cover restricts to `CoverAt` at any window bound (items restricted to
those with no predicted word, `xQ`). -/
theorem coverAt_of_overCr {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    (hsto : E.sto l = some c) (h : OverCrE E s cr l c) {wB : Ts} (hW : WinGL E s l wB) :
    TermPlantOpG.CoverAt s E cr l c wB := by
  obtain ⟨Gs, ⟨hnd, hit, hcov, -, -⟩, -⟩ := h
  refine ⟨Gs.map (xQ E l), ?_, fun y hy => ?_, fun o tw hi hv hl hle hov => ?_⟩
  · rw [List.map_map]
    exact hnd
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact crItem_of_Q (hit x hx)
  · obtain ⟨x, hx, usS, i, hus, h1, hio, hk⟩ := hcov o tw (.inl hi) hv hl (winG_of_L (winGL_mono hW hle) o) hov
    refine ⟨xQ E l x, List.mem_map.2 ⟨x, hx, rfl⟩, usS, i, hus, h1, hio, ?_⟩
    show kQ E l x i = true
    rw [kQ_eq hsto (hit x hx) hus h1 hi]
    exact hk

#print axioms coverAt_of_overCr

/-- **The cover part of `PlantOp` (`PlantOpG`) from the pool clause** `OverCrG` at the credits
plus the pool credits `cr + pl` (R4). -/
theorem plantOpG_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} :
    TermPlantOpG.PlantOpG p k arch Sp Init MintOK c0 (fun c Eg cr pl => OverCrG Eg c (fun j t => cr j t + pl j t)) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs pl X Y hq _ lab cl hsto hown hpf _ wB hAo hB _
  have hCE : CE η = Cut Eg i S := Y.1
  rw [hCE] at hsto hpf hB ⊢
  rw [hCE] at hown
  exact coverAt_of_overCr hsto (hq i th S X.hth lab cl hsto (by rw [hown]; rfl) hpf) ⟨hAo, hB⟩

#print axioms plantOpG_of

/-! ## Step 1: no promises -/

/-- With no own promises nothing is overtaken (`LowOwn` needs a promise): the empty cover. -/
theorem overCr_noProm {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    (h : s.promises = []) : OverCrE E s cr l c := by
  refine ⟨[], ⟨List.nodup_nil, fun x hx => absurd hx (List.not_mem_nil (a := x)), fun o tw _ _ hl _ _ => ?_,
    fun x hx => absurd hx (List.not_mem_nil (a := x)),
    fun t m ht => by rw [h] at ht; exact absurd ht (List.not_mem_nil (a := t))⟩,
    fun x hx => absurd hx (List.not_mem_nil (a := x))⟩
  have h1 := hl.1
  rw [h] at h1
  exact absurd h1 (List.not_mem_nil (a := tw))

#print axioms overCr_noProm

/-- (init) **The system clause at a promise-free configuration.** -/
theorem overCrG_noProm {Eg : GEnv} {c : Cfg} {cr : Nat → Ts → Res} (h : AllNoProm c) : OverCrG Eg c cr :=
  fun i th _ hth _ _ _ _ _ => overCr_noProm (h i th hth)

#print axioms overCrG_noProm

/-! ## Steps 2-3: the frame (memory prefix kept, promises only added at the top) -/

section frame
variable {s s' : St}
  (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
  (hpr : ∀ t, t ∈ s.promises → t ∈ s'.promises)
  (hnew : ∀ t, t ∈ s'.promises → t ∉ s.promises → s.mem.size ≤ t)
  (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
include hpre hpr hnew hP

/-- An old lowest own promise stays lowest (new promises lie above the old memory). -/
theorem lowOwn_fwd {a : Address} {tw : Ts} (h : TermPlant.LowOwn s a tw) : TermPlant.LowOwn s' a tw := by
  obtain ⟨h1, ⟨m, hm, hl⟩, h3⟩ := h
  refine ⟨hpr tw h1, ⟨m, by rw [hpre tw (hP tw h1)]; exact hm, hl⟩, fun t' m' ht' hm' hl' => ?_⟩
  by_cases hin : t' ∈ s.promises
  · exact h3 t' m' hin (by rw [← hpre t' (hP t' hin)]; exact hm') hl'
  · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (hP tw h1) (hnew t' ht' hin))

omit hnew in
/-- A lowest own promise after that is an old promise was lowest before. -/
theorem lowOwn_back {a : Address} {tw : Ts} (h : TermPlant.LowOwn s' a tw) (hin : tw ∈ s.promises) :
    TermPlant.LowOwn s a tw := by
  obtain ⟨-, ⟨m, hm, hl⟩, h3⟩ := h
  refine ⟨hin, ⟨m, by rw [← hpre tw (hP tw hin)]; exact hm, hl⟩, fun t' m' ht' hm' hl' => ?_⟩
  exact h3 t' m' (hpr t' ht') (by rw [hpre t' (hP t' ht')]; exact hm') hl'

omit hpre hpr hnew hP in
/-- **Predicted units stay predicted** along a step keeping the cell, its frontier, and not
lowering `ini` nor raising `rc` at `l`. -/
theorem predU_mono_of {E E' : TEnv} {l : AllocLabel}
    (hsto : E'.sto l = E.sto l) (hpf : E.pfr l ≠ none → E'.pfr l ≠ none)
    (hini : E.ini l ≤ E'.ini l) (hrc : E'.rc l ≤ E.rc l) :
    ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩ := by
  intro o ⟨h1, h2, h3⟩
  refine ⟨hpf h1, fun c N e us hc ht ha => ?_, fun hw => h3 fun c N e us hc ht ha => ?_⟩
  · exact Nat.lt_of_lt_of_le (h2 c N e us (by rw [← hsto]; exact hc) ht ha) (Nat.mul_le_mul_right _ hini)
  · exact Nat.lt_of_lt_of_le (hw c N e us (by rw [hsto]; exact hc) ht ha) (Nat.mul_le_mul_right _ hrc)

/-- **A credited item is kept**, given its access-window fact (`WinA`). -/
theorem crItem_frame {E E' : TEnv} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hcr : ∀ t, t ∈ s.promises → cr t ≤ cr' t)
    (hwa : ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (h : CrItemQ E s cr l c x) : CrItemQ E' s' cr' l c x := by
  obtain ⟨mh, usS, hmh, hlab, hlo, hnw, hat, hsol, husS, hq1, hq2, hwl, hvr, hR, hpin⟩ := h
  refine ⟨mh, usS, by rw [hpre _ (hP _ hlo.1)]; exact hmh, hlab, lowOwn_fwd hpre hpr hnew hP hlo,
    fun hw => hnw ?_, hat, hsol, husS, hq1, hq2, hwl, hV _ _ _ hvr,
    Res.le_trans hR (hcr _ hlo.1), fun i o w tw' hk hi hw hl => ?_⟩
  · obtain ⟨c1, hc1, hor⟩ := hw
    exact ⟨c1, by rw [hlab, ← hsto, ← hlab]; exact hc1, hor⟩
  · obtain ⟨t0, h0⟩ := hwa usS i o husS hk hi
    have e : tw' = t0 := TermPlant.LowOwn_uniq hl (lowOwn_fwd hpre hpr hnew hP h0)
    subst e
    exact (hpin i o w tw' hk hi hw h0).imp (TermPlant.PredAt_mono (hP _ h0.1) hpre)
      (pinQ_pre hpre (hPU _))

#print axioms crItem_frame

/-- **The credited cover is kept** along a step that keeps memory's prefix, only adds
promises (above the old memory, with no message at `l` above a new one: `hTop`), keeps the
cell's typing and values' resources, does not lower credits, adds no real-count unit, and
newly overtakes no unit at an old lowest promise (`hO`).  Covers a promise step (the new
promise is the top message) and a step changing nothing at `l`. -/
theorem overCr_frame {E E' : TEnv} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell}
    (hTop : ∀ t, t ∈ s'.promises → t ∉ s.promises → ∀ t' m, t < t' → s'.mem[t']? = some m →
      m.loc.label ≠ l)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hcr : ∀ t, t ∈ s.promises → cr t ≤ cr' t)
    (hI : ∀ o, CovU E' c l o → CovU E c l o)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hG : ∀ o tw, WinG E' s' l o tw → WinG E s l o tw)
    (hO : ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      TermPlant.OverT E s ⟨l, o⟩ tw)
    (hcr0 : ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr' t ≠ .zero → t ∈ s.promises ∧ cr t ≠ .zero)
    (h : OverCrE E s cr l c) : OverCrE E' s' cr' l c := by
  obtain ⟨Gs, ⟨hnd, hit, hcov, hwa, hz⟩, hHL⟩ := h
  have hHL' : HolderLow s' l Gs := holderLow_tr (fun t m _ hin hm => by rw [← hpre t (hP t hin)]; exact hm)
    (fun t ht hin x hx => by
      obtain ⟨_mh0, _us0, _hm0, _hl0, hlo0, _⟩ := hit x hx
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le (hP _ hlo0.1) (hnew t ht hin))) hHL
  refine ⟨Gs, ⟨hnd, fun x hx => crItem_frame hpre hpr hnew hP hsto hV hcr (hwa x hx) hPU (hit x hx),
    fun o tw hi hv hl hg hov => ?_, fun x hx usS i o h1 h2 h3 => ?_,
    fun t m ht hm hl hw hnz => ?_⟩, hHL'⟩
  · by_cases hin : tw ∈ s.promises
    · have hl0 := lowOwn_back hpre hpr hP hl hin
      exact hcov o tw (hI o hi) (hVU o hv) hl0 (hG o tw hg) (hO o tw hl0 hov)
    · obtain ⟨t', m, hlt, hm, hloc, -⟩ := hov
      exact absurd (by rw [hloc]) (hTop tw hl.1 hin t' m hlt hm)
  · obtain ⟨t0, h0⟩ := hwa x hx usS i o h1 h2 h3
    exact ⟨t0, lowOwn_fwd hpre hpr hnew hP h0⟩
  · have hw0 : ¬ WordUnit E m.loc := fun hw0 => hw (by
      obtain ⟨c1, hc1, hor⟩ := hw0
      exact ⟨c1, by rw [hl, hsto, ← hl]; exact hc1, hor⟩)
    obtain ⟨hin, hnz0⟩ := hcr0 t m ht hm hl hw0 hnz
    exact hz t m hin (by rw [← hpre t (hP t hin)]; exact hm) hl hw0 hnz0

#print axioms overCr_frame

end frame

/-! ## Step 4a: a funded plant credit inside its window is a credited item -/

/-- **A funded plant credit gives a `CrItem`** (components explicit): the credit's piece is a
piece of the cell's type, `tw` is the unit's lowest own promise, and at every unit `K` selects
the lowest own promise lies in the credit window (so `winL`'s lowest is the real lowest). -/
theorem item_of_plantCr {E : TEnv} {s : St} {cr : Ts → Res} {m : Msg} {tw : Ts} {R : Res} {c : Cell}
    {sb b0 wb : Nat} {S0 S : Ty} {us : List Acc} {K : Nat → Bool} {ws : List Word} {R0 : Res}
    (hm : s.mem[tw]? = some m) (hseg : SegOf c.ty sb S0)
    (hat : AtOff S0 b0 S) (hS : Solid S) (hnw : ¬ WordUnit E m.loc) (hus : accs S = some us)
    (hn : 0 < nWords us) (h1 : sb + b0 ≤ m.loc.offset) (h2 : m.loc.offset < sb + b0 + nWords us)
    (hlen : ws.length = nWords us) (hv : ValOfR E S ws R0) (hR0 : R0 ≤ R)
    (hpin : PinW s.mem (winL wb s.promises) m.loc.label (sb + b0) us K ws)
    (hlow : TermPlant.LowOwn s m.loc tw) (hcr : R ≤ cr tw)
    (hW : ∀ i o tw', K i = true → InAcc us i o → TermPlant.LowOwn s ⟨m.loc.label, sb + b0 + o⟩ tw' → tw' ≤ wb) :
    TermPlant.CrItem E s cr m.loc.label c (tw, sb + b0, S, ws, R0, K) := by
  refine ⟨m, us, hm, rfl, hlow, hnw, (TermPlant.plant_piece hseg hat hS (wc_of_accs hus) hn).1, hS, hus,
    h1, h2, hlen, hv, Res.le_trans hR0 hcr, fun i o w tw' hK hio hw hl => ?_⟩
  have hle := hW i o tw' hK hio hl
  obtain ⟨hp, hmsg, hmin⟩ := hl
  refine hpin i o w tw' hK hio hw ⟨List.mem_filter.2 ⟨hp, decide_eq_true hle⟩, hmsg, fun t' ht' hm' => ?_⟩
  obtain ⟨m', hm'1, hm'2⟩ := hm'
  exact hmin t' m' (List.mem_filter.1 ht').1 hm'1 hm'2

#print axioms item_of_plantCr

/-- **A plant credit with all `K`-units' lowest own promises inside any admissible window
is a credited item, or zero.** -/
theorem item_of_plantCr_ex {E : TEnv} {s : St} {cr : Ts → Res} {m : Msg} {tw : Ts} {R : Res}
    (hm : s.mem[tw]? = some m) (hP : PlantCr E s m tw R) (hlow : TermPlant.LowOwn s m.loc tw) (hcr : R ≤ cr tw)
    (hW : ∀ wb, tw ≤ wb → wb < s.mem.size → ∀ (sb b0 : Nat) (S : Ty) (us : List Acc) (K : Nat → Bool) (i o : Nat) (tw' : Ts), accs S = some us → K i = true →
      InAcc us i o → TermPlant.LowOwn s ⟨m.loc.label, sb + b0 + o⟩ tw' → tw' ≤ wb) :
    R = .zero ∨ ∃ c x, E.sto m.loc.label = some c ∧ x.1 = tw ∧ TermPlant.CrItem E s cr m.loc.label c x := by
  obtain ⟨c, sb, S0, b0, S, us, wb, hsto, -, -, hseg, hat, hS, hnw, hus, hn, h1, h2, htw, hwb, -, -, hK⟩ := hP
  rcases hK with ⟨K, ws, R0, hlen, hv, hR0, hpin⟩ | hz
  · exact .inr ⟨c, _, hsto, rfl, item_of_plantCr hm hseg hat hS hnw hus hn h1 h2 hlen hv hR0 hpin hlow hcr
      (fun i o tw' hK hio hl => hW wb htw hwb sb b0 S us K i o tw' hus hK hio hl)⟩
  · exact .inl hz

#print axioms item_of_plantCr_ex

end TermOverCr
