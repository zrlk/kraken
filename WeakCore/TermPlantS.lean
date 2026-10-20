/-
**The simultaneous raise** (B): planted labels with new slots whose element type
is a copyable word-free type of single-word units (`accs e = some us`, all `.one`,
`affineIn [] e = false`).  Their new slots are values carrying nothing, typed at the final
environment.
-/
import WeakCore.TermPlantE
import WeakCore.TermBlkZ
namespace TermPlantS
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermMain TermPlantR TermPlantW TermPlantL TermPlantE
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## A typed word of a copyable single-unit slot is a resource-free value -/

/-- `WordOK` at a buffer of single-unit elements: word `o` is (above) a one-word value
of the element type. -/
theorem WordOK_unit {E : TEnv} {N : Nat} {e : Ty} {o : Nat} {w : Word} (hu : accs e = some [.one])
    (h : WordOK E (.array (.lit N) e) o w) : ∃ w0, ValOf E e [w0] ∧ WLe1 w0 w := by
  obtain ⟨b, S, ws, o', w0, hs, ⟨hv, hsh⟩, hw, hle, -⟩ := h
  rcases hs with ⟨-, -, ha⟩ | ⟨N', us, j, hT, hus, -, -⟩
  · simp [accs] at ha
  · cases hT
    rw [hu] at hus; cases hus
    have hl : ws.length = 1 := by simpa [nWords, Acc.size] using hsh _ hu
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hl
    cases o' with
    | zero => cases hw; exact ⟨_, hv, hle⟩
    | succ _ => simp at hw

/-- A copyable closed value carries nothing. -/
theorem ValOfR_copy {E : TEnv} {e : Ty} {ws : List Word} (ha : Ty.affineIn [] e = false)
    (htb : tb 0 e = true) (h : ValOf E e ws) : ValOfR E e ws .zero :=
  ⟨VR_VRR_copy e [] _ _ _ _ ha htb (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) h.1, h.2⟩

/-- **The new-slot value**: a word typed (`WordOK`) at a copyable single-unit buffer is
a resource-free value of the element type. -/
theorem slotR_of_wordOK {E : TEnv} {N : Nat} {e : Ty} {o : Nat} {w : Word} (hu : accs e = some [.one])
    (ha : Ty.affineIn [] e = false) (htb : tb 0 e = true) (h : WordOK E (.array (.lit N) e) o w) :
    ValOfR E e [w] .zero := by
  obtain ⟨w0, hv, hle⟩ := WordOK_unit hu h
  exact ValOfR_copy ha htb ⟨VR_up e _ [w0] [w] ⟨hle, trivial⟩ hv.1,
    Valid_vals e [w0] [w] (WLe.vals ⟨hle, trivial⟩) hv.2⟩

/-! ## (S2) The memory side of a simultaneous raise at word-free buffers -/

/-- (S2) A word-free cell type has no word unit. -/
theorem noWU_dwf {E : TEnv} {l : AllocLabel} {c : Cell} {o : Nat} (hc : E.sto l = some c)
    (hd : dwf c.ty = true) : ¬ WordUnit E ⟨l, o⟩ := by
  rintro ⟨c', hc', h⟩
  rw [hc] at hc'; cases hc'
  rcases h with ⟨r, P, -, ha⟩ | ⟨r, P, ha⟩ | ⟨r, P, -, ha⟩
  · rw [AtOff_dwf rfl (fun _ h => by cases h) ha] at hd; cases hd
  · rw [AtOff_dwf rfl (fun _ h => by cases h) ha] at hd; cases hd
  · rw [AtOff_dwf rfl (fun _ h => by cases h) ha] at hd; cases hd

/-- (S2) A word-free cell type has no protocol word. -/
theorem noWordAt_dwf {E : TEnv} {l : AllocLabel} {c : Cell} {o : Nat} (hc : E.sto l = some c)
    (hd : dwf c.ty = true) : ∀ n P, ¬ WordAt E ⟨l, o⟩ n P := by
  rintro n P ⟨c', hc', ha, -⟩
  rw [hc] at hc'; cases hc'
  rw [AtOff_dwf rfl (fun _ h => by cases h) ha] at hd; cases hd

/-- (S2) **One label's entry at the raise** of a word-free buffer, every new slot carrying
nothing: each new unit reads its first write (everything above it is a promise or a frontier
promise, `hR1`), and the words so read of each new slot are a value of the element type
(`hslot`). -/
theorem HeldEntry_raiseU {E E' : TEnv} {s : St} {l : AllocLabel} {R : Res} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc}
    (he : HeldEntry E s l R) (hsl : E'.sto l = E.sto l) (htid : E'.tid = E.tid) (hpf : E'.pfr l = E.pfr l)
    (hfp : E'.fp = E.fp) (hri : E'.rini l = E.rini l)
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us) (hd : dwf e = true)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hil : E.ini l ≤ E'.ini l) (hN : E'.ini l ≤ N) (hrl : E.rini l ≤ E.ini l) (hpfl : E.pfr l ≠ none)
    (hR1 : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      ∃ h, FirstW s.mem ⟨l, o⟩ h ∧
        ∀ t m', h < t → s.mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ s.promises ++ E.fp)
    (hslot : ∀ j, E.ini l ≤ j → j < E'.ini l → ∀ ws : List Word, ws.length = nWords us →
      (∀ i w, ws[i]? = some w → ∃ h m, FirstW s.mem ⟨l, j * nWords us + i⟩ h ∧ s.mem[h]? = some m ∧ w = mw m) →
      ValOfR E' e ws .zero) :
    HeldEntry E' s l R := by
  have hdc : dwf c.ty = true := by rw [hT]; exact hd
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
  -- every new unit reads its first write under `E'`
  have hex : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us → ∃ h m, FirstW s.mem ⟨l, o⟩ h ∧
      s.mem[h]? = some m ∧ LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (mw m) := by
    intro o h1 h2
    obtain ⟨hh, hfw, habove⟩ := hR1 o h1 h2
    have hwu' : ¬ VisU E' ⟨l, o⟩ := fun hv' => noWU_dwf hc' hdc hv'.1
    have hq : PredU E' ⟨l, o⟩ := by
      refine ⟨hpfl', (IniW_iff hc' hT hu).2 h2, fun hr => ?_⟩
      rw [IniWr_iff hc' hT hu, hrc, hrcE] at hr
      have := Nat.mul_le_mul_right (nWords us) hrl; omega
    obtain ⟨⟨m, hm, hml, -⟩, -⟩ := id hfw
    refine ⟨hh, m, hfw, hm, hh, m, ?_, hm, hml, rfl, fun t' m' hlt hm' hl' => ?_⟩
    · rw [mem_PromAt_pred hwu' hq]
      rintro ⟨-, h', hf', hlt'⟩
      rw [FirstW_uniq hf' hfw] at hlt'; exact Nat.lt_irrefl _ hlt'
    · rw [mem_PromAt_pred hwu' hq, FpAt_vis hvis', hfp]
      exact ⟨habove t' m' hlt hm' hl', hh, hfw, hlt⟩
  let f : Nat → Word := fun o =>
    if hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us then
      mw (Classical.choose (Classical.choose_spec (hex o hh.1 hh.2)))
    else default
  have hf : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us → ∃ h m, FirstW s.mem ⟨l, o⟩ h ∧
      s.mem[h]? = some m ∧ f o = mw m ∧ LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (f o) := by
    intro o h1 h2
    have hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us := ⟨h1, h2⟩
    obtain ⟨a1, a2, a3⟩ := Classical.choose_spec (Classical.choose_spec (hex o h1 h2))
    refine ⟨_, _, a1, a2, ?_, ?_⟩
    · simp only [f, hh, and_self, dite_true]
    · simp only [f, hh, and_self, dite_true]; exact a3
  have he' := HeldEntry_raise (Rf := fun _ => .zero) (f := f) he hc hc' hT hu hv hil hN hrc hpa
    (fun o h1 h2 => by
      obtain ⟨-, -, -, -, -, h5⟩ := hf o h1 h2
      exact h5)
    (fun _ _ _ _ => rfl)
    (fun j hj1 hj2 => by
      refine hslot j hj1 hj2 _ (by simp) (fun i w hw => ?_)
      rw [List.getElem?_map] at hw
      by_cases hi : i < nWords us
      · rw [List.getElem?_range hi, Option.map_some, Option.some.injEq] at hw
        subst hw
        have h1 : E.ini l * nWords us ≤ j * nWords us := Nat.mul_le_mul_right _ hj1
        have h2 : (j + 1) * nWords us ≤ E'.ini l * nWords us := Nat.mul_le_mul_right _ hj2
        rw [Nat.succ_mul] at h2
        obtain ⟨h, m, a1, a2, a3, -⟩ := hf (j * nWords us + i) (Nat.le_trans h1 (Nat.le_add_right _ _))
          (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) h2)
        exact ⟨h, m, a1, a2, a3⟩
      · have h0 : (List.range (nWords us))[i]? = none :=
          List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hi)
        rw [h0] at hw; cases hw)
  rwa [Res.sum_map_zero, Res.add_zero] at he'

/-- (S2, R1 groundwork) **One label's entry at the raise, resourceful**: as `HeldEntry_raiseU`,
each new slot (read at its units' first writes) being a value of resources `Rf j`; memory's
holding gains their sum. -/
theorem HeldEntry_raiseUR {E E' : TEnv} {s : St} {l : AllocLabel} {R : Res} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} {Rf : Nat → Res}
    (he : HeldEntry E s l R) (hsl : E'.sto l = E.sto l) (htid : E'.tid = E.tid) (hpf : E'.pfr l = E.pfr l)
    (hfp : E'.fp = E.fp) (hri : E'.rini l = E.rini l)
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us) (hd : dwf e = true)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hil : E.ini l ≤ E'.ini l) (hN : E'.ini l ≤ N) (hrl : E.rini l ≤ E.ini l) (hpfl : E.pfr l ≠ none)
    (hR1 : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      ∃ h, FirstW s.mem ⟨l, o⟩ h ∧
        ∀ t m', h < t → s.mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ s.promises ++ E.fp)
    (hslot : ∀ j, E.ini l ≤ j → j < E'.ini l → ∀ ws : List Word, ws.length = nWords us →
      (∀ i w, ws[i]? = some w → ∃ h m, FirstW s.mem ⟨l, j * nWords us + i⟩ h ∧ s.mem[h]? = some m ∧ w = mw m) →
      ValOfR E' e ws (Rf j))
    (hz : ∀ j, nWords us = 0 → Rf j = .zero) :
    HeldEntry E' s l (R + Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf)) := by
  have hdc : dwf c.ty = true := by rw [hT]; exact hd
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
  -- every new unit reads its first write under `E'`
  have hex : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us → ∃ h m, FirstW s.mem ⟨l, o⟩ h ∧
      s.mem[h]? = some m ∧ LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (mw m) := by
    intro o h1 h2
    obtain ⟨hh, hfw, habove⟩ := hR1 o h1 h2
    have hwu' : ¬ VisU E' ⟨l, o⟩ := fun hv' => noWU_dwf hc' hdc hv'.1
    have hq : PredU E' ⟨l, o⟩ := by
      refine ⟨hpfl', (IniW_iff hc' hT hu).2 h2, fun hr => ?_⟩
      rw [IniWr_iff hc' hT hu, hrc, hrcE] at hr
      have := Nat.mul_le_mul_right (nWords us) hrl; omega
    obtain ⟨⟨m, hm, hml, -⟩, -⟩ := id hfw
    refine ⟨hh, m, hfw, hm, hh, m, ?_, hm, hml, rfl, fun t' m' hlt hm' hl' => ?_⟩
    · rw [mem_PromAt_pred hwu' hq]
      rintro ⟨-, h', hf', hlt'⟩
      rw [FirstW_uniq hf' hfw] at hlt'; exact Nat.lt_irrefl _ hlt'
    · rw [mem_PromAt_pred hwu' hq, FpAt_vis hvis', hfp]
      exact ⟨habove t' m' hlt hm' hl', hh, hfw, hlt⟩
  let f : Nat → Word := fun o =>
    if hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us then
      mw (Classical.choose (Classical.choose_spec (hex o hh.1 hh.2)))
    else default
  have hf : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us → ∃ h m, FirstW s.mem ⟨l, o⟩ h ∧
      s.mem[h]? = some m ∧ f o = mw m ∧ LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (f o) := by
    intro o h1 h2
    have hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us := ⟨h1, h2⟩
    obtain ⟨a1, a2, a3⟩ := Classical.choose_spec (Classical.choose_spec (hex o h1 h2))
    refine ⟨_, _, a1, a2, ?_, ?_⟩
    · simp only [f, hh, and_self, dite_true]
    · simp only [f, hh, and_self, dite_true]; exact a3
  exact HeldEntry_raise (Rf := Rf) (f := f) he hc hc' hT hu hv hil hN hrc hpa
    (fun o h1 h2 => by
      obtain ⟨-, -, -, -, -, h5⟩ := hf o h1 h2
      exact h5)
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
        obtain ⟨h, m, a1, a2, a3, -⟩ := hf (j * nWords us + i) (Nat.le_trans h1 (Nat.le_add_right _ _))
          (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) h2)
        exact ⟨h, m, a1, a2, a3⟩
      · have h0 : (List.range (nWords us))[i]? = none :=
          List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hi)
        rw [h0] at hw; cases hw)

/-- (S2) **One label's entry at the raise of a zero-width buffer**: the buffer has no words,
and every new slot (at or above the real count) carries nothing. -/
theorem HeldEntry_raiseZ {E E' : TEnv} {s : St} {l : AllocLabel} {R : Res} {c : Cell} {N : Nat} {e : Ty}
    (he : HeldEntry E s l R) (hsl : E'.sto l = E.sto l) (hri : E'.rini l = E.rini l)
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some [])
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hil : E.ini l ≤ E'.ini l) (hN : E'.ini l ≤ N) (hrl : E.rini l ≤ E.ini l) :
    HeldEntry E' s l R := by
  have hc' : E'.sto l = some c := by rw [hsl]; exact hc
  have hrc : E'.rc l = E.rc l := by
    unfold TEnv.rc; rw [hri]; omega
  have hrcE : E.rc l = E.rini l := by unfold TEnv.rc; omega
  obtain ⟨-, hent⟩ := he
  obtain ⟨vals, -, hok⟩ := hent c hc
  have hb : BufOKR E (E.ini l) (E.rc l) c.ty vals R := by
    rcases hok with ⟨hw, -⟩ | hb
    · rw [hT] at hw; simp [wc, accs] at hw
    · exact hb
  obtain ⟨N0, e0, us0, Rs, hT0, hu0, -, hl, hRs, hR, hj⟩ := hb
  rw [hT] at hT0; cases hT0
  rw [hu] at hu0; cases hu0
  have hw0 : nWords ([] : List Acc) = 0 := rfl
  refine ⟨fun h0 => (by rw [hc'] at h0; cases h0), fun c' hc'' => ?_⟩
  rw [hc'] at hc''; cases hc''
  refine ⟨[], fun o w hw => by simp at hw, Or.inr ?_⟩
  refine ⟨N, e, [], Rs ++ (List.range' (E.ini l) (E'.ini l - E.ini l)).map (fun _ => Res.zero), hT, hu, hN,
    by simp [hw0], by simp only [List.length_append, List.length_map, List.length_range']; omega,
    by rw [hR, Res.sum_append, TermStep.sum_map_zero, Res.add_zero], fun j Rj hjn hRj => ?_⟩
  by_cases hjo : j < E.ini l
  · rw [List.getElem?_append_left (by omega)] at hRj
    have := hj j Rj hjo hRj
    refine slotR_imp this hrc (fun hb => ?_)
    have e1 : ∀ vs : List Word, (vs.drop (j * nWords ([] : List Acc))).take (nWords ([] : List Acc)) = [] := by
      intro vs; simp [hw0]
    rw [e1] at hb ⊢; exact hv hb
  · rw [List.getElem?_append_right (by omega), List.getElem?_map, List.getElem?_range' (by omega)] at hRj
    simp only [Option.map_some, Option.some.injEq] at hRj
    subst hRj
    refine ⟨fun _ _ => rfl, fun h => ?_⟩
    rcases h with h | h
    · rw [hrc, hrcE] at h; omega
    · rw [hw0] at h; exact absurd h (Nat.lt_irrefl 0)

/-- (S2) A label's entry, moved to an environment agreeing at it. -/
theorem HeldEntry_tr {E E' : TEnv} {s : St} {l : AllocLabel} {R : Res} (he : HeldEntry E s l R)
    (hsl : E'.sto l = E.sto l) (htid : E'.tid = E.tid) (hpf : E'.pfr l = E.pfr l) (hfp : E'.fp = E.fp)
    (hil : E'.ini l = E.ini l) (hri : E'.rini l = E.rini l)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R) :
    HeldEntry E' s l R := by
  obtain ⟨h0, h1⟩ := he
  refine ⟨fun hn => h0 (by rw [← hsl]; exact hn), fun c hc => ?_⟩
  obtain ⟨vals, hL, hC⟩ := h1 c (by rw [← hsl]; exact hc)
  refine ⟨vals, fun o w hw => by
    rw [PromAt_congr (a := ⟨l, o⟩) hsl htid hpf hfp hil (TEnv.rc_congr hil hri)]
    exact hL o w hw, ?_⟩
  rw [hil, TEnv.rc_congr hil hri]
  rcases hC with ⟨h1, h2⟩ | ⟨N, e, us, Rs, hT, hu, hn, hl, hRs, hR, hj⟩
  · exact Or.inl ⟨h1, hv h2⟩
  · exact Or.inr ⟨N, e, us, Rs, hT, hu, hn, hl, hRs, hR, fun j Rj h1 h2 => slotR_imp (hj j Rj h1 h2) rfl hv⟩

/-- (S2) Memory's holding, entry by entry. -/
theorem MemHeld_entries {E E' : TEnv} {s : St} {H : Res} (h : MemHeld E s H)
    (hsto : ∀ l, E'.sto l = E.sto l) (he : ∀ l R, HeldEntry E s l R → HeldEntry E' s l R) :
    MemHeld E' s H := by
  obtain ⟨L, Rl, hnd, hcov, rfl, hent⟩ := h
  exact ⟨L, Rl, hnd, fun l c hc => hcov l c (by rw [← hsto]; exact hc), rfl,
    fun l hl => he l (Rl l) (hent l hl)⟩

/-- (S2) **`MemHeld_raiseQ`**: raising the counts of the labels `Q` (word-free buffers with
frontiers) keeps memory's holding: the new slots carry nothing. -/
theorem MemHeld_raiseQ {E E' : TEnv} {s : St} {H : Res} {Q : AllocLabel → Prop}
    (h : MemHeld E s H) (hsto : ∀ l, E'.sto l = E.sto l) (htid : E'.tid = E.tid)
    (hpf : ∀ l, E'.pfr l = E.pfr l) (hfp : E'.fp = E.fp) (hri : ∀ l, E'.rini l = E.rini l)
    (hini : ∀ l, ¬ Q l → E'.ini l = E.ini l)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hQ : ∀ l, Q l → ∃ c N e us, E.sto l = some c ∧ c.ty = .array (.lit N) e ∧ accs e = some us ∧
      E.ini l ≤ E'.ini l ∧ E'.ini l ≤ N ∧ E.rini l ≤ E.ini l ∧ E.pfr l ≠ none ∧
      (∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
        ∃ h, FirstW s.mem ⟨l, o⟩ h ∧
          ∀ t m', h < t → s.mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ s.promises ++ E.fp) ∧
      (us = [] ∨ (dwf e = true ∧
      (∀ j, E.ini l ≤ j → j < E'.ini l → ∀ ws : List Word, ws.length = nWords us →
        (∀ i w, ws[i]? = some w → ∃ h m, FirstW s.mem ⟨l, j * nWords us + i⟩ h ∧ s.mem[h]? = some m ∧
          w = mw m) →
        ValOfR E' e ws .zero)))) :
    MemHeld E' s H := by
  classical
  refine MemHeld_entries h hsto fun l R he => ?_
  by_cases hq : Q l
  · obtain ⟨c, N, e, us, hc, hT, hu, hil, hN, hrl, hpfl, hR1, hZ⟩ := hQ l hq
    rcases hZ with rfl | ⟨hd, hslot⟩
    · exact HeldEntry_raiseZ he (hsto l) (hri l) hc hT hu hv hil hN hrl
    · exact HeldEntry_raiseU he (hsto l) htid (hpf l) hfp (hri l) hc hT hu hd hv hil hN hrl hpfl hR1 hslot
  · exact HeldEntry_tr he (hsto l) htid (hpf l) hfp (hini l hq) (hri l) hv

/-- (S2) **The credits at the raise** are kept: at a newly counted unit (a word-free cell) the
old credit and debit are nothing, and so are the new ones. -/
theorem PromCr_raiseQ {E E' : TEnv} {s : St} {cr db : Ts → Res} (hC : PromCr E s cr db)
    (hsto : ∀ l, E'.sto l = E.sto l) (htid : E'.tid = E.tid) (hpf : ∀ l, E'.pfr l = E.pfr l)
    (hmono : ∀ a, IniW E a → IniW E' a)
    (hrc : ∀ l, E'.rc l = E.rc l) (hbx : ∀ l B, E.box l = some B → E'.box l = some B)
    (hnw : ∀ a, IniW E' a → ¬ IniW E a → ∀ n P, ¬ WordAt E' a n P)
    (hbz : ∀ a tw, IniW E' a → ¬ IniW E a → DesigAt E' s.mem a tw → BlkDb E' s.mem a .zero) :
    PromCr E' s cr db := by
  refine (PromCr_raise (cr' := cr) (db' := db) hC hsto htid hpf hmono hrc hbx ?_ fun _ _ _ => ⟨rfl, rfl⟩).1
  intro tw m htw hm h1 h2
  obtain ⟨m', hm', hd, hcr⟩ := hC tw htw
  rw [hm] at hm'; cases hm'
  have hdz : db tw = .zero := (DbRes_uninit h2).1 hd
  have hcz : cr tw = .zero := by
    rcases hcr with ⟨w, -, hv⟩ | ⟨-, hz⟩
    · exact (VRes_uninit h2).1 hv
    · exact hz
  have hn := hnw m.loc h1 h2
  rw [hdz, hcz]
  refine ⟨?_, ?_⟩
  · by_cases hvi : Vis E' m.loc.label ∧ IniW E' m.loc
    · exact Or.inl ⟨hvi.1, hvi.2, fun _ => ⟨.zero, .zero, Or.inr ⟨hn, rfl⟩, hbz m.loc tw h1 h2,
        fun _ => rfl, rfl⟩, fun _ => Or.inr ⟨fun n P hw => absurd hw (hn n P), rfl⟩⟩
    · exact Or.inr ⟨hvi, rfl⟩
  · by_cases hp : ∃ w, PredAt s.mem m.loc tw w
    · obtain ⟨w, hw⟩ := hp
      refine Or.inl ⟨w, hw, ?_⟩
      by_cases hvi : Vis E' m.loc.label ∧ IniW E' m.loc
      · exact Or.inl ⟨hvi.1, hvi.2, Or.inr ⟨fun n P hw => absurd hw (hn n P), rfl⟩⟩
      · exact Or.inr ⟨hvi, rfl⟩
    · exact Or.inr ⟨fun w hw => hp ⟨w, hw⟩, rfl⟩

/-! ## (S3) The simultaneous flip and the keyed credits off a label set -/

/-- (S3) `MemHeld_flipLH` at a set `Q` of own labels: the flip of every member at once. -/
theorem MemHeld_flipQ {g : G} {E E' : TEnv} {s : St} {H : Res} {cr db : Ts → Res} {Q : AllocLabel → Prop}
    (hm : MemInv g E s) (hH : MemHeld E s H) (hC : PromCr E s cr db) (hpa : PromAbove s)
    (hs : ∀ l, E'.sto l = E.sto l) (hi : ∀ l, E'.ini l = E.ini l)
    (hmono : ∀ l, Vis E l → Vis E' l) (hl : ∀ l', ¬ Q l' → Vis E' l' → Vis E l')
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hf : ∀ l, Q l → FlipOK E s l) (hfo : FpOK E s)
    (hol : ∀ l, Q l → OwnL E l) (hpm : ∀ l', E.pfr l' ≠ none → E'.pfr l' ≠ none)
    (hpo : ∀ l', ¬ Q l' → E'.pfr l' ≠ none → E.pfr l' ≠ none)
    (hfp : E'.fp = E.fp) (hri : ∀ l, E'.rini l = E.rini l)
    (htid : E'.tid = E.tid) (hbx : ∀ l B, E.box l = some B → E'.box l = some B) :
    ∃ H' cr' db', MemHeld E' s H' ∧ PromCr E' s cr' db' ∧
      (∀ t m, t ∈ s.promises → s.mem[t]? = some m → ¬ (VisU E' m.loc ∧ ¬ VisU E m.loc) →
        cr' t = cr t ∧ db' t = db t) ∧
      H' + pSum s cr' + pSum s db = H + pSum s cr + pSum s db' := by
  have hq : ∀ a : Address, PredU E' a ↔ PredU E a := fun a => by
    have hrc' : E'.rc a.label = E.rc a.label := TEnv.rc_congr (hi _) (hri _)
    unfold PredU
    rw [IniW_congrU (hs _) (hi _), IniWr_congr (hs _) hrc']
    by_cases hv0 : E.pfr a.label = none
    · refine ⟨fun h => absurd h ?_, fun h => absurd hv0 h.1⟩
      rintro ⟨hpf', hiw, hnr⟩
      have hle : Q a.label := Classical.byContradiction fun hne => hpo _ hne hpf' hv0
      obtain ⟨c, hc, hown⟩ := hol _ hle
      have hrc : E.ini a.label ≤ E.rc a.label := Nat.le_of_not_lt fun hlt => by
        obtain ⟨f, hf, -⟩ := hm.2.2.2.2.2.1.2 _ c hc hown hlt
        rw [hv0] at hf; cases hf
      exact hnr fun c' N e us hc' hT hu =>
        Nat.lt_of_lt_of_le (hiw c' N e us hc' hT hu) (Nat.mul_le_mul_right _ hrc)
    · exact ⟨fun h => ⟨hv0, h.2⟩, fun h => ⟨hpm _ hv0, h.2⟩⟩
  obtain ⟨H', cr', db', h1, h2, h4, h3⟩ := MemHeld_flip hH hC (MemInv_promLt hm) (hm.2.2.2.2.2.2.2.2.2.2.1 : s.promises.Nodup) hs hi hmono hv
    (fun t m ht hm' hv1 hv2 hIW => by
      have hwu : WordUnit E m.loc := (WordUnit_congr (hs _)).1 hv1.1
      have hpv : Priv E m.loc.label := Classical.byContradiction fun h => hv2 ⟨hwu, h⟩
      have hle : Q m.loc.label := Classical.byContradiction fun h => hl _ h hv1.2 hpv
      obtain ⟨c, n, P, hsto, hat, hg, hini, hp, hin⟩ := hf _ hle hpv t m ht hm' rfl hwu hIW
      obtain ⟨⟨c', hc', hown⟩, hpf0⟩ := hpv
      rw [hsto] at hc'
      obtain rfl : c = c' := Option.some.inj hc'
      refine ⟨⟨c, n, P, hsto, hat, hg, hini, hp, hin⟩, fun t' m' ht' hm'' hl' => ?_⟩
      have hrc : E.ini m.loc.label ≤ E.rc m.loc.label := Nat.le_of_not_lt fun hlt => by
        obtain ⟨f, hf, -⟩ := hm.2.2.2.2.2.1.2 _ c hsto hown hlt
        rw [hpf0] at hf; cases hf
      have htail := own_tailW (OwnOKPF_cellP hm.2.1 hsto hown hpf0) hsto hat hg (IniAt_monoAt hrc hini)
      have h1 := hpa t ht m hm'
      by_cases hlt : s.vs.coh m.loc < t'
      · exact absurd (htail t' m' hlt hm'' hl') ht'
      · exact Nat.lt_of_le_of_lt (Nat.le_of_not_lt hlt) h1) hfp (fun t m ht hm _ => hfo.2 t m ht hm) hq
    htid hbx hri
  exact ⟨H', cr', db', h1, h2, h4, h3⟩

/-- (S3) `PromCrK_lift` with the label replaced by a set `Ql`: plant credits sit off `Ql`. -/
theorem PromCrK_liftQ {E E2 : TEnv} {s : St} {H : Res} {cr db : Ts → Res} {Ql : AllocLabel → Prop}
    (hC : TermPlant.PromCrK E s cr db)
    (hPl : ∀ tw m R, s.mem[tw]? = some m → PlantCr E s m tw R → ¬ Ql m.loc.label)
    (hPT : ∀ tw m R, s.mem[tw]? = some m → ¬ Ql m.loc.label → PlantCr E s m tw R → PlantCr E2 s m tw R)
    (hstep : ∀ cr0 : Ts → Res, PromCr E s cr0 db → ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ PromCr E2 s cr2 db2 ∧
      (∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → ¬ Ql m.loc.label → cr2 tw = cr0 tw ∧ db2 tw = db tw) ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr0 + pSum s db2) :
    ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ TermPlant.PromCrK E2 s cr2 db2 ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr + pSum s db2 := by
    obtain ⟨x0, x1, x2, h0, h1, h2, -⟩ := TermPlantW.PromCrK_liftG hC hPl hPT hstep
    exact ⟨x0, x1, x2, h0, h1, h2⟩

/-! ## (S4) The simultaneous plant at the thread's system invariant -/

open Classical in
/-- `Eg` with every label of `Q` planted at frontier `F l` and reader-visible count `Np l`. -/
noncomputable def plantS (Eg : GEnv) (Q : AllocLabel → Prop) (F : AllocLabel → Ts) (Np : AllocLabel → Nat) :
    GEnv :=
  { Eg with pfr := fun l => if Q l then some (F l) else Eg.pfr l
            ini := fun l => if Q l then Np l else Eg.ini l }

/-- (S4) Planting own labels keeps every cut's store of their owner. -/
theorem cutSto_plantS {Eg : GEnv} {Q : AllocLabel → Prop} {F : AllocLabel → Ts} {Np : AllocLabel → Nat} {j : Nat}
    (hQ : ∀ l, Q l → ∃ c, Eg.sto l = some c ∧ c.owner = some j) :
    cutSto (plantS Eg Q F Np) j = cutSto Eg j := by
  classical
  funext l'
  refine cutSto_congr rfl (fun c' hc' hn => ?_)
  by_cases he : Q l'
  · obtain ⟨c, hc, ho⟩ := hQ l' he
    rw [hc] at hc'; cases hc'; exact absurd ho hn
  · simp [plantS, GEnv.Shared, he]

open Classical in
/-- (S4) The simultaneously raised frame environment is a cut. -/
theorem CE_withSto_CutS {η : TEnv} {Eg : GEnv} {j : Nat} {S : AllocLabel → Prop} {Q : AllocLabel → Prop}
    {F : AllocLabel → Ts} {Np : AllocLabel → Nat} (hE : CE η = Cut Eg j S)
    (hQ : ∀ l, Q l → ∃ c, Eg.sto l = some c ∧ c.owner = some j) :
    CE (η.withSto η.sto (fun l' => if Q l' then Np l' else η.ini l') (fun l' => if Q l' then some (F l') else η.pfr l')
      η.seen) = Cut (plantS Eg Q F Np) j S := by
  have h1 : η.prog = Eg.prog := congrArg TEnv.prog hE
  have h2 : η.sto = cutSto Eg j := congrArg TEnv.sto hE
  have h3 : η.tid = j := congrArg TEnv.tid hE
  have h4 : η.ini = Eg.ini := congrArg TEnv.ini hE
  have h5 : η.rini = Eg.rini := congrArg TEnv.rini hE
  have h6 : η.pfr = Eg.pfr := congrArg TEnv.pfr hE
  have h7 : η.seen = S := congrArg TEnv.seen hE
  have h8 : η.box = Eg.box := congrArg TEnv.box hE
  have h9 : η.fp = Eg.fpOf j := congrArg TEnv.fp hE
  unfold Cut
  rw [cutSto_plantS hQ]
  simp only [CE, TEnv.withSto, plantS, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-! ## (S5) Event-layer helpers -/

/-- A copyable word-free buffer type whose access units are single words. -/
def UnitT (T : Ty) : Prop :=
  ∃ N e us, T = .array (.lit N) e ∧ accs e = some us ∧ (∀ u ∈ us, u = Acc.one) ∧
    (us = [] ∨ (us ≠ [] ∧ Ty.affineIn [] e = false ∧ dwf e = true ∧
      (TermBlkZ.SkFree e = true ∨ TermTv.mg e = true)))

theorem not_unit_of_wordbuf {T : Ty} (h : WordBufT T) : ¬ UnitT T := by
  obtain ⟨N, n, P, rfl, hg⟩ := h
  rintro ⟨N', e, us, he, hu, -, hZ⟩
  cases he
  rcases hZ with rfl | ⟨-, -, hd, -⟩
  · simp [accs, hg] at hu
  · simp [dwf] at hd

/-- A least witness. -/
theorem exists_least {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  classical
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hm : ∃ m, m < n ∧ P m
    · obtain ⟨m, hmn, hPm⟩ := hm; exact ih m hmn hPm
    · exact ⟨n, hn, fun m hmn hPm => hm ⟨m, hmn, hPm⟩⟩

/-- (S5) At a unit shaped by R1w (one placeholder below, every other message a promise of `Pr`
above it, at least one) the first write is a promise of `Pr`, and so is everything above it. -/
theorem firstW_of_R1w {mem : Memory} {Pr : List Ts} {a : Address}
    (hR : ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = a ∧ m0.val = .undef ∧ t0 ∉ Pr ∧ (∃ t, AtA mem a t0 t = true) ∧
      ∀ t m, mem[t]? = some m → m.loc = a → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ Pr) :
    ∃ h, FirstW mem a h ∧ h ∈ Pr ∧ ∀ t m', h < t → mem[t]? = some m' → m'.loc = a → t ∈ Pr := by
  obtain ⟨t0, m0, hm0, hl0, hv0, -, ⟨t1, ht1⟩, hall⟩ := hR
  have hex : ∃ t, (∃ m, mem[t]? = some m ∧ m.loc = a) ∧ t ≠ t0 := by
    simp only [AtA, decide_eq_true_eq] at ht1; exact ⟨t1, ht1⟩
  obtain ⟨h, ⟨⟨m, hm, hml⟩, hne⟩, hmin⟩ := exists_least hex
  obtain ⟨hlt0, hvm, hPr⟩ := hall h m hm hml hne
  refine ⟨h, ⟨⟨m, hm, hml, hvm⟩, fun t m' ht hm' hl' => ?_⟩, hPr, fun t m' ht hm' hl' => ?_⟩
  · by_cases e : t = t0
    · subst e; rw [hm0] at hm'; cases hm'; exact hv0
    · exact absurd ⟨⟨m', hm', hl'⟩, e⟩ (hmin t ht)
  · exact (hall t m' hm' hl' (fun e => Nat.lt_asymm hlt0 (e ▸ ht))).2.2

/-- (S5) The words of a layout of single words. -/
theorem nWords_ones : ∀ {us : List Acc}, (∀ u ∈ us, u = Acc.one) → nWords us = us.length
  | [], _ => rfl
  | u :: us, h => by
    have hu := h u List.mem_cons_self
    subst hu
    have ih := nWords_ones (fun u' hu' => h u' (List.mem_cons_of_mem _ hu'))
    have hc : nWords (Acc.one :: us) = Acc.one.size + nWords us := by simp [nWords]
    rw [hc, ih]; simp [Acc.size]; omega

theorem nWords_take_ones {us : List Acc} (h : ∀ u ∈ us, u = Acc.one) (i : Nat) :
    nWords (us.take i) = min i us.length := by
  rw [nWords_ones (fun u hu => h u (List.mem_of_mem_take hu)), List.length_take]

theorem slot_eq {n j j' i o' : Nat} (hi : i < n) (ho : o' < n) (h : j' * n + o' = j * n + i) : o' = i := by
  have := congrArg (· % n) h
  simp only [Nat.mul_comm j' n, Nat.mul_comm j n, Nat.mul_add_mod, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt ho] at this
  exact this

/-- (S5) `WordOK` at word `i` of slot `jj` of a buffer: it is (above) word `i` of a value of the
element type. -/
theorem WordOK_slot {E : TEnv} {N : Nat} {e : Ty} {us : List Acc} {o jj i : Nat} {w : Word}
    (hu : accs e = some us) (hi : i < nWords us) (ho : o = jj * nWords us + i)
    (h : WordOK E (.array (.lit N) e) o w) :
    ∃ ws0 x, ValOf E e ws0 ∧ ws0.length = nWords us ∧ ws0[i]? = some x ∧ WLe1 x w := by
  obtain ⟨b, S, ws, o', w0, hs, ⟨hv, hsh⟩, hw, hle, hbo⟩ := h
  rcases hs with ⟨-, -, ha⟩ | ⟨N', us', j', hT, hus, -, hb⟩
  · simp [accs] at ha
  · cases hT
    rw [hu] at hus; cases hus
    have hl := hsh _ hu
    have ho' : o' < nWords us := by
      rw [← hl]; exact (List.getElem?_eq_some_iff.1 hw).1
    subst hb
    have e1 : o' = i := slot_eq hi ho' (hbo.trans ho)
    subst e1
    exact ⟨ws, w0, hv, hl, hw, hle⟩

/-- (S5) The published part of `Eg` is in every cut. -/
theorem Incl_pub_cut (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) : Incl (PubE Eg) (Cut Eg i S) := by
  refine ⟨rfl, fun l c hc => ?_, fun _ => Nat.le_refl _, fun _ _ h => h, fun _ _ h => h, fun _ => Nat.le_refl _⟩
  simp only [PubE] at hc
  split at hc
  · exact cutSto_shared hc (by assumption)
  · cases hc

/-- (S5) `FpOK` at an environment agreeing on the cut store, the promise frontiers and (up to
publication) the frontiers. -/
theorem FpOK_agreeW {Eg0 Eg : GEnv} {j : Nat} {S : AllocLabel → Prop} {s : St}
    (hcs : cutSto Eg j = cutSto Eg0 j) (hfp : Eg.fpOf = Eg0.fpOf)
    (hvis : ∀ l', Eg.pfr l' = Eg0.pfr l' ∨ ∃ f, Eg.pfr l' = some f)
    (h : FpOK (Cut Eg0 j S) s) : FpOK (Cut Eg j S) s := by
  have hfp' : (Cut Eg j S).fp = (Cut Eg0 j S).fp := by show Eg.fpOf j = Eg0.fpOf j; rw [hfp]
  refine ⟨fun t ht => h.1 t (hfp' ▸ ht), fun t m ht hm => ?_⟩
  have h0 := h.2 t m (hfp' ▸ ht) hm
  rcases hvis m.loc.label with hp | ⟨f, hp⟩
  · exact (Vis_congr (E := Cut Eg0 j S) (E' := Cut Eg j S)
      (by show cutSto Eg j _ = cutSto Eg0 j _; rw [hcs]) rfl hp).2 h0
  · intro hpv; have h2 : Eg.pfr m.loc.label = none := hpv.2
    rw [hp] at h2; cases h2

/-- (S5) Planting the labels of `L` one at a time, then the set `Q` at once, is the ghost plant. -/
theorem plantS_plantL_eq {Eg : GEnv} {Fm : AllocLabel → Ts} {Nm : AllocLabel → Nat} {P : AllocLabel → Option Ts}
    {N : AllocLabel → Nat} {L : List AllocLabel} {Q : AllocLabel → Prop}
    (hL : ∀ l, l ∈ L ↔ P l ≠ none ∧ ¬ Q l) (hQ : ∀ l, Q l → P l ≠ none)
    (hF : ∀ l f, P l = some f → Fm l = f) (hN : ∀ l, P l ≠ none → Nm l = max (Eg.ini l) (N l)) :
    plantS (plantL Eg Fm Nm L) Q Fm Nm = plantG Eg P N := by
  classical
  have e1 : ∀ l, (plantS (plantL Eg Fm Nm L) Q Fm Nm).ini l = (plantG Eg P N).ini l := fun l => by
    by_cases hq : Q l
    · have hp := hQ l hq
      obtain ⟨f, e⟩ := Option.ne_none_iff_exists'.mp hp
      simp only [plantS, hq, ite_true, plantG, e]; exact hN l hp
    · simp only [plantS, hq, ite_false, plantG]
      cases e : P l with
      | none => exact (plantL_out (fun h => ((hL l).1 h).1 e)).1
      | some f =>
        have hl := (hL l).2 ⟨by rw [e]; exact Option.some_ne_none _, hq⟩
        rw [plantL_ini_in hl, hN l (by rw [e]; exact Option.some_ne_none _)]
  have e2 : ∀ l, (plantS (plantL Eg Fm Nm L) Q Fm Nm).pfr l = (plantG Eg P N).pfr l := fun l => by
    by_cases hq : Q l
    · have hp := hQ l hq
      obtain ⟨f, e⟩ := Option.ne_none_iff_exists'.mp hp
      simp only [plantS, hq, ite_true, plantG, e]; rw [hF l f e]
    · simp only [plantS, hq, ite_false, plantG]
      cases e : P l with
      | none => exact (plantL_out (fun h => ((hL l).1 h).1 e)).2
      | some f =>
        rw [plantL_in ((hL l).2 ⟨by rw [e]; exact Option.some_ne_none _, hq⟩), hF l f e]
  have hs := plantL_shape Eg Fm Nm L
  have hi : (plantS (plantL Eg Fm Nm L) Q Fm Nm).ini = (plantG Eg P N).ini := funext e1
  have hp : (plantS (plantL Eg Fm Nm L) Q Fm Nm).pfr = (plantG Eg P N).pfr := funext e2
  revert hi hp
  unfold plantS plantG
  rw [hs]
  intro hi hp
  simp only at hi hp ⊢
  rw [hi, hp]

/-! ## (S6) The per-label facts of a planted copyable buffer of single-word units -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **Shared master of `unitFacts` and `r1Facts`**: the facts at a new-slot label `l`
of an array type, with the element-specific conjunct `Z cl N e us` supplied by `hZ`. -/
theorem slotFacts (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop} {l : AllocLabel}
    {Z : Cell → Nat → Ty → List Acc → Prop}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hS : ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hm0 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf c.mem c.pairs th))
    (hH0 : MemHeldP (Cut Eg j S) (stOf c.mem c.pairs th) (HP j))
    (hTE1 : ThInvE p (Cut Eg j S) (thP th c.mem.size))
    (hm1 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)))
    (hpl0 : TermPlantF.plantOf c Eg j a v w l ≠ none)
    (hU : ∀ cl, Eg.sto l = some cl → ∃ N e us, cl.ty = .array (.lit N) e ∧ accs e = some us)
    (hR1w : ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e → accs e = some us →
      ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises)
    {Eg1 EgF : GEnv} (A : PAgree Eg Eg1 j l)
    (hF : Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S =
      Cut EgF j S)
    (hFi : EgF.ini l = max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hZ : ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e → accs e = some us →
      max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ≤ N →
      (∀ b S', SegOf cl.ty b S' → accs S' ≠ none → TearOK S') → Ty.noOwnIn [] cl.ty = true →
      Clo e → tb 0 e = true → Z cl N e us) :
    ∃ cl N e us, Eg1.sto l = some cl ∧ cl.owner = some j ∧ Eg1.pfr l = none ∧
      cl.ty = .array (.lit N) e ∧ accs e = some us ∧ Eg1.rini l ≤ Eg1.ini l ∧
      Eg1.ini l ≤ max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ∧
      max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ≤ N ∧
      FlipOK (Cut Eg1 j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) l ∧
      (∀ o, Eg1.ini l * nWords us ≤ o → o < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
        ∃ h, FirstW (c.mem.push ⟨a, v, w⟩) ⟨l, o⟩ h ∧
          ∀ t m', h < t → (c.mem.push ⟨a, v, w⟩)[t]? = some m' → m'.loc = ⟨l, o⟩ →
            t ∈ (thP th c.mem.size).promises ++ Eg1.fpOf j) ∧
      Z cl N e us ∧
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
  obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X hpl
  obtain ⟨cl, hcl, ho, hnone, -, hcpl, hcT, hnT, hrT⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  obtain ⟨N, e, us, hTc, hu⟩ := hU cl hcl
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hb : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => X.inv.plt j th t X.hth ht
  have hEsto : (Cut Eg j S).sto l = some cl := cutSto_own hcl ho
  have hPsto : (TermPlantF.cutP Eg j).sto l = some cl := cutSto_own hcl ho
  have hpriv : Priv (Cut Eg j S) l := ⟨⟨cl, hEsto, ho⟩, hnone⟩
  have hcap : Eg.ini l ≤ N := iniCap_of_heldP hH0 hpriv hEsto hTc
  have hkN : NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l ≤ N := NpZ_le hPsto hTc
  have hNl : max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ≤ N := by
    rw [plantN_eq l X]; exact Nat.max_le.2 ⟨hcap, hkN⟩
  have hpa1 : PromAbove (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) := by
    have h1 := TermTyped.certified_promAboveSt X.cert hpi.2.1
    rw [hpi.2.2] at h1
    exact h1
  have hpa0 : PromAbove (stOf c.mem c.pairs th) := fun t ht m hm =>
    hpa1 t (List.mem_append_left _ ht) m (by
      show (c.mem.push ⟨a, v, w⟩)[t]? = some m
      rw [getElem_push_lt (hb t ht)]; exact hm)
  have hk : PrefixHeld (Cut Eg j S) (stOf c.mem c.pairs th) l cl
      (NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l) := PrefixHeld_NpZ hPsto
  obtain ⟨-, -, h3, h4⟩ := plant_holdF (E := Cut Eg j S)
    (E' := Cut (plant1 Eg l (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
      (max (Eg.ini l) (NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l))) j S)
    hm0 hEsto ho hnone hpa0
    (fun Na e' us hT _ => by
      rw [hTc] at hT; cases hT
      rw [Cut_plant1_ini]; exact Nat.max_le.2 ⟨hcap, hkN⟩)
    (held_of_prefix hk Cut_plant1_ini)
  have hFE : plantF (Cut Eg j S) (stOf c.mem c.pairs th) l =
      plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l := plantF_congrE fun _ _ => Iff.rfl
  rw [hFE] at h3 h4
  have hi1 : Eg1.ini l = Eg.ini l := A.ini
  have hclo : Clo cl.ty := X.inv.clo l cl hcl
  have htb : tb 0 e = true := by have := hclo.1; rw [hTc] at this; simpa [tb] using this
  have hCe : Clo e := by
    refine ⟨htb, fun ρ W e' f => ?_⟩
    have := hclo.2 ρ W e' f; rw [hTc] at this; simp only [TermClose.cl, Ty.array.injEq] at this; exact this.2
  have hFi' : (Cut EgF j S).ini l = (Cut (plant1 Eg l (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
      (max (Eg.ini l) (NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l))) j S).ini l := by
    rw [Cut_plant1_ini]; show EgF.ini l = _; rw [hFi, plantN_eq l X]
  have hi1' : (Cut Eg1 j S).ini l = (Cut Eg j S).ini l := hi1
  refine ⟨cl, N, e, us, by rw [A.sto]; exact hcl, ho, by rw [A.pfr]; exact hnone, hTc, hu,
    by rw [A.rini, hi1]; exact X.inv.rle l, by rw [hi1]; exact Nat.le_max_left _ _, hNl,
    FlipOK_agree A (flipOK_post (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hS hTE1 hm1 l), fun o h1 h2 => ?_,
    hZ cl N e us hcl hTc hu hNl hcpl hnT hCe htb,
    (h3.imp id (HoldW_prom hb)).imp id (HoldW_agree A), ?_, fun b S' us' hs ha hI hnI => ?_,
    hcpl, hcT, hnT, hrT⟩
  · rw [hi1] at h1
    obtain ⟨hh, hfw, -, hab⟩ := firstW_of_R1w (hR1w cl N e us hcl hTc hu o h1 h2)
    exact ⟨hh, hfw, fun t m' a1 a2 a3 => List.mem_append_left _ (hab t m' a1 a2 a3)⟩
  · have H := hhold_prom (a := a) (v := v) (w := w) (Q := fun o => InitR _ cl l o ∧ ¬ InitR _ cl l o)
      (fun o hQ => h4 o hQ.1 hQ.2)
    intro o h1 h2
    exact H o ⟨(InitR_iff hFi').1 h1, fun h => h2 ((InitR_iff hi1').2 h)⟩
  · have hI : IniSeg (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        j S) cl l b := by rw [hF]; exact hI
    obtain ⟨ws, hv, hl⟩ := hInh X j S l f cl b S' us' hpl hcl hs ha (fun h => hnI ((IniSeg_iff hi1').2 h)) hI
    rw [hF] at hv
    exact ⟨ws, hv, hl⟩

/-- (S6) **The facts at a new-slot unit-buffer label `l`** after the promise, at a partial plant
`Eg1` agreeing with `Eg` at `l`, against the final environment `EgF` (whose cut is the published
planted one): the hypotheses of `ThSysAt_plantS` and of `MemInv_plantSet` at `l`. -/
theorem unitFacts (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
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
    (hU : ∀ cl, Eg.sto l = some cl → UnitT cl.ty)
    (hR1w : ∀ cl N e us, Eg.sto l = some cl → cl.ty = .array (.lit N) e → accs e = some us →
      ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises)
    {Eg1 EgF : GEnv} (A : PAgree Eg Eg1 j l)
    (hF : Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S =
      Cut EgF j S)
    (hFi : EgF.ini l = max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ cl N e us, Eg1.sto l = some cl ∧ cl.owner = some j ∧ Eg1.pfr l = none ∧
      cl.ty = .array (.lit N) e ∧ accs e = some us ∧ Eg1.rini l ≤ Eg1.ini l ∧
      Eg1.ini l ≤ max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ∧
      max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) ≤ N ∧
      FlipOK (Cut Eg1 j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) l ∧
      (∀ o, Eg1.ini l * nWords us ≤ o → o < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
        ∃ h, FirstW (c.mem.push ⟨a, v, w⟩) ⟨l, o⟩ h ∧
          ∀ t m', h < t → (c.mem.push ⟨a, v, w⟩)[t]? = some m' → m'.loc = ⟨l, o⟩ →
            t ∈ (thP th c.mem.size).promises ++ Eg1.fpOf j) ∧
      (us = [] ∨ (dwf e = true ∧
      (∀ jj, Eg1.ini l ≤ jj → jj < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
        ∀ ws : List Word, ws.length = nWords us →
        (∀ i w', ws[i]? = some w' → ∃ h m, FirstW (c.mem.push ⟨a, v, w⟩) ⟨l, jj * nWords us + i⟩ h ∧
          (c.mem.push ⟨a, v, w⟩)[h]? = some m ∧ w' = mw m) →
          ValOfR (Cut EgF j S) e ws .zero) ∧
        (TermBlkZ.SkFree e = true ∨ (Clo e ∧ TermTv.mg e = true)))) ∧
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
  obtain ⟨N', e', us', hTc', hu', hone, hZ⟩ := hU cl hcl
  rw [hTc] at hTc'
  simp only [Ty.array.injEq, Idx.lit.injEq] at hTc'
  obtain ⟨rfl, rfl⟩ := hTc'
  obtain rfl : us = us' := Option.some.inj (hu.symm.trans hu')
  have hty := promTyL X hPO hNO hpl hcl
  have hsl : us ≠ [] → Ty.affineIn [] e = false → ∀ jj, Eg1.ini l ≤ jj → jj < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
      ∀ ws : List Word, ws.length = nWords us →
      (∀ i w', ws[i]? = some w' → ∃ h m, FirstW (c.mem.push ⟨a, v, w⟩) ⟨l, jj * nWords us + i⟩ h ∧
        (c.mem.push ⟨a, v, w⟩)[h]? = some m ∧ w' = mw m) →
        ValOfR (Cut EgF j S) e ws .zero := by
    intro hne haf jj h1 h2 ws hl hw
    rw [hi1] at h1
    have hjN : jj < N := Nat.lt_of_lt_of_le h2 hNl
    have hTO : TearOK e := hcpl _ e (Or.inr ⟨N, us, jj, hTc, hu, hjN, rfl⟩) (by rw [hu]; exact Option.some_ne_none _)
    -- each word of the slot is a word of a value of `e`
    have hwd : ∀ i, i < nWords us → ∃ ws0 x, ValOf (Cut EgF j S) e ws0 ∧ ws0.length = nWords us ∧
        ws0[i]? = some x ∧ ∀ y, ws[i]? = some y → WLe1 x y := by
      intro i hi
      have hwi : ∃ y, ws[i]? = some y := ⟨ws[i]'(by rw [hl]; exact hi), List.getElem?_eq_getElem _⟩
      obtain ⟨y, hy⟩ := hwi
      obtain ⟨h, m, hfw, hm, rfl⟩ := hw i y hy
      have r1 : Eg.ini l * nWords us ≤ jj * nWords us + i :=
        Nat.le_trans (Nat.mul_le_mul_right _ h1) (Nat.le_add_right _ _)
      have r2 : jj * nWords us + i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us := by
        have := Nat.mul_le_mul_right (nWords us) (Nat.succ_le_of_lt h2)
        rw [Nat.succ_mul] at this; omega
      obtain ⟨hh', hfw', hpr, -⟩ := firstW_of_R1w (hR1w cl N e us hcl hTc hu _ r1 r2)
      rw [FirstW_uniq hfw hfw'] at hm
      obtain ⟨⟨m1, hm1', hml1, -⟩, -⟩ := hfw'
      rw [hm] at hm1'; cases hm1'
      have hok := hty hh' m hpr hm (by rw [hml1])
      have hok2 := WordOK_transfer (Incl_pub_cut _ j S) hnT hok
      rw [hF, hTc, hml1] at hok2
      obtain ⟨ws0, x, hv0, hl0, hx, hle⟩ := WordOK_slot hu hi rfl hok2
      exact ⟨ws0, x, hv0, hl0, hx, fun y' hy' => by rw [hy] at hy'; cases hy'; exact hle⟩
    obtain ⟨vals, ⟨hvals, -⟩, hle⟩ :=
      TermTear.assemble (P := fun ws => ValOf (Cut EgF j S) e ws ∧ ws.length = nWords us)
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
          have e1 : jx = i := by omega
          subst e1
          rw [hx] at hx'; cases hx'; exact hle y hy)
        (by
          have h0 : 0 < nWords us := by
            rw [nWords_ones hone]; exact List.length_pos_iff.2 hne
          obtain ⟨ws0, -, hv0, hl0, -⟩ := hwd 0 h0
          exact ⟨ws0, hv0, hl0⟩)
    exact ValOfR_copy haf htb ⟨VR_up e _ vals ws hle hvals.1, Valid_vals e vals ws (WLe.vals hle) hvals.2⟩
  exact hZ.imp id (fun h => ⟨h.2.2.1, hsl h.1 h.2.1, h.2.2.2.imp id (fun hm => ⟨hCe, hm⟩)⟩)

end

/-! ## (S7) `ThSys_plantS`: word buffers and no-new-slot labels one at a time, unit buffers at once -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}

/-- The planted labels with new slots whose cell is a copyable buffer of single-word units. -/
def QU (c : Cfg) (Eg : GEnv) (j : Nat) (a : Address) (v : WeakMem.Val) (w : Ts) (l : AllocLabel) : Prop :=
  TermPlantF.plantOf c Eg j a v w l ≠ none ∧ ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l ∧
    ∃ cl, Eg.sto l = some cl ∧ UnitT cl.ty

/-! ## (S8) The `selfPlant` field from `ThSys_plantS` and two residual fields -/

/-- (residual, **PrivSlotFresh**) every new word of a planted single-word protocol buffer or
copyable word-free buffer of single-word units has one placeholder below and, otherwise, only
the promiser's promises (`hR1w`, per word). -/
def PrivSlotF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ l f, TermPlantF.plantOf c Eg j a v w l = some f → ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l →
      ∀ cl N e us, Eg.sto l = some cl → (WordBufT cl.ty ∨ UnitT cl.ty) → cl.ty = .array (.lit N) e →
      accs e = some us → ∀ i, Eg.ini l * nWords us ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) * nWords us →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises

/-- (residual, **selfPlantRest**) `selfPlant` at events planting a label with new slots
(`plantN > ini`) that is neither a single-word protocol buffer nor a copyable buffer of single-word units. -/
def SelfPlantRestF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    (∃ l f cl, TermPlantF.plantOf c Eg j a v w l = some f ∧ ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l ∧
      Eg.sto l = some cl ∧ ¬ WordBufT cl.ty ∧ ¬ UnitT cl.ty) →
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db'

end

end TermPlantS

#print axioms TermPlantS.WordOK_unit
#print axioms TermPlantS.ValOfR_copy
#print axioms TermPlantS.slotR_of_wordOK
#print axioms TermPlantS.HeldEntry_raiseU
#print axioms TermPlantS.MemHeld_raiseQ
#print axioms TermPlantS.PromCr_raiseQ
#print axioms TermPlantS.MemHeld_flipQ
#print axioms TermPlantS.PromCrK_liftQ
#print axioms TermPlantS.firstW_of_R1w
#print axioms TermPlantS.plantS_plantL_eq
#print axioms TermPlantS.slotFacts
#print axioms TermPlantS.unitFacts
#print axioms TermPlantS.nWords_ones
#print axioms TermPlantS.nWords_take_ones
#print axioms TermPlantS.slot_eq
#print axioms TermPlantS.WordOK_slot
#print axioms TermPlantS.HeldEntry_raiseZ
#print axioms TermPlantS.HeldEntry_raiseUR
