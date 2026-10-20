/-
The plant's `ini` raise for memory's holding: `MemHeld_raise`.
Against the s15 chain (TermStep).  Raising a buffer's reader-visible count
from `ini` to `ini'` adds, to memory's holding, the resources of the newly counted slots'
readings.
-/
import WeakCore.TermStep
namespace TermPlantR
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The words of slot `j` (slots of `k` words). -/
def slotW (vals : List Word) (j k : Nat) : List Word := (vals.drop (j * k)).take k

theorem slotW_congr {vals vals' : List Word} {n j k : Nat} (hj : j < n)
    (hpre : ∀ o, o < n * k → vals'[o]? = vals[o]?) : slotW vals' j k = slotW vals j k := by
  apply List.ext_getElem?
  intro i
  simp only [slotW, List.getElem?_take, List.getElem?_drop]
  by_cases hi : i < k
  · simp only [hi, ite_true]
    have : j * k + i < n * k := by
      have h1 : (j + 1) * k ≤ n * k := Nat.mul_le_mul_right k hj
      rw [Nat.succ_mul] at h1; omega
    exact hpre _ this
  · simp only [hi, ite_false]

/-- **Raising a buffer's count** from `n` to `n'`: the old slots keep their words; each new
slot `j` is a value of resources `Rf j`. -/
theorem BufOKR_raise {E E' : TEnv} {n n' nr N : Nat} {e : Ty} {us : List Acc} {T : Ty}
    {vals vals' : List Word} {R : Res} {Rf : Nat → Res}
    (h : BufOKR E n nr T vals R) (hT : T = .array (.lit N) e) (hu : accs e = some us)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hnn : n ≤ n') (hn' : n' ≤ N) (hlen : vals'.length = vals.length)
    (hpre : ∀ o, o < n * nWords us → vals'[o]? = vals[o]?)
    (hz : ∀ j, n ≤ j → j < n' → nWords us = 0 → Rf j = .zero)
    (hslot : ∀ j, n ≤ j → j < n' → ValOfR E' e (slotW vals' j (nWords us)) (Rf j)) :
    BufOKR E' n' nr T vals' (R + Res.sum ((List.range' n (n' - n)).map Rf)) := by
  obtain ⟨N0, e0, us0, Rs, hT0, hu0, -, hl, hRs, hR, hj⟩ := h
  rw [hT] at hT0; cases hT0
  rw [hu] at hu0; cases hu0
  refine ⟨N, e, us, Rs ++ (List.range' n (n' - n)).map Rf, hT, hu, hn', by rw [hlen]; exact hl,
    by simp only [List.length_append, List.length_map, List.length_range']; omega,
    by rw [hR, Res.sum_append], fun j Rj hjn hRj => ?_⟩
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


/-- The words `g (j*k) … g (j*k + k - 1)` of a tabulated list. -/
theorem slotW_map_range {g : Nat → Word} {M j k : Nat} (h : (j + 1) * k ≤ M) :
    slotW ((List.range M).map g) j k = (List.range k).map fun i => g (j * k + i) := by
  apply List.ext_getElem?
  intro i
  simp only [slotW, List.getElem?_take, List.getElem?_drop, List.getElem?_map]
  by_cases hi : i < k
  · have : j * k + i < M := by rw [Nat.succ_mul] at h; omega
    simp only [hi, ite_true, List.getElem?_range this, List.getElem?_range hi, Option.map_some]
  · have h0 : (List.range k)[i]? = none :=
      List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hi)
    simp only [hi, ite_false, h0, Option.map_none]

/-- (Raise) Label `l`'s entry after raising its count from `E.ini l` to `E'.ini l`: off the
new slots' words memory reads as before (`hpa`); on them it reads `f` under `E'` (`hf`), and
each new slot is a value of resources `Rf j`. -/
theorem HeldEntry_raise {E E' : TEnv} {s : St} {l : AllocLabel} {R : Res} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} {f : Nat → Word} {Rf : Nat → Res}
    (h : HeldEntry E s l R) (hc : E.sto l = some c) (hc' : E'.sto l = some c)
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
    HeldEntry E' s l (R + Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf)) := by
  obtain ⟨-, hent⟩ := h
  obtain ⟨vals, hrd, hok⟩ := hent c hc
  have hb : BufOKR E (E.ini l) (E.rc l) c.ty vals R := by
    rcases hok with ⟨hw, -⟩ | hb
    · rw [hT] at hw; simp [wc, accs] at hw
    · exact hb
  have hl : vals.length = N * nWords us := by
    obtain ⟨N0, e0, us0, _, hT0, hu0, _, hl, _⟩ := hb
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
    refine BufOKR_raise (Rf := Rf) hb hT hu hv hini hN (by simp [hl]) (fun o ho => ?_) hz (fun j hj1 hj2 => ?_)
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

/-- **`MemHeld_raise`** (one label): raising `l`'s count adds the new slots' resources to
memory's holding (the other labels are untouched). -/
theorem MemHeld_raise {E E' : TEnv} {s : St} {H : Res} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} {f : Nat → Word} {Rf : Nat → Res}
    (h : MemHeld E s H) (hsto : ∀ l', E'.sto l' = E.sto l') (hini : ∀ l', l' ≠ l → E'.ini l' = E.ini l')
    (htid : E'.tid = E.tid) (hpf : ∀ l', E'.pfr l' = E.pfr l') (hfp : E'.fp = E.fp)
    (hri : ∀ l', E'.rini l' = E.rini l')
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hil : E.ini l ≤ E'.ini l) (hN : E'.ini l ≤ N) (hrc : E'.rc l = E.rc l)
    (hpa : ∀ o, ¬ (E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us) →
      PromAt E' s ⟨l, o⟩ = PromAt E s ⟨l, o⟩)
    (hf : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (f o))
    (hz : ∀ j, E.ini l ≤ j → j < E'.ini l → nWords us = 0 → Rf j = .zero)
    (hslot : ∀ j, E.ini l ≤ j → j < E'.ini l →
      ValOfR E' e ((List.range (nWords us)).map fun i => f (j * nWords us + i)) (Rf j)) :
    MemHeld E' s (H + Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf)) := by
  obtain ⟨R0, H0, rfl, he, hX⟩ := MemHeld_focus h l
  have hX' : MemHeldX E' s l H0 :=
    MemHeldX_tr hX (fun l' _ => hsto l') hini (fun _ _ _ _ hw => hw) hv
      (htid := htid) (hpf := fun l' _ => hpf l') (hfp := hfp) (hri := fun l' _ => hri l')
  have he' := HeldEntry_raise he hc (by rw [hsto]; exact hc) hT hu hv hil hN hrc hpa hf hz hslot
  have := MemHeld_unfocus hX' he'
  rwa [Res.add_assoc, Res.add_comm _ H0, ← Res.add_assoc] at this

theorem IniW_iff {E : TEnv} {l : AllocLabel} {o : Nat} {c : Cell} {N : Nat} {e : Ty} {us : List Acc}
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us) :
    IniW E ⟨l, o⟩ ↔ o < E.ini l * nWords us := by
  refine ⟨fun h => h c N e us hc hT hu, fun ho c' N' e' us' hc' hT' hu' => ?_⟩
  rw [hc] at hc'; cases hc'; rw [hT] at hT'; cases hT'; rw [hu] at hu'; cases hu'; exact ho

theorem IniWr_iff {E : TEnv} {l : AllocLabel} {o : Nat} {c : Cell} {N : Nat} {e : Ty} {us : List Acc}
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us) :
    IniWr E ⟨l, o⟩ ↔ o < E.rc l * nWords us := by
  refine ⟨fun h => h c N e us hc hT hu, fun ho c' N' e' us' hc' hT' hu' => ?_⟩
  rw [hc] at hc'; cases hc'; rw [hT] at hT'; cases hT'; rw [hu] at hu'; cases hu'; exact ho

/-- `PromAt` reads only the store, the thread, the frontiers, the foreign promises and the
two counts at the address. -/
theorem PromAt_congrE {E E' : TEnv} {s : St} {a : Address}
    (hs : E'.sto a.label = E.sto a.label) (ht : E'.tid = E.tid) (hp : E'.pfr a.label = E.pfr a.label)
    (hfp : E'.fp = E.fp) (hw : IniW E' a ↔ IniW E a) (hr : IniWr E' a ↔ IniWr E a) :
    PromAt E' s a = PromAt E s a := by
  have hvis := Vis_congr (l := a.label) hs ht hp
  have hV : VisU E' a = VisU E a := propext (by unfold VisU WordUnit; rw [hs, hvis])
  have hQ : PredU E' a = PredU E a := propext (by unfold PredU; rw [hp, hw, hr])
  have hF : FpAt E' a = FpAt E a := by
    unfold FpAt; rw [hfp]
    by_cases hv : Vis E a.label
    · simp only [hv, hvis.2 hv, ↓reduceIte]
    · simp only [hv, mt hvis.1 hv, ↓reduceIte]
  unfold PromAt; rw [hF]
  by_cases h1 : VisU E a
  · have h1' : VisU E' a := by rw [hV]; exact h1
    simp only [h1, h1', ↓reduceIte]
  · have h1' : ¬ VisU E' a := by rw [hV]; exact h1
    by_cases h2 : PredU E a
    · have h2' : PredU E' a := by rw [hQ]; exact h2
      simp only [h1, h1', h2, h2', ↓reduceIte]
    · have h2' : ¬ PredU E' a := by rw [hQ]; exact h2
      simp only [h1, h1', h2, h2', ↓reduceIte]

/-- (Raise, structured) `MemHeld_raise` at a buffer with a frontier whose real count is at most its
old one (`hrl`): the new slots' word units read as before (memory reads promises there), and
each non-word unit reads its first write, everything above which is a promise (`hR1`). -/
theorem MemHeld_raiseS {E E' : TEnv} {s : St} {H : Res} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} {Rf : Nat → Res}
    (h : MemHeld E s H) (hsto : ∀ l', E'.sto l' = E.sto l') (hini : ∀ l', l' ≠ l → E'.ini l' = E.ini l')
    (htid : E'.tid = E.tid) (hpf : ∀ l', E'.pfr l' = E.pfr l') (hfp : E'.fp = E.fp)
    (hri : ∀ l', E'.rini l' = E.rini l')
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hil : E.ini l ≤ E'.ini l) (hN : E'.ini l ≤ N) (hrl : E.rini l ≤ E.ini l) (hpfl : E.pfr l ≠ none)
    (hR1 : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us → ¬ WordUnit E ⟨l, o⟩ →
      ∃ h, FirstW s.mem ⟨l, o⟩ h ∧
        ∀ t m', h < t → s.mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ s.promises ++ E.fp)
    (hz : ∀ j, E.ini l ≤ j → j < E'.ini l → nWords us = 0 → Rf j = .zero)
    (hslot : ∀ j, E.ini l ≤ j → j < E'.ini l → ∀ ws : List Word, ws.length = nWords us →
      (∀ i w, ws[i]? = some w → LatestNP s.mem (PromAt E' s ⟨l, j * nWords us + i⟩) ⟨l, j * nWords us + i⟩ w) →
      ValOfR E' e ws (Rf j)) :
    MemHeld E' s (H + Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf)) := by
  have hc' : E'.sto l = some c := by rw [hsto]; exact hc
  have hrc : E'.rc l = E.rc l := by
    unfold TEnv.rc; rw [hri l]; omega
  have hrcE : E.rc l = E.rini l := by unfold TEnv.rc; omega
  have hvis : Vis E l := by
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hpfl; exact Vis_pfr hf
  have hvis' : Vis E' l := (Vis_congr (hsto l) htid (hpf l)).2 hvis
  have hpfl' : E'.pfr l ≠ none := by rw [hpf]; exact hpfl
  have hpa : ∀ o, ¬ (E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us) →
      PromAt E' s ⟨l, o⟩ = PromAt E s ⟨l, o⟩ := by
    intro o ho
    have h1 := Nat.mul_le_mul_right (nWords us) hil
    refine PromAt_congrE (hsto l) htid (hpf l) hfp ?_ ?_
    · rw [IniW_iff hc' hT hu, IniW_iff hc hT hu]; omega
    · rw [IniWr_iff hc' hT hu, IniWr_iff hc hT hu, hrc]
  -- every new unit has a reading under `E'`
  obtain ⟨R0, H0, -, he, -⟩ := MemHeld_focus h l
  obtain ⟨vals, hrd, hok⟩ := he.2 c hc
  have hl : vals.length = N * nWords us := by
    rcases hok with ⟨hw, -⟩ | hb
    · rw [hT] at hw; simp [wc, accs] at hw
    · obtain ⟨N0, e0, us0, _, hT0, hu0, _, hl, _⟩ := hb
      rw [hT] at hT0; cases hT0; rw [hu] at hu0; cases hu0; exact hl
  have hex : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      ∃ w, LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ w := by
    intro o h1 h2
    by_cases hwu : WordUnit E ⟨l, o⟩
    · -- a word unit: memory reads promises there under both
      have hV : VisU E ⟨l, o⟩ := ⟨hwu, hvis⟩
      have hV' : VisU E' ⟨l, o⟩ := ⟨by unfold WordUnit at hwu ⊢; rw [hsto]; exact hwu, hvis'⟩
      have hlt : o < vals.length := by
        have := Nat.mul_le_mul_right (nWords us) hN; omega
      have h3 := hrd o vals[o] (List.getElem?_eq_getElem hlt)
      rw [PromAt_word hV] at h3
      exact ⟨_, by rw [PromAt_word hV']; exact h3⟩
    · obtain ⟨hh, hfw, habove⟩ := hR1 o h1 h2 hwu
      have hwu' : ¬ VisU E' ⟨l, o⟩ := fun hv' => hwu (by
        have := hv'.1; unfold WordUnit at this ⊢; rw [hsto] at this; exact this)
      have hq : PredU E' ⟨l, o⟩ := by
        refine ⟨hpfl', (IniW_iff hc' hT hu).2 h2, fun hr => ?_⟩
        rw [IniWr_iff hc' hT hu, hrc, hrcE] at hr
        have := Nat.mul_le_mul_right (nWords us) hrl; omega
      obtain ⟨⟨m, hm, hml, -⟩, -⟩ := id hfw
      refine ⟨mw m, hh, m, ?_, hm, hml, rfl, fun t' m' hlt hm' hl' => ?_⟩
      · rw [mem_PromAt_pred hwu' hq]
        rintro ⟨-, h', hf', hlt'⟩
        rw [FirstW_uniq hf' hfw] at hlt'; exact Nat.lt_irrefl _ hlt'
      · rw [mem_PromAt_pred hwu' hq, FpAt_vis hvis', hfp]
        exact ⟨habove t' m' hlt hm' hl', hh, hfw, hlt⟩
  let f : Nat → Word := fun o =>
    if hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us then Classical.choose (hex o hh.1 hh.2)
    else default
  have hf : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us →
      LatestNP s.mem (PromAt E' s ⟨l, o⟩) ⟨l, o⟩ (f o) := by
    intro o h1 h2
    have hh : E.ini l * nWords us ≤ o ∧ o < E'.ini l * nWords us := ⟨h1, h2⟩
    simp only [f, hh, and_self, dite_true]
    exact Classical.choose_spec (hex o h1 h2)
  refine MemHeld_raise h hsto hini htid hpf hfp hri hc hT hu hv hil hN hrc hpa hf hz (fun j hj1 hj2 => ?_)
  refine hslot j hj1 hj2 _ (by simp) (fun i w hw => ?_)
  rw [List.getElem?_map] at hw
  by_cases hi : i < nWords us
  · rw [List.getElem?_range hi, Option.map_some, Option.some.injEq] at hw
    subst hw
    have h1 : E.ini l * nWords us ≤ j * nWords us := Nat.mul_le_mul_right _ hj1
    have h2 : (j + 1) * nWords us ≤ E'.ini l * nWords us := Nat.mul_le_mul_right _ hj2
    rw [Nat.succ_mul] at h2
    exact hf _ (Nat.le_trans h1 (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) h2)
  · have h0 : (List.range (nWords us))[i]? = none :=
      List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hi)
    rw [h0] at hw; cases hw

/-! ### The credits at the raise -/

theorem VRes_congrW {E E' : TEnv} {a : Address} (hs : E'.sto a.label = E.sto a.label) (ht : E'.tid = E.tid)
    (hp : E'.pfr a.label = E.pfr a.label) (hw : IniW E' a ↔ IniW E a) {w : Word} {R : Res} :
    VRes E' a w R ↔ VRes E a w R := by
  unfold VRes; rw [Vis_congr hs ht hp, WRes_congr hs, hw]

theorem DbRes_congrW {E E' : TEnv} {mem : Memory} {m : Msg} {tw : Ts} {R : Res}
    (hs : E'.sto m.loc.label = E.sto m.loc.label) (ht : E'.tid = E.tid)
    (hp : E'.pfr m.loc.label = E.pfr m.loc.label) (hw : IniW E' m.loc ↔ IniW E m.loc)
    (hr : IniWr E' m.loc ↔ IniWr E m.loc) (hb : ∀ l B, E.box l = some B → E'.box l = some B)
    (h : DbRes E mem m tw R) : DbRes E' mem m tw R := by
  have hD : DesigAt E' mem m.loc tw ↔ DesigAt E mem m.loc tw := by
    unfold DesigAt PredU; rw [hp, hw, hr, DStart_congr hs ht]
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨(Vis_congr hs ht hp).2 h1, hw.2 h2, fun hI => ?_,
      fun hI => (WRes_congr hs).2 (h4 hI)⟩
    obtain ⟨R₁, Z, hF, hS, hZ, hR⟩ := h3 hI
    exact ⟨R₁, Z, (FRes_congr hs).2 hF, fun h' => BlkDb_mono hs hb (hS (hD.1 h')),
      fun h' => hZ (fun h'' => h' (hD.2 h'')), hR⟩
  · exact Or.inr ⟨by rw [Vis_congr hs ht hp, hw]; exact h1, h2⟩

open Classical in
/-- The promises at a newly counted unit. -/
noncomputable def NewP (E E' : TEnv) (s : St) (tw : Ts) : Bool :=
  decide (∃ m, s.mem[tw]? = some m ∧ IniW E' m.loc ∧ ¬ IniW E m.loc)

theorem Res.sum_filter_split (f : Ts → Res) (q : Ts → Bool) : ∀ L : List Ts,
    Res.sum (L.map f) = Res.sum ((L.filter q).map f) + Res.sum ((L.filter (fun t => !q t)).map f)
  | [] => by simp
  | t :: L => by
      have ih := Res.sum_filter_split f q L
      cases hq : q t
      · simp only [List.filter_cons, hq, Bool.not_false, ite_true, List.map_cons, Res.sum_cons,
          Bool.false_eq_true, ite_false]
        rw [ih]; apply Res.ext; intro k; simp only [Res.add_apply]; omega
      · simp only [List.filter_cons, hq, Bool.not_true, ite_true, List.map_cons, Res.sum_cons,
          Bool.false_eq_true, ite_false]
        rw [ih]; apply Res.ext; intro k; simp only [Res.add_apply]; omega

theorem Res.sum_map_congr {f g : Ts → Res} : ∀ {L : List Ts}, (∀ t, t ∈ L → f t = g t) →
    Res.sum (L.map f) = Res.sum (L.map g)
  | [], _ => rfl
  | t :: L, h => by
      simp only [List.map_cons, Res.sum_cons]
      rw [h t (List.mem_cons_self ..), Res.sum_map_congr (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

/-- **`PromCr_raise`**: the credits after raising counts.  Off the newly counted units the
credits and debits are kept (`hold`); at them the old ones are zero, and the new ones are
given (`hnew`). -/
theorem PromCr_raise {E E' : TEnv} {s : St} {cr db cr' db' : Ts → Res} (hC : PromCr E s cr db)
    (hsto : ∀ l', E'.sto l' = E.sto l') (htid : E'.tid = E.tid) (hpf : ∀ l', E'.pfr l' = E.pfr l')
    (hmono : ∀ a, IniW E a → IniW E' a)
    (hrc : ∀ l', E'.rc l' = E.rc l') (hbx : ∀ l B, E.box l = some B → E'.box l = some B)
    (hnew : ∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → IniW E' m.loc → ¬ IniW E m.loc →
      DbRes E' s.mem m tw (db' tw) ∧ ((∃ w, PredAt s.mem m.loc tw w ∧ VRes E' m.loc w (cr' tw)) ∨
        ((∀ w, ¬ PredAt s.mem m.loc tw w) ∧ cr' tw = .zero)))
    (hold : ∀ tw, tw ∈ s.promises → NewP E E' s tw = false → cr' tw = cr tw ∧ db' tw = db tw) :
    PromCr E' s cr' db' ∧ ∀ tw, tw ∈ s.promises → NewP E E' s tw = true → cr tw = .zero ∧ db tw = .zero := by
  refine ⟨fun tw htw => ?_, fun tw htw hn => ?_⟩
  · obtain ⟨m, hm, hd, hcr⟩ := hC tw htw
    by_cases hN : IniW E' m.loc ∧ ¬ IniW E m.loc
    · exact ⟨m, hm, hnew tw m htw hm hN.1 hN.2⟩
    · have hn : NewP E E' s tw = false := by
        simp only [NewP, decide_eq_false_iff_not]
        rintro ⟨m', hm', h1, h2⟩; rw [hm] at hm'; cases hm'; exact hN ⟨h1, h2⟩
      obtain ⟨e1, e2⟩ := hold tw htw hn
      have hw : IniW E' m.loc ↔ IniW E m.loc := ⟨fun h => Classical.byContradiction fun h' => hN ⟨h, h'⟩, hmono _⟩
      have hr : IniWr E' m.loc ↔ IniWr E m.loc := by unfold IniWr; rw [hsto, hrc]
      refine ⟨m, hm, by rw [e2]; exact DbRes_congrW (hsto _) htid (hpf _) hw hr hbx hd, ?_⟩
      rw [e1]
      rcases hcr with ⟨w, hpw, hv⟩ | hz
      · exact Or.inl ⟨w, hpw, (VRes_congrW (hsto _) htid (hpf _) hw).2 hv⟩
      · exact Or.inr hz
  · simp only [NewP, decide_eq_true_eq] at hn
    obtain ⟨m', hm', -, h2⟩ := hn
    obtain ⟨m, hm, hd, hcr⟩ := hC tw htw
    rw [hm] at hm'; cases hm'
    refine ⟨?_, (DbRes_uninit h2).1 hd⟩
    rcases hcr with ⟨w, -, hv⟩ | ⟨-, hz⟩
    · exact (VRes_uninit h2).1 hv
    · exact hz

/-- The accounting at the raise: memory gains `X`; at the newly counted units the new
credits plus `X` are the new debits (`hacc`). -/
theorem acct_raise {E E' : TEnv} {s : St} {cr db cr' db' : Ts → Res} {H X : Res}
    (hz : ∀ tw, tw ∈ s.promises → NewP E E' s tw = true → cr tw = .zero ∧ db tw = .zero)
    (hold : ∀ tw, tw ∈ s.promises → NewP E E' s tw = false → cr' tw = cr tw ∧ db' tw = db tw)
    (hacc : X + Res.sum ((s.promises.filter (NewP E E' s)).map cr') =
      Res.sum ((s.promises.filter (NewP E E' s)).map db')) :
    (H + X) + pSum s cr' + pSum s db = H + pSum s cr + pSum s db' := by
  unfold pSum
  rw [Res.sum_filter_split cr' (NewP E E' s), Res.sum_filter_split db (NewP E E' s),
    Res.sum_filter_split cr (NewP E E' s), Res.sum_filter_split db' (NewP E E' s)]
  have z1 : Res.sum ((s.promises.filter (NewP E E' s)).map cr) = .zero := by
    rw [Res.sum_map_congr (g := fun _ => Res.zero) (fun t ht => by
      rw [List.mem_filter] at ht; exact (hz t ht.1 ht.2).1)]
    induction (s.promises.filter (NewP E E' s)) with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  have z2 : Res.sum ((s.promises.filter (NewP E E' s)).map db) = .zero := by
    rw [Res.sum_map_congr (g := fun _ => Res.zero) (fun t ht => by
      rw [List.mem_filter] at ht; exact (hz t ht.1 ht.2).2)]
    induction (s.promises.filter (NewP E E' s)) with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  have o1 : Res.sum ((s.promises.filter (fun t => !NewP E E' s t)).map cr') =
      Res.sum ((s.promises.filter (fun t => !NewP E E' s t)).map cr) :=
    Res.sum_map_congr fun t ht => by
      rw [List.mem_filter, Bool.not_eq_true'] at ht; exact (hold t ht.1 ht.2).1
  have o2 : Res.sum ((s.promises.filter (fun t => !NewP E E' s t)).map db') =
      Res.sum ((s.promises.filter (fun t => !NewP E E' s t)).map db) :=
    Res.sum_map_congr fun t ht => by
      rw [List.mem_filter, Bool.not_eq_true'] at ht; exact (hold t ht.1 ht.2).2
  rw [z1, z2, o1, o2, ← hacc]
  apply Res.ext; intro k; simp only [Res.add_apply, Res.zero_apply]; omega

/-! ### The telescope at a newly counted word unit -/

/-- Consecutive promises at a unit: each one's credit is what the one before it holds. -/
def ChainCr (g cr' db' : Ts → Res) : Ts → List Ts → Prop
  | _, [] => True
  | p, c :: r => db' c = g c ∧ cr' c = g p ∧ ChainCr g cr' db' c r

theorem tele_aux {g cr' db' : Ts → Res} : ∀ (p : Ts) (r : List Ts), ChainCr g cr' db' p r →
    Res.sum (r.map db') + g p = g ((p :: r).getLast (List.cons_ne_nil _ _)) + Res.sum (r.map cr')
  | p, [], _ => by simp
  | p, c :: r, ⟨h1, h2, h3⟩ => by
      have ih := tele_aux c r h3
      simp only [List.map_cons, Res.sum_cons, List.getLast_cons_cons] at ih ⊢
      rw [h1, h2]
      apply Res.ext; intro k
      have := congrArg (fun R => R k) ih
      simp only [Res.add_apply] at this ⊢; omega

/-- **The telescope**: the promises `c₀ < c₁ < …` at a newly counted word unit, `c₀`
initialising it (debit `g c₀ + w`, credit `0`), each later one crediting what the one before
holds.  Their debits are their credits plus what memory now reads there, `g` of the last,
plus the word's own `w`. -/
theorem tele_chain {g cr' db' : Ts → Res} {w : Res} {c0 : Ts} {r : List Ts}
    (h0 : db' c0 = g c0 + w) (hz : cr' c0 = .zero) (hc : ChainCr g cr' db' c0 r) :
    Res.sum ((c0 :: r).map db') = (g ((c0 :: r).getLast (List.cons_ne_nil _ _)) + w) +
      Res.sum ((c0 :: r).map cr') := by
  have := tele_aux c0 r hc
  simp only [List.map_cons, Res.sum_cons, h0, hz]
  apply Res.ext; intro k
  have := congrArg (fun R => R k) this
  simp only [Res.add_apply, Res.zero_apply] at this ⊢; omega

/-- Sums of resources over permuted lists agree. -/
theorem Res.sum_perm {f : Ts → Res} {L₁ L₂ : List Ts} (h : L₁.Perm L₂) :
    Res.sum (L₁.map f) = Res.sum (L₂.map f) := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.map_cons, Res.sum_cons, ih]
  | swap x y L =>
      simp only [List.map_cons, Res.sum_cons]
      apply Res.ext; intro k; simp only [Res.add_apply]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- The real count is kept by a raise of `ini` at a label whose `rini` is at most its `ini`. -/
theorem rc_raise {E E' : TEnv} {l : AllocLabel} (hini : ∀ l', l' ≠ l → E'.ini l' = E.ini l')
    (hri : ∀ l', E'.rini l' = E.rini l') (hil : E.ini l ≤ E'.ini l) (hrl : E.rini l ≤ E.ini l) :
    ∀ l', E'.rc l' = E.rc l' := by
  intro l'
  by_cases h : l' = l
  · subst h; unfold TEnv.rc; rw [hri]; omega
  · exact TEnv.rc_congr (hini l' h) (hri l')

/-- **`ThInvMC_raise`**: the raise of one planted buffer's count at the thread level.  The
typing and memory invariants at `E'` come from the plant (`Ext_withSto`, `MemInv_plantFN`);
memory's holding grows by the new slots (`MemHeld_raiseS`); the credits move by `PromCr_raise`
and the accounting by `hacc` (the telescope, `tele_chain`, at each new word unit). -/
theorem ThInvMC_raise {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Tot H : Res}
    {E E' : TEnv} {cr db cr' db' : Ts → Res} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} {Rf : Nat → Res}
    (hRE' : ThInvRE p E' th Tot) (hMI' : MemInv g E' (stOf mem pairs th))
    (hH : MemHeld E (stOf mem pairs th) H) (hC : PromCr E (stOf mem pairs th) cr db)
    (hsto : ∀ l', E'.sto l' = E.sto l') (hini : ∀ l', l' ≠ l → E'.ini l' = E.ini l')
    (htid : E'.tid = E.tid) (hpf : ∀ l', E'.pfr l' = E.pfr l') (hfp : E'.fp = E.fp)
    (hri : ∀ l', E'.rini l' = E.rini l')
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hil : E.ini l ≤ E'.ini l) (hN : E'.ini l ≤ N) (hrl : E.rini l ≤ E.ini l) (hpfl : E.pfr l ≠ none)
    (hR1 : ∀ o, E.ini l * nWords us ≤ o → o < E'.ini l * nWords us → ¬ WordUnit E ⟨l, o⟩ →
      ∃ h, FirstW mem ⟨l, o⟩ h ∧
        ∀ t m', h < t → mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ th.promises ++ E.fp)
    (hz : ∀ j, E.ini l ≤ j → j < E'.ini l → nWords us = 0 → Rf j = .zero)
    (hslot : ∀ j, E.ini l ≤ j → j < E'.ini l → ∀ ws : List Word, ws.length = nWords us →
      (∀ i w, ws[i]? = some w → LatestNP mem (PromAt E' (stOf mem pairs th) ⟨l, j * nWords us + i⟩)
        ⟨l, j * nWords us + i⟩ w) → ValOfR E' e ws (Rf j))
    (hnew : ∀ tw m, tw ∈ th.promises → mem[tw]? = some m → IniW E' m.loc → ¬ IniW E m.loc →
      DbRes E' mem m tw (db' tw) ∧ ((∃ w, PredAt mem m.loc tw w ∧ VRes E' m.loc w (cr' tw)) ∨
        ((∀ w, ¬ PredAt mem m.loc tw w) ∧ cr' tw = .zero)))
    (hold : ∀ tw, tw ∈ th.promises → NewP E E' (stOf mem pairs th) tw = false → cr' tw = cr tw ∧ db' tw = db tw)
    (hacc : Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf) +
      Res.sum ((th.promises.filter (NewP E E' (stOf mem pairs th))).map cr') =
      Res.sum ((th.promises.filter (NewP E E' (stOf mem pairs th))).map db'))
    (hbx : ∀ l B, E.box l = some B → E'.box l = some B) :
    ThInvMC p g mem pairs th Tot (H + Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf)) cr' db' ∧
      (H + Res.sum ((List.range' (E.ini l) (E'.ini l - E.ini l)).map Rf)) + pSum (stOf mem pairs th) cr' +
        pSum (stOf mem pairs th) db = H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
  have hmono : ∀ a, IniW E a → IniW E' a := by
    intro a ha c' N' e' us' hc' hT' hu'
    rw [hsto] at hc'
    have := ha c' N' e' us' hc' hT' hu'
    by_cases hl : a.label = l
    · rw [hl] at this ⊢; exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hil)
    · rw [hini _ hl]; exact this
  obtain ⟨hC', hzc⟩ := PromCr_raise hC hsto htid hpf hmono (rc_raise hini hri hil hrl) hbx hnew hold
  exact ⟨⟨E', hRE', hMI', MemHeld_raiseS hH hsto hini htid hpf hfp hri hc hT hu hv hil hN hrl hpfl hR1 hz hslot,
    hC'⟩, acct_raise hzc hold hacc⟩

/-- `TermStep.MemHeld_flipL`, also keeping the credits off the newly visible units. -/
theorem MemHeld_flipLH {g : G} {E E' : TEnv} {s : St} {H : Res} {cr db : Ts → Res} {l : AllocLabel}
    (hm : MemInv g E s) (hH : MemHeld E s H) (hC : PromCr E s cr db) (hpa : PromAbove s)
    (hs : ∀ l, E'.sto l = E.sto l) (hi : ∀ l, E'.ini l = E.ini l)
    (hmono : ∀ l, Vis E l → Vis E' l) (hl : ∀ l', l' ≠ l → Vis E' l' → Vis E l')
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E' T vs R)
    (hf : FlipOK E s l) (hfo : FpOK E s)
    (hol : OwnL E l) (hpm : ∀ l', E.pfr l' ≠ none → E'.pfr l' ≠ none)
    (hpo : ∀ l', l' ≠ l → E'.pfr l' ≠ none → E.pfr l' ≠ none)
    (hfp : E'.fp = E.fp := by first | rfl | assumption)
    (hri : ∀ l, E'.rini l = E.rini l := by first | exact fun _ => rfl | assumption)
    (htid : E'.tid = E.tid := by first | rfl | assumption)
    (hbx : ∀ l B, E.box l = some B → E'.box l = some B := by first | exact fun _ _ h => h | assumption) :
    ∃ H' cr' db', MemHeld E' s H' ∧ PromCr E' s cr' db' ∧
      (∀ t m, t ∈ s.promises → s.mem[t]? = some m → ¬ (VisU E' m.loc ∧ ¬ VisU E m.loc) →
        cr' t = cr t ∧ db' t = db t) ∧
      H' + pSum s cr' + pSum s db = H + pSum s cr + pSum s db' := by
  -- (U3) the flip creates no predicted unit: a private cell has no planted count
  have hq : ∀ a : Address, PredU E' a ↔ PredU E a := fun a => by
    have hrc' : E'.rc a.label = E.rc a.label := TEnv.rc_congr (hi _) (hri _)
    unfold PredU
    rw [IniW_congrU (hs _) (hi _), IniWr_congr (hs _) hrc']
    by_cases hv0 : E.pfr a.label = none
    · refine ⟨fun h => absurd h ?_, fun h => absurd hv0 h.1⟩
      rintro ⟨hpf', hiw, hnr⟩
      have hle : a.label = l := Classical.byContradiction fun hne => hpo _ hne hpf' hv0
      obtain ⟨c, hc, hown⟩ := hol
      rw [← hle] at hc
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
      have hle : m.loc.label = l := Classical.byContradiction fun h => hl _ h hv1.2 hpv
      obtain ⟨c, n, P, hsto, hat, hg, hini, hp, hin⟩ := hf (by rw [← hle]; exact hpv) t m ht hm' hle hwu hIW
      rw [← hle] at hsto
      obtain ⟨⟨c', hc', hown⟩, hpf0⟩ := hpv
      rw [hsto] at hc'
      obtain rfl : c = c' := Option.some.inj hc'
      refine ⟨⟨c, n, P, hsto, hat, hg, hini, hp, hin⟩, fun t' m' ht' hm'' hl' => ?_⟩
      -- a cell without a frontier has no planted count (`OwnHidP`'s second part)
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

/-- **The plant at a buffer, memory side** (`E → E₁ → E₂`): the flip (`MemHeld_flipL`, the
frontier) then the raise of the count (`MemHeld_raiseS`, `PromCr_raise`).  At the newly counted
units the credits and debits are `crN`/`dbN` (`hnew`), balancing memory's gain (`hacc`). -/
theorem MemHeld_plantN {g : G} {E E1 E2 : TEnv} {s : St} {H : Res} {cr db crN dbN : Ts → Res}
    {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc} {Rf : Nat → Res}
    (hm : MemInv g E s) (hH : MemHeld E s H) (hC : PromCr E s cr db) (hpa : PromAbove s)
    -- the flip
    (hs1 : ∀ l, E1.sto l = E.sto l) (hi1 : ∀ l, E1.ini l = E.ini l)
    (hmono : ∀ l, Vis E l → Vis E1 l) (hl : ∀ l', l' ≠ l → Vis E1 l' → Vis E l')
    (hv1 : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E1 T vs R)
    (hf : FlipOK E s l) (hfo : FpOK E s)
    (hol : OwnL E l) (hpm : ∀ l', E.pfr l' ≠ none → E1.pfr l' ≠ none)
    (hpo : ∀ l', l' ≠ l → E1.pfr l' ≠ none → E.pfr l' ≠ none)
    (hfp1 : E1.fp = E.fp) (hri1 : ∀ l, E1.rini l = E.rini l)
    (htid1 : E1.tid = E.tid) (hbx1 : ∀ l B, E.box l = some B → E1.box l = some B)
    -- the raise
    (hsto : ∀ l', E2.sto l' = E1.sto l') (hini : ∀ l', l' ≠ l → E2.ini l' = E1.ini l')
    (htid : E2.tid = E1.tid) (hpf : ∀ l', E2.pfr l' = E1.pfr l') (hfp : E2.fp = E1.fp)
    (hri : ∀ l', E2.rini l' = E1.rini l')
    (hc : E1.sto l = some c) (hT : c.ty = .array (.lit N) e) (hu : accs e = some us)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E1 T vs R → ValOfR E2 T vs R)
    (hil : E1.ini l ≤ E2.ini l) (hN : E2.ini l ≤ N) (hrl : E1.rini l ≤ E1.ini l) (hpfl : E1.pfr l ≠ none)
    (hR1 : ∀ o, E1.ini l * nWords us ≤ o → o < E2.ini l * nWords us → ¬ WordUnit E1 ⟨l, o⟩ →
      ∃ h, FirstW s.mem ⟨l, o⟩ h ∧
        ∀ t m', h < t → s.mem[t]? = some m' → m'.loc = ⟨l, o⟩ → t ∈ s.promises ++ E1.fp)
    (hbx : ∀ l B, E1.box l = some B → E2.box l = some B)
    (hz : ∀ j, E1.ini l ≤ j → j < E2.ini l → nWords us = 0 → Rf j = .zero)
    (hslot : ∀ j, E1.ini l ≤ j → j < E2.ini l → ∀ ws : List Word, ws.length = nWords us →
      (∀ i w, ws[i]? = some w → LatestNP s.mem (PromAt E2 s ⟨l, j * nWords us + i⟩) ⟨l, j * nWords us + i⟩ w) →
      ValOfR E2 e ws (Rf j))
    (hnew : ∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → IniW E2 m.loc → ¬ IniW E1 m.loc →
      DbRes E2 s.mem m tw (dbN tw) ∧ ((∃ w, PredAt s.mem m.loc tw w ∧ VRes E2 m.loc w (crN tw)) ∨
        ((∀ w, ¬ PredAt s.mem m.loc tw w) ∧ crN tw = .zero)))
    (hacc : Res.sum ((List.range' (E1.ini l) (E2.ini l - E1.ini l)).map Rf) +
      Res.sum ((s.promises.filter (NewP E1 E2 s)).map crN) =
      Res.sum ((s.promises.filter (NewP E1 E2 s)).map dbN)) :
    ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ PromCr E2 s cr2 db2 ∧
      (∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → m.loc.label ≠ l → cr2 tw = cr tw ∧ db2 tw = db tw) ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr + pSum s db2 := by
  obtain ⟨H1, cr1, db1, hH1, hC1, hk1, e1⟩ :=
    MemHeld_flipLH hm hH hC hpa hs1 hi1 hmono hl hv1 hf hfo hol hpm hpo hfp1 hri1 htid1 hbx1
  let cr2 : Ts → Res := fun t => if NewP E1 E2 s t then crN t else cr1 t
  let db2 : Ts → Res := fun t => if NewP E1 E2 s t then dbN t else db1 t
  have hold : ∀ tw, tw ∈ s.promises → NewP E1 E2 s tw = false → cr2 tw = cr1 tw ∧ db2 tw = db1 tw :=
    fun tw _ hn => by simp only [cr2, db2, hn, Bool.false_eq_true, ite_false, and_self]
  have hnew2 : ∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → IniW E2 m.loc → ¬ IniW E1 m.loc →
      DbRes E2 s.mem m tw (db2 tw) ∧ ((∃ w, PredAt s.mem m.loc tw w ∧ VRes E2 m.loc w (cr2 tw)) ∨
        ((∀ w, ¬ PredAt s.mem m.loc tw w) ∧ cr2 tw = .zero)) := by
    intro tw m htw hm' h1 h2
    have hn : NewP E1 E2 s tw = true := by
      simp only [NewP, decide_eq_true_eq]; exact ⟨m, hm', h1, h2⟩
    simp only [cr2, db2, hn, ite_true]
    exact hnew tw m htw hm' h1 h2
  have hacc2 : Res.sum ((List.range' (E1.ini l) (E2.ini l - E1.ini l)).map Rf) +
      Res.sum ((s.promises.filter (NewP E1 E2 s)).map cr2) =
      Res.sum ((s.promises.filter (NewP E1 E2 s)).map db2) := by
    have q1 : Res.sum ((s.promises.filter (NewP E1 E2 s)).map cr2) =
        Res.sum ((s.promises.filter (NewP E1 E2 s)).map crN) :=
      Res.sum_map_congr fun t ht => by
        rw [List.mem_filter] at ht; simp only [cr2, ht.2, ite_true]
    have q2 : Res.sum ((s.promises.filter (NewP E1 E2 s)).map db2) =
        Res.sum ((s.promises.filter (NewP E1 E2 s)).map dbN) :=
      Res.sum_map_congr fun t ht => by
        rw [List.mem_filter] at ht; simp only [db2, ht.2, ite_true]
    rw [q1, q2]; exact hacc
  have hmono2 : ∀ a, IniW E1 a → IniW E2 a := by
    intro a ha c' N' e' us' hc' hT' hu'
    rw [hsto] at hc'
    have := ha c' N' e' us' hc' hT' hu'
    by_cases hla : a.label = l
    · rw [hla] at this ⊢; exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hil)
    · rw [hini _ hla]; exact this
  obtain ⟨hC2, hzc⟩ := PromCr_raise hC1 hsto htid hpf hmono2 (rc_raise hini hri hil hrl) hbx hnew2 hold
  refine ⟨_, cr2, db2, MemHeld_raiseS hH1 hsto hini htid hpf hfp hri hc hT hu hv hil hN hrl hpfl hR1 hz hslot,
    hC2, fun tw m htw hm' hla => ?_, ?_⟩
  · have hn : NewP E1 E2 s tw = false := by
      simp only [NewP, decide_eq_false_iff_not]
      rintro ⟨m', hm'', h1, h2⟩
      rw [hm'] at hm''; cases hm''
      apply h2
      have e : IniW E2 m.loc ↔ IniW E1 m.loc := by unfold IniW; rw [hsto, hini _ hla]
      exact e.1 h1
    obtain ⟨e1', e2'⟩ := hold tw htw hn
    have hv' : ¬ (VisU E1 m.loc ∧ ¬ VisU E m.loc) := fun ⟨h1, h2⟩ =>
      h2 ⟨(WordUnit_congr (hs1 _)).1 h1.1, hl _ hla h1.2⟩
    obtain ⟨e3, e4⟩ := hk1 tw m htw hm' hv'
    exact ⟨e1'.trans e3, e2'.trans e4⟩
  have e2 := acct_raise (H := H1) hzc hold hacc2
  apply Res.ext; intro k
  have a1 := congrArg (fun R => R k) e1
  have a2 := congrArg (fun R => R k) e2
  simp only [Res.add_apply] at a1 a2 ⊢; omega

/-! ### (C) The accounting at a newly counted single-word unit -/

open Classical in
/-- `t` is a message at `a` other than the placeholder `t0`. -/
noncomputable def AtA (mem : Memory) (a : Address) (t0 t : Ts) : Bool :=
  decide ((∃ m, mem[t]? = some m ∧ m.loc = a) ∧ t ≠ t0)

open Classical in
/-- What the word just below `t` at `a` holds (`0` if none). -/
noncomputable def PredR (mem : Memory) (a : Address) (P : Proto) (n : Nat) (t : Ts) : Res :=
  if h : ∃ w, PredAt mem a t w then wr P n (Classical.choose h).val else .zero

open Classical in
/-- The debit at a word unit under `DbRes`: what the promised word holds, plus the word's own
`w` if it initialises the unit. -/
noncomputable def DbW (mem : Memory) (a : Address) (P : Proto) (n : Nat) (w : Res) (t : Ts) : Res :=
  (match mem[t]? with | some m => wr P n m.val | none => .zero) + (if InitAt mem a t then w else .zero)

theorem PredR_eq {mem : Memory} {a : Address} {P : Proto} {n : Nat} {t : Ts} {w : Word}
    (h : PredAt mem a t w) : PredR mem a P n t = wr P n w.val := by
  have hx : ∃ w, PredAt mem a t w := ⟨w, h⟩
  simp only [PredR, hx, dite_true]
  rw [PredAt_uniq (Classical.choose_spec hx) h]

theorem PredR_none {mem : Memory} {a : Address} {P : Proto} {n : Nat} {t : Ts}
    (h : ∀ w, ¬ PredAt mem a t w) : PredR mem a P n t = .zero := by
  have hx : ¬ ∃ w, PredAt mem a t w := fun ⟨w, hw⟩ => h w hw
  simp only [PredR, hx, dite_false]

theorem PredAt_succ_at {mem : Memory} {a : Address} {B : Ts} {m : Msg} (hm : mem[B]? = some m)
    (hl : m.loc = a) : PredAt mem a (B + 1) (mw m) :=
  ⟨B, m, Nat.lt_succ_self B, hm, hl, rfl, fun _t' _ h1 h2 _ => absurd (Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h2)) (Nat.lt_irrefl _)⟩

theorem PredAt_succ_not {mem : Memory} {a : Address} {B : Ts} {w : Word}
    (hn : ∀ m, mem[B]? = some m → m.loc ≠ a) : PredAt mem a (B + 1) w ↔ PredAt mem a B w := by
  constructor
  · rintro ⟨t0, m, hlt, hm, hl, hw, hb⟩
    have hne : t0 ≠ B := fun e => by subst e; exact hn m hm hl
    exact ⟨t0, m, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) hne, hm, hl, hw,
      fun t' m' h1 h2 h3 => hb t' m' h1 (Nat.lt_succ_of_lt h2) h3⟩
  · rintro ⟨t0, m, hlt, hm, hl, hw, hb⟩
    refine ⟨t0, m, Nat.lt_succ_of_lt hlt, hm, hl, hw, fun t' m' h1 h2 h3 => ?_⟩
    by_cases e : t' = B
    · subst e; exact hn m' h3
    · exact hb t' m' h1 (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h2) e) h3

/-- **The unit telescope** by induction on a bound `B`: over the messages at `a` below `B`
other than the placeholder `t0` (all of them above it and not `.undef`), the debits `DbW` are
the credits `PredR` plus what the word just below `B` holds, plus `w` once any is there. -/
theorem unit_tele {mem : Memory} {a : Address} {t0 : Ts} {m0 : Msg} {P : Proto} {n : Nat} {w : Res}
    (hm0 : mem[t0]? = some m0) (hl0 : m0.loc = a) (hu0 : m0.val = .undef)
    (hcl : ∀ t m, mem[t]? = some m → m.loc = a → t ≠ t0 → t0 < t ∧ m.val ≠ .undef) :
    ∀ B : Nat,
      (((∃ t, t < B ∧ AtA mem a t0 t = true) → ∃ w', PredAt mem a B w' ∧ w'.val ≠ .undef) ∧
        ((¬ ∃ t, t < B ∧ AtA mem a t0 t = true) → ∀ w', PredAt mem a B w' → w'.val = .undef)) ∧
      Res.sum (((List.range B).filter (AtA mem a t0)).map (DbW mem a P n w)) =
        PredR mem a P n B + (if ∃ t, t < B ∧ AtA mem a t0 t = true then w else .zero) +
          Res.sum (((List.range B).filter (AtA mem a t0)).map (PredR mem a P n)) := by
  have hwu : wr P n .undef = .zero := by simp [wr, WordHolds]
  intro B
  induction B with
  | zero =>
      have hne : ¬ ∃ t, t < 0 ∧ AtA mem a t0 t = true := fun ⟨t, ht, _⟩ => Nat.not_lt_zero _ ht
      refine ⟨⟨fun h => absurd h hne, fun _ w' ⟨_, _, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩, ?_⟩
      have hp : PredR mem a P n 0 = .zero := PredR_none fun w' ⟨_, _, h, _⟩ => absurd h (Nat.not_lt_zero _)
      simp only [List.range_zero, List.filter_nil, List.map_nil, Res.sum_nil, hp, hne, ite_false,
        Res.zero_add]
  | succ B ih =>
      obtain ⟨⟨ihE, ihN⟩, ihS⟩ := ih
      rw [List.range_succ, List.filter_append, List.map_append, List.map_append, Res.sum_append, Res.sum_append]
      by_cases hB : AtA mem a t0 B = true
      · -- a message at `a` above the placeholder
        have hB' := hB
        simp only [AtA, decide_eq_true_eq] at hB'
        obtain ⟨⟨m, hm, hl⟩, hne0⟩ := hB'
        have hpB := PredAt_succ_at hm hl
        have hex : ∃ t, t < B + 1 ∧ AtA mem a t0 t = true := ⟨B, Nat.lt_succ_self B, hB⟩
        have hnu : m.val ≠ .undef := (hcl B m hm hl hne0).2
        refine ⟨⟨fun _ => ⟨mw m, hpB, hnu⟩, fun h => absurd hex h⟩, ?_⟩
        simp only [List.filter_cons, hB, ite_true, List.filter_nil, List.map_cons, List.map_nil,
          Res.sum_cons, Res.sum_nil, Res.add_zero, hex, ite_true, PredR_eq hpB, ihS]
        have hdb : DbW mem a P n w B = wr P n m.val + (if ∃ t, t < B ∧ AtA mem a t0 t = true then .zero else w) := by
          simp only [DbW, hm]
          congr 1
          by_cases hE : ∃ t, t < B ∧ AtA mem a t0 t = true
          · obtain ⟨w', hw', hwu'⟩ := ihE hE
            have hni : ¬ InitAt mem a B := fun hi => hwu' (hi w' hw')
            simp only [hni, hE, ite_true, ite_false]
          · have hi : InitAt mem a B := ihN hE
            simp only [hi, hE, ite_true, ite_false]
        rw [hdb, show (mw m).val = m.val from rfl]
        apply Res.ext; intro k
        by_cases hE : ∃ t, t < B ∧ AtA mem a t0 t = true
        · simp only [hE, ite_true, Res.add_apply, Res.zero_apply]; omega
        · simp only [hE, ite_false, Res.add_apply, Res.zero_apply]; omega
      · have hBf : AtA mem a t0 B = false := by simpa using hB
        have hiff : (∃ t, t < B + 1 ∧ AtA mem a t0 t = true) ↔ (∃ t, t < B ∧ AtA mem a t0 t = true) :=
          ⟨fun ⟨t, h1, h2⟩ => ⟨t, by
            rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
            · exact h
            · subst h; exact absurd h2 hB, h2⟩, fun ⟨t, h1, h2⟩ => ⟨t, by omega, h2⟩⟩
        simp only [List.filter_cons, hBf, Bool.false_eq_true, ite_false, List.filter_nil, List.map_nil,
          Res.sum_nil, Res.add_zero]
        by_cases ht0 : B = t0
        · -- the placeholder itself: nothing at `a` below it
          subst ht0
          have hE : ¬ ∃ t, t < B ∧ AtA mem a B t = true := fun ⟨t, h1, h2⟩ => by
            simp only [AtA, decide_eq_true_eq] at h2
            obtain ⟨⟨m, hm, hl⟩, hne⟩ := h2
            exact Nat.lt_asymm h1 (hcl t m hm hl hne).1
          have hE' : ¬ ∃ t, t < B + 1 ∧ AtA mem a B t = true := fun h => hE (hiff.1 h)
          have hp1 : PredR mem a P n (B + 1) = .zero := by
            rw [PredR_eq (PredAt_succ_at hm0 hl0), show (mw m0).val = m0.val from rfl, hu0]; exact hwu
          have hp0 : PredR mem a P n B = .zero := by
            by_cases hx : ∃ w', PredAt mem a B w'
            · obtain ⟨w', hw'⟩ := hx; rw [PredR_eq hw', ihN hE w' hw']; exact hwu
            · exact PredR_none fun w' hw' => hx ⟨w', hw'⟩
          refine ⟨⟨fun h => absurd h hE', fun _ w' hw' => ?_⟩, ?_⟩
          · rw [PredAt_uniq hw' (PredAt_succ_at hm0 hl0)]; exact hu0
          · rw [ihS, hp0, hp1]; simp only [hE, hE', ite_false]
        · have hn : ∀ m, mem[B]? = some m → m.loc ≠ a := fun m hm hl => hB (by
            simp only [AtA, decide_eq_true_eq]; exact ⟨⟨m, hm, hl⟩, ht0⟩)
          have hpe : PredR mem a P n (B + 1) = PredR mem a P n B := by
            by_cases hx : ∃ w', PredAt mem a B w'
            · obtain ⟨w', hw'⟩ := hx
              rw [PredR_eq hw', PredR_eq ((PredAt_succ_not hn).2 hw')]
            · rw [PredR_none fun w' hw' => hx ⟨w', hw'⟩,
                PredR_none fun w' hw' => hx ⟨w', (PredAt_succ_not hn).1 hw'⟩]
          refine ⟨⟨fun h => ?_, fun h w' hw' => ihN (fun h' => h (hiff.2 h')) w' ((PredAt_succ_not hn).1 hw')⟩, ?_⟩
          · obtain ⟨w', hw', hu'⟩ := ihE (hiff.1 h); exact ⟨w', (PredAt_succ_not hn).2 hw', hu'⟩
          · rw [ihS, hpe]; simp only [hiff]

/-- A resource sum over `J` of a value at its one matching index. -/
theorem Res.sum_ind {x : Res} {q : Nat → Bool} : ∀ {J : List Nat}, J.Nodup →
    (∀ j j', j ∈ J → j' ∈ J → q j = true → q j' = true → j = j') →
    Res.sum (J.map fun j => if q j then x else .zero) = if (∃ j, j ∈ J ∧ q j = true) then x else .zero
  | [], _, _ => by simp
  | j :: J, hnd, hu => by
      have hnd' := (List.nodup_cons.mp hnd)
      have ih := Res.sum_ind (q := q) (x := x) hnd'.2 (fun a b ha hb => hu a b (List.mem_cons_of_mem _ ha)
        (List.mem_cons_of_mem _ hb))
      simp only [List.map_cons, Res.sum_cons, ih]
      by_cases hj : q j = true
      · have hn : ¬ ∃ j', j' ∈ J ∧ q j' = true := fun ⟨j', hj', hq⟩ =>
          hnd'.1 (by rw [hu j j' (List.mem_cons_self ..) (List.mem_cons_of_mem _ hj') hj hq]; exact hj')
        have hy : ∃ j', j' ∈ j :: J ∧ q j' = true := ⟨j, List.mem_cons_self .., hj⟩
        simp only [hj, hn, hy, ite_true, ite_false, Res.add_zero]
      · have he : (∃ j', j' ∈ j :: J ∧ q j' = true) ↔ (∃ j', j' ∈ J ∧ q j' = true) :=
          ⟨fun ⟨j', h1, h2⟩ => ⟨j', by
            rcases List.mem_cons.mp h1 with h | h
            · subst h; exact absurd h2 hj
            · exact h, h2⟩, fun ⟨j', h1, h2⟩ => ⟨j', List.mem_cons_of_mem _ h1, h2⟩⟩
        simp only [hj, Bool.false_eq_true, ite_false, Res.zero_add, he]

theorem Res.sum_map_zero : ∀ J : List Nat, Res.sum (J.map fun _ => Res.zero) = .zero
  | [] => rfl
  | _ :: J => by simp only [List.map_cons, Res.sum_cons, Res.zero_add]; exact Res.sum_map_zero J

/-- **Regrouping** a filtered sum by a partition indexed by `J`. -/
theorem Res.sum_regroup {f : Ts → Res} {q : Ts → Bool} {qj : Nat → Ts → Bool} {J : List Nat}
    (hnd : J.Nodup) (hu : ∀ t j j', j ∈ J → j' ∈ J → qj j t = true → qj j' t = true → j = j') :
    ∀ {L : List Ts}, (∀ t, t ∈ L → (q t = true ↔ ∃ j, j ∈ J ∧ qj j t = true)) →
      Res.sum ((L.filter q).map f) = Res.sum (J.map fun j => Res.sum ((L.filter (qj j)).map f))
  | [], _ => by
      simp only [List.filter_nil, List.map_nil, Res.sum_nil]; exact (Res.sum_map_zero J).symm
  | t :: L, hL => by
      have ih := Res.sum_regroup (f := f) (q := q) hnd hu (L := L) (fun t' ht' => hL t' (List.mem_cons_of_mem _ ht'))
      have hsplit : (J.map fun j => Res.sum (((t :: L).filter (qj j)).map f)) =
          J.map fun j => (if qj j t then f t else .zero) + Res.sum ((L.filter (qj j)).map f) := by
        apply List.map_congr_left; intro j _
        by_cases h : qj j t = true
        · simp only [List.filter_cons, h, ite_true, List.map_cons, Res.sum_cons]
        · simp only [List.filter_cons, h, Bool.false_eq_true, ite_false, Res.zero_add]
      have hsum : ∀ (A B : Nat → Res) (J : List Nat), Res.sum (J.map fun j => A j + B j) =
          Res.sum (J.map A) + Res.sum (J.map B) := by
        intro A B J; induction J with
        | nil => simp
        | cons j J ih =>
            simp only [List.map_cons, Res.sum_cons, ih]
            apply Res.ext; intro k; simp only [Res.add_apply]; omega
      rw [hsplit, hsum, Res.sum_ind (q := fun j => qj j t) hnd (fun j j' hj hj' h1 h2 => hu t j j' hj hj' h1 h2), ← ih]
      have ht := hL t (List.mem_cons_self ..)
      by_cases hq : q t = true
      · simp only [List.filter_cons, hq, ite_true, List.map_cons, Res.sum_cons, ht.1 hq]
      · have hn : ¬ ∃ j, j ∈ J ∧ qj j t = true := fun h => hq (ht.2 h)
        simp only [List.filter_cons, hq, Bool.false_eq_true, ite_false, hn, Res.zero_add]

/-- A filtered sum over a duplicate-free list is a sum over any duplicate-free list with the
same members. -/
theorem Res.sum_nodup_eq {f : Ts → Res} {L₁ L₂ : List Ts} (h1 : L₁.Nodup) (h2 : L₂.Nodup)
    (he : ∀ t, t ∈ L₁ ↔ t ∈ L₂) : Res.sum (L₁.map f) = Res.sum (L₂.map f) := by
  apply Res.sum_perm
  rw [List.perm_iff_count]; intro t
  rw [List.Nodup.count h1, List.Nodup.count h2]
  by_cases ht : t ∈ L₁
  · simp only [ht, (he t).1 ht, ite_true]
  · simp only [ht, mt (he t).2 ht, ite_false]

/-! ### (C) The word-slot buffer: `hnew` and `hacc` -/

theorem AtOff_word_elem {T : Ty} {N n j : Nat} {P : Proto}
    (hT : T = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false) (hj : j < N) :
    AtOff T j (.word (.lit n) P) := by
  rw [hT]
  have := AtOff.elem (o := 0) (accs_word (r := .lit n) hP) hj (AtOff.here (Or.inl (by simp [accs, hP])))
  have e : j * nWords [Acc.one] + 0 = j := by rw [show nWords [Acc.one] = 1 from rfl]; omega
  rw [e] at this; exact this

theorem WordAt_elem {E : TEnv} {l : AllocLabel} {c : Cell} {N n j : Nat} {P : Proto}
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false)
    (hj : j < N) : WordAt E ⟨l, j⟩ n P :=
  ⟨c, hc, AtOff_word_elem hT hP hj, hP⟩

theorem WordAt_elem_uniq {E : TEnv} {l : AllocLabel} {c : Cell} {N n j : Nat} {P : Proto}
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false)
    (hj : j < N) {n' : Nat} {P' : Proto} (h : WordAt E ⟨l, j⟩ n' P') : n' = n ∧ P' = P := by
  obtain ⟨c', hc', hA, hP'⟩ := h
  rw [hc] at hc'; cases hc'
  obtain ⟨e1, e2⟩ := AtOff_word_uniq hP' hP hA (AtOff_word_elem hT hP hj)
  cases e1; exact ⟨rfl, e2⟩

theorem WRes_wr {E : TEnv} {a : Address} {n : Nat} {P : Proto} (hW : WordAt E a n P)
    (hu : ∀ n' P', WordAt E a n' P' → n' = n ∧ P' = P) (w : Word) : WRes E a w (wr P n w.val) := by
  by_cases hh : WordHolds P [w.val]
  · exact Or.inl ⟨n, P, hW, hh, by simp [wr, hh]⟩
  · refine Or.inr ⟨fun n' P' hW' => ?_, by simp [wr, hh]⟩
    obtain ⟨rfl, rfl⟩ := hu n' P' hW'; exact hh

open Classical in
/-- The new credit: what the word just below a promise at its unit holds. -/
noncomputable def CrN (mem : Memory) (P : Proto) (n : Nat) (t : Ts) : Res :=
  match mem[t]? with | some m => PredR mem m.loc P n t | none => .zero

open Classical in
/-- The new debit (`DbRes` at a word unit). -/
noncomputable def DbN (mem : Memory) (P : Proto) (n : Nat) (t : Ts) : Res :=
  match mem[t]? with | some m => DbW mem m.loc P n (wdW P n) t | none => .zero

/-- (H) At a non-ghost word-slot buffer the non-word part of a debit is nothing. -/
theorem blkDb_word_zero {E : TEnv} {mem : Memory} {a : Address} {c : Cell} {N n : Nat} {P : Proto}
    (hc : E.sto a.label = some c) (hT : c.ty = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false) :
    BlkDb E mem a .zero := by
  refine ⟨.zero, .zero, Or.inr ⟨fun U hB => ?_, rfl⟩, ?_, ?_⟩
  · obtain ⟨c', N', e', us', j, o, w, hc', hT', -, -, -, -, hat, hatom, -, -, hg⟩ := hB
    rw [hc] at hc'; cases hc'
    rw [hT] at hT'; cases hT'
    obtain ⟨-, rfl⟩ := AtOff_solid (Solid_word _ P) hatom.2 hat
    rw [hg _ _ rfl] at hP; cases hP
  · by_cases hS : SlotStart E a
    · refine Or.inl ⟨hS, c, N, .word (.lit n) P, [.one], [], [], E, hc, hT, accs_word hP,
        ?_, rfl, rfl, fun _ _ h => h, fun i U Ri h _ => by simp at h⟩
      have hw : wc (.word (.lit n) P) = some (0 + 1) := by
        simp [wc]; exact ⟨[.one], accs_word hP, rfl⟩
      exact ZwL.pos (t := .word (.lit n) P) (n := 0) ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩ hw
    · exact Or.inr ⟨hS, rfl⟩
  · apply Res.ext; intro k; cases k <;> simp [noOwnR]

/-- **`hnew` at a word-slot buffer**: at a newly counted unit the credit `CrN` and debit
`DbN` are what `PromCr` asks under `DbRes`. -/
theorem hnew_word {E : TEnv} {mem : Memory} {l : AllocLabel} {c : Cell} {N n : Nat} {P : Proto}
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false)
    (hvis : Vis E l) {tw : Ts} {m : Msg} (hm : mem[tw]? = some m) (hl : m.loc.label = l)
    (hj : m.loc.offset < N) (hI : IniW E m.loc) :
    DbRes E mem m tw (DbN mem P n tw) ∧ ((∃ w, PredAt mem m.loc tw w ∧ VRes E m.loc w (CrN mem P n tw)) ∨
      ((∀ w, ¬ PredAt mem m.loc tw w) ∧ CrN mem P n tw = .zero)) := by
  have ha : m.loc = ⟨l, m.loc.offset⟩ := by rw [← hl]
  have hW : WordAt E m.loc n P := by rw [ha]; exact WordAt_elem hc hT hP hj
  have hu : ∀ n' P', WordAt E m.loc n' P' → n' = n ∧ P' = P := fun n' P' h => by
    rw [ha] at h; exact WordAt_elem_uniq hc hT hP hj h
  have hv : Vis E m.loc.label := by rw [hl]; exact hvis
  refine ⟨Or.inl ⟨hv, hI, fun hi => ⟨DbN mem P n tw, .zero, ?_, fun _ => blkDb_word_zero
      (by rw [hl]; exact hc) hT hP, fun _ => rfl, (Res.add_zero _).symm⟩, fun hni => ?_⟩, ?_⟩
  · simp only [DbN, hm, DbW, hi, ite_true]
    exact Or.inl ⟨n, P, hW, rfl⟩
  · simp only [DbN, hm, DbW, hni, ite_false, Res.add_zero]
    exact WRes_wr hW hu (mw m)
  · by_cases hx : ∃ w, PredAt mem m.loc tw w
    · obtain ⟨w, hw⟩ := hx
      refine Or.inl ⟨w, hw, ?_⟩
      simp only [CrN, hm, PredR_eq hw]
      exact Or.inl ⟨hv, hI, WRes_wr hW hu w⟩
    · refine Or.inr ⟨fun w hw => hx ⟨w, hw⟩, ?_⟩
      simp only [CrN, hm]; exact PredR_none fun w hw => hx ⟨w, hw⟩

theorem Res.sum_map_add (A B : Nat → Res) : ∀ J : List Nat,
    Res.sum (J.map fun j => A j + B j) = Res.sum (J.map A) + Res.sum (J.map B)
  | [] => by simp
  | j :: J => by
      simp only [List.map_cons, Res.sum_cons, Res.sum_map_add A B J]
      apply Res.ext; intro k; simp only [Res.add_apply]; omega

open Classical in
/-- `t` is a message at `a`. -/
noncomputable def MsgAt (mem : Memory) (a : Address) (t : Ts) : Bool :=
  decide (∃ m, mem[t]? = some m ∧ m.loc = a)

/-- **`hacc` at a word-slot buffer** (`nWords = 1`): at each newly counted unit `⟨l, j⟩`, the
messages are the placeholder `t0 j` (no promise) and promises above it, not `.undef`, at
least one (`hR1w`).  Then memory's gain, what the latest word at each new unit holds plus the
word's own, balances the new credits and debits. -/
theorem hacc_word {E1 E2 : TEnv} {s : St} {l : AllocLabel} {n : Nat} {P : Proto} {us : List Acc}
    (hus : nWords us = 1) (hnd : s.promises.Nodup)
    (hnew : ∀ t, t ∈ s.promises → (NewP E1 E2 s t = true ↔
      ∃ m, s.mem[t]? = some m ∧ m.loc.label = l ∧ E1.ini l ≤ m.loc.offset ∧ m.loc.offset < E2.ini l))
    (hR1w : ∀ j, E1.ini l ≤ j → j < E2.ini l → ∃ t0 m0, s.mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧
      m0.val = .undef ∧ t0 ∉ s.promises ∧ (∃ t, AtA s.mem ⟨l, j⟩ t0 t = true) ∧
      ∀ t m, s.mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ s.promises) :
    Res.sum ((List.range' (E1.ini l) (E2.ini l - E1.ini l)).map
        fun j => PredR s.mem ⟨l, j⟩ P n s.mem.size + wdW P n) +
      Res.sum ((s.promises.filter (NewP E1 E2 s)).map (CrN s.mem P n)) =
      Res.sum ((s.promises.filter (NewP E1 E2 s)).map (DbN s.mem P n)) := by
  have _ := hus
  let J := List.range' (E1.ini l) (E2.ini l - E1.ini l)
  have hJ : J.Nodup := List.nodup_range' (s := E1.ini l) (n := E2.ini l - E1.ini l) 1 (by decide)
  have hmJ : ∀ j, j ∈ J ↔ E1.ini l ≤ j ∧ j < E2.ini l := fun j => by
    simp only [J, List.mem_range'_1]; omega
  have hu : ∀ t j j', j ∈ J → j' ∈ J → MsgAt s.mem ⟨l, j⟩ t = true → MsgAt s.mem ⟨l, j'⟩ t = true → j = j' := by
    intro t j j' _ _ h1 h2
    simp only [MsgAt, decide_eq_true_eq] at h1 h2
    obtain ⟨m, hm, hl⟩ := h1; obtain ⟨m', hm', hl'⟩ := h2
    rw [hm] at hm'; cases hm'; rw [hl] at hl'; cases hl'; rfl
  have hq : ∀ t, t ∈ s.promises → (NewP E1 E2 s t = true ↔ ∃ j, j ∈ J ∧ MsgAt s.mem ⟨l, j⟩ t = true) := by
    intro t ht
    rw [hnew t ht]
    constructor
    · rintro ⟨m, hm, hl, h1, h2⟩
      refine ⟨m.loc.offset, (hmJ _).2 ⟨h1, h2⟩, ?_⟩
      simp only [MsgAt, decide_eq_true_eq]; exact ⟨m, hm, by rw [← hl]⟩
    · rintro ⟨j, hj, hmj⟩
      simp only [MsgAt, decide_eq_true_eq] at hmj
      obtain ⟨m, hm, hl⟩ := hmj
      obtain ⟨h1, h2⟩ := (hmJ j).1 hj
      exact ⟨m, hm, by rw [hl], by rw [hl]; exact h1, by rw [hl]; exact h2⟩
  rw [Res.sum_regroup hJ hu hq, Res.sum_regroup hJ hu hq, ← Res.sum_map_add]
  apply congrArg Res.sum
  apply List.map_congr_left
  intro j hj
  obtain ⟨h1, h2⟩ := (hmJ j).1 hj
  obtain ⟨t0, m0, hm0, hl0, hu0, hnp, ⟨t1, ht1⟩, hcl⟩ := hR1w j h1 h2
  -- the unit's promises are its messages above the placeholder
  have heq : ∀ f : Ts → Res, Res.sum ((s.promises.filter (MsgAt s.mem ⟨l, j⟩)).map f) =
      Res.sum (((List.range s.mem.size).filter (AtA s.mem ⟨l, j⟩ t0)).map f) := by
    intro f
    apply Res.sum_nodup_eq (hnd.sublist (List.filter_sublist ..))
      ((List.nodup_range).sublist (List.filter_sublist ..))
    intro t
    simp only [List.mem_filter, List.mem_range, MsgAt, AtA, decide_eq_true_eq]
    constructor
    · rintro ⟨htp, m, hm, hl⟩
      exact ⟨lt_of_get hm, ⟨m, hm, hl⟩, fun e => hnp (e ▸ htp)⟩
    · rintro ⟨-, ⟨m, hm, hl⟩, hne⟩
      exact ⟨(hcl t m hm hl hne).2.2, m, hm, hl⟩
  have hcl' : ∀ t m, s.mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef :=
    fun t m hm hl hne => ⟨(hcl t m hm hl hne).1, (hcl t m hm hl hne).2.1⟩
  obtain ⟨-, hT⟩ := unit_tele (P := P) (n := n) (w := wdW P n) hm0 hl0 hu0 hcl' s.mem.size
  rw [heq, heq]
  have hcr : Res.sum (((List.range s.mem.size).filter (AtA s.mem ⟨l, j⟩ t0)).map (CrN s.mem P n)) =
      Res.sum (((List.range s.mem.size).filter (AtA s.mem ⟨l, j⟩ t0)).map (PredR s.mem ⟨l, j⟩ P n)) :=
    Res.sum_map_congr fun t ht => by
      simp only [List.mem_filter, AtA, decide_eq_true_eq] at ht
      obtain ⟨-, ⟨m, hm, hl⟩, -⟩ := ht
      simp only [CrN, hm, hl]
  have hdb : Res.sum (((List.range s.mem.size).filter (AtA s.mem ⟨l, j⟩ t0)).map (DbN s.mem P n)) =
      Res.sum (((List.range s.mem.size).filter (AtA s.mem ⟨l, j⟩ t0)).map (DbW s.mem ⟨l, j⟩ P n (wdW P n))) :=
    Res.sum_map_congr fun t ht => by
      simp only [List.mem_filter, AtA, decide_eq_true_eq] at ht
      obtain ⟨-, ⟨m, hm, hl⟩, -⟩ := ht
      simp only [DbN, hm, hl]
  have hex : ∃ t, t < s.mem.size ∧ AtA s.mem ⟨l, j⟩ t0 t = true := by
    refine ⟨t1, ?_, ht1⟩
    simp only [AtA, decide_eq_true_eq] at ht1
    obtain ⟨⟨m, hm, -⟩, -⟩ := ht1; exact lt_of_get hm
  rw [hcr, hdb, hT]
  simp only [hex, ite_true]

theorem PredAt_size_of_latest {mem : Memory} {a : Address} {w : Word} (h : LatestNP mem [] a w) :
    PredAt mem a mem.size w := by
  obtain ⟨t, m, -, hm, hl, hw, hn⟩ := h
  exact ⟨t, m, lt_of_get hm, hm, hl, hw, fun t' m' h1 _ h3 h4 => by have := hn t' m' h1 h3 h4; simp at this⟩

/-- **The plant of a word-slot buffer, memory side, discharged** (`(C)`, `nWords = 1`):
`MemHeld_plantN` with the credits `CrN`, debits `DbN` and memory's gain at each new unit
`PredR … + wdW` (what the latest word there holds, plus the word itself).  Remaining
hypotheses: the flip's, the raise's congruences, `hR1w` (each new unit: the placeholder then
own promises, at least one) and `hval` (R3: the reading is a value). -/
theorem MemHeld_plantW {g : G} {E E1 E2 : TEnv} {s : St} {H : Res} {cr db : Ts → Res}
    {l : AllocLabel} {c : Cell} {N n : Nat} {P : Proto}
    (hm : MemInv g E s) (hH : MemHeld E s H) (hC : PromCr E s cr db) (hpa : PromAbove s)
    (hs1 : ∀ l, E1.sto l = E.sto l) (hi1 : ∀ l, E1.ini l = E.ini l)
    (hmono : ∀ l, Vis E l → Vis E1 l) (hl : ∀ l', l' ≠ l → Vis E1 l' → Vis E l')
    (hv1 : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E T vs R → ValOfR E1 T vs R)
    (hf : FlipOK E s l) (hfo : FpOK E s)
    (hol : OwnL E l) (hpm : ∀ l', E.pfr l' ≠ none → E1.pfr l' ≠ none)
    (hpo : ∀ l', l' ≠ l → E1.pfr l' ≠ none → E.pfr l' ≠ none)
    (hfp1 : E1.fp = E.fp) (hri1 : ∀ l, E1.rini l = E.rini l)
    (htid1 : E1.tid = E.tid) (hbx1 : ∀ l B, E.box l = some B → E1.box l = some B)
    (hsto : ∀ l', E2.sto l' = E1.sto l') (hini : ∀ l', l' ≠ l → E2.ini l' = E1.ini l')
    (htid : E2.tid = E1.tid) (hpf : ∀ l', E2.pfr l' = E1.pfr l') (hfp : E2.fp = E1.fp)
    (hri : ∀ l', E2.rini l' = E1.rini l')
    (hc : E1.sto l = some c) (hT : c.ty = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR E1 T vs R → ValOfR E2 T vs R)
    (hil : E1.ini l ≤ E2.ini l) (hN : E2.ini l ≤ N) (hrl : E1.rini l ≤ E1.ini l) (hpfl : E1.pfr l ≠ none)
    (hbx : ∀ l B, E1.box l = some B → E2.box l = some B)
    (hnd : s.promises.Nodup)
    (hR1w : ∀ j, E1.ini l ≤ j → j < E2.ini l → ∃ t0 m0, s.mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧
      m0.val = .undef ∧ t0 ∉ s.promises ∧ (∃ t, AtA s.mem ⟨l, j⟩ t0 t = true) ∧
      ∀ t m, s.mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ s.promises)
    (hval : ∀ j, E1.ini l ≤ j → j < E2.ini l → ∀ w, LatestNP s.mem [] ⟨l, j⟩ w →
      ∃ R, ValOfR E2 (.word (.lit n) P) [w] R) :
    ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ PromCr E2 s cr2 db2 ∧
      (∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → m.loc.label ≠ l → cr2 tw = cr tw ∧ db2 tw = db tw) ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr + pSum s db2 := by
  have hu1 : accs (Ty.word (.lit n) P) = some [Acc.one] := accs_word hP
  have hc2 : E2.sto l = some c := by rw [hsto]; exact hc
  have hvis1 : Vis E1 l := by
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hpfl; exact Vis_pfr hf
  have hvis2 : Vis E2 l := (Vis_congr (hsto l) htid (hpf l)).2 hvis1
  have hk : nWords [Acc.one] = 1 := rfl
  -- off `l` the two counts agree
  have hIo : ∀ a : Address, a.label ≠ l → (IniW E2 a ↔ IniW E1 a) := fun a ha => by
    unfold IniW; rw [hsto, hini _ ha]
  have hIl : ∀ o, IniW E2 ⟨l, o⟩ ↔ o < E2.ini l := fun o => by
    rw [IniW_iff hc2 hT hu1, hk, Nat.mul_one]
  have hIl1 : ∀ o, IniW E1 ⟨l, o⟩ ↔ o < E1.ini l := fun o => by
    rw [IniW_iff hc hT hu1, hk, Nat.mul_one]
  have hnewc : ∀ (tw : Ts) (m : Msg), s.mem[tw]? = some m → IniW E2 m.loc → ¬ IniW E1 m.loc →
      m.loc.label = l ∧ E1.ini l ≤ m.loc.offset ∧ m.loc.offset < E2.ini l := by
    intro tw m _ h1 h2
    by_cases hla : m.loc.label = l
    · have ha : m.loc = ⟨l, m.loc.offset⟩ := by rw [← hla]
      rw [ha, hIl] at h1; rw [ha, hIl1] at h2
      exact ⟨hla, Nat.le_of_not_lt h2, h1⟩
    · exact absurd ((hIo _ hla).1 h1) h2
  refine MemHeld_plantN (us := [Acc.one]) (crN := CrN s.mem P n) (dbN := DbN s.mem P n)
    (Rf := fun j => PredR s.mem ⟨l, j⟩ P n s.mem.size + wdW P n)
    hm hH hC hpa hs1 hi1 hmono hl hv1 hf hfo hol hpm hpo hfp1 hri1 htid1 hbx1 hsto hini htid hpf hfp hri hc hT hu1 hv
    hil hN hrl hpfl ?_ hbx (fun _ _ _ h => absurd h (by decide)) ?_ ?_ ?_
  · -- every new unit is a word unit
    intro o h1 h2 hnw
    exfalso; apply hnw
    rw [hk, Nat.mul_one] at h2
    exact ⟨c, hc, Or.inl ⟨.lit n, P, hP, AtOff_word_elem hT hP (Nat.lt_of_lt_of_le h2 hN)⟩⟩
  · -- R3: the reading is the latest word, a value holding `PredR … + wdW`
    intro j h1 h2 ws hlen hrd
    rw [hk] at hlen
    match ws, hlen with
    | [w], _ =>
      have hWU : VisU E2 ⟨l, j * 1 + 0⟩ := ⟨⟨c, hc2, Or.inl ⟨.lit n, P, hP, by
        rw [Nat.mul_one, Nat.add_zero]; exact AtOff_word_elem hT hP (Nat.lt_of_lt_of_le h2 hN)⟩⟩, hvis2⟩
      have hr := hrd 0 w rfl
      rw [hk, PromAt_word hWU] at hr
      simp only [Nat.mul_one, Nat.add_zero] at hr
      obtain ⟨R, hR⟩ := hval j h1 h2 w hr
      have e := VRR_word_wr hR.1
      rw [PredR_eq (PredAt_size_of_latest hr), ← e]
      exact hR
  · intro tw m htw hm' h1 h2
    obtain ⟨hla, -, ho⟩ := hnewc tw m hm' h1 h2
    exact hnew_word hc2 hT hP hvis2 hm' hla (Nat.lt_of_lt_of_le ho hN) h1
  · refine hacc_word hk hnd (fun t _ => ?_) hR1w
    simp only [NewP, decide_eq_true_eq]
    constructor
    · rintro ⟨m, hm', h1, h2⟩; exact ⟨m, hm', hnewc t m hm' h1 h2⟩
    · rintro ⟨m, hm', hla, h1, h2⟩
      have ha : m.loc = ⟨l, m.loc.offset⟩ := by rw [← hla]
      refine ⟨m, hm', ?_, ?_⟩
      · rw [ha, hIl]; exact h2
      · rw [ha, hIl1]; exact Nat.not_lt.mpr h1

/-- **(selfPlant, B1) The plant of a word-slot buffer at the thread level**: the cell `l`
gets the frontier `F` and its reader-visible count rises to `Np` (`EgP`'s `plantF`/`plantN`,
one buffer).  Memory's holding and the credits move by an equality of totals.  Side
conditions per witness `η` (`hpl`): the plant's (`MemInv_plantFN`, `FlipOK`, `FpOK`), and at
each newly counted unit the placeholder-then-own-promises shape (`R1w`) and a value reading
(`R3`). -/
theorem ThInvMC_plantW {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Tot H : Res}
    {cr db : Ts → Res} {l : AllocLabel}
    (h : ThInvMC p g mem pairs th Tot H cr db) (hpa : PromAbove (stOf mem pairs th))
    (hpl : ∀ η : TEnv, ThInvRE p (CE η) th Tot → MemInv g (CE η) (stOf mem pairs th) →
      ∃ (c : Cell) (N n : Nat) (P : Proto) (F Np : Ts), η.sto l = some c ∧ c.owner = some η.tid ∧
        η.pfr l = none ∧ c.ty = .array (.lit N) (.word (.lit n) P) ∧ P.ghost = false ∧
        η.rini l ≤ η.ini l ∧ η.ini l ≤ Np ∧ Np ≤ N ∧
        (F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (CE η) (stOf mem pairs th) l F) ∧
        (η.ini l < Np → (stOf mem pairs th).vs.vWr ≤ F) ∧
        (∀ o, InitR (CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
            (fun l' => if l' = l then some F else η.pfr l') η.seen)) c l o → ¬ InitR (CE η) c l o →
          ∀ (t : Nat) (m : Msg), t ∉ th.promises → mem[t]? = some m → m.loc = ⟨l, o⟩ →
          ∃ (t' : Nat) (m' : Msg), t < t' ∧ t' ≤ F ∧ mem[t']? = some m' ∧ m'.loc = ⟨l, o⟩) ∧
        (∀ b S us, SegOf c.ty b S → accs S = some us →
          IniSeg (CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
            (fun l' => if l' = l then some F else η.pfr l') η.seen)) c l b → ¬ IniSeg (CE η) c l b →
          ∃ ws, ValOf (CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
            (fun l' => if l' = l then some F else η.pfr l') η.seen)) S ws ∧ ws.length = nWords us) ∧
        (∀ b S, SegOf c.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c.ty = true ∧
        Ty.noOwnIn [] c.ty = true ∧ rgnFree c.ty = true ∧
        FlipOK (CE η) (stOf mem pairs th) l ∧ FpOK (CE η) (stOf mem pairs th) ∧
        (∀ j, η.ini l ≤ j → j < Np → ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧
          m0.val = .undef ∧ t0 ∉ th.promises ∧ (∃ t, AtA mem ⟨l, j⟩ t0 t = true) ∧
          ∀ t m, mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ th.promises) ∧
        (∀ j, η.ini l ≤ j → j < Np → ∀ w, LatestNP mem [] ⟨l, j⟩ w →
          ∃ R, ValOfR (CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
            (fun l' => if l' = l then some F else η.pfr l') η.seen)) (.word (.lit n) P) [w] R)) :
    ∃ H' cr' db', ThInvMC p g mem pairs th Tot H' cr' db' ∧
      H' + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
  obtain ⟨E, hT, hm, hH, hC⟩ := h
  obtain ⟨ρ, η, cx, Rf, Rs, hE0, hE, hTy, htv, hFI, hsum⟩ := hT
  subst hE0
  obtain ⟨c, N, n, P, F, Np, hsto, hown, hnone, hTc, hP, hrl, hNp, hNN, hF, hFw, hhold, hinh, hcpl, hcT,
    hnT, hrT, hf, hfo, hR1w, hval⟩ := hpl η ⟨ρ, η, cx, Rf, Rs, rfl, hE, hTy, htv, hFI, hsum⟩ hm
  let P1 : AllocLabel → Option Ts := fun l' => if l' = l then some F else η.pfr l'
  let I2 : AllocLabel → Nat := fun l' => if l' = l then Np else η.ini l'
  have hP1 : ∀ l' f, η.pfr l' = some f → P1 l' = some f := fun l' f h => by
    by_cases he : l' = l
    · subst he; rw [hnone] at h; cases h
    · simp [P1, he, h]
  have hI2 : ∀ l', η.ini l' ≤ I2 l' := fun l' => by
    by_cases he : l' = l
    · subst he; simp [I2, hNp]
    · simp [I2, he]
  have hx : Ext η (η.withSto η.sto I2 P1 η.seen) :=
    Ext_withSto hE.2.1 (fun _ _ h => h) hI2 hP1
  have hE' : EnvOK p (η.withSto η.sto I2 P1 η.seen) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
  have hMI := MemInv_plantFN (E' := CE (η.withSto η.sto I2 P1 η.seen)) (N := Np) hm hsto hown hnone
    rfl rfl rfl rfl hNp hrl rfl rfl rfl hF hFw hhold hinh hcpl hcT hnT hrT
  have hnd : th.promises.Nodup := MemInv_nodup hm
  have hvisE : ∀ l', (CE (η.withSto η.sto η.ini P1 η.seen)).pfr l' = P1 l' := fun _ => rfl
  obtain ⟨H', cr', db', hH', hC', -, heq⟩ := MemHeld_plantW (E := CE η)
    (E1 := CE (η.withSto η.sto η.ini P1 η.seen)) (E2 := CE (η.withSto η.sto I2 P1 η.seen))
    (c := c) (N := N) (n := n) (P := P)
    hm hH hC hpa (fun _ => rfl) (fun _ => rfl)
    (fun l' hv hpr => hv ⟨hpr.1, by
      by_cases he : l' = l
      · subst he; have := hpr.2; simp [CE, TEnv.withSto, P1] at this
      · have := hpr.2; simpa [CE, TEnv.withSto, P1, he] using this⟩)
    (fun l' hne hv hpr => hv ⟨hpr.1, by simpa [CE, TEnv.withSto, P1, hne] using hpr.2⟩)
    (fun h => ValOfR_mono (η₁ := CE η) (η₂ := CE (η.withSto η.sto η.ini P1 η.seen)) rfl rfl
      (fun _ _ h => h) (fun _ => Nat.le_refl _) h hP1 (fun _ _ h => h) (fun _ => Nat.le_refl _))
    hf hfo ⟨c, hsto, hown⟩
    (fun l' hne => by
      by_cases he : l' = l
      · subst he; simp [CE, TEnv.withSto, P1]
      · simpa [CE, TEnv.withSto, P1, he] using hne)
    (fun l' hne h1 => by simpa [CE, TEnv.withSto, P1, hne] using h1)
    rfl (fun _ => rfl) rfl (fun _ _ h => h) (fun _ => rfl)
    (fun l' hne => by simp [CE, TEnv.withSto, I2, hne]) rfl (fun _ => rfl) rfl (fun _ => rfl)
    hsto hTc hP
    (fun h => ValOfR_mono (η₁ := CE (η.withSto η.sto η.ini P1 η.seen))
      (η₂ := CE (η.withSto η.sto I2 P1 η.seen)) rfl rfl (fun _ _ h => h) hI2 h (fun _ _ h => h)
      (fun _ _ h => h) (fun _ => Nat.le_refl _))
    (by simp [CE, TEnv.withSto, I2, hNp]) (by simp [CE, TEnv.withSto, I2, hNN]) hrl
    (by simp [CE, TEnv.withSto, P1]) (fun _ _ h => h) hnd
    (fun j h1 h2 => hR1w j h1 (by simpa [CE, TEnv.withSto, I2] using h2))
    (fun j h1 h2 => hval j h1 (by simpa [CE, TEnv.withSto, I2] using h2))
  exact ⟨H', cr', db', ⟨_, ⟨ρ, _, cx, Rf, Rs, rfl, hE', hTy, htv, FInvR_ext hE.2.1 hE.2.2 hx hFI, hsum⟩,
    hMI, hH', hC'⟩, heq⟩


/-! ### (F) The plant's `hval` from named facts: R1w, a holder at every new unit, and the
typing of the own promises at the planted cell. -/

/-- (F) A word of a buffer of non-ghost protocol words that `WordOK` admits is a state. -/
theorem WordOK_wordbuf {E : TEnv} {N n o : Nat} {P : Proto} {w : Word}
    (h : WordOK E (.array (.lit N) (.word (.lit n) P)) o w) (hg : P.ghost = false) :
    pwf P = true ∧ ∃ v, w.val = .num v ∧ InP P v := by
  obtain ⟨b, S, ws, o', w0, hS, hV, hw0, hle, -⟩ := h
  rcases hS with ⟨-, rfl, hacc⟩ | ⟨N', us, j, hT, -, -, -⟩
  · exact absurd rfl hacc
  · cases hT
    obtain ⟨⟨hvr, -⟩, -⟩ := hV
    obtain ⟨hp, hv⟩ := hvr
    obtain ⟨v, hvs, hin⟩ := hv hg
    rcases ws with _ | ⟨x, _ | ⟨y, ws⟩⟩
    · simp at hvs
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvs
      cases o' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw0
        subst hw0
        exact ⟨hp, v, by rw [← hle.1]; exact hvs, hin⟩
      | succ k => simp at hw0
    · simp at hvs

/-- (F) A protocol state gives the word's resource. -/
theorem hval_of_num {E : TEnv} {n : Nat} {P : Proto} {w : Word} (hp : pwf P = true)
    (h : ∃ v, w.val = .num v ∧ InP P v) : ∃ R, ValOfR E (.word (.lit n) P) [w] R :=
  ⟨_, VRR_word_of hp h, by simp [Valid]⟩

/-- (F) At a new unit shaped by R1w (one placeholder below, every other message an own
promise above it) that holds some own promise, memory's latest word is an own promise's. -/
theorem latest_prom {mem : Memory} {Pr : List Ts} {a : Address} {w : Word}
    (hR1 : ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = a ∧ m0.val = .undef ∧ t0 ∉ Pr ∧
      ∀ t m, mem[t]? = some m → m.loc = a → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ Pr)
    (hh : ∃ t m, t ∈ Pr ∧ mem[t]? = some m ∧ m.loc = a) (hl : LatestNP mem [] a w) :
    ∃ t m, t ∈ Pr ∧ mem[t]? = some m ∧ m.loc = a ∧ mw m = w := by
  obtain ⟨t, m, -, hm, hma, hw, hmax⟩ := hl
  obtain ⟨t0, m0, -, -, -, ht0, hall⟩ := hR1
  by_cases e : t = t0
  · subst e
    obtain ⟨t1, m1, ht1, hm1, hma1⟩ := hh
    have hne : t1 ≠ t := fun e => ht0 (e ▸ ht1)
    have := hmax t1 m1 (hall t1 m1 hm1 hma1 hne).1 hm1 hma1
    simp at this
  · exact ⟨t, m, (hall t m hm hma e).2.2, hm, hma, hw⟩

/-- (F) **`hval` from named facts**: R1w at each new unit, an own promise at each new unit
(BH1), and the own promises at `l` typed (`WordOK`, the plant's `promTy`). -/
theorem hval_of {E E0 : TEnv} {mem : Memory} {Pr : List Ts} {l : AllocLabel} {c : Cell}
    {N n : Nat} {P : Proto} {i0 Np : Nat}
    (hT : c.ty = .array (.lit N) (.word (.lit n) P)) (hg : P.ghost = false)
    (hR1 : ∀ j, i0 ≤ j → j < Np → ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧ m0.val = .undef ∧
      t0 ∉ Pr ∧ ∀ t m, mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ Pr)
    (hh : ∀ j, i0 ≤ j → j < Np → ∃ t m, t ∈ Pr ∧ mem[t]? = some m ∧ m.loc = ⟨l, j⟩)
    (hty : ∀ t m, t ∈ Pr → mem[t]? = some m → m.loc.label = l → WordOK E0 c.ty m.loc.offset (mw m)) :
    ∀ j, i0 ≤ j → j < Np → ∀ w, LatestNP mem [] ⟨l, j⟩ w → ∃ R, ValOfR E (.word (.lit n) P) [w] R := by
  intro j h1 h2 w hl
  obtain ⟨t, m, ht, hm, hma, hw⟩ := latest_prom (hR1 j h1 h2) (hh j h1 h2) hl
  have hok := hty t m ht hm (by rw [hma])
  rw [hT, hw] at hok
  obtain ⟨hp, hv⟩ := WordOK_wordbuf hok hg
  exact hval_of_num hp hv


/-- (F) `ThInvMC_plantW` with `hval` discharged (`hval_of`): in its place, an own promise at
every new unit (BH1) and the own promises at `l` typed (`promTy`). -/
theorem ThInvMC_plantWH {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Tot H : Res}
    {cr db : Ts → Res} {l : AllocLabel}
    (h : ThInvMC p g mem pairs th Tot H cr db) (hpa : PromAbove (stOf mem pairs th))
    (hpl : ∀ η : TEnv, ThInvRE p (CE η) th Tot → MemInv g (CE η) (stOf mem pairs th) →
      ∃ (c : Cell) (N n : Nat) (P : Proto) (F Np : Ts), η.sto l = some c ∧ c.owner = some η.tid ∧
        η.pfr l = none ∧ c.ty = .array (.lit N) (.word (.lit n) P) ∧ P.ghost = false ∧
        η.rini l ≤ η.ini l ∧ η.ini l ≤ Np ∧ Np ≤ N ∧
        (F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (CE η) (stOf mem pairs th) l F) ∧
        (η.ini l < Np → (stOf mem pairs th).vs.vWr ≤ F) ∧
        (∀ o, InitR (CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
            (fun l' => if l' = l then some F else η.pfr l') η.seen)) c l o → ¬ InitR (CE η) c l o →
          ∀ (t : Nat) (m : Msg), t ∉ th.promises → mem[t]? = some m → m.loc = ⟨l, o⟩ →
          ∃ (t' : Nat) (m' : Msg), t < t' ∧ t' ≤ F ∧ mem[t']? = some m' ∧ m'.loc = ⟨l, o⟩) ∧
        (∀ b S us, SegOf c.ty b S → accs S = some us →
          IniSeg (CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
            (fun l' => if l' = l then some F else η.pfr l') η.seen)) c l b → ¬ IniSeg (CE η) c l b →
          ∃ ws, ValOf (CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
            (fun l' => if l' = l then some F else η.pfr l') η.seen)) S ws ∧ ws.length = nWords us) ∧
        (∀ b S, SegOf c.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c.ty = true ∧
        Ty.noOwnIn [] c.ty = true ∧ rgnFree c.ty = true ∧
        FlipOK (CE η) (stOf mem pairs th) l ∧ FpOK (CE η) (stOf mem pairs th) ∧
        (∀ j, η.ini l ≤ j → j < Np → ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧
          m0.val = .undef ∧ t0 ∉ th.promises ∧ (∃ t, AtA mem ⟨l, j⟩ t0 t = true) ∧
          ∀ t m, mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ th.promises) ∧
        (∀ j, η.ini l ≤ j → j < Np → ∃ t m, t ∈ th.promises ∧ mem[t]? = some m ∧ m.loc = ⟨l, j⟩) ∧
        (∃ E0 : TEnv, ∀ t m, t ∈ th.promises → mem[t]? = some m → m.loc.label = l →
          WordOK E0 c.ty m.loc.offset (mw m))) :
    ∃ H' cr' db', ThInvMC p g mem pairs th Tot H' cr' db' ∧
      H' + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
  refine ThInvMC_plantW (l := l) h hpa (fun η hR hM => ?_)
  obtain ⟨c, N, n, P, F, Np, hsto, hown, hnone, hTc, hP, hrl, hNp, hNN, hF, hFw, hhold, hinh, hcpl, hcT,
    hnT, hrT, hf, hfo, hR1w, hh, E0, hty⟩ := hpl η hR hM
  refine ⟨c, N, n, P, F, Np, hsto, hown, hnone, hTc, hP, hrl, hNp, hNN, hF, hFw, hhold, hinh, hcpl, hcT,
    hnT, hrT, hf, hfo, hR1w, hval_of hTc hP (fun j h1 h2 => ?_) hh hty⟩
  obtain ⟨t0, m0, h0, h0l, h0u, h0p, -, hall⟩ := hR1w j h1 h2
  exact ⟨t0, m0, h0, h0l, h0u, h0p, hall⟩

/-- (F) `ThInvMC_plantWH` at the constructed frontier `F := plantF` (the `plant_holdF`): `hF`,
`hFw` and `hhold` are discharged from `hh` (BH1); left: `hinh` (P4b `plantInh`), the type facts,
`FlipOK`/`FpOK`, R1w (`PrivSlotFresh`) and `hty` (`promTy`). -/
theorem ThInvMC_plantWF {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Tot H : Res}
    {cr db : Ts → Res} {l : AllocLabel}
    (h : ThInvMC p g mem pairs th Tot H cr db) (hpa : PromAbove (stOf mem pairs th))
    (hpl : ∀ η : TEnv, ThInvRE p (CE η) th Tot → MemInv g (CE η) (stOf mem pairs th) →
      ∃ (c : Cell) (N n : Nat) (P : Proto) (Np : Ts), η.sto l = some c ∧ c.owner = some η.tid ∧
        η.pfr l = none ∧ c.ty = .array (.lit N) (.word (.lit n) P) ∧ P.ghost = false ∧
        η.rini l ≤ η.ini l ∧ η.ini l ≤ Np ∧ Np ≤ N ∧
        (∀ b S us, SegOf c.ty b S → accs S = some us →
          IniSeg (CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
            (fun l' => if l' = l then some (plantF (CE η) (stOf mem pairs th) l) else η.pfr l') η.seen)) c l b → ¬ IniSeg (CE η) c l b →
          ∃ ws, ValOf (CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
            (fun l' => if l' = l then some (plantF (CE η) (stOf mem pairs th) l) else η.pfr l') η.seen)) S ws ∧ ws.length = nWords us) ∧
        (∀ b S, SegOf c.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c.ty = true ∧
        Ty.noOwnIn [] c.ty = true ∧ rgnFree c.ty = true ∧
        FlipOK (CE η) (stOf mem pairs th) l ∧ FpOK (CE η) (stOf mem pairs th) ∧
        (∀ j, η.ini l ≤ j → j < Np → ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧
          m0.val = .undef ∧ t0 ∉ th.promises ∧ (∃ t, AtA mem ⟨l, j⟩ t0 t = true) ∧
          ∀ t m, mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ th.promises) ∧
        (∀ j, η.ini l ≤ j → j < Np → ∃ t m, t ∈ th.promises ∧ mem[t]? = some m ∧ m.loc = ⟨l, j⟩) ∧
        (∃ E0 : TEnv, ∀ t m, t ∈ th.promises → mem[t]? = some m → m.loc.label = l →
          WordOK E0 c.ty m.loc.offset (mw m))) :
    ∃ H' cr' db', ThInvMC p g mem pairs th Tot H' cr' db' ∧
      H' + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
  refine ThInvMC_plantWH (l := l) h hpa (fun η hR hM => ?_)
  obtain ⟨c, N, n, P, Np, hsto, hown, hnone, hTc, hP, hrl, hNp, hNN, hinh, hcpl, hcT,
    hnT, hrT, hf, hfo, hR1w, hh, hty⟩ := hpl η hR hM
  have hacc : accs (.word (.lit n) P) = some [Acc.one] := by simp [accs, hP]
  let E2 := CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l')
      (fun l' => if l' = l then some (plantF (CE η) (stOf mem pairs th) l) else η.pfr l') η.seen)
  have hNa : ∀ Na e us, c.ty = .array (.lit Na) e → accs e = some us → E2.ini l ≤ Na := by
    intro Na e us hT hus
    rw [hTc] at hT
    cases hT
    simp only [E2, CE, TEnv.withSto, ↓reduceIte]
    exact hNN
  have hheld : ∀ o, InitR E2 c l o → ¬ InitR (CE η) c l o →
      ∃ u ∈ (stOf mem pairs th).promises, ∃ m, (stOf mem pairs th).mem[u]? = some m ∧ m.loc = ⟨l, o⟩ := by
    intro o hi hni
    have hlt : o < Np := by
      have := hi N _ [Acc.one] hTc hacc
      simpa [E2, CE, TEnv.withSto, nWords, Acc.size] using this
    have hge : η.ini l ≤ o := Nat.le_of_not_lt fun hlt0 => hni fun N' e' us' hT' hus' => by
      rw [hTc] at hT'
      cases hT'
      rw [hacc] at hus'
      cases hus'
      simpa [CE, nWords, Acc.size] using hlt0
    obtain ⟨t, m, ht, hm, hml⟩ := hh o hge hlt
    exact ⟨t, ht, m, hm, hml⟩
  obtain ⟨h1, -, h3, h4⟩ := plant_holdF (E' := E2) hM hsto hown hnone hpa hNa hheld
  exact ⟨c, N, n, P, plantF (CE η) (stOf mem pairs th) l, Np, hsto, hown, hnone, hTc, hP, hrl, hNp, hNN,
    h3, fun _ => h1, h4, hinh, hcpl, hcT, hnT, hrT, hf, hfo, hR1w, hh, hty⟩

/-- (F) The planted frontier depends on the environment only through `IniWr` at `l`
(bridge `plantF (CE η) = plantF (cutP Eg j)`, `plantOf`'s frontier). -/
theorem plantF_congrE {E E' : TEnv} {s : St} {l : AllocLabel}
    (hi : ∀ a : Address, a.label = l → (IniWr E' a ↔ IniWr E a)) : plantF E' s l = plantF E s l := by
  have hH : ∀ u, HoldW E' s l u ↔ HoldW E s l u := fun u =>
    ⟨fun h => h.congrE fun a ha h' => (hi a ha).2 h', fun h => h.congrE fun a ha h' => (hi a ha).1 h'⟩
  have e : HoldW E' s l = HoldW E s l := funext fun u => propext (hH u)
  unfold plantF plantT
  rw [e]

end TermPlantR

#print axioms TermPlantR.MemHeld_raise
#print axioms TermPlantR.MemHeld_raiseS
#print axioms TermPlantR.PromCr_raise
#print axioms TermPlantR.acct_raise
#print axioms TermPlantR.tele_chain
#print axioms TermPlantR.ThInvMC_raise
#print axioms TermPlantR.MemHeld_flipLH
#print axioms TermPlantR.MemHeld_plantN
#print axioms TermPlantR.unit_tele
#print axioms TermPlantR.hnew_word
#print axioms TermPlantR.hacc_word
#print axioms TermPlantR.MemHeld_plantW
#print axioms TermPlantR.ThInvMC_plantW
#print axioms TermPlantR.WordOK_wordbuf
#print axioms TermPlantR.latest_prom
#print axioms TermPlantR.hval_of
#print axioms TermPlantR.ThInvMC_plantWH
#print axioms TermPlantR.ThInvMC_plantWF
#print axioms TermPlantR.plantF_congrE
