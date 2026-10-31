import WeakCore.TermPredHold
import WeakCore.TermW2New
import WeakCore.TermMainDefs
import WeakCore.ScalB

/-! # PlantedHolder: a (b)-failure at an anchored adversarial typing yields a planted holder

Over W typing only (the η-lineage).  Setting: thread `i` at the cut `c` (SysInvN gives
`PredHoldG Eg c`), a solo window `c →Solo c1`, and an adversarial typing `η` at `c1` with the anchored
antecedents of `PubWinSAN` (`Ext`, `IniAnch`, `RiniMem` over `E1 = Cut Eg i S`).  If NoHold's part (b),
`ZW l ∨ ini l ≤ rini l`, fails at `CE η`, then some unit of slot `η.rini l` carries a planted holder: the first
write there at `c`, at most the frontier, still an outstanding promise of `i` at `c1`, at a unit that `CE η`
does not count (`¬ IniWr`).

Fulfilled holders are what RiniMem counts (index ≤ frontier, not a promise, not `undef`), so the slot
`η.rini l` (which RiniMem does not count) keeps at least one outstanding holder.
-/

namespace DebtG3
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermStep TermCut TermTyped
open WeakMem (Msg Memory Address Ts Arch AllocLabel)

/-- (P) A planted holder outstanding at the publish. -/
def PreHolder (Eg : GEnv) (mem0 : Memory) (E : TEnv) (s1 : St) (l : AllocLabel) (h : Ts) : Prop :=
  ∃ (a : Address) (m : Msg), a.label = l ∧ FirstW mem0 a h ∧ h ∈ s1.promises ∧ s1.mem[h]? = some m ∧
    m.loc = a ∧ (∀ F, Eg.pfr l = some F → h ≤ F) ∧ ¬ IniWr E a

/-- A cell of thread `i` is in `i`'s cut. -/
theorem cutSto_own {Eg : GEnv} {i : Nat} {l : AllocLabel} {cl : Cell} (h : Eg.sto l = some cl)
    (ho : cl.owner = some i) : cutSto Eg i l = some cl := by
  unfold cutSto
  simp only [show Eg.InCut i l from ⟨cl, h, Or.inl ho⟩, ↓reduceIte]
  exact h

/-- The (b)-arithmetic: if the anchor's counts agree at `l`, (b) holds at every anchored extension. -/
theorem b_of_anchor_le {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {η : TEnv} {l : AllocLabel}
    (hExt : Ext (Cut Eg i S) (CE η)) (hA : IniAnch (Cut Eg i S) (CE η)) (hs : η.sto l ≠ none)
    (hle : Eg.ini l ≤ Eg.rini l) : η.ini l ≤ η.rini l := by
  have h1 := hA l hs
  have h2 := Ext.rini hExt l
  simp only [Cut_ini, Cut_rini, CE_ini, CE_rini] at h1 h2
  have : max (Eg.ini l) (η.rini l) = η.rini l := Nat.max_eq_right (Nat.le_trans hle h2)
  omega

/-- Slot arithmetic: an offset of slot `j` (width `w > 0`) is below `n` slots iff `j < n`. -/
theorem slot_lt {j w o n : Nat} (hlo : j * w ≤ o) (hhi : o < (j + 1) * w) : o < n * w ↔ j < n := by
  constructor
  · intro h
    exact Nat.lt_of_not_le fun hn => Nat.lt_irrefl o (Nat.lt_of_lt_of_le h
      (Nat.le_trans (Nat.mul_le_mul_right w hn) hlo))
  · intro h
    exact Nat.lt_of_lt_of_le hhi (Nat.mul_le_mul_right w h)

/-- A typed word of a buffer cell lies inside the buffer. -/
theorem wordOK_arr_lt {E : TEnv} {N : Nat} {e : Ty} {us : List Acc} {o : Nat} {w : Word}
    (hus : accs e = some us) (h : WordOK E (.array (.lit N) e) o w) : o < N * nWords us := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨-, hsh⟩, hw0, -, hbo⟩ := h
  rcases hseg with ⟨-, -, hA⟩ | ⟨N', us', j, hT, hus', hj, hb⟩
  · exact absurd rfl hA
  · cases hT
    rw [hus] at hus'; cases hus'
    have hl : ws.length = nWords us := hsh us hus
    have ho' : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
    have : (j + 1) * nWords us ≤ N * nWords us := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at this
    omega

/-- **`hcap` of L9**: at a planted, unpublished buffer of thread `i` whose counts disagree, the global count is
at most the slot count (a predicted unit past the buffer would carry an outstanding promise there, but
`PromTyAOK` types every outstanding promise at a shared cell inside it). -/
theorem ini_le_slots {Eg : GEnv} {c : Cfg} {i : Nat} {th : TTh} {l : AllocLabel} {cl : Cell} {F : Ts}
    {N : Nat} {e : Ty} {us : List Acc}
    (hPH : TermPredHold.PredHoldG Eg c) (hPT : TermMain.PromTyAOK Eg c) (hth : c.ths[i]? = some th)
    (hEg : Eg.sto l = some cl) (ho : cl.owner = some i) (hnp : ¬ Eg.pubd l) (hF : Eg.pfr l = some F)
    (hty : cl.ty = .array (.lit N) e) (hus : accs e = some us) (hpos : 0 < nWords us)
    (hdis : Eg.rini l < Eg.ini l) : Eg.ini l ≤ N := by
  refine Nat.le_of_not_lt fun hNI => ?_
  have hcut : (Cut Eg i (fun _ => False)).sto l = some cl := cutSto_own hEg ho
  have hjI : max N (Eg.rini l) < Eg.ini l := Nat.max_lt.2 ⟨hNI, hdis⟩
  have hPU : PredU (Cut Eg i (fun _ => False)) ⟨l, max N (Eg.rini l) * nWords us⟩ := by
    refine ⟨by simp only [Cut_pfr]; rw [hF]; exact Option.some_ne_none _, ?_, ?_⟩
    · intro c' N' e' us' h1 h2 h3
      change (Cut Eg i (fun _ => False)).sto l = some c' at h1
      rw [hcut] at h1; cases h1
      rw [hty] at h2; cases h2
      rw [hus] at h3; cases h3
      simp only [Cut_ini]
      exact Nat.mul_lt_mul_of_pos_right hjI hpos
    · intro hw
      have h1 := hw cl N e us hcut hty hus
      have h2 : (Cut Eg i (fun _ => False)).rc l ≤ max N (Eg.rini l) := by
        unfold TEnv.rc; simp only [Cut_ini, Cut_rini]; omega
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2))
  obtain ⟨h, hFW, hhp, -⟩ := hPH i th (fun _ => False) _ hth ⟨cl, hEg, ho⟩ hnp hPU
  obtain ⟨m, hm, hml, -⟩ := hFW.1
  have hsh : Eg.Shared m.loc.label := by rw [hml]; exact ⟨F, hF⟩
  have hsto' : Eg.sto m.loc.label = some cl := by rw [hml]; exact hEg
  have hW := hPT i th h m hth hhp hm cl hsto' hsh
  rw [hty, hml] at hW
  have := wordOK_arr_lt hus hW
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)))

/-- **The slot lemma** (shared by L9 and L8d).  At a planted slot `j` of `i`'s unpublished buffer (`Eg.rc ≤ j <
Eg.ini`, `j < N`) that the adversarial `η` does not count (`η.rini ≤ j`), some unit carries a planted holder that
is still outstanding at `c1`: fulfilled holders are what RiniMem counts. -/
theorem slot_holder {p : Prog} {k : Promises.Knobs} {arch : Arch} {Eg : GEnv} {c c1 : Cfg} {i : Nat}
    {th th1 : TTh} {S : AllocLabel → Prop} {η : TEnv} {l : AllocLabel} {cl : Cell} {F : Ts}
    {N : Nat} {e : Ty} {us : List Acc} {j : Nat}
    (hPH : TermPredHold.PredHoldG Eg c) (hth : c.ths[i]? = some th) (hsolo : Solo p k arch i c c1)
    (hExt : Ext (Cut Eg i S) (CE η)) (hR : RiniMem (Cut Eg i S) (CE η) (stOf c1.mem c1.pairs th1))
    (hEg : Eg.sto l = some cl) (hsto : η.sto l = some cl) (hown : cl.owner = some i) (hns : ¬ η.seen l)
    (hnp : ¬ Eg.pubd l) (hF : Eg.pfr l = some F)
    (hty : cl.ty = .array (.lit N) e) (hus : accs e = some us) (hpos : 0 < nWords us)
    (hjN : j < N) (hrcj : (Cut Eg i S).rc l ≤ j) (hjI : j < Eg.ini l) (hjr : η.rini l ≤ j) :
    ∃ h, PreHolder Eg c.mem (CE η) (stOf c1.mem c1.pairs th1) l h := by
  have hcut : (Cut Eg i S).sto l = some cl := cutSto_own hEg hown
  have hη0 : (CE η).sto l = some cl := hsto
  have htid : (CE η).tid = i := by
    have := hExt.2.2.2.1; simp only [Cut_tid] at this; exact this
  obtain ⟨o, hlo, hhi, hno⟩ : ∃ o, j * nWords us ≤ o ∧ o < (j + 1) * nWords us ∧
      ¬ ∃ (t : Nat) (m : Msg), t ∉ (stOf c1.mem c1.pairs th1).promises ∧ (stOf c1.mem c1.pairs th1).mem[t]? = some m ∧
        m.loc = ⟨l, o⟩ ∧ m.val ≠ .undef ∧ (∀ f, (Cut Eg i S).pfr l = some f → t ≤ f) := by
    refine Classical.byContradiction fun hn => ?_
    have hall : ∀ o, j * nWords us ≤ o → o < (j + 1) * nWords us →
        ∃ (t : Nat) (m : Msg), t ∉ (stOf c1.mem c1.pairs th1).promises ∧
          (stOf c1.mem c1.pairs th1).mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val ≠ .undef ∧
          (∀ f, (Cut Eg i S).pfr l = some f → t ≤ f) :=
      fun o h1 h2 => Classical.byContradiction fun h3 => hn ⟨o, h1, h2, h3⟩
    have := hR l cl N e us j hη0 (by rw [htid]; exact hown) hns hty hus hpos hjN hall
    simp only [CE_rini] at this
    omega
  have hPU : PredU (Cut Eg i S) ⟨l, o⟩ := by
    refine ⟨by simp only [Cut_pfr]; rw [hF]; exact Option.some_ne_none _, ?_, ?_⟩
    · intro c' N' e' us' h1 h2 h3
      change (Cut Eg i S).sto l = some c' at h1
      rw [hcut] at h1; cases h1
      rw [hty] at h2; cases h2
      rw [hus] at h3; cases h3
      simp only [Cut_ini]
      exact (slot_lt hlo hhi).2 hjI
    · intro hw
      have := hw cl N e us hcut hty hus
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ((slot_lt hlo hhi).1 this) hrcj)
  obtain ⟨h, hFW, hhp, hhF⟩ := hPH i th S ⟨l, o⟩ hth ⟨cl, hEg, hown⟩ hnp hPU
  obtain ⟨m, hm, hml, hmv⟩ := hFW.1
  have hm1 : c1.mem[h]? = some m := W2New.solo_mem hsolo hm
  have hout : h ∈ th1.promises := Classical.byContradiction fun hn =>
    hno ⟨h, m, hn, hm1, hml, hmv, fun f hf => hhF f (by simpa only [Cut_pfr] using hf)⟩
  refine ⟨h, ⟨l, o⟩, m, rfl, hFW, hout, hm1, hml, hhF, ?_⟩
  intro hw
  have h1 := hw cl N e us hη0 hty hus
  have h2 : (CE η).rc l ≤ j := by unfold TEnv.rc; simp only [CE_ini, CE_rini]; omega
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ((slot_lt hlo hhi).1 h1) h2)

/-- **L9 (B10).** A (b)-failure at the anchored adversarial typing `η` yields a planted holder.

Named hypotheses, beyond the PubWinSAN antecedents (`hExt`, `hA`, `hR`) and SysInvN (`hPH`, `hPT`, `hm0`):
* `hlab`: `l` is `i`'s cell at `c`, or its global count is `0` there (a label allocated in the window is fresh at
  `c`: `GFreshL`). Resource lineage: `i` holds the own key of `l` at `c1`.
* `hnp`: `l` is not published at `c` (resource lineage: `OwnPubG`).
* `hsc`: W's `ScalIni Eg` clause (`SysInvN.scalIni`, ♭ copy `ScalFlat.ScalIni`); at the planted own cell
  (frontier `F`) it gives `ini ≤ rini` off layout-bearing buffers (`ScalFlat.scal_cut`, `LayT` from `PubCpl`). -/
theorem bfail_holder {p : Prog} {k : Promises.Knobs} {arch : Arch} {g : G} {Eg : GEnv} {c c1 : Cfg} {i : Nat}
    {th th1 : TTh} {S : AllocLabel → Prop} {η : TEnv} {l : AllocLabel} {cl : Cell}
    (hPH : TermPredHold.PredHoldG Eg c) (hPT : TermMain.PromTyAOK Eg c) (hth : c.ths[i]? = some th)
    (hm0 : MemInv g (Cut Eg i S) (stOf c.mem c.pairs th))
    (hsolo : Solo p k arch i c c1)
    (hExt : Ext (Cut Eg i S) (CE η)) (hA : IniAnch (Cut Eg i S) (CE η))
    (hR : RiniMem (Cut Eg i S) (CE η) (stOf c1.mem c1.pairs th1))
    (hsto : η.sto l = some cl) (hns : ¬ η.seen l)
    (hlab : (∃ cl0, Eg.sto l = some cl0 ∧ cl0.owner = some i) ∨ Eg.ini l = 0)
    (hnp : ¬ Eg.pubd l)
    (hsc : ScalFlat.ScalIni Eg)
    (hb : ¬ (ZW (CE η) l ∨ η.ini l ≤ η.rini l)) :
    ∃ h, PreHolder Eg c.mem (CE η) (stOf c1.mem c1.pairs th1) l h := by
  have hsn : η.sto l ≠ none := by rw [hsto]; exact Option.some_ne_none _
  have hnb : ¬ η.ini l ≤ η.rini l := fun h => hb (Or.inr h)
  have hnz : ¬ ZW (CE η) l := fun h => hb (Or.inl h)
  have hdis : ¬ Eg.ini l ≤ Eg.rini l := fun hle => hnb (b_of_anchor_le hExt hA hsn hle)
  obtain ⟨cl0, hEg, ho0⟩ : ∃ cl0, Eg.sto l = some cl0 ∧ cl0.owner = some i := by
    rcases hlab with h | h
    · exact h
    · exact absurd (by rw [h]; exact Nat.zero_le _) hdis
  have hcut : (Cut Eg i S).sto l = some cl0 := cutSto_own hEg ho0
  have hηs : η.sto l = some cl0 := hExt.2.2.2.2.1 l cl0 hcut
  rw [hsto] at hηs; cases hηs
  obtain ⟨F, hF⟩ : ∃ F, Eg.pfr l = some F := by
    cases hq : Eg.pfr l with
    | some F => exact ⟨F, rfl⟩
    | none =>
      have hOH := hm0.2.2.2.2.2.1.2 l cl hcut ho0
      have : ¬ (Cut Eg i S).rc l < (Cut Eg i S).ini l := fun hlt => by
        obtain ⟨f, hf, -⟩ := hOH hlt
        simp only [Cut_pfr] at hf; rw [hq] at hf; cases hf
      exact absurd (by unfold TEnv.rc at this; simp only [Cut_ini, Cut_rini] at this; omega) hdis
  have hA1 := hA l hsn
  simp only [Cut_ini, CE_ini, CE_rini] at hA1
  have hjI : η.rini l < Eg.ini l := by
    have : η.ini l ≤ Eg.ini l := by
      rcases Nat.le_total (Eg.ini l) (η.rini l) with h | h
      · rw [Nat.max_eq_right h] at hA1; exact absurd hA1 hnb
      · rw [Nat.max_eq_left h] at hA1; exact hA1
    omega
  obtain ⟨N, e, us, hty, hus⟩ : ∃ N e us, cl.ty = .array (.lit N) e ∧ accs e = some us :=
    Classical.byContradiction fun hn => hdis (ScalFlat.scal_cut hsc (ScalFlat.memInv_pubCpl hm0) hEg hcut hF
      fun N e us h1 h2 => hn ⟨N, e, us, h1, h2⟩)
  have hpos : 0 < nWords us := Nat.pos_of_ne_zero fun h0 => hnz ⟨cl, N, e, us, hsto, hty, hus, h0⟩
  have hjN : η.rini l < N := Nat.lt_of_lt_of_le hjI
    (ini_le_slots hPH hPT hth hEg ho0 hnp hF hty hus hpos (Nat.lt_of_not_le hdis))
  have hrc : (Cut Eg i S).rc l ≤ η.rini l := by
    have := Ext.rini hExt l
    simp only [Cut_rini, CE_rini] at this
    unfold TEnv.rc; simp only [Cut_ini, Cut_rini]; omega
  exact slot_holder hPH hth hsolo hExt hR hEg hsto ho0 hns hnp hF hty hus hpos hjN hrc hjI (Nat.le_refl _)

/-- **L8d (B9), the F3 cross-check.** An outstanding promise of `i` at `c1` sitting at a *planted* unit (predicted at
the cut) that the adversarial typing does not count (`¬ IniWr (CE η)`) — in particular a `HoldW` witness at a planted
slot, post-frontier or not — forces a planted holder outstanding at `c1` (possibly at another unit of its slot).
So a post-frontier promise at a planted slot is never the end of the story: either its own holder or a sibling's
is outstanding (and G4 shows such a holder is never fulfilled), or the whole slot was written at timestamps at most
the frontier, which RiniMem counts, making the unit `IniWr` at `η` (excluded here). -/
theorem planted_holder {p : Prog} {k : Promises.Knobs} {arch : Arch} {Eg : GEnv} {c c1 : Cfg} {i : Nat}
    {th th1 : TTh} {S : AllocLabel → Prop} {η : TEnv} {a : Address} {cl : Cell}
    (hPH : TermPredHold.PredHoldG Eg c) (hPT : TermMain.PromTyAOK Eg c) (hth : c.ths[i]? = some th)
    (hsolo : Solo p k arch i c c1)
    (hExt : Ext (Cut Eg i S) (CE η)) (hR : RiniMem (Cut Eg i S) (CE η) (stOf c1.mem c1.pairs th1))
    (hEg : Eg.sto a.label = some cl) (hown : cl.owner = some i) (hns : ¬ η.seen a.label)
    (hnp : ¬ Eg.pubd a.label)
    (hPU : PredU (Cut Eg i S) a) (hni : ¬ IniWr (CE η) a) :
    ∃ h, PreHolder Eg c.mem (CE η) (stOf c1.mem c1.pairs th1) a.label h := by
  have hcut : (Cut Eg i S).sto a.label = some cl := cutSto_own hEg hown
  have hsto : η.sto a.label = some cl := hExt.2.2.2.2.1 _ cl hcut
  obtain ⟨F, hF⟩ : ∃ F, Eg.pfr a.label = some F := by
    have h1 := hPU.1; simp only [Cut_pfr] at h1
    exact Option.ne_none_iff_exists'.1 h1
  -- the layout: ¬IniWr at η forces a buffer with a layout
  obtain ⟨N, e, us, hty, hus⟩ : ∃ N e us, cl.ty = .array (.lit N) e ∧ accs e = some us :=
    Classical.byContradiction fun hn => hni fun c' N e us h1 h2 h3 => by
      change η.sto a.label = some c' at h1
      rw [hsto] at h1; cases h1
      exact absurd ⟨N, e, us, h2, h3⟩ hn
  have hIW := hPU.2.1 cl N e us hcut hty hus
  have hIWr : ¬ a.offset < (Cut Eg i S).rc a.label * nWords us := fun h =>
    hPU.2.2 fun c' N' e' us' h1 h2 h3 => by
      change (Cut Eg i S).sto a.label = some c' at h1
      rw [hcut] at h1; cases h1
      rw [hty] at h2; cases h2
      rw [hus] at h3; cases h3
      exact h
  simp only [Cut_ini] at hIW
  have hpos : 0 < nWords us := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hIW; exact Nat.not_lt_zero _ hIW
  -- the slot of `a`
  have hlo : a.offset / nWords us * nWords us ≤ a.offset := Nat.div_mul_le_self _ _
  have hhi : a.offset < (a.offset / nWords us + 1) * nWords us :=
    (Nat.div_lt_iff_lt_mul hpos).1 (Nat.lt_succ_self _)
  have hjI : a.offset / nWords us < Eg.ini a.label := (slot_lt hlo hhi).1 hIW
  have hrcj : (Cut Eg i S).rc a.label ≤ a.offset / nWords us :=
    Nat.le_of_not_lt fun h => hIWr ((slot_lt hlo hhi).2 h)
  have hdis : Eg.rini a.label < Eg.ini a.label := by
    have : (Cut Eg i S).rc a.label < Eg.ini a.label := Nat.lt_of_le_of_lt hrcj hjI
    unfold TEnv.rc at this; simp only [Cut_ini, Cut_rini] at this; omega
  have hjN : a.offset / nWords us < N :=
    Nat.lt_of_lt_of_le hjI (ini_le_slots hPH hPT hth hEg hown hnp hF hty hus hpos hdis)
  -- if η counted the slot, `a` would be `IniWr` at η
  have hjr : η.rini a.label ≤ a.offset / nWords us := by
    refine Nat.le_of_not_lt fun hlt => hni fun c' N' e' us' h1 h2 h3 => ?_
    change η.sto a.label = some c' at h1
    rw [hsto] at h1; cases h1
    rw [hty] at h2; cases h2
    rw [hus] at h3; cases h3
    have hi := hExt.2.2.2.2.2.1 a.label
    simp only [Cut_ini, CE_ini] at hi
    have : a.offset / nWords us < (CE η).rc a.label := by
      unfold TEnv.rc; simp only [CE_ini, CE_rini]
      exact Nat.lt_min.2 ⟨Nat.lt_of_lt_of_le hjI hi, hlt⟩
    exact (slot_lt hlo hhi).2 this
  exact slot_holder hPH hth hsolo hExt hR hEg hsto hown hns hnp hF hty hus hpos hjN hrcj hjI hjr

end DebtG3

#print axioms DebtG3.cutSto_own
#print axioms DebtG3.b_of_anchor_le
#print axioms DebtG3.slot_lt
#print axioms DebtG3.wordOK_arr_lt
#print axioms DebtG3.ini_le_slots
#print axioms DebtG3.slot_holder
#print axioms DebtG3.bfail_holder
#print axioms DebtG3.planted_holder
