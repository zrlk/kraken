/-
Option A′ (NoHold), module 1: `publish` without the window premise outside
planted-unseen cells, the weak footprint `EFootW`, and step lemmas that need
`NoHold` only at planted-unseen publishes (`PubWinT3`).
-/
import WeakCore.TermStep

namespace TermStep
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- **`publish` keeps `MemInv` without `PubWin`** when the published cell has
no frontier or is already seen (`hU`): `OwnHidP.2` and `SeenLE` supply the
window. -/
theorem MemInv_publish0 {g : G} {E E' : TEnv} {s : St} {l : AllocLabel} {c : Cell}
    (hm : MemInv g E s) (hsto : E.sto l = some c) (hown : c.owner = some E.tid)
    (hp : E.prog = E'.prog) (ht : E.tid = E'.tid) (hs : E'.sto = E.sto) (hi : E'.ini = E.ini)
    (hP : E'.pfr = pubP E l s.vs.vWr) (hS : E'.seen = pubS E l) (hR : E'.rini = E.rini)
    (hcpl : ∀ b S, SegOf c.ty b S → accs S ≠ none → TearOK S) (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true) (hU : ∀ f, E.pfr l = some f → E.seen l)
    (hbx : ∀ l B, E.box l = some B → E'.box l = some B := by first | exact fun _ _ h => h | simp_all | (intro _ _ h; simpa [CE, TEnv.withSto] using h))
    (hbe : E'.box = E.box := by first | rfl | simp_all)
    (hri : ∀ l, E.rini l ≤ E'.rini l := by rini_le) :
    MemInv g E' (fenceS s .st) := by
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  have hsub : ∀ l c, E.sto l = some c → E'.sto l = some c := fun l c h => by rw [hs]; exact h
  have hile : ∀ l, E.ini l ≤ E'.ini l := fun l => by rw [hi]; exact Nat.le_refl _
  have hPm : ∀ l' f, E.pfr l' = some f → E'.pfr l' = some f := fun l' f h => by
    rw [hP]; exact pubP_mono E l s.vs.vWr l' f h
  have hSm : ∀ l', E.seen l' → E'.seen l' := fun l' h => by rw [hS]; exact Or.inr h
  have hmono : ∀ {U : Ty} {vs : List Word}, ValOf E U vs → ValOf E' U vs :=
    fun h => ValOf_mono hp ht hsub hile h hPm hSm hbx
  have hwE : ∀ T o w, WordOK E T o w → WordOK E' T o w := fun T o w h =>
    WordOK_mono hp ht hsub hile hPm hSm h hbx
  have hiniR : ∀ c' l' o, InitR E' c' l' o → InitR E c' l' o := fun c' l' o h N e us h1 h2 => by
    have := h N e us h1 h2; rw [hi] at this; exact this
  have hrcE : ∀ l', E'.rc l' = E.rc l' := fun l' => TEnv.rc_congr (by rw [hi]) (by rw [hR])
  have hnew0 : ∀ (l' : AllocLabel) (o : Nat) (t : Nat) (m : Msg), s.mem.size ≤ t → (fenceS s .st).mem[t]? = some m →
      m.loc = ⟨l', o⟩ → ∀ T, WordOK E' T o (mw m) := fun _ _ t m ht hm _ _ =>
    (Nat.not_le.2 (lt_of_get (show s.mem[t]? = some m from hm)) ht).elim
  refine ⟨MemOKP_mono hmo hp ht hsub hile (fun t m c h hc => by rw [hs] at hc; exact hc) hPm hSm hbx,
    ?_, hpl, ?_, ?_, ?_, ?_, ?_, ?_, BoxInv_tr hbi hbe
      (fun l' B hl h => by
        rw [hS] at h
        rcases h with h | h
        · have h0 := (hbi.2.2 l' B hl).1; rw [h, hsto] at h0; cases h0
        · exact h)
      (fun l _ _ => by rw [hs]) (fun l _ _ => by rw [hi])
      (Nat.le_refl _) (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h), hpo⟩
  · -- OwnOK
    intro l' c' hc ho
    rw [hs] at hc
    refine OwnCellF_pub (hoo l' c' hc (by rw [ht]; exact ho)) hmono (by rw [hi]) ?_ hmo.2.2 (by rw [hR])
    rw [hP]
    rcases hpf0 : E.pfr l' with _ | f0
    · exact Or.inl rfl
    · exact Or.inr (pubP_mono _ _ _ l' f0 hpf0)
  · -- FreshL
    refine ⟨fun j hj => ?_, PrivCoh_env (s := s) hfr.2 hs ht hPm fun l' => Nat.le_of_eq (hrcE l').symm⟩

    obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj
    have hne : freshLabel g.lbase g.n g.i j ≠ l := fun he => by rw [he, hsto] at f1; cases f1
    exact ⟨by rw [hs]; exact f1, f2, by rw [hi]; exact f4, by rw [hP, pubP_ne hne]; exact f5⟩
  · -- SeenLE, at the raised `vRelSt`
    intro l' hl'
    rw [hS] at hl'
    show ∃ f, E'.pfr l' = some f ∧ f ≤ max s.vs.vRelSt s.vs.vWr
    rw [hP]
    rcases hl' with he | hl'
    · simp only [pubP, he, ↓reduceIte]
      cases hpf : E.pfr l with
      | none => exact ⟨s.vs.vWr, rfl, Nat.le_max_right _ _⟩
      | some f0 =>
        by_cases hsl : E.seen l
        · obtain ⟨f, h1, h2⟩ := hsn l hsl
          rw [hpf] at h1
          have e : f0 = f := Option.some.inj h1
          subst e
          exact ⟨_, rfl, Nat.le_trans h2 (Nat.le_max_left _ _)⟩
        · exact absurd (hU f0 hpf) hsl
    · obtain ⟨f, h1, h2⟩ := hsn l' hl'
      exact ⟨f, pubP_mono E l s.vs.vWr l' f h1, Nat.le_trans h2 (Nat.le_max_left _ _)⟩
  · -- OwnHid: memory and `vWr` are unchanged; the published cell is not planted (P3)
    refine ⟨fun l' c' hc ho o hio => ?_, fun l' c' hc ho hlt => ?_⟩
    · rw [hs] at hc
      exact HiddenP_grow (hoh.1 l' c' hc (by rw [ht]; exact ho) o (fun N e us h1 h2 => by
          have := hio N e us h1 h2; rw [hrcE] at this; exact this)) (hwE _ _)
        (Nat.le_refl _) (fun _ _ => rfl) (fun t m ht' hm hl => hnew0 l' o t m ht' hm hl _)
        (fun _ _ h1 h2 => absurd h1 h2)
    · rw [hs] at hc
      rw [hrcE, hi] at hlt
      by_cases he : l' = l
      · rw [he] at hlt hc ⊢
        obtain ⟨f, hf, hns, -⟩ := hoh.2 l c hsto hown hlt
        by_cases hz : ZW E l
        · exact ⟨(E.pfr l).getD s.vs.vWr, by rw [hP]; simp [pubP],
            fun hz' => absurd ((ZW.stoAt (congrFun hs l)).2 hz) hz',
            fun o hio => absurd hz (ZW.not_of_initR hc (hiniR c' l o hio))⟩
        · exact absurd (hU f hf) (hns hz)
      · obtain ⟨f, hf, hns, hH⟩ := hoh.2 l' c' hc (by rw [ht]; exact ho) hlt
        refine ⟨f, by rw [hP, pubP_ne he]; exact hf,
          by rw [hS]; exact fun hz h => h.elim he (hns (fun hz0 => hz ((ZW.stoAt (congrFun hs l')).2 hz0))),
          fun o hio => ?_⟩
        exact HiddenP_grow (hH o (hiniR c' l' o hio)) (hwE _ _)
          (Nat.le_refl _) (fun _ _ => rfl) (fun t m ht' hm hl => hnew0 l' o t m ht' hm hl _)
          (fun _ _ h1 h2 => absurd h1 h2)
  · -- PubDef: the published cell is the thread's own
    intro l' c' f hc hown' hf o hio
    rw [hs] at hc
    by_cases he : l' = l
    · rw [he, hsto] at hc
      cases hc
      exact (hown' (by rw [← ht]; exact hown)).elim
    · rw [hP, pubP_ne he] at hf
      exact HiddenP_grow (hpd l' c' f hc (by rw [ht]; exact hown') hf o (hiniR c' l' o hio)) (hwE _ _)
        (Nat.le_refl _) (fun _ _ => rfl) (fun t m ht' hm hl => hnew0 l' o t m ht' hm hl _)
        (fun _ _ h1 h2 => absurd h1 h2)
  · -- OwnPub
    intro l' c' f hc ho hf
    rw [hS]
    by_cases he : l' = l
    · exact Or.inl (Or.inl he)
    · rw [hP, pubP_ne he] at hf
      rw [hs] at hc
      rcases hopub l' c' f hc (by rw [ht]; exact ho) hf with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (h.congrE fun _ _ h => IniWr.ofEq hs hi hR h))
  · -- PubInv: `l` is the thread's own, and its type is coupled
    obtain ⟨hS0, hI0, hC0, hPP0, hLV0⟩ := hpi
    refine ⟨fun l' hl' => ?_, fun l' c' b S us hc hseg hu hini => ?_, fun l' c' f hc hf => ?_, ?_, ?_⟩
    · rw [hS] at hl'
      rcases hl' with he | hl'
      · rw [he]; exact .inl ⟨c, by rw [hs]; exact hsto, by rw [← ht]; exact hown⟩
      · rcases hS0 l' hl' with ⟨c', h1, h2⟩ | ⟨h1, h2⟩
        · exact .inl ⟨c', by rw [hs]; exact h1, by rw [← ht]; exact h2⟩
        · exact .inr ⟨by rw [hs]; exact h1, by rw [hbe]; exact h2⟩
    · rw [hs] at hc
      obtain ⟨ws, h1, h2⟩ := hI0 l' c' b S us hc hseg hu (fun N e h1 => by
        have := hini N e h1; rw [hi] at this; exact this)
      exact ⟨ws, hmono h1, h2⟩
    · rw [hs] at hc
      by_cases he : l' = l
      · rw [he, hsto] at hc
        rw [← Option.some.inj hc]
        obtain ⟨vals, hcell, -⟩ := hoo l c hsto hown
        exact ⟨LayT_of_CellOK hcell, hcpl, hcT, hnT, hrT⟩
      · rw [hP, pubP_ne he] at hf; exact hC0 l' c' f hc hf
    · intro l' c' f o hc hown' hf htw t0 t1 m0 m1 hn0 hn1 hm0 hm1 hl0 hl1 hh0 hh1 hst
      rw [hs] at hc
      have he : l' ≠ l := fun he => by
        rw [he, hsto] at hc
        rw [← Option.some.inj hc] at hown'
        rcases hown' with ⟨h, -⟩ | ⟨h, b2, S2, us2, o2, hseg2, hL2, htw2, -, -, hiS2⟩
        · exact h (by rw [← ht]; exact hown)
        · rw [he, hrcE, hi] at h
          rw [he, hi] at hiS2
          obtain ⟨f, hf, hns, -⟩ := hoh.2 l c hsto hown h
          exact absurd (hU f hf) (hns (ZW.not_of_initR hsto
            (InitR_of_IniSeg (o := o2) hiS2 hseg2 hL2 (by have := TwoAt_lt htw2; omega))))
      rw [hP, pubP_ne he] at hf
      exact PairOK_mono hp ht hsub hile hPm hSm
        (hPP0 l' c' f o hc (PubG_tr ht (Nat.le_of_eq (hrcE l').symm) (fun h => ⟨by rw [hrcE, hi] at h; exact h, Nat.le_of_eq (by rw [hi])⟩)
          (fun _ => Nat.le_of_eq (by rw [hi])) hown') hf htw t0 t1 m0 m1 hn0 hn1 hm0 hm1 hl0 hl1 hh0 hh1 hst) hbx
    · intro l' c' f b S us o hc hown' hf hseg hu ho
      rw [hs] at hc
      have he : l' ≠ l := fun he => by
        rw [he, hsto] at hc
        rw [← Option.some.inj hc] at hown'
        exact hown' (by rw [← ht]; exact hown)
      rw [hP, pubP_ne he] at hf
      exact hLV0 l' c' f b S us o hc (by rw [ht]; exact hown') hf hseg hu ho

/-- **`publish` keeps `MemInv` given the window only at a planted-unseen cell**
(`hF3`); elsewhere `MemInv_publish0`. -/
theorem MemInv_publishW {g : G} {E E' : TEnv} {s : St} {l : AllocLabel} {c : Cell}
    (hm : MemInv g E s) (hsto : E.sto l = some c) (hown : c.owner = some E.tid)
    (hp : E.prog = E'.prog) (ht : E.tid = E'.tid) (hs : E'.sto = E.sto) (hi : E'.ini = E.ini)
    (hP : E'.pfr = pubP E l s.vs.vWr) (hS : E'.seen = pubS E l) (hR : E'.rini = E.rini)
    (hcpl : ∀ b S, SegOf c.ty b S → accs S ≠ none → TearOK S) (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hF3 : ∀ f, E.pfr l = some f → ¬ E.seen l → PubWin E s l)
    (hbx : ∀ l B, E.box l = some B → E'.box l = some B := by first | exact fun _ _ h => h | simp_all | (intro _ _ h; simpa [CE, TEnv.withSto] using h))
    (hbe : E'.box = E.box := by first | rfl | simp_all)
    (hri : ∀ l, E.rini l ≤ E'.rini l := by rini_le) :
    MemInv g E' (fenceS s .st) := by
  by_cases hpu : ∃ f, E.pfr l = some f ∧ ¬ E.seen l
  · obtain ⟨f, hf, hns⟩ := hpu
    exact MemInv_publish hm hsto hown hp ht hs hi hP hS hR hcpl hcT hnT hrT (hF3 f hf hns) hbx hbe hri
  · exact MemInv_publish0 hm hsto hown hp ht hs hi hP hS hR hcpl hcT hnT hrT
      (fun f hf => Classical.byContradiction fun hns => hpu ⟨f, hf, hns⟩) hbx hbe hri

/-- (A′) **The weak footprint**: `EFoot` without the holder bound at a frontier
set by the step. -/
def EFootW (g : G) (E E' : TEnv) (s s' : St) : Prop :=
  E'.prog = E.prog ∧ E'.tid = E.tid ∧
  (∀ l, E'.sto l = E.sto l ∨
    (FreshIn g s.nalloc s'.nalloc l ∧ ∃ T, E'.sto l = some ⟨T, some E.tid⟩ ∧ (Clo T ∧ mg T = true ∧ noIallV T = true) ∧ UndefAtT s'.mem l T ∧
      NewAtT s.mem.size s'.mem l T)) ∧
  (∀ l, E'.box l = E.box l ∨
    (FreshIn g s.nalloc s'.nalloc l ∧ ∃ B, E'.box l = some B ∧ B.own = E.tid ∧ s.mem.size ≤ B.fr + 1 ∧
      B.fr ≤ s'.vs.vWr ∧ s.mem.size + B.pay.length ≤ B.fr)) ∧
  (∀ l, E.ini l ≤ E'.ini l ∧ (E'.ini l = E.ini l ∨ FreshIn g s.nalloc s'.nalloc l ∨
    (OwnAt E l ∧ E'.ini l ≤ max (E.ini l) (E'.rini l) ∧
      (E.pfr l ≠ none → E'.ini l = E.ini l ∨ E.ini l ≤ E.rini l)))) ∧
  (∀ l, E'.pfr l = E.pfr l ∨
    (E.pfr l = none ∧ ∃ F, E'.pfr l = some F ∧ s.vs.vWr ≤ F ∧ F ≤ max s.vs.vWr s.mem.size ∧ OwnAt E l ∧
      s'.vs.vWr ≤ F ∧
      (¬ E'.seen l → ∀ cl N e us, E'.sto l = some cl → cl.ty = .array (.lit N) e → accs e = some us →
        nWords us = 0 → (∃ ws, ValOf ({ prog := E.prog } : TEnv) e ws ∧ ws.length = 0) → N ≤ E'.ini l)) ∨
    (FreshIn g s.nalloc s'.nalloc l ∧ E.pfr l = none ∧ E'.sto l = none)) ∧
  (∀ l, E.seen l → E'.seen l) ∧ (∀ l, E'.seen l → E.seen l ∨ OwnAt E l ∨ FreshIn g s.nalloc s'.nalloc l) ∧
  E'.fp = E.fp ∧ (∀ l, E.rini l ≤ E'.rini l) ∧
  ((∀ l, E.rini l ≤ E.ini l) → ∀ l, E'.rini l ≤ E'.ini l) ∧ RiniW E E' s s'.vs.vWr ∧
  (∀ l, E'.rini l = E.rini l ∨ FreshIn g s.nalloc s'.nalloc l ∨ OwnAt E l)

theorem EFootB.weak {W : Ty → Prop} {g : G} {E E' : TEnv} {s s' : St} (h : EFootB W g E E' s s') :
    EFootW g E E' s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := h
  refine ⟨h1, h2, fun l => (h3 l).imp id fun ⟨hf, T, e, ⟨a1, a2, a3, _⟩, u, n⟩ => ⟨hf, T, e, ⟨a1, a2, a3⟩, u, n⟩, h4, h5, fun l => ?_, h7, h8, h9, h10, h11, h12, h13⟩
  rcases h6 l with e | ⟨h0, F, e, a1, a2, a3, a4, -, a5, -⟩ | e
  · exact .inl e
  · exact .inr (.inl ⟨h0, F, e, a1, a2, a3, a4, a5⟩)
  · exact .inr (.inr e)

theorem EFoot.weak {g : G} {E E' : TEnv} {s s' : St} (h : EFoot g E E' s s') : EFootW g E E' s s' :=
  EFootB.weak h

theorem EFootW.riniW {g : G} {E E' : TEnv} {s s' : St} (h : EFootW g E E' s s') : RiniW E E' s s'.vs.vWr :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

/-- `EFoot_pub` without the no-holder premise. -/
theorem EFootW_pub {g : G} {E E' : TEnv} {s s' : St} {l0 : AllocLabel}
    (hp : E'.prog = E.prog) (ht : E'.tid = E.tid) (hs : E'.sto = E.sto) (hbx : E'.box = E.box)
    (hini : E'.ini = E.ini) (hown : OwnAt E l0)
    (hpf : ∀ l, E'.pfr l = if l = l0 then some ((E.pfr l0).getD s.vs.vWr) else E.pfr l)
    (hse : ∀ l, E'.seen l ↔ (l = l0 ∨ E.seen l))
    (hfp : E'.fp = E.fp := by first | rfl | assumption)
    (hri : ∀ l, E.rini l ≤ E'.rini l := by rini_le)
    (hrl : (∀ l, E.rini l ≤ E.ini l) → ∀ l, E'.rini l ≤ E'.ini l := by rini_ini)
    (hrw : RiniW E E' s s'.vs.vWr := by riniW_tac)
    (hrq : ∀ l, E'.rini l = E.rini l ∨ l = l0 := by rini_eq)
    (hvw : s'.vs.vWr ≤ s.vs.vWr := by first | exact Nat.le_refl _ | assumption) : EFootW g E E' s s' := by
  have hother : ∀ l, l ≠ l0 → E'.pfr l = E.pfr l := fun l h => by rw [hpf l]; simp [h]
  refine ⟨hp, ht, fun l => .inl (by rw [hs]), fun l => .inl (by rw [hbx]),
    fun l => ⟨by rw [hini]; exact Nat.le_refl _, .inl (by rw [hini])⟩, fun l => ?_,
    fun l h => (hse l).2 (.inr h), fun l h => ?_, hfp, hri, hrl, hrw,
    fun l => (hrq l).imp id fun h => .inr (by subst h; exact hown)⟩
  · by_cases hl : l = l0
    · subst hl
      cases hE : E.pfr l with
      | some f => exact .inl (by rw [hpf l]; simp [hE])
      | none =>
        exact .inr (.inl ⟨rfl, s.vs.vWr, by rw [hpf l]; simp [hE], Nat.le_refl _, Nat.le_max_left _ _, hown, hvw,
          fun hns => absurd ((hse l).2 (.inl rfl)) hns⟩)
    · exact .inl (hother l hl)
  · rcases (hse l).1 h with h | h
    · subst h; exact .inr (.inl hown)
    · exact .inl h

/-- (A′) `ThInvMF` with the weak footprint. -/
def ThInvMFW (p : Prog) (g : G) (E : TEnv) (s : St) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∃ E', EFootW g E E' s (stOf mem pairs th) ∧ ThInvE p E' th ∧ MemInv g E' (stOf mem pairs th)

theorem ThInvMF.weak {p : Prog} {g : G} {E : TEnv} {s : St} {mem : Memory} {pairs : List Ts} {th : TTh}
    (h : ThInvMF p g E s mem pairs th) : ThInvMFW p g E s mem pairs th :=
  let ⟨E', hf, h1, h2⟩ := h
  ⟨E', hf.weak, h1, h2⟩

/-- (A′) `ThInvMCFS` with the weak footprint. -/
def ThInvMCFSW (p : Prog) (g : G) (E : TEnv) (s : St) (S0 : AllocLabel → List Res) (mem : Memory) (pairs : List Ts)
    (th : TTh) (Tot H : Res) (cr db : Ts → Res) : Prop :=
  ∃ E', EFootW g E E' s (stOf mem pairs th) ∧ ThInvRE p E' th Tot ∧ MemInv g E' (stOf mem pairs th) ∧
    MemHeldK E s S0 E' (stOf mem pairs th) H ∧ PromCr E' (stOf mem pairs th) cr db

theorem ThInvMCFS.weak {Sp : AllocLabel → List Res} {p : Prog} {g : G} {E : TEnv} {s : St} {mem : Memory} {pairs : List Ts}
    {th : TTh} {Tot H : Res} {cr db : Ts → Res}
    (h : ThInvMCFS p g E s Sp mem pairs th Tot H cr db) : ThInvMCFSW p g E s Sp mem pairs th Tot H cr db :=
  let ⟨E', hf, _, _, h1, h2, h3, h4⟩ := h
  ⟨E', hf.weak, h1, h2, h3, h4⟩

/-- (A′) The step-level window premise, only at a planted-unseen published cell. -/
def PubWinT3 (E : TEnv) (s : St) (th : TTh) : Prop :=
  ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ∀ f, E.pfr ad.label = some f → ¬ E.seen ad.label → PubWin E s ad.label

/-- `NoHold` at an own cell gives `PubWinT3`'s window. -/
theorem PubWinT3_of {g : G} {E : TEnv} {s : St} {th : TTh} (hm : MemInv g E s) (h : PubWinT E s th)
    (hown : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → ∃ c, E.sto ad.label = some c ∧ c.owner = some E.tid) :
    PubWinT3 E s th := fun x a e rt ws ad ht hea hws _ _ _ => by
  obtain ⟨c, hc, ho⟩ := hown x a e rt ws ad ht hea hws
  exact PubWin_of_NoHold hm hc ho (h x a e rt ws ad ht hea hws)
theorem tstepM_publishW {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : PubScope cx a)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      ∀ f, (CE η).pfr ad.label = some f → ¬ (CE η).seen ad.label → PubWin (CE η) (stOf mem pairs th) ad.label) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFW p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu, hsh, hb⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) ∧
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind x (.ptr .pub u) = .ok c' := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
    simp only [VR] at hv
    obtain ⟨⟨lab, off⟩, c, hws, hoff, hsto, hcty, hmode, hacc⟩ := hv
    simp only at hoff; subst hoff
    obtain ⟨pw, rfl, hpw⟩ : ∃ pw, ws = [pw] ∧ pw.val = .loc ⟨lab, 0⟩ 0 := by
      match ws, hws with
      | [pw], h => exact ⟨pw, rfl, by simpa using h⟩
      | [], h => simp at h
      | _ :: _ :: _, h => simp at h
    have hsk := hl.2.1
    rw [close_ptr] at hsk
    obtain ⟨ru, rfl, hsku⟩ : ∃ ru, rt = .ptr .own ru ∧ etok (skel ru) = etok (skel (close th.σs u)) := by
      cases rt <;> simp [skel, etok] at hsk
      case ptr μ ru =>
        cases μ <;> simp [skelM, etok] at hsk
        exact ⟨ru, rfl, hsk⟩
      case refine t ψ => unfold rf at hsk; split at hsk <;> simp [etok] at hsk
    have hown : c.owner = some η.tid := hmode
    have hx : Ext η (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)) :=
      Ext_withSto hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _) (fun l h => Or.inr h)
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .ptr .pub ru, [pw]) :: th.env } (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    have hvr : VR ρ (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab))
        (.ptr .pub u) (shp (.ptr .pub ru)) [pw] := by
      simp only [VR]
      exact ⟨⟨lab, 0⟩, c, hws, rfl, hsto, hcty,
        ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withSto, pubP], Or.inl (Or.inl rfl)⟩, hacc⟩
    have hlay : Lay th.σs (.ptr .pub u) (.ptr .pub ru) [pw] :=
      ⟨fun us h => by simp [accs] at h; subst h; rfl, by rw [close_ptr]; simp only [skel, etok, hsku],
        by simp [wc, accs], ⟨⟨lab, 0⟩, hws⟩, by
          simp only [close, substTs, lyt, etok]; rw [(cell_lyt hl.2.2.2.2 rfl rfl).2]; rfl⟩
    exact ⟨CE (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)),
      EFootW_pub rfl rfl rfl rfl rfl ⟨c, hsto, hown⟩ (fun _ => rfl) (fun _ => Iff.rfl),
      ⟨ρ, η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab), c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', bind_FInv hb (FInv_ext hE.2.1 hx hi1) hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_publishW (E := CE η) (hF3 := hwin _ _ ⟨lab, 0⟩ hea (by simp [hpw])) hm hsto hown rfl rfl rfl rfl rfl rfl rfl (fun b S hseg _ => by
        obtain ⟨-, rfl⟩ := SegOf_lay hacc hseg
        have hcu : Ty.coupledOKIn c₁.ke u = true := by
          simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
        have htbu : tb c₁.ke.length u = true := by
          have h := (use_TvOK hu htv).2.1
          rw [← (use_TvOK hu htv).2.2] at h
          simpa [tb] using h
        exact TearOK_Fd hcty (TearOK_of_cpl
          (coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu)))
        (coupledOK_Fd hcty (by
          have hcu : Ty.coupledOKIn c₁.ke u = true := by
            simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
          have htbu : tb c₁.ke.length u = true := by
            have h := (use_TvOK hu htv).2.1
            rw [← (use_TvOK hu htv).2.2] at h
            simpa [tb] using h
          exact coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu))
        (noOwn_Fd hcty (by
          have hnu : Ty.noOwnIn c₁.ke u = true := by
            simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
          have htbu : tb c₁.ke.length u = true := by
            have h := (use_TvOK hu htv).2.1
            rw [← (use_TvOK hu htv).2.2] at h
            simpa [tb] using h
          exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
            (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) u hnu htbu))
        (rgnFree_Fd hcty (rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk)
          (by simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1)
          (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))))⟩
  | publishBuf hu hsh hb =>
    obtain ⟨n, k, u, c₁, hu, hsh, hb⟩ : ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) ∧
        Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true ∧
        c₁.bind x (.refine (.loc .pub (.array n u)) (.ini k)) = .ok c' := ⟨_, _, _, _, hu, hsh, hb⟩
    obtain ⟨hi1, rb, wsb, hea, hvb, hlb⟩ := use_FInv hu hi
    simp only [VR] at hvb
    obtain ⟨hv, hir⟩ := hvb
    have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
      rw [hlb.2.1]; rfl
    obtain ⟨μr, nr, ur, ψ, rfl, hμ, hsu⟩ := buf_runtime' hs'
    have hlay : Lay th.σs (.refine (.loc .pub (.array n u)) (.ini k)) (.refine (.loc .pub (.array nr ur)) ψ) wsb := by
      obtain ⟨h1, -, h3, h4⟩ := hlb
      refine ⟨h1, ?_, h3, h4.1, ?_⟩
      · rw [close_refine]
        show etok (rf (skel (.loc .pub (.array nr ur)))) = etok (rf (skel (close th.σs (.loc .pub (.array n u)))))
        rw [skel_close_locArr]
        show rf (.loc (skelM .pub) (.array (.lit 0) (etok (skel ur)))) = _
        rw [hsu]; rfl
      · simp only [close, substTs, lyt, etok, anyB_zero, Bool.false_eq_true, ite_false, idxC, ofMs, modeC]
        rw [(buf_lyt h4.2 rfl).2]; rfl
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .refine (.loc .pub (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat, hFU, hmode, hini⟩
    · -- a null handle (an empty buffer): only the fence
      have hvr : VR ρ η (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VR]; exact ⟨Or.inl ⟨hnull, e0, he0⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      exact ⟨CE η, (EFoot.weak EFoot_refl), ⟨ρ, η, c', rfl, hE, he, htv', bind_FInv hb hi1 hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩, MemInv_fence hm⟩
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c.owner = some η.tid := hmode
      have hx : Ext η (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)) :=
        Ext_withSto hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _) (fun l h => Or.inr h)
      have hvr : VR ρ (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label))
          (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VR]
        exact ⟨Or.inr ⟨ad, c, _, hws, hsto, hat, .refl,
          ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withSto, pubP], Or.inl (Or.inl rfl)⟩,
          (IniAt_mono (modeIni_le_ini _ _ _) hini)⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      exact ⟨CE (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)),
        EFootW_pub rfl rfl rfl rfl rfl ⟨c, hsto, hown⟩ (fun _ => rfl) (fun _ => Iff.rfl),
        ⟨ρ, η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label), c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', bind_FInv hb (FInv_ext hE.2.1 hx hi1) hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
        MemInv_publishW (E := CE η) (hF3 := hwin _ _ ad hea hws) hm hsto hown rfl rfl rfl rfl rfl rfl rfl
          (fun b S hseg ha => by
            rcases hseg with ⟨-, rfl, -⟩ | ⟨N, usS, j, hT, -, -, -⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · have e1 := AtOff_arr_here hat hT ha (by simp [cl, accs])
              rw [hT] at e1
              simp only [cl, Ty.array.injEq] at e1
              obtain ⟨-, rfl⟩ := e1
              have hcu : Ty.coupledOKIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
              have htbu : tb c₁.ke.length (.array n u) = true := by
                have h := (use_TvOK hu htv).2.1
                rw [← (use_TvOK hu htv).2.2] at h
                simpa [tb] using h
              have := coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk)
                hcu htbu
              simp only [cl, Ty.coupledOK, Ty.coupledOKIn] at this; exact TearOK_of_cpl this)
          (by
            obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
            rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              have hcu : Ty.coupledOKIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
              have htbu : tb c₁.ke.length (.array n u) = true := by
                have h := (use_TvOK hu htv).2.1
                rw [← (use_TvOK hu htv).2.2] at h
                simpa [tb] using h
              exact coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk)
                hcu htbu)
          (by
            obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
            rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              have hnu : Ty.noOwnIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
              have htbu : tb c₁.ke.length (.array n u) = true := by
                have h := (use_TvOK hu htv).2.1
                rw [← (use_TvOK hu htv).2.2] at h
                simpa [tb] using h
              exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
                (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) _ hnu htbu)
          (by
            obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
            rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              exact rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk)
                (by simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1)
                (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩)))⟩


/-! ## §17 (M5b) Loading through a `pub` locative

A `pub` locative's target is a component of a segment of its cell (`at_seg`):
the whole cell, or a buffer slot below the initialised count.  A torn read of
another thread's cell is assembled over the whole segment (`TermTear.assemble`):
the units the load does not read are taken from a value of the segment type
(`Inh`), the units it reads are words of values of that one segment
(`SegOf_unique`), and the target's words are then cut out (`VR_at`). -/

theorem tstepMR_publishW {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr}
    {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hsc : PubScope cx a)
    {cr db : Ts → Res} (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hwp : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      ∀ f, (CE η).pfr ad.label = some f → ¬ (CE η).seen ad.label → PubWin (CE η) (stOf mem pairs th) ad.label)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' cr' db' rt ws, evalAt th.env a = some (rt, ws) ∧
        (∀ ad g', ws.map (·.val) = [.loc ad g'] → η.sto ad.label ≠ none) ∧
        ThInvMCFSW p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + ownW .own ws ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu, hsh, hb⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) ∧
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind x (.ptr .pub u) = .ok c' := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨rt, ws, R0, Rr, hea, hv, hl, hvR, hi1R, hle⟩ := useR hu hi hE.2.2
    have hR0 := VRR_cell_R rfl hvR
    have hi1 := hi1R.1
    simp only [VR] at hv
    obtain ⟨⟨lab, off⟩, c, hws, hoff, hsto, hcty, hmode, hacc⟩ := hv
    simp only at hoff; subst hoff
    obtain ⟨pw, rfl, hpw⟩ : ∃ pw, ws = [pw] ∧ pw.val = .loc ⟨lab, 0⟩ 0 := by
      match ws, hws with
      | [pw], h => exact ⟨pw, rfl, by simpa using h⟩
      | [], h => simp at h
      | _ :: _ :: _, h => simp at h
    have hsk := hl.2.1
    rw [close_ptr] at hsk
    obtain ⟨ru, rfl, hsku⟩ : ∃ ru, rt = .ptr .own ru ∧ etok (skel ru) = etok (skel (close th.σs u)) := by
      cases rt <;> simp [skel, etok] at hsk
      case ptr μ ru =>
        cases μ <;> simp [skelM, etok] at hsk
        exact ⟨ru, rfl, hsk⟩
      case refine t ψ => unfold rf at hsk; split at hsk <;> simp [etok] at hsk
    have hown : c.owner = some η.tid := hmode
    have hx : Ext η (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)) :=
      Ext_withSto hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _) (fun l h => Or.inr h)
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .ptr .pub ru, [pw]) :: th.env } (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr hpa0 => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    have hvr : VR ρ (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab))
        (.ptr .pub u) (shp (.ptr .pub ru)) [pw] := by
      simp only [VR]
      exact ⟨⟨lab, 0⟩, c, hws, rfl, hsto, hcty,
        ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withSto, pubP], Or.inl (Or.inl rfl)⟩, hacc⟩
    have hlay : Lay th.σs (.ptr .pub u) (.ptr .pub ru) [pw] :=
      ⟨fun us h => by simp [accs] at h; subst h; rfl, by rw [close_ptr]; simp only [skel, etok, hsku],
        by simp [wc, accs], ⟨⟨lab, 0⟩, hws⟩, by
          simp only [close, substTs, lyt, etok]; rw [(cell_lyt hl.2.2.2.2 rfl rfl).2]; rfl⟩
    have hE' : EnvOK p (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)) :=
      ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    have hvz : VRR ρ (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab))
        (.ptr .pub u) (shp (.ptr .pub ru)) [pw] .zero := by
      simp only [VR] at hvr; simp only [VRR]; exact ⟨hvr, rfl⟩
    have hfr := bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1R) (RLink_of hE'.2.1 hE'.2.2) hvz hlay
    rw [Res.add_zero] at hfr
    have hpa : PromAbove (stOf mem pairs th) := fun t ht m hm' => hpa0 t ht m hm'
    obtain ⟨H', cr', db', ⟨S', hH'L, hSK⟩, hC', heq⟩ :=
      MemHeld_pubS (V := (stOf mem pairs th).vs.vWr) (S := pubS η lab) hm hH hC hpa (hwp _ _ ⟨lab, 0⟩ hea (by simp [hpw])) hfo
        ⟨c, hsto, hown⟩
    have hHn : MemHeldK (CE η) (stOf mem pairs th) Sp (CE (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)))
        (fenceS (stOf mem pairs th) .st) H' := ⟨S', MemHeldL_eqs hH'L rfl rfl, hSK.toT _ _⟩
    have hCn : PromCr (CE (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)))
        (fenceS (stOf mem pairs th) .st) cr' db' :=
      PromCr_keep hC' rfl (MemInv_promLt hm) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    have hleT : Rr + Rs + H' + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db + ownW .own [pw] ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' :=
      Res.le_def.2 fun k => by
        have h1 := Res.le_def.1 hle k
        have h2 := congrArg (fun R : Res => R k) heq
        have h3 := congrArg (fun R : Res => R k) hR0
        simp only [Res.add_apply] at h1 h2 h3 ⊢; omega
    exact ⟨Rr + Rs, H', cr', db', _, [pw], hea,
      (fun ad g' h => by simp only [List.map_cons, List.map_nil, hpw] at h; cases h; simp [hsto]), ⟨CE (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)),
      EFootW_pub rfl rfl rfl rfl rfl ⟨c, hsto, hown⟩ (fun _ => rfl) (fun _ => Iff.rfl),
      ⟨ρ, η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab), c', Rr, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_publishW (E := CE η) (hF3 := hwin _ _ ⟨lab, 0⟩ hea (by simp [hpw])) hm hsto hown rfl rfl rfl rfl rfl rfl rfl (fun b S hseg _ => by
        obtain ⟨-, rfl⟩ := SegOf_lay hacc hseg
        have hcu : Ty.coupledOKIn c₁.ke u = true := by
          simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
        have htbu : tb c₁.ke.length u = true := by
          have h := (use_TvOK hu htv).2.1
          rw [← (use_TvOK hu htv).2.2] at h
          simpa [tb] using h
        exact TearOK_Fd hcty (TearOK_of_cpl
          (coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu)))
        (coupledOK_Fd hcty (by
          have hcu : Ty.coupledOKIn c₁.ke u = true := by
            simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
          have htbu : tb c₁.ke.length u = true := by
            have h := (use_TvOK hu htv).2.1
            rw [← (use_TvOK hu htv).2.2] at h
            simpa [tb] using h
          exact coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu))
        (noOwn_Fd hcty (by
          have hnu : Ty.noOwnIn c₁.ke u = true := by
            simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
          have htbu : tb c₁.ke.length u = true := by
            have h := (use_TvOK hu htv).2.1
            rw [← (use_TvOK hu htv).2.2] at h
            simpa [tb] using h
          exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
            (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) u hnu htbu))
        (rgnFree_Fd hcty (rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk)
          (by simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1)
          (hsc _ (use_cases hu).1 _ _ (Or.inl rfl)))),
      hHn, hCn⟩, hleT⟩
  | publishBuf hu hsh hb =>
    obtain ⟨n, k, u, c₁, hu, hsh, hb⟩ : ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) ∧
        Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true ∧
        c₁.bind x (.refine (.loc .pub (.array n u)) (.ini k)) = .ok c' := ⟨_, _, _, _, hu, hsh, hb⟩
    obtain ⟨rb, wsb, R0, Rr, hea, hvb, hlb, hvR, hi1R, hle⟩ := useR hu hi hE.2.2
    have hR0 := VRR_buf_R rfl hvR
    have hi1 := hi1R.1
    simp only [VR] at hvb
    obtain ⟨hv, hir⟩ := hvb
    have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
      rw [hlb.2.1]; rfl
    obtain ⟨μr, nr, ur, ψ, rfl, hμ, hsu⟩ := buf_runtime' hs'
    have hlay : Lay th.σs (.refine (.loc .pub (.array n u)) (.ini k)) (.refine (.loc .pub (.array nr ur)) ψ) wsb := by
      obtain ⟨h1, -, h3, h4⟩ := hlb
      refine ⟨h1, ?_, h3, h4.1, ?_⟩
      · rw [close_refine]
        show etok (rf (skel (.loc .pub (.array nr ur)))) = etok (rf (skel (close th.σs (.loc .pub (.array n u)))))
        rw [skel_close_locArr]
        show rf (.loc (skelM .pub) (.array (.lit 0) (etok (skel ur)))) = _
        rw [hsu]; rfl
      · simp only [close, substTs, lyt, etok, anyB_zero, Bool.false_eq_true, ite_false, idxC, ofMs, modeC]
        rw [(buf_lyt h4.2 rfl).2]; rfl
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .refine (.loc .pub (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr hpa0 => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat, hFU, hmode, hini⟩
    · -- a null handle (an empty buffer): only the fence
      have hvr : VR ρ η (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VR]; exact ⟨Or.inl ⟨hnull, e0, he0⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      have hvz : VRR ρ η (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb .zero := by
        simp only [VRR]; exact ⟨⟨Or.inl ⟨hnull, e0, he0⟩, rfl⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      have hfr := bindR hb hi1R (RLink_of hE.2.1 hE.2.2) hvz hlay
      rw [Res.add_zero] at hfr
      have hleT : Rr + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db + ownW .own wsb ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db :=
        Res.le_def.2 fun k => by
          have h1 := Res.le_def.1 hle k
          have h3 := congrArg (fun R : Res => R k) hR0
          simp only [Res.add_apply] at h1 h3 ⊢; omega
      exact ⟨Rr + Rs, H, cr, db, _, wsb, hea, (fun ad' g' h => by rw [hnull] at h; cases h), ⟨CE η, (EFoot.weak EFoot_refl), ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩, MemInv_fence hm,
        MemHeldK_eqs hH rfl rfl, PromCr_keep hC rfl (MemInv_promLt hm) (fun _ _ => rfl) (fun _ _ _ _ => rfl)⟩, hleT⟩
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c.owner = some η.tid := hmode
      have hx : Ext η (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)) :=
        Ext_withSto hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _) (fun l h => Or.inr h)
      have hvr : VR ρ (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label))
          (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VR]
        exact ⟨Or.inr ⟨ad, c, _, hws, hsto, hat, .refl,
          ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withSto, pubP], Or.inl (Or.inl rfl)⟩,
          (IniAt_mono (modeIni_le_ini _ _ _) hini)⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      have hE' : EnvOK p (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)) :=
        ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
      have hvz : VRR ρ (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label))
          (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb .zero := by
        simp only [VR] at hvr; simp only [VRR]; exact ⟨⟨hvr.1, rfl⟩, hvr.2⟩
      have hfr := bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1R) (RLink_of hE'.2.1 hE'.2.2) hvz hlay
      rw [Res.add_zero] at hfr
      have hpa : PromAbove (stOf mem pairs th) := fun t ht m hm' => hpa0 t ht m hm'
      obtain ⟨H', cr', db', ⟨S', hH'L, hSK⟩, hC', heq⟩ :=
        MemHeld_pubS (V := (stOf mem pairs th).vs.vWr) (S := pubS η ad.label) hm hH hC hpa (hwp _ _ ad hea hws) hfo
          ⟨c, hsto, hown⟩
      have hHn : MemHeldK (CE η) (stOf mem pairs th) Sp (CE (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)))
          (fenceS (stOf mem pairs th) .st) H' := ⟨S', MemHeldL_eqs hH'L rfl rfl, hSK.toT _ _⟩
      have hCn : PromCr (CE (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)))
          (fenceS (stOf mem pairs th) .st) cr' db' :=
        PromCr_keep hC' rfl (MemInv_promLt hm) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      have hleT : Rr + Rs + H' + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db + ownW .own wsb ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' :=
        Res.le_def.2 fun k => by
          have h1 := Res.le_def.1 hle k
          have h2 := congrArg (fun R : Res => R k) heq
          have h3 := congrArg (fun R : Res => R k) hR0
          simp only [Res.add_apply] at h1 h2 h3 ⊢; omega
      exact ⟨Rr + Rs, H', cr', db', _, wsb, hea, (fun ad' g' h => by rw [hws] at h; cases h; simp [hsto]), ⟨CE (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)),
        EFootW_pub rfl rfl rfl rfl rfl ⟨c, hsto, hown⟩ (fun _ => rfl) (fun _ => Iff.rfl),
        ⟨ρ, η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label), c', Rr, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
        MemInv_publishW (E := CE η) (hF3 := hwin _ _ ad hea hws) hm hsto hown rfl rfl rfl rfl rfl rfl rfl
          (fun b S hseg ha => by
            rcases hseg with ⟨-, rfl, -⟩ | ⟨N, usS, j, hT, -, -, -⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · have e1 := AtOff_arr_here hat hT ha (by simp [cl, accs])
              rw [hT] at e1
              simp only [cl, Ty.array.injEq] at e1
              obtain ⟨-, rfl⟩ := e1
              have hcu : Ty.coupledOKIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
              have htbu : tb c₁.ke.length (.array n u) = true := by
                have h := (use_TvOK hu htv).2.1
                rw [← (use_TvOK hu htv).2.2] at h
                simpa [tb] using h
              have := coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk)
                hcu htbu
              simp only [cl, Ty.coupledOK, Ty.coupledOKIn] at this; exact TearOK_of_cpl this)
          (by
            obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
            rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              have hcu : Ty.coupledOKIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
              have htbu : tb c₁.ke.length (.array n u) = true := by
                have h := (use_TvOK hu htv).2.1
                rw [← (use_TvOK hu htv).2.2] at h
                simpa [tb] using h
              exact coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk)
                hcu htbu)
          (by
            obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
            rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              have hnu : Ty.noOwnIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
              have htbu : tb c₁.ke.length (.array n u) = true := by
                have h := (use_TvOK hu htv).2.1
                rw [← (use_TvOK hu htv).2.2] at h
                simpa [tb] using h
              exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
                (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) _ hnu htbu)
          (by
            obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
            rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              exact rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk)
                (by simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1)
                (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))),
        hHn, hCn⟩, hleT⟩

theorem tstepMC_publishW {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr}
    {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    {cr db : Ts → Res} (hC : PromCr (CE η) (stOf mem pairs th) cr db) (hsc : PubScope cx a)
    (hwp : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      ∀ f, (CE η).pfr ad.label = some f → ¬ (CE η).seen ad.label → PubWin (CE η) (stOf mem pairs th) ad.label)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F cr' db',
      ThInvMCFSW p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F := by
  have h := tstepMR_publishW hterm hP hT hCk hi hE htv hm hH hsc hC hwp hwin hfo hRP hPS
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨Tot, H', cr', db', -, ws, -, -, h1, h2⟩ := h.2 r hr hpa
  refine ⟨Tot, H', ownW .own ws, .zero, cr', db', h1, .consume .own ws, ?_⟩
  simp only [Res.add_zero]; exact h2
/-- (A′) `Foot` with the weak footprint. -/
def FootW (g : G) (E E' : TEnv) (s s' : St) : Prop :=
  EFootW g E E' s s' ∧ ∀ l, FreshIn g s.nalloc s'.nalloc l →
    E.sto l = none ∧ E.box l = none ∧ E.ini l = 0 ∧ E.pfr l = none

theorem Foot.weak {g : G} {E E' : TEnv} {s s' : St} (h : Foot g E E' s s') : FootW g E E' s s' :=
  ⟨h.1.weak, h.2⟩

theorem FootW_ext {g : G} {η η' : TEnv} {s s' : St} (hf : FootW g (CE η) (CE η') s s') : Ext (CE η) (CE η') := by
  obtain ⟨⟨hp, ht, hst, hbx, hin, hpf, hse, -, -, hri, -⟩, hbl⟩ := hf
  refine ⟨Coh_CE η', rfl, hp, ht, fun l c hc => ?_, fun l => (hin l).1, fun l f hfl => ?_, hse,
    fun l B hB => ?_, Nat.le_refl _, CohR_CE η', hri⟩
  · rcases hst l with h | ⟨hl, -⟩
    · rw [h]; exact hc
    · rw [(hbl l hl).1] at hc; cases hc
  · rcases hpf l with h | ⟨h0, -⟩ | ⟨-, h0, -⟩
    · rw [h]; exact hfl
    · rw [h0] at hfl; cases hfl
    · rw [h0] at hfl; cases hfl
  · rcases hbx l with h | ⟨hl, -⟩
    · rw [h]; exact hB
    · rw [(hbl l hl).2.1] at hB; cases hB

theorem cNXW {Sp : AllocLabel → List Res} {t : Expr} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {η : TEnv}
    {Rf Rs H : Res} {cr db : Ts → Res}
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F cr' db',
      ThInvMCFSW p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F cr' db',
      ThInvMCFSW p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAt t C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F :=
  ⟨h.1, fun r hr hpa => let ⟨Tot, H', C, F, cr', db', h1, h2, h3⟩ := h.2 r hr hpa
    ⟨Tot, H', C, F, cr', db', h1, h2.toM, h2.claimAt _, h3⟩⟩

/-- (A′) `ThInvMCF` with the weak footprint. -/
def ThInvMCFW (p : Prog) (g : G) (E : TEnv) (s : St) (mem : Memory) (pairs : List Ts) (th : TTh) (Tot H : Res)
    (cr db : Ts → Res) : Prop :=
  ∃ E', EFootW g E E' s (stOf mem pairs th) ∧ ThInvRE p E' th Tot ∧ MemInv g E' (stOf mem pairs th) ∧
    MemHeld E' (stOf mem pairs th) H ∧ PromCr E' (stOf mem pairs th) cr db

theorem ThInvMCFSW.toF {p : Prog} {g : G} {E : TEnv} {s : St} {S0 : AllocLabel → List Res} {mem : Memory}
    {pairs : List Ts} {th : TTh} {Tot H : Res} {cr db : Ts → Res} (h : ThInvMCFSW p g E s S0 mem pairs th Tot H cr db) :
    ThInvMCFW p g E s mem pairs th Tot H cr db :=
  let ⟨E', h0, h1, h2, h3, h4⟩ := h
  ⟨E', h0, h1, h2, h3.memHeld, h4⟩

theorem tstepMF_stepW {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT3 (CE η) (stOf mem pairs th) th)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZ : ∀ l, BufInitOn th l → ¬ g.zf l := by exact fun _ _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ThInvMFW p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  by_cases hpub : ∃ x a e, th.term = .let_ x (.publish a) e
  · obtain ⟨x, a, e, ht⟩ := hpub
    have hsc' := hsc
    rw [ht] at hsc'
    exact paW <| tstepM_publishW ht hP hT hi hE htv hm hsc' (fun rt ws ad => hwin _ _ _ rt ws ad ht) hRP hPS
  · have h := tstepMF_step (hZ := ZOK_of_not hZ) (hPb := hPb) hP hp hn hnd hsc hT hi hE htv hm hbf hpx (fun x a e _ _ _ h => absurd ⟨x, a, e, h⟩ hpub) hRP hPS hSub hSig
    exact ⟨h.1, fun r hr hpa => (h.2 r hr hpa).weak⟩

theorem tstep_footprintW {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : ScopeD th.σs cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT3 (CE η) (stOf mem pairs th) th)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZ : ∀ l, BufInitOn th l → ¬ g.zf l := by exact fun _ _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', FootW g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) := by
  rcases hsc with hsc | ⟨-, hc⟩
  case inr =>
    have k := tstep_cap (g := g) (mem := mem) (pairs := pairs) hP hc hT hi hE htv hRP hPS
    refine ⟨k.1, fun r hr _ => ?_⟩
    have hF : FootW g (CE η) (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) :=
      ⟨(EFoot.weak EFoot_refl), fun l hl => fresh_blank hm hl⟩
    exact ⟨CE η, hF, FootW_ext hF, (k.2 r hr).1, MemInv_same hm (k.2 r hr).2⟩
  have h := tstepMF_stepW (hZ := hZ) (hPb := hPb) (hbf := hbf) hP hp hn hnd hsc hT hi hE htv hm hpx hwin hRP hPS hSub hSig
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨E', hF, h1, h2⟩ := h.2 r hr hpa
  have hF' : FootW g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := ⟨hF, fun l hl => fresh_blank hm hl⟩
  have hx : Ext (CE η) E' := by
    obtain ⟨_, η', _, hce, _⟩ := h1
    subst hce; exact FootW_ext hF'
  exact ⟨E', hF', hx, h1, h2⟩

theorem tstepMCF_stepLW {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th) (hnvp : OwnOpT cx th.term → OwnNVPF (CE η) (stOf mem pairs th))
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT3 (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRF : OwnFrontierRMWT (CE η) (stOf mem pairs th) th.term) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZ : ∀ l, BufInitOn th l → ¬ g.zf l := by exact fun _ _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F cr' db',
      ThInvMCFSW p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAt th.term C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F := by
  by_cases hpub : ∃ x a e, th.term = .let_ x (.publish a) e
  · obtain ⟨x, a, e, ht⟩ := hpub
    by_cases hR : StepScopeR th.σs cx th.term
    · have h := mcX (paW <| tstepMC_frame hP hp hnd hR hT hCk hi hE htv hm hH hC hRP hPS hSub hSig)
      exact ⟨h.1, fun r hr hpa => let ⟨Tot, H', C, F, cr', db', h1, h2⟩ := h.2 r hr hpa
        ⟨Tot, H', C, F, cr', db', h1.weak, h2⟩⟩
    · have hsc' := hsc.resolve_right hR
      rw [ht] at hsc'
      exact cNXW <| tstepMC_publishW ht hP hT hCk hi hE htv hm hH hC hsc' (fun rt ws ad => hwp x a e rt ws ad ht)
        (fun rt ws ad => hwin x a e rt ws ad ht) hfo hRP hPS
  · have h := mcX (tstepMCF_stepK (hZ := ZOK_of_not hZ) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia hdw hnvp
      (fun x a e h => hpub ⟨x, a, e, h⟩) hfo hRF hrmw hbf hRP hPS hSub hSig)
    exact ⟨h.1, fun r hr hpa => let ⟨Tot, H', C, F, cr', db', h1, h2⟩ := h.2 r hr hpa
      ⟨Tot, H', C, F, cr', db', h1.weak, h2⟩⟩

theorem tstepMCF_stepW {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hpx : PAx g mem pairs th) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th) (hnvp : OwnOpT cx th.term → OwnNVPF (CE η) (stOf mem pairs th))
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT3 (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRF : OwnFrontierRMWT (CE η) (stOf mem pairs th) th.term) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZ : ∀ l, BufInitOn th l → ¬ g.zf l := by exact fun _ _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F cr' db',
      ThInvMCFW p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAt th.term C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F := by
  obtain ⟨Sp, hH⟩ := hH.toS
  have h := tstepMCF_stepLW (hZ := hZ) (hPb := hPb) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia hdw hnvp hwp hwin hfo hRF hrmw hbf hRP hPS hSub hSig
  exact ⟨h.1, fun r hr hpa => let ⟨Tot, H', C, F, cr', db', h1, h2⟩ := h.2 r hr hpa
    ⟨Tot, H', C, F, cr', db', h1.toF, h2⟩⟩

theorem tstep_footprintMCW {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hpx : PAx g mem pairs th) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th) (hnvp : OwnOpT cx th.term → OwnNVPF (CE η) (stOf mem pairs th))
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT3 (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRF : OwnFrontierRMWT (CE η) (stOf mem pairs th) th.term) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZ : ∀ l, BufInitOn th l → ¬ g.zf l := by exact fun _ _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F cr' db',
      (∃ E', FootW g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvRE p E' r.2.2 Tot ∧
        MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ MemHeld E' (stOf r.1 r.2.1 r.2.2) H' ∧
        PromCr E' (stOf r.1 r.2.1 r.2.2) cr' db') ∧
      MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F := by
  have h := tstepMCF_stepW (hZ := hZ) (hPb := hPb) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia hdw hnvp hwp hwin hfo hRF hrmw hbf hRP hPS hSub hSig
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨Tot, H', C, F, cr', db', ⟨E', hF, h1, h2, h3, h4⟩, h5, -, h6⟩ := h.2 r hr hpa
  have hF' : FootW g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := ⟨hF, fun l hl => fresh_blank hm hl⟩
  have hx : Ext (CE η) E' := by
    obtain ⟨_, η', _, _, _, hce, _⟩ := h1
    subst hce; exact FootW_ext hF'
  exact ⟨Tot, H', C, F, cr', db', ⟨E', hF', hx, h1, h2, h3, h4⟩, h5, h6⟩

#print axioms TermStep.MemInv_publish0
#print axioms TermStep.MemInv_publishW
#print axioms TermStep.EFoot.weak
#print axioms TermStep.EFootW.riniW
#print axioms TermStep.EFootW_pub
#print axioms TermStep.ThInvMF.weak
#print axioms TermStep.ThInvMCFS.weak
#print axioms TermStep.PubWinT3_of
#print axioms TermStep.tstepM_publishW
#print axioms TermStep.tstepMR_publishW
#print axioms TermStep.tstepMC_publishW
#print axioms TermStep.Foot.weak
#print axioms TermStep.FootW_ext
#print axioms TermStep.cNXW
#print axioms TermStep.ThInvMCFSW.toF
#print axioms TermStep.tstepMF_stepW
#print axioms TermStep.tstep_footprintW
#print axioms TermStep.tstepMCF_stepLW
#print axioms TermStep.tstepMCF_stepW
#print axioms TermStep.tstep_footprintMCW
