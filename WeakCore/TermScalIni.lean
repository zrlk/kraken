import WeakCore.TermMainDefs
import WeakCore.TermPlantF

/-!
# TermScalIni — the scalar clause (`SysInvN.scalIni`)

At a cell with a frontier, a reader-visible count past the real count is a buffer's.  As a predicate
`ScalIni Eg` (the field's body): it holds at a frontier-free start (`scalIni_init`), and the promise
step's plant (`scalIni_egP`: a plant's count is 0 off buffers, `PlantN0`; `plantN_nonarr` for
`TermPlantF.plantN`), a thread step's `EgT` (`scalIni_egT`), and `withFp`
keep it (the spawn's box: `TermBoxG.sysInvN_box`).  `hscal_of` is its consumer form at an own cell.
-/

namespace TermScalIni

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The scalar clause: at a cell with a frontier, a reader-visible count past the real count is a
buffer's. -/
def ScalIni (Eg : GEnv) : Prop :=
  ∀ l cl f, Eg.sto l = some cl → Eg.pfr l = some f → Eg.rini l < Eg.ini l → ∃ N e, cl.ty = .array (.lit N) e

/-- Contrapositive form: a non-buffer cell with a frontier has `ini ≤ rini`. -/
theorem scalIni_le {Eg : GEnv} (h : ScalIni Eg) {l : AllocLabel} {cl : Cell} {f : Ts} (hs : Eg.sto l = some cl)
    (hf : Eg.pfr l = some f) (hna : ∀ N e, cl.ty ≠ .array (.lit N) e) : Eg.ini l ≤ Eg.rini l :=
  Nat.le_of_not_lt fun hlt => let ⟨N, e, he⟩ := h l cl f hs hf hlt; hna N e he

/-- At the initial configuration (no frontier anywhere) the clause holds. -/
theorem scalIni_init {Eg : GEnv} (h : ∀ l, Eg.pfr l = none) : ScalIni Eg := by
  intro l cl f _ hf; rw [h l] at hf; cases hf

/-- At a configuration with every count zero (a direct `StartOKX` start) the clause holds. -/
theorem scalIni_ini0 {Eg : GEnv} (h : ∀ l, Eg.ini l = 0) : ScalIni Eg := by
  intro l cl f _ _ hlt; rw [h l] at hlt; exact absurd hlt (Nat.not_lt_zero _)

/-- `slotCnt` is 0 off buffers. -/
theorem slotCnt_nonarr {c : Cell} (hna : ∀ N e, c.ty ≠ .array (.lit N) e) : slotCnt c = 0 := by
  unfold slotCnt
  split
  · rename_i Na e h; exact absurd h (hna Na e)
  · rfl

/-- The maximal held prefix is 0 at a label whose cell (if any) is not a buffer. -/
theorem np_nonarr {E : TEnv} {s : St} {l : AllocLabel}
    (hna : ∀ c, E.sto l = some c → ∀ N e, c.ty ≠ .array (.lit N) e) : Np E s l = 0 := by
  classical
  cases hc : E.sto l with
  | none => unfold Np; rw [hc]
  | some c =>
    rw [Np_of hc, slotCnt_nonarr (hna c hc)]
    rcases foldr_max_mem ((List.range (0 + 1)).filter fun n =>
        @decide (PrefixHeld E s l c n) (Classical.propDecidable _)) with h | h
    · exact h
    · have := List.mem_range.1 (List.mem_filter.1 h).1; omega

theorem npZ_nonarr {E : TEnv} {s : St} {l : AllocLabel}
    (hna : ∀ c, E.sto l = some c → ∀ N e, c.ty ≠ .array (.lit N) e) : NpZ E s l = 0 := by
  by_cases hz : EmptyZ E l
  · exact NpZ_of_empty hz
  · rw [NpZ_of_not hz]; exact np_nonarr hna

/-- The plant's count is 0 at a non-buffer cell of `Eg` (the cut's cell is `Eg`'s, or none). -/
theorem plantN_nonarr {c : Cfg} {Eg : GEnv} {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts}
    {l : AllocLabel} {cl : Cell} (hs : Eg.sto l = some cl) (hna : ∀ N e, cl.ty ≠ .array (.lit N) e) :
    TermPlantF.plantN c Eg j a v w l = 0 := by
  unfold TermPlantF.plantN
  split
  · rfl
  · refine npZ_nonarr fun c' hc' => ?_
    have h1 : cutSto Eg j l = some c' := hc'
    unfold cutSto at h1
    split at h1
    · rw [hs] at h1; cases h1; exact hna
    · cases h1


/-- (fresh-cell bound) An own cell with no frontier has `ini ≤ rini` (`OwnHidP.2`, contrapositive). -/
theorem ini_le_rini_of_ownHid {E : TEnv} {mem : Memory} {vs : VState} {P : List Ts} {l : AllocLabel} {c : Cell}
    (hH : OwnHidP E mem vs P) (hs : E.sto l = some c) (ho : c.owner = some E.tid) (hp : E.pfr l = none) :
    E.ini l ≤ E.rini l := by
  have hle : E.ini l ≤ E.rc l := Nat.le_of_not_lt fun hlt => by
    obtain ⟨f, hf, -⟩ := hH.2 l c hs ho hlt
    rw [hp] at hf; cases hf
  have : E.rc l ≤ E.rini l := by unfold TEnv.rc; exact Nat.min_le_right _ _
  omega

/-- (fresh-cell bound) A step's fresh cell has no frontier: `EFootB` sets frontiers only at old own
cells or at non-cell fresh labels. -/
theorem fresh_pfr_none {W : Ty → Prop} {g : G} {E E' : TEnv} {s s' : St} {l : AllocLabel} {cl : Cell}
    (hF : EFootB W g E E' s s') (hE : E.sto l = none) (hp : E.pfr l = none) (hs : E'.sto l = some cl) :
    E'.pfr l = none := by
  obtain ⟨-, -, -, -, -, hpf, -⟩ := hF
  rcases hpf l with h | ⟨-, F, -, -, -, ⟨c0, hc0, -⟩, -⟩ | ⟨-, -, hn⟩
  · rw [h]; exact hp
  · rw [hE] at hc0; cases hc0
  · rw [hn] at hs; cases hs

/-- An own cell of the cut (`tid = i`) with no frontier has `Eg.ini ≤ Eg.rini` (`OwnHidP.2` at the cut). -/
theorem cut_ini_le {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {mem : Memory} {vs : VState} {P : List Ts}
    {l : AllocLabel} {cl : Cell} (hH : OwnHidP (Cut Eg i S) mem vs P) (hs : Eg.sto l = some cl)
    (ho : cl.owner = some i) (hp : Eg.pfr l = none) : Eg.ini l ≤ Eg.rini l :=
  ini_le_rini_of_ownHid (E := Cut Eg i S) hH
    (show cutSto Eg i l = some cl by
      unfold cutSto; simp only [show Eg.InCut i l from ⟨cl, hs, Or.inl ho⟩, ↓reduceIte]; exact hs) ho hp

/-- A plant `(P, N)` at `Eg` has count 0 at a planted non-buffer cell. -/
def PlantN0 (Eg : GEnv) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) : Prop :=
  ∀ l f cl, P l = some f → Eg.sto l = some cl → (∀ N e, cl.ty ≠ .array (.lit N) e) → N l = 0

/-- `TermPlantF.plantN` is such a plant count. -/
theorem plantN0_of (c : Cfg) (Eg : GEnv) (j : Nat) (a : Address) (v : WeakMem.Val) (w : Ts) :
    PlantN0 Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) :=
  fun _ _ _ _ hs hna => plantN_nonarr hs hna

/-- **Promise step**: the plant keeps the clause (`PlantSpec`: a planted label is a frontier-free own
cell of the promiser `j`; `PlantN0`: its count is 0 off buffers). -/
theorem scalIni_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {Nf : AllocLabel → Nat} {j n n0 : Nat}
    {S : AllocLabel → Prop} {mem : Memory} {vs : VState} {Ps : List Ts}
    (h : ScalIni Eg) (hspec : PlantSpec Eg P j n0) (hN0 : PlantN0 Eg P Nf)
    (hH : OwnHidP (Cut Eg j S) mem vs Ps) :
    ScalIni (EgP Eg P Nf j n) := by
  intro l cl f hs hf hlt
  have hs0 : Eg.sto l = some cl := hs
  refine Classical.byContradiction fun hne => ?_
  have hna : ∀ N e, cl.ty ≠ .array (.lit N) e := fun N e he => hne ⟨N, e, he⟩
  have hr : (EgP Eg P Nf j n).rini l = Eg.rini l := rfl
  have hle : Eg.ini l ≤ Eg.rini l := by
    cases hq : P l with
    | none =>
      have : (EgP Eg P Nf j n).pfr l = Eg.pfr l := by
        show (plantG Eg P Nf).pfr l = _
        simp only [plantG, hq]
      rw [this] at hf; exact scalIni_le h hs0 hf hna
    | some f' =>
      obtain ⟨hp0, ⟨c1, hc1, ho1⟩, -⟩ := hspec l f' hq
      rw [hs0] at hc1; cases hc1
      exact cut_ini_le hH hs0 ho1 hp0
  have hi : (EgP Eg P Nf j n).ini l ≤ Eg.ini l := by
    show (plantG Eg P Nf).ini l ≤ _
    simp only [plantG]
    split
    · rename_i f' hq; rw [hN0 l f' cl hq hs0 hna]; omega
    · exact Nat.le_refl _
  omega

/-- **Thread step** of `i` (cut `Cut Eg i S`, pre-state `OwnHidP`): `EgT` keeps the clause.  A fresh cell
has no frontier (`fresh_pfr_none`, from `GFreshL`); an old cell's count rises only at an own cell, to
at most `max ini rini'`; a frontier set in the step is at an own frontier-free cell (`OwnHidP.2`). -/
theorem scalIni_egT {W : Ty → Prop} {g : G} {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {E' : TEnv}
    {s s' : St} {c' : Cfg} {mem : Memory} {vs : VState} {P : List Ts}
    (h : ScalIni Eg) (hF : EFootB W g (Cut Eg i S) E' s s') (hH : OwnHidP (Cut Eg i S) mem vs P)
    (hfr0 : ∀ l, FreshIn g s.nalloc s'.nalloc l → Eg.sto l = none ∧ Eg.pfr l = none) :
    ScalIni (EgT Eg g s.nalloc s'.nalloc E' c') := by
  have hF' := hF
  obtain ⟨-, -, -, -, hini, hpf, -, -, -, hrm, -⟩ := hF
  intro l cl f hs hf hlt
  have hi' : (EgT Eg g s.nalloc s'.nalloc E' c').ini l = E'.ini l := rfl
  have hr' : (EgT Eg g s.nalloc s'.nalloc E' c').rini l = E'.rini l := rfl
  have hf' : E'.pfr l = some f := hf
  rw [hi', hr'] at hlt
  refine Classical.byContradiction fun hne => ?_
  have hna : ∀ N e, cl.ty ≠ .array (.lit N) e := fun N e he => hne ⟨N, e, he⟩
  by_cases hfr : FreshIn g s.nalloc s'.nalloc l
  · have hs1 : E'.sto l = some cl := by
      have : (EgT Eg g s.nalloc s'.nalloc E' c').sto l = E'.sto l := by
        show (Eg.post g s.nalloc s'.nalloc E').sto l = _
        exact post_sto_fresh hfr
      rw [← this]; exact hs
    obtain ⟨hn1, hn2⟩ := hfr0 l hfr
    have := fresh_pfr_none hF' (E := Cut Eg i S) (by show cutSto Eg i l = none; unfold cutSto; split <;> simp [hn1]) hn2 hs1
    rw [this] at hf'; cases hf'
  · have hs0 : Eg.sto l = some cl := by
      have : (EgT Eg g s.nalloc s'.nalloc E' c').sto l = Eg.sto l := by
        show (Eg.post g s.nalloc s'.nalloc E').sto l = _
        exact post_sto_old hfr
      rw [← this]; exact hs
    have hle : Eg.ini l ≤ Eg.rini l := by
      cases hq : Eg.pfr l with
      | some f0 => exact scalIni_le h hs0 hq hna
      | none =>
        rcases hpf l with he | ⟨-, F, -, -, -, ⟨c1, hc1, ho1⟩, -⟩ | ⟨hf2, -, -⟩
        · change E'.pfr l = Eg.pfr l at he; rw [he, hq] at hf'; cases hf'
        · have hc1' : cutSto Eg i l = some c1 := hc1
          unfold cutSto at hc1'
          split at hc1'
          · rw [hs0] at hc1'; cases hc1'
            exact cut_ini_le hH hs0 ho1 hq
          · cases hc1'
        · exact absurd hf2 hfr
    have hr := hrm l
    obtain ⟨-, hc⟩ := hini l
    change Eg.rini l ≤ E'.rini l at hr
    rcases hc with he | hf2 | ⟨-, hmax, -⟩
    · change E'.ini l = Eg.ini l at he; omega
    · exact hfr hf2
    · change E'.ini l ≤ max (Eg.ini l) (E'.rini l) at hmax; omega


/-- **L9's `hscal` from the clause** (`DebtG3.bfail_holder`): at `i`'s own cell, a frontier-free one by
`OwnHidP.2`, one with a frontier by the clause plus `stoLay` (an array-lit `LayT` element has `accs`). -/
theorem hscal_of {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {mem : Memory} {vs : VState} {P : List Ts}
    {l : AllocLabel} {cl : Cell} (hsc : ScalIni Eg) (hH : OwnHidP (Cut Eg i S) mem vs P)
    (hlay : ∀ l cl, Eg.sto l = some cl → LayT cl.ty)
    (hlab : (∃ cl0, Eg.sto l = some cl0 ∧ cl0.owner = some i) ∨ Eg.ini l = 0)
    (hcl : ∀ cl0, Eg.sto l = some cl0 → cl0 = cl) :
    (∀ N e us, cl.ty = .array (.lit N) e → accs e = some us → False) → Eg.ini l ≤ Eg.rini l := by
  intro hnb
  rcases hlab with ⟨cl0, hs0, ho0⟩ | h0
  · have e0 := hcl cl0 hs0
    subst e0
    cases hq : Eg.pfr l with
    | none => exact cut_ini_le hH hs0 ho0 hq
    | some f =>
      refine Nat.le_of_not_lt fun hlt => ?_
      obtain ⟨N, e, he⟩ := hsc l cl0 f hs0 hq hlt
      rcases hlay l cl0 hs0 with ha | ⟨n, e', he', ha⟩
      · rw [he] at ha; exact ha (by simp [accs])
      · rw [he] at he'; cases he'
        cases hu : accs e with
        | none => exact ha hu
        | some us => exact hnb N e us he hu
  · omega


/-- `withFp` (foreign promises) does not touch the clause. -/
theorem scalIni_withFp {Eg : GEnv} {F : Nat → List Ts} (h : ScalIni Eg) : ScalIni (Eg.withFp F) :=
  fun l cl f hs hf hlt => h l cl f hs hf hlt

end TermScalIni

#print axioms TermScalIni.scalIni_le
#print axioms TermScalIni.np_nonarr
#print axioms TermScalIni.plantN_nonarr
#print axioms TermScalIni.scalIni_egP
#print axioms TermScalIni.plantN0_of
#print axioms TermScalIni.scalIni_egT
#print axioms TermScalIni.ini_le_rini_of_ownHid
#print axioms TermScalIni.fresh_pfr_none
#print axioms TermScalIni.scalIni_init
#print axioms TermScalIni.cut_ini_le
#print axioms TermScalIni.hscal_of
#print axioms TermScalIni.scalIni_withFp
#print axioms TermScalIni.slotCnt_nonarr
#print axioms TermScalIni.npZ_nonarr
#print axioms TermScalIni.scalIni_ini0
