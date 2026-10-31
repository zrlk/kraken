import WeakCore.TermOverCrBII
import WeakCore.TermBal
import WeakCore.TermOwnFresh

/-!
# Pool staging: the twelve pool members as named explicit hypotheses

Members (each a `∀`-implicit `Prop`, no instance, no sorry, no axiom):
`ownA ownC fgnCov f1T poolTagOwnT poolBalT poolKnetT poolRidT poolBalP poolKnetP poolRidP poolTagP`.

Thread step of `i` (`Eg' := EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c'`,
`s := stOf c.mem c.pairs th`, `s' := stOf r.1 r.2.1 r.2.2`): the transfer `δ` splits as
`δc + δh` (credited / pool part, `δc`/`δh` below are the intended instances); the post credits
and pool are `updD cr i cr' δc` and `updD pl i (plStep pl i s' plh) δh` (`crN`).
-/

namespace TermPoolStaging
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII TermBal TermOwnFresh
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Shapes -/

/-- The `PoolTag` body for thread `j` (state `thj`) at `t`, at credit family `f`. -/
def PTag (Eg : GEnv) (c : Cfg) (j : Nat) (thj : TTh) (f : Ts → Res) (t : Ts) : Prop :=
  t ∈ thj.promises ∧ TermPlant.CrKeys (f t) ∧
    ∃ m, c.mem[t]? = some m ∧
      ((∀ S : AllocLabel → Prop, ∃ fq mf, fq ∈ FpAt (Cut Eg j S) ⟨m.loc.label, 0⟩ ∧ c.mem[fq]? = some mf ∧
          mf.loc.label = m.loc.label ∧ fq ≤ t) ∨
        ∀ S : AllocLabel → Prop, (Cut Eg j S).pfr m.loc.label ≠ none ∧
          ∃ cl x, (Cut Eg j S).sto m.loc.label = some cl ∧ cl.owner = some j ∧ x.1 = t ∧
            (∀ i, x.2.2.2.2.2 i = false) ∧
            TermPiece.CrItem (Cut Eg j S) (stOf c.mem c.pairs thj) f m.loc.label cl x) ∧
      ∀ S : AllocLabel → Prop, ∃ cl x, (Cut Eg j S).sto m.loc.label = some cl ∧ cl.owner = some j ∧ x.1 = t ∧
        TermPiece.CrItem (Cut Eg j S) (stOf c.mem c.pairs thj) f m.loc.label cl x ∧
        PieceLow c.mem thj.promises m.loc.label x.2.1 x.2.2.1 t

theorem poolTag_iff {Eg : GEnv} {c : Cfg} {pl : Nat → Ts → Res} :
    PoolTag Eg c pl ↔ (∀ j thj t, c.ths[j]? = some thj → pl j t ≠ .zero → PTag Eg c j thj (pl j) t) ∧
      PoolCovUL Eg c pl :=
  Iff.rfl

/-- (QC) `V` is a key-free plant credit of `t` at every cut of `j` after the step. -/
def QC (Eg' : GEnv) (c' : Cfg) (j : Nat) (t : Ts) (V : Res) : Prop :=
  ∃ m, c'.mem[t]? = some m ∧ ∀ (Sj : AllocLabel → Prop) thj', c'.ths[j]? = some thj' →
    PlantCr (Cut Eg' j Sj) (stOf c'.mem c'.pairs thj') m t V ∧ TermPlant.CrKeys V

/-- (F-Pool) `t` is the first write at a predicted slot unit of `j` (every cut): at
`bufInit` its credit is consumed inside the slot's payment (`SlotPayS`, stated at the actual
credits), so a transfer to it is routed to the pool instead (`QCr`). -/
def SlotFW (Eg' : GEnv) (c' : Cfg) (j : Nat) (t : Ts) : Prop :=
  ∃ m, c'.mem[t]? = some m ∧ FirstW c'.mem m.loc t ∧ ∀ Sj : AllocLabel → Prop, PredU (Cut Eg' j Sj) m.loc

/-- The credited-part test: a plant credit (`QC`) at a target off `SlotFW`. -/
def QCr (Eg' : GEnv) (c' : Cfg) (j : Nat) (t : Ts) (V : Res) : Prop :=
  QC Eg' c' j t V ∧ ¬ SlotFW Eg' c' j t

theorem QCr.qc {Eg' : GEnv} {c' : Cfg} {j : Nat} {t : Ts} {V : Res} (h : QCr Eg' c' j t V) :
    QC Eg' c' j t V := h.1

/-- The credited part of the transfer: at a foreign promise where it is a plant credit (off
`SlotFW`, `QCr`). -/
noncomputable def δc (δ : Ts → Res) (cr : Nat → Ts → Res) (c c' : Cfg) (Eg' : GEnv) (i : Nat) : Ts → Res := by
  classical
  exact fun t => if ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ QCr Eg' c' j t (cr j t + δ t)
    then δ t else .zero

/-- The pool part of the transfer: off `δc`'s support, at a foreign promise where it is no
credited plant credit (`QCr`: no plant credit, or a `SlotFW` target) but a pool tag. -/
noncomputable def δh (δ : Ts → Res) (cr pl : Nat → Ts → Res) (c c' : Cfg) (Eg' : GEnv) (i : Nat) : Ts → Res := by
  classical
  exact fun t => if (¬ ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ QCr Eg' c' j t (cr j t + δ t)) ∧
      ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ ¬ QCr Eg' c' j t (cr j t + δ t) ∧
      ∀ thj', c'.ths[j]? = some thj' → PTag Eg' c' j thj' (fun u => pl j u + δ u) t
    then δ t else .zero

/-- `PTag` reads its credit family only at `t`. -/
theorem PTag_congr {Eg : GEnv} {c : Cfg} {j : Nat} {thj : TTh} {f g : Ts → Res} {t : Ts} (e : f t = g t)
    (h : PTag Eg c j thj f t) : PTag Eg c j thj g t := by
  obtain ⟨h1, h2, m, hm, h3, h4⟩ := h
  refine ⟨h1, by rw [← e]; exact h2, m, hm, ?_, fun S => ?_⟩
  · refine h3.imp id fun h3 S => ?_
    obtain ⟨hpf, cl, x, hcl, ho, hx, hK, ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩⟩ :=
      h3 S
    refine ⟨hpf, cl, x, hcl, ho, hx, hK, ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, ?_, a13⟩⟩
    rw [hx, ← e]; rw [hx] at a12; exact a12
  obtain ⟨cl, x, hcl, ho, hx, ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩, hpl⟩ := h4 S
  refine ⟨cl, x, hcl, ho, hx, ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, ?_, a13⟩, hpl⟩
  rw [hx, ← e]; rw [hx] at a12; exact a12

/-- The two parts are disjoint: together at most the transfer. -/
theorem δc_add_δh_le (δ : Ts → Res) (cr pl : Nat → Ts → Res) (c c' : Cfg) (Eg' : GEnv) (i : Nat) (t : Ts) :
    δc δ cr c c' Eg' i t + δh δ cr pl c c' Eg' i t ≤ δ t := by
  classical
  unfold δc δh
  by_cases hC : ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ QCr Eg' c' j t (cr j t + δ t)
  · have hn : ¬ ((¬ ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ QCr Eg' c' j t (cr j t + δ t)) ∧
        ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ ¬ QCr Eg' c' j t (cr j t + δ t) ∧
        ∀ thj', c'.ths[j]? = some thj' → PTag Eg' c' j thj' (fun u => pl j u + δ u) t) := fun h => h.1 hC
    simp only [ite_eq_left hC, ite_eq_right hn, Res.add_zero]; exact Res.le_refl _
  · simp only [ite_eq_right hC, Res.zero_add]
    split
    · exact Res.le_refl _
    · exact Res.zero_le _

/-- `δc` is a `CrShiftP` transfer. -/
theorem crShiftP_δc (δ : Ts → Res) (cr : Nat → Ts → Res) (c c' : Cfg) (Eg' : GEnv) (i : Nat) :
    CrShiftP c c' Eg' cr i (δc δ cr c c' Eg' i) := by
  classical
  intro t ht
  unfold δc at ht ⊢
  by_cases hC : ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ QCr Eg' c' j t (cr j t + δ t)
  · obtain ⟨j, thj, hji, hj, ht', ⟨m, hm, hq⟩, hns⟩ := hC
    have hC' : ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ QCr Eg' c' j t (cr j t + δ t) :=
      ⟨j, thj, hji, hj, ht', ⟨m, hm, hq⟩, hns⟩
    simp only [ite_eq_left hC']
    exact ⟨j, thj, m, hji, hj, ht', hm, hq⟩
  · simp only [ite_eq_right hC] at ht; exact absurd rfl ht

/-- `δh`'s items are pool tags at post (`f1T`'s pool hypothesis at the instance). -/
theorem δh_tag (δ : Ts → Res) (cr pl : Nat → Ts → Res) (c c' : Cfg) (Eg' : GEnv) (i : Nat) :
    ∀ t, δh δ cr pl c c' Eg' i t ≠ .zero → ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧
      ∀ thj', c'.ths[j]? = some thj' → PTag Eg' c' j thj' (fun u => pl j u + δh δ cr pl c c' Eg' i u) t := by
  classical
  intro t ht
  by_cases hH : (¬ ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ QCr Eg' c' j t (cr j t + δ t)) ∧
      ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ ¬ QCr Eg' c' j t (cr j t + δ t) ∧
      ∀ thj', c'.ths[j]? = some thj' → PTag Eg' c' j thj' (fun u => pl j u + δ u) t
  · have e : δh δ cr pl c c' Eg' i t = δ t := by unfold δh; rw [ite_eq_left hH]
    obtain ⟨-, j, thj, hji, hj, ht', -, hP⟩ := hH
    exact ⟨j, thj, hji, hj, ht', fun thj' h' => PTag_congr (by show pl j t + δ t = pl j t + _; rw [e]) (hP thj' h')⟩
  · exact absurd (by unfold δh; rw [ite_eq_right hH]) ht

-- HOLE(hWbR COVER): the COVER conjunct of `PoolTag`/`PTag` goes
-- here (and in `TermPool.PoolTag`) if route (i) joins this revision.

/-- The post-step credits plus pool of a thread step of `i`. -/
noncomputable def crN (cr pl : Nat → Ts → Res) (i : Nat) (cr' : Ts → Res) (s' : St) (plh dc dh : Ts → Res) :
    Nat → Ts → Res :=
  crPl (updD cr i cr' dc) (updD pl i (plStep pl i s' plh) dh)

/-- The pool invariant (the intended `SysInvN.pool` field): tags, cover, balance, net keys and rid
freshness at credits plus pool. -/
structure PoolInv (Init : Res) (MintOK : Res → Prop) (c : Cfg) (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res)
    (cr db pl : Nat → Ts → Res) : Prop where
  tag : PoolTag Eg c pl
  cov : TermOverCr.OverCrG Eg c (crPl cr pl)
  bal : ∃ M, MintOK M ∧
    thSum c.ths.size (fun i => Tot i + pSumAt c i (crPl cr pl i) + HP i) + HS ≤
      Init + M + thSum c.ths.size (fun i => pSumAt c i (db i))
  knet : ∀ key, ExclKey key → KeyNet c Tot HP HS (crPl cr pl) db key
  rid : ∃ rc, RidOK c Tot HP HS (crPl cr pl) db rc

/-! ## Monotonicity -/

theorem cr_le_crPl (cr pl : Nat → Ts → Res) (j : Nat) (t : Ts) : cr j t ≤ crPl cr pl j t :=
  Res.le_add_right _ _

theorem crPl_apply (cr pl : Nat → Ts → Res) (j : Nat) (t : Ts) : crPl cr pl j t = cr j t + pl j t := rfl

theorem nsum_mono {ns : List Nat} {f g : Nat → Nat} (h : ∀ n, f n ≤ g n) : (ns.map f).sum ≤ (ns.map g).sum := by
  induction ns with
  | nil => exact Nat.le_refl _
  | cons n ns ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h n) ih

theorem pSumAt_mono (c : Cfg) (n : Nat) {f g : Ts → Res} (h : ∀ t, f t ≤ g t) : pSumAt c n f ≤ pSumAt c n g := by
  unfold pSumAt
  split
  · exact sum_map_le _ (fun t _ => h t)
  · exact Res.le_refl _

theorem pSumAt_le_crPl (c : Cfg) (cr pl : Nat → Ts → Res) (n : Nat) : pSumAt c n (cr n) ≤ pSumAt c n (crPl cr pl n) :=
  pSumAt_mono c n (fun t => cr_le_crPl cr pl n t)

/-- The pool balance gives the old `SysInvN.bal` (credits only). -/
theorem bal_of_pool {Init : Res} {MintOK : Res → Prop} {c : Cfg} {Tot HP : Nat → Res} {HS : Res}
    {cr db pl : Nat → Ts → Res}
    (h : ∃ M, MintOK M ∧
      thSum c.ths.size (fun i => Tot i + pSumAt c i (crPl cr pl i) + HP i) + HS ≤
        Init + M + thSum c.ths.size (fun i => pSumAt c i (db i))) :
    ∃ M, MintOK M ∧
      thSum c.ths.size (fun i => Tot i + pSumAt c i (cr i) + HP i) + HS ≤
        Init + M + thSum c.ths.size (fun i => pSumAt c i (db i)) := by
  obtain ⟨M, hM, hb⟩ := h
  refine ⟨M, hM, Res.le_trans (fun key => ?_) hb⟩
  simp only [Res.add_apply, thSum_apply]
  refine Nat.add_le_add_right (nsum_mono (fun n => ?_)) _
  have := pSumAt_le_crPl c cr pl n key
  omega

/-- The pool net key bound gives the old one (credits only). -/
theorem knet_of_pool {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {key : Key}
    (h : KeyNet c Tot HP HS (crPl cr pl) db key) : KeyNet c Tot HP HS cr db key := by
  refine Nat.le_trans (Nat.add_le_add_right (nsum_mono (fun n => ?_)) _) h
  simp only [Res.add_apply]
  have := pSumAt_le_crPl c cr pl n key
  omega

/-- The pool rid freshness gives the old one (credits only). -/
theorem rid_of_pool {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {rc : Nat → Nat}
    (h : RidOK c Tot HP HS (crPl cr pl) db rc) : RidOK c Tot HP HS cr db rc := by
  intro n hn key hk
  refine Nat.le_trans (Nat.add_le_add_right (nsum_mono (fun m => ?_)) _) (h n hn key hk)
  simp only [Res.add_apply]
  have := pSumAt_le_crPl c cr pl m key
  omega

/-- `PoolInv` gives the old `SysInvN` fields `bal`, `knet`, `rid` at the credits `cr` alone. -/
theorem PoolInv.old {Init : Res} {MintOK : Res → Prop} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db pl : Nat → Ts → Res} (h : PoolInv Init MintOK c Eg Tot HP HS cr db pl) :
    (∃ M, MintOK M ∧
      thSum c.ths.size (fun i => Tot i + pSumAt c i (cr i) + HP i) + HS ≤
        Init + M + thSum c.ths.size (fun i => pSumAt c i (db i))) ∧
    (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧ (∃ rc, RidOK c Tot HP HS cr db rc) :=
  ⟨bal_of_pool h.bal, fun key hk => knet_of_pool (h.knet key hk),
    let ⟨rc, hrc⟩ := h.rid; ⟨rc, rid_of_pool hrc⟩⟩

/-! ## The members -/

/-- own cover, own-path kinds.  Discharge: new (the `OpenOverCrOwnA` proof). -/
def ownA (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  OpenOverCrOwnA p k arch Sp Init MintOK c0

/-- own cover, remaining kinds.  Discharge: new (the `OpenOverCrOwnC` proof). -/
def ownC (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  OpenOverCrOwnC p k arch Sp Init MintOK c0

/-- The target facts `hPd` of `TermOverCrW.foreign_overCrCfg1PV` (verbatim). -/
def HPd (c c' : Cfg) (Eg : GEnv) (Gd : List TermPiece.GdE) (tg : TermPiece.GdE → Option Ts) : Prop :=
  ∀ g ∈ Gd, ∀ t, tg g = some t → ∃ j0 thj0 m, c.ths[j0]? = some thj0 ∧ t ∈ thj0.promises ∧
    c'.mem[t]? = some m ∧ m.loc.label = g.l ∧ ∃ us, accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us ∧
      (∀ t' m', t' ∈ thj0.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      (∃ cl0, Eg.sto m.loc.label = some cl0 ∧ cl0.owner = some j0) ∧
      ∀ S0 : AllocLabel → Prop, ¬ WordUnit (Cut Eg j0 S0) m.loc

/-- `htgW1` of `TermOverCrW.foreign_overCrCfg1PV` (verbatim). -/
def HtgW1At (c : Cfg) (Eg : GEnv) (j : Nat) (thj : TTh) (Sj : AllocLabel → Prop) (l : AllocLabel) (cl : Cell)
    (Gd : List TermPiece.GdE) (tg : TermPiece.GdE → Option Ts) : Prop :=
  ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
    ¬ WordUnit (Cut Eg j Sj) ⟨l, o⟩ →
    ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
    (AtOff cl.ty g.b g.S → ∀ jj, TwoAt us jj → o ≠ g.b + jj ∧ o ≠ g.b + jj + 1) → ∃ t, tg g = some t

/-- **The stepper's target facts** for the drop list `Gd`/`tg` of a thread step of `i`
(`fgnCov`'s `tg` is otherwise constrained only by `δ`): the `pub`-store coverage export, the
targets (`hPd`), `htgW1` at every foreign owner's frontier cell after the step, and off a `pub`
store an empty drop list with the stepper's `MemInv`. -/
def StepTgt (p : Prog) (k : Promises.Knobs) (arch : Arch) (c c' : Cfg) (Eg : GEnv) (i : Nat)
    (th : TTh) (r : Memory × List Ts × TTh) (η : TEnv) (cx : Cx) (E' : TEnv)
    (Gd : List TermPiece.GdE) (tg : TermPiece.GdE → Option Ts) : Prop :=
  (TermPiece.PubShape cx th → TermPiece.GdCovT (CE η) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) ∧
    HPd c c' Eg Gd tg ∧
    (∀ (j : Nat) (thj : TTh) (Sj : AllocLabel → Prop) (l : AllocLabel) (cl : Cell), j ≠ i →
      c.ths[j]? = some thj →
      (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl → cl.owner = some j →
      (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none →
      HtgW1At c Eg j thj Sj l cl Gd tg) ∧
    (¬ TermPiece.PubShape cx th → Gd = [] ∧ MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))

/-- **Foreign cover after a thread step**, at `crN`, for every owner `j ≠ i` of a published
cell, given the pre-state pool cover, the transfer `δ = plantD1 Gd GdE.R tg` from the drop list,
at the split instance `δc`/`δh` (so the coverage content — every item the cover needs is `QC` or a
pool tag — lives here).  Discharge: `TermOverCrW.foreign_overCrCfg1PV` at `cv := crPl cr pl` (+ `NPOUV`). -/
def fgnCov (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ plh : Ts → Res}
    {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ → StepCrQ cr pl i r.2.2.promises crS →
    TermOverCr.OverCrG Eg c (crPl cr pl) → PoolTag Eg c pl →
    TermPiece.Drop (CE η) (stOf c.mem c.pairs th) Gd →
    (∀ t, δ t = TermPlant.plantD1 Gd TermPiece.GdE.R tg t) →
    StepTgt p k arch c c' Eg i th r η cx E' Gd tg →
    ∀ (j : Nat) (thj : TTh) (Sj : AllocLabel → Prop) (l : AllocLabel) (cl : Cell), j ≠ i →
      c.ths[j]? = some thj →
      (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl → cl.owner = some j →
      (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none →
      TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj)
        (crN cr pl i cr' (stOf r.1 r.2.1 r.2.2) plh
          (δc δ cr c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i)
          (δh δ cr pl c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i) j) l cl

/-- A pool item with its key bits extended by `K` (at its holder and offset): holder,
offset, type, words and resource unchanged, bits only grow. -/
def bitExt (K : Ts → Nat → Nat → Bool) (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :
    Ts × Nat × Ty × List Word × Res × (Nat → Bool) :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, fun ii => x.2.2.2.2.2 ii || K x.1 x.2.1 ii)

theorem sum_bitExt (K : Ts → Nat → Nat → Bool) (Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))
    (t : Ts) : Res.sum (((Gs.map (bitExt K)).filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1)) =
      Res.sum ((Gs.filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1)) := by
  induction Gs with
  | nil => rfl
  | cons a G ih =>
    by_cases h : a.1 = t
    · simp only [List.map_cons, List.filter_cons, bitExt, h, decide_true, ite_true, Res.sum]
      exact congrArg _ ih
    · simp only [List.map_cons, List.filter_cons, bitExt, h, decide_false]
      exact ih

/-- (F1T `hNew`) **The new foreign items after a step**, at an owned, published,
unpublished cell `l` of a foreign thread `j ≠ i`: for every pre list `Gs` (pre items at `pl j`
covering the pre-state units), a bit extension `Gs.map (bitExt K)` (pre items re-pinned after the
step, e.g. at a same-holder second creation) and new items `Gn` funded by the deposits `dh` are
post items at `pl j + dh` and cover every post unit. -/
def FgnNewC (p : Prog) (k : Promises.Knobs) (arch : Arch) (c c' : Cfg) (Eg : GEnv) (pl : Nat → Ts → Res)
    (i : Nat) (th : TTh) (r : Memory × List Ts × TTh) (E' : TEnv) (dh : Ts → Res) (j : Nat) (thj thj' : TTh)
    (Sj : AllocLabel → Prop) (l : AllocLabel) (cl : Cell) : Prop :=
  ∀ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)),
    ((Cut Eg j Sj).sto l = some cl ∧ Eg.pfr l ≠ none ∧ ¬ Eg.pubd l ∨ Gs = []) →
    (∀ x ∈ Gs, TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj) (pl j) l cl x) →
    (∀ o tw, (Cut Eg j Sj).sto l = some cl ∧ Eg.pfr l ≠ none ∧ ¬ Eg.pubd l ∧
        PredU (Cut Eg j Sj) ⟨l, o⟩ ∧ ¬ VisU (Cut Eg j Sj) ⟨l, o⟩ ∧
        TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw ∧ FirstW c.mem ⟨l, o⟩ tw ∧
        TermPlant.OverT (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      ∃ x ∈ Gs, ∃ usS ii, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS ii (o - x.2.1) ∧
        x.2.2.2.2.2 ii = true) →
    ∃ (K : Ts → Nat → Nat → Bool) (Gn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))),
      (∀ t, Res.sum ((Gn.filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1)) ≤ dh t) ∧
      (∀ x ∈ Gs.map (bitExt K) ++ Gn,
        TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
          (stOf c'.mem c'.pairs thj') (fun u => pl j u + dh u) l cl x) ∧
      ∀ o tw, PredU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
        ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
        TermPlant.LowOwn (stOf c'.mem c'.pairs thj') ⟨l, o⟩ tw → FirstW c'.mem ⟨l, o⟩ tw →
        TermPlant.OverT (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
          (stOf c'.mem c'.pairs thj') ⟨l, o⟩ tw →
        ∃ x ∈ Gs.map (bitExt K) ++ Gn, ∃ usS ii, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
          InAcc usS ii (o - x.2.1) ∧ x.2.2.2.2.2 ii = true

/-- **F1T, foreign part**: the post credits plus pool `crN` re-split as `crPl cr2 pl2`, with
`i`'s credits `cr'` and pool `plStep` untouched, foreign pool items tagged at post (an item whose
tag fails at post converts to a plant credit), no own key moved, and foreign `PromCrK` kept.  Discharge: new (`TermPoolF1`). -/
def f1T (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ dc dh plh : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ → StepCrQ cr pl i r.2.2.promises crS →
    TermOverCr.OverCrG Eg c (crPl cr pl) → PoolTag Eg c pl →
    (∀ t, dc t + dh t ≤ δ t) →
    CrShiftP c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') cr i dc →
    (∀ t, dh t ≠ .zero → ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧
      ∀ thj', c'.ths[j]? = some thj' →
        PTag (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j thj' (fun u => pl j u + dh u) t) →
    (∀ (j : Nat) (thj thj' : TTh) (Sj : AllocLabel → Prop) (l : AllocLabel) (cl : Cell), j ≠ i →
      c.ths[j]? = some thj → c'.ths[j]? = some thj' →
      (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl → cl.owner = some j → (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none → ¬ (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pubd l →
      FgnNewC p k arch c c' Eg pl i th r E' dh j thj thj' Sj l cl) →
    ∃ cr2 pl2 : Nat → Ts → Res,
      cr2 i = cr' ∧ pl2 i = plStep pl i (stOf r.1 r.2.1 r.2.2) plh ∧
      crPl cr2 pl2 = crN cr pl i cr' (stOf r.1 r.2.1 r.2.2) plh dc dh ∧
      (∀ j thj' t, j ≠ i → c'.ths[j]? = some thj' → pl2 j t ≠ .zero →
        PTag (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j thj' (pl2 j) t) ∧
      (∀ j t l, cr2 j t (.own l) = updD cr i cr' dc j t (.own l)) ∧
      (∀ j thj' (Sj : AllocLabel → Prop), j ≠ i → c'.ths[j]? = some thj' →
        TermPlant.PromCrK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
            (stOf c'.mem c'.pairs thj') (fun t => cr j t + dc t) (db j) →
          TermPlant.PromCrK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
            (stOf c'.mem c'.pairs thj') (cr2 j) (db j)) ∧
      ∀ (j : Nat) (thj' : TTh) (Sj : AllocLabel → Prop), j ≠ i → c'.ths[j]? = some thj' →
        ∀ l cl, (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl → cl.owner = some j → (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none → ¬ (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pubd l →
        ∃ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)),
          (∀ t, Res.sum ((Gs.filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1)) ≤ pl2 j t) ∧
          (∀ x ∈ Gs, TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj') (pl2 j) l cl x) ∧
          ∀ o tw, PredU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ → ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
            TermPlant.LowOwn (stOf c'.mem c'.pairs thj') ⟨l, o⟩ tw → FirstW c'.mem ⟨l, o⟩ tw →
            TermPlant.OverT (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj') ⟨l, o⟩ tw →
            ∃ x ∈ Gs, ∃ usS ii, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS ii (o - x.2.1) ∧
              x.2.2.2.2.2 ii = true

/-- **The stepper's own pool after its step is tagged**: `plStep pl i s' plh` (kept old items
at still outstanding promises, plus `KeepQRS`'s new items `plh`) satisfies the tag shape at `i`
after the step.  Premise (whole-piece discharge; supplied at the consumer by
`TermFulW.tctx_wpd`, which states it verbatim): a step that discharges an own non-word promise at an own
frontier cell discharges the lowest own promise at every unit of each piece containing it, so a
surviving holder's item keeps its pins.  Discharge: new (from `KeepQRS`'s `RepinQh`). -/
def poolTagOwnT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ plh : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ → StepCrQ cr pl i r.2.2.promises crS →
    TermOverCr.OverCrG Eg c (crPl cr pl) → PoolTag Eg c pl →
    TermPlant.KeepQRS (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) th crS cr' plh →
    (∀ (t : Ts) (m : Msg) (cl : Cell), t ∈ th.promises → t ∉ r.2.2.promises → c.mem[t]? = some m →
      (CE η).sto m.loc.label = some cl → cl.owner = some i → (CE η).pfr m.loc.label ≠ none →
      ¬ WordUnit (CE η) m.loc →
      ∀ q S usS, TermPiece.Piece cl.ty q S → accs S = some usS → q ≤ m.loc.offset →
        m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
          TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨m.loc.label, o⟩ th0 → th0 ∉ r.2.2.promises) →
    (∀ (Sj : AllocLabel → Prop) l o tw, (CE η).pfr l = none → E'.pfr l ≠ none → E'.sto l ≠ none →
      ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c'.mem c'.pairs r.2.2) ⟨l, o⟩ tw →
      ¬ TermPlant.OverT (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj)
        (stOf c'.mem c'.pairs r.2.2) ⟨l, o⟩ tw) →
    (∀ t, plStep pl i (stOf r.1 r.2.1 r.2.2) plh t ≠ .zero →
      PTag (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' i r.2.2
        (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) t) ∧
      (∀ (Sj : AllocLabel → Prop) l cl, (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj).sto l =
          some cl → cl.owner = some i →
        (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none →
        ¬ (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pubd l →
        ∃ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)),
          (∀ t, Res.sum ((Gs.filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1)) ≤
            plStep pl i (stOf r.1 r.2.1 r.2.2) plh t) ∧
          (∀ x ∈ Gs, TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj)
            (stOf c'.mem c'.pairs r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) l cl x) ∧
          ∀ o tw, PredU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj) ⟨l, o⟩ →
            ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj) ⟨l, o⟩ →
            TermPlant.LowOwn (stOf c'.mem c'.pairs r.2.2) ⟨l, o⟩ tw → FirstW c'.mem ⟨l, o⟩ tw →
            TermPlant.OverT (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj)
              (stOf c'.mem c'.pairs r.2.2) ⟨l, o⟩ tw →
            ∃ x ∈ Gs, ∃ usS ii, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS ii (o - x.2.1) ∧
              x.2.2.2.2.2 ii = true)

/-- The thread step's inequality with the pool items `plh` and the whole transfer `δ` (over a
cover `Fd` of its support). -/
def IneqH (Tot' HP' HS' C F Rf Rs H : Res) (s s' : St) (cr cr' db db' plh δ : Ts → Res) : Prop :=
  ∃ Fd : List Ts, (∀ t, δ t ≠ .zero → t ∈ Fd) ∧
    Tot' + (HP' + HS') + pSum s' cr' + pSum s' plh + Res.sum (Fd.map δ) + pSum s db + C ≤
      Rf + Rs + H + pSum s cr + pSum s' db' + F

/-- balance after a thread step, at `crN`.  Discharge: copy of `TermBal.balT_D`. -/
def poolBalT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  MintClosedT p k arch Sp Init MintOK c0 → PromNodupR p k arch Sp c0 →
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ dc dh plh : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ → StepCrQ cr pl i r.2.2.promises crS →
    (∀ t, dc t + dh t ≤ δ t) → PoolInv Init MintOK c Eg Tot HP HS cr db pl →
    (∀ t, plh t ≠ .zero → t ∈ r.2.2.promises) →
    IneqH Tot' HP' HS' C F Rf Rs (HP i + HS) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) crS cr' (db i) db'
      plh δ →
    ∃ M, MintOK M ∧
      thSum c'.ths.size (fun j => upd Tot i Tot' j +
          pSumAt c' j (crN cr pl i cr' (stOf r.1 r.2.1 r.2.2) plh dc dh j) + upd HP i HP' j) + HS' ≤
        Init + M + thSum c'.ths.size (fun j => pSumAt c' j (upd db i db' j))

/-- net key bounds after a thread step, at `crN`.  Discharge: copy of `TermOwnFresh.knetT_F`. -/
def poolKnetT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  AllocGT p k arch Sp Init MintOK c0 → TicketFreeRun p k arch Sp c0 → PromNodupR p k arch Sp c0 →
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ dc dh plh : Ts → Res} {rc : Nat → Nat},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ → StepCrQ cr pl i r.2.2.promises crS →
    (∀ t, dc t + dh t ≤ δ t) → PoolInv Init MintOK c Eg Tot HP HS cr db pl →
    (∀ t, plh t ≠ .zero → t ∈ r.2.2.promises) → (∀ t, TermPlant.CrKeys (plh t)) →
    (∀ t, TermPlant.CrKeys (dh t)) →
    IneqH Tot' HP' HS' C F Rf Rs (HP i + HS) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) crS cr' (db i) db'
      plh δ →
    ClaimAt th.term C F → OwnFreshZ c Tot HP HS cr →
    RidOK c Tot HP HS (crPl cr pl) db rc → rc i ≤ η.rid →
    ∀ key, ExclKey key → KeyNet c' (upd Tot i Tot') (upd HP i HP') HS'
      (crN cr pl i cr' (stOf r.1 r.2.1 r.2.2) plh dc dh) (upd db i db') key

/-- rid freshness after a thread step, at `crN`.  Discharge: copy of `TermBal.ridT_N`. -/
def poolRidT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  TicketFreeRun p k arch Sp c0 → PromNodupR p k arch Sp c0 →
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ dc dh plh : Ts → Res} {rc : Nat → Nat},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ → StepCrQ cr pl i r.2.2.promises crS →
    (∀ t, dc t + dh t ≤ δ t) → PoolInv Init MintOK c Eg Tot HP HS cr db pl →
    (∀ t, plh t ≠ .zero → t ∈ r.2.2.promises) →
    IneqH Tot' HP' HS' C F Rf Rs (HP i + HS) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) crS cr' (db i) db'
      plh δ →
    ClaimAt th.term C F → RidOK c Tot HP HS (crPl cr pl) db rc → rc i ≤ η.rid →
    ∃ rc', RidOK c' (upd Tot i Tot') (upd HP i HP') HS' (crN cr pl i cr' (stOf r.1 r.2.1 r.2.2) plh dc dh)
      (upd db i db') rc'

/-- balance after a promise step, pool unchanged.  Discharge: copy of `TermBal.balP_proof`. -/
def poolBalP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' →
    PoolInv Init MintOK c Eg Tot HP HS cr db pl →
    ∃ M, MintOK M ∧
      thSum (promise c j a v w).ths.size
          (fun i => Tot i + pSumAt (promise c j a v w) i (crPl (upd cr j cr') pl i) + upd HP j HP' i) + HS' ≤
        Init + M + thSum (promise c j a v w).ths.size (fun i => pSumAt (promise c j a v w) i (upd db j db' i))

/-- net key bounds after a promise step, pool unchanged.  Discharge: copy of `TermBal.knetP_proof`. -/
def poolKnetP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' →
    PoolInv Init MintOK c Eg Tot HP HS cr db pl →
    ∀ key, ExclKey key → KeyNet (promise c j a v w) Tot (upd HP j HP') HS' (crPl (upd cr j cr') pl)
      (upd db j db') key

/-- rid freshness after a promise step, pool unchanged.  Discharge: copy of `TermBal.ridP_N`. -/
def poolRidP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' →
    PoolInv Init MintOK c Eg Tot HP HS cr db pl →
    ∃ rc', RidOK (promise c j a v w) Tot (upd HP j HP') HS' (crPl (upd cr j cr') pl) (upd db j db') rc'

/-- tags after a promise step (pool unchanged, planted environment).  Discharge: new (frame
lemma); UNVERIFIED pending the F1T3 verdict (new promise may change `LowOwn`/`PredAt` of own items). -/
def poolTagP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PlantSpec Eg (plantOf c Eg j a v w) j c.mem.size →
    PoolTag Eg c pl →
    PoolTag (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) pl

/-- The twelve members bundled (a structure: never instance-resolved). -/
structure PoolStaging (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop where
  hOwnA : ownA p k arch Sp Init MintOK c0
  hOwnC : ownC p k arch Sp Init MintOK c0
  hFgnCov : fgnCov p k arch Sp Init MintOK c0
  hF1T : f1T p k arch Sp Init MintOK c0
  hPoolTagOwnT : poolTagOwnT p k arch Sp Init MintOK c0
  hPoolBalT : poolBalT p k arch Sp Init MintOK c0
  hPoolKnetT : poolKnetT p k arch Sp Init MintOK c0
  hPoolRidT : poolRidT p k arch Sp Init MintOK c0
  hPoolBalP : poolBalP p k arch Sp Init MintOK c0
  hPoolKnetP : poolKnetP p k arch Sp Init MintOK c0
  hPoolRidP : poolRidP p k arch Sp Init MintOK c0
  hPoolTagP : poolTagP p k arch Sp Init MintOK c0 plantOf plantN

end TermPoolStaging

#print axioms TermPoolStaging.poolTag_iff
#print axioms TermPoolStaging.cr_le_crPl
#print axioms TermPoolStaging.PoolInv.old
#print axioms TermPoolStaging.δc_add_δh_le
#print axioms TermPoolStaging.crShiftP_δc
#print axioms TermPoolStaging.δh_tag
