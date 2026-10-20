/-
**The plant iteration** for `ThSys_plantW`: one label's plant at a partially
planted environment from its hypotheses at the base environment (`PAgree`), and the iteration
over a list of labels.  Against the green_sw chain.
-/
import WeakCore.TermPlantW
namespace TermPlantL
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermMain TermPlantR TermPlantW
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## (L0) Agreement of a partial plant with the base environment at one label -/

/-- `Eg` (the base `Eg0` with other own labels of thread `j` planted) agrees with `Eg0` at `l`. -/
structure PAgree (Eg0 Eg : GEnv) (j : Nat) (l : AllocLabel) : Prop where
  sto : Eg.sto = Eg0.sto
  csto : cutSto Eg j = cutSto Eg0 j
  rini : Eg.rini = Eg0.rini
  fp : Eg.fpOf = Eg0.fpOf
  ini : Eg.ini l = Eg0.ini l
  pfr : Eg.pfr l = Eg0.pfr l
  vis : ∀ l', Eg.pfr l' = Eg0.pfr l' ∨ ∃ f, Eg.pfr l' = some f

theorem PAgree.refl (Eg : GEnv) (j : Nat) (l : AllocLabel) : PAgree Eg Eg j l :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => .inl rfl⟩

theorem HoldW_agree {Eg0 Eg : GEnv} {j : Nat} {l : AllocLabel} {S : AllocLabel → Prop} {s : St} {F : Ts}
    (A : PAgree Eg0 Eg j l) (h : HoldW (Cut Eg0 j S) s l F) : HoldW (Cut Eg j S) s l F :=
  h.congrE fun a ha hw =>
    (IniWr_congr (E := Cut Eg0 j S) (E' := Cut Eg j S)
      (by show cutSto Eg j a.label = cutSto Eg0 j a.label; rw [A.csto])
      (TEnv.rc_congr (by show Eg.ini a.label = Eg0.ini a.label; rw [ha]; exact A.ini)
        (by show Eg.rini a.label = Eg0.rini a.label; rw [A.rini]))).1 hw

theorem InitR_iff {η η' : TEnv} {c : Cell} {l : AllocLabel} {o : Nat} (h : η'.ini l = η.ini l) :
    InitR η' c l o ↔ InitR η c l o := by
  unfold InitR; rw [h]

theorem IniSeg_iff {η η' : TEnv} {c : Cell} {l : AllocLabel} {b : Nat} (h : η'.ini l = η.ini l) :
    IniSeg η' c l b ↔ IniSeg η c l b := by
  unfold IniSeg; rw [h]

theorem IniAt_congr {ini ini' : AllocLabel → Nat} {c : Cell} {a : Address} {U : Ty}
    (h : ini' a.label = ini a.label) (hI : IniAt ini c a U) : IniAt ini' c a U := by
  unfold IniAt at *; rw [h]; exact hI

theorem ValOf_word {η η' : TEnv} {r : Idx} {P : Proto} {ws : List Word} (h : ValOf η (.word r P) ws) :
    ValOf η' (.word r P) ws := h

theorem ValOfR_word {η η' : TEnv} {r : Idx} {P : Proto} {ws : List Word} {R : Res}
    (h : ValOfR η (.word r P) ws R) : ValOfR η' (.word r P) ws R := h

theorem plant1_ini_self (Eg : GEnv) (l : AllocLabel) (F : Ts) (Np : Nat) : (plant1 Eg l F Np).ini l = Np := by
  simp [plant1]

theorem FlipOK_agree {Eg0 Eg : GEnv} {j : Nat} {l : AllocLabel} {S : AllocLabel → Prop} {s : St}
    (A : PAgree Eg0 Eg j l) (h : FlipOK (Cut Eg0 j S) s l) : FlipOK (Cut Eg j S) s l := by
  have hs : ∀ l', (Cut Eg j S).sto l' = (Cut Eg0 j S).sto l' := fun l' => by
    show cutSto Eg j l' = cutSto Eg0 j l'; rw [A.csto]
  intro hpv t m ht hm hl hwu hiw
  have hpv0 : Priv (Cut Eg0 j S) l := by
    obtain ⟨⟨c, hc, ho⟩, hp⟩ := hpv
    exact ⟨⟨c, (hs l) ▸ hc, ho⟩, by show Eg0.pfr l = none; rw [← A.pfr]; exact hp⟩
  have hwu0 := (WordUnit_congr (E := Cut Eg0 j S) (E' := Cut Eg j S) (hs _)).1 hwu
  have hiw0 := (IniW_congr (E := Cut Eg0 j S) (E' := Cut Eg j S) (hs _)
    (by show Eg.ini m.loc.label = Eg0.ini m.loc.label; rw [hl]; exact A.ini)).1 hiw
  obtain ⟨c, n, P, hc, hA, hg, hI, hw, v, hv, hin⟩ := h hpv0 t m ht hm hl hwu0 hiw0
  exact ⟨c, n, P, (hs l).trans hc, hA, hg,
    IniAt_congr (by show Eg.ini m.loc.label = Eg0.ini m.loc.label; rw [hl]; exact A.ini) hI, hw, v, hv, hin⟩

theorem FpOK_agree {Eg0 Eg : GEnv} {j : Nat} {l : AllocLabel} {S : AllocLabel → Prop} {s : St}
    (A : PAgree Eg0 Eg j l) (h : FpOK (Cut Eg0 j S) s) : FpOK (Cut Eg j S) s := by
  have hfp : (Cut Eg j S).fp = (Cut Eg0 j S).fp := by show Eg.fpOf j = Eg0.fpOf j; rw [A.fp]
  refine ⟨fun t ht => h.1 t (hfp ▸ ht), fun t m ht hm => ?_⟩
  have h0 := h.2 t m (hfp ▸ ht) hm
  rcases A.vis m.loc.label with hp | ⟨f, hp⟩
  · exact (Vis_congr (E := Cut Eg0 j S) (E' := Cut Eg j S)
      (by show cutSto Eg j _ = cutSto Eg0 j _; rw [A.csto]) rfl hp).2 h0
  · intro hpv; have h2 : Eg.pfr m.loc.label = none := hpv.2
    rw [hp] at h2; cases h2

/-! ## (L1) One label's plant at a partial plant, from its hypotheses at the base -/

/-- (dedup) master of `ThSysAt_plant1B`: also exports `KeepNW` (old non-word credits kept). -/
theorem ThSysAt_plant1BK {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg0 Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell} {N n : Nat}
    {P : Proto} {F Np : Ts} (A : PAgree Eg0 Eg g.i l)
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hc : Eg0.sto l = some c) (ho : c.owner = some g.i) (hnone : Eg0.pfr l = none)
    (hTc : c.ty = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false)
    (hrl : Eg0.rini l ≤ Eg0.ini l) (hNp : Eg0.ini l ≤ Np) (hNN : Np ≤ N)
    (hF : F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (Cut Eg0 g.i S) (stOf mem pairs th) l F)
    (hFw : Eg0.ini l < Np → (stOf mem pairs th).vs.vWr ≤ F)
    (hhold : ∀ o, InitR (Cut (plant1 Eg0 l F Np) g.i S) c l o → ¬ InitR (Cut Eg0 g.i S) c l o →
      ∀ (t : Nat) (m : Msg), t ∉ th.promises → mem[t]? = some m → m.loc = ⟨l, o⟩ →
      ∃ (t' : Nat) (m' : Msg), t < t' ∧ t' ≤ F ∧ mem[t']? = some m' ∧ m'.loc = ⟨l, o⟩)
    (hinh : ∀ b S' us, SegOf c.ty b S' → accs S' = some us →
      IniSeg (Cut (plant1 Eg0 l F Np) g.i S) c l b → ¬ IniSeg (Cut Eg0 g.i S) c l b →
      ∃ ws, ValOf (Cut (plant1 Eg0 l F Np) g.i S) S' ws ∧ ws.length = nWords us)
    (hcpl : ∀ b S', SegOf c.ty b S' → accs S' ≠ none → TearOK S') (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hf : FlipOK (Cut Eg0 g.i S) (stOf mem pairs th) l) (hfo : FpOK (Cut Eg0 g.i S) (stOf mem pairs th))
    (hR1w : ∀ j, Eg0.ini l ≤ j → j < Np → ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧
      m0.val = .undef ∧ t0 ∉ th.promises ∧ (∃ t, AtA mem ⟨l, j⟩ t0 t = true) ∧
      ∀ t m, mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ th.promises)
    (hval : ∀ j, Eg0.ini l ≤ j → j < Np → ∀ w, LatestNP mem [] ⟨l, j⟩ w →
      ∃ R, ValOfR (Cut (plant1 Eg0 l F Np) g.i S) (.word (.lit n) P) [w] R) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' ∧
      KeepNW (Cut Eg0 g.i S) mem th.promises cr cr' := by
  refine exK_sto (E := Cut Eg g.i S) A.csto ?_
  have hini := A.ini
  have hi1 : (Cut (plant1 Eg l F Np) g.i S).ini l = (Cut (plant1 Eg0 l F Np) g.i S).ini l := by
    show (plant1 Eg l F Np).ini l = (plant1 Eg0 l F Np).ini l; rw [plant1_ini_self, plant1_ini_self]
  have hi0 : (Cut Eg g.i S).ini l = (Cut Eg0 g.i S).ini l := hini
  have hSeg : ∀ b S', SegOf c.ty b S' → accs S' ≠ none → S' = .word (.lit n) P := by
    intro b S' hs ha
    rcases hs with ⟨-, rfl, -⟩ | ⟨N', us, j', he, -, -, -⟩
    · rw [hTc] at ha; exact absurd rfl ha
    · rw [hTc] at he; cases he; rfl
  refine ThSysAt_plant1K h hpa (by rw [A.sto]; exact hc) ho (by rw [A.pfr]; exact hnone) hTc hP
    (by rw [A.rini, hini]; exact hrl) (by rw [hini]; exact hNp) hNN
    (hF.imp id (HoldW_agree A)) (by rw [hini]; exact hFw)
    (fun o h1 h2 => hhold o ((InitR_iff hi1).1 h1) (fun h3 => h2 ((InitR_iff hi0).2 h3)))
    (fun b S' us hs ha h1 h2 => ?_) hcpl hcT hnT hrT (FlipOK_agree A hf) (FpOK_agree A hfo)
    (by rw [hini]; exact hR1w)
    (fun j h1 h2 w hw => ?_)
  · obtain ⟨ws, hv, hl⟩ := hinh b S' us hs ha ((IniSeg_iff hi1).1 h1) (fun h3 => h2 ((IniSeg_iff hi0).2 h3))
    have e := hSeg b S' hs (by rw [ha]; exact Option.some_ne_none _)
    subst e
    exact ⟨ws, ValOf_word hv, hl⟩
  · obtain ⟨R, hR⟩ := hval j (by rw [← hini]; exact h1) h2 w hw
    exact ⟨R, ValOfR_word hR⟩

/-- (L1) `ThSysAt_plant1` at a partial plant `Eg` agreeing with the base `Eg0` at `l`, its
hypotheses stated at `Eg0` (and at `plant1 Eg0 l F Np`). -/
theorem ThSysAt_plant1B {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg0 Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell} {N n : Nat}
    {P : Proto} {F Np : Ts} (A : PAgree Eg0 Eg g.i l)
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hc : Eg0.sto l = some c) (ho : c.owner = some g.i) (hnone : Eg0.pfr l = none)
    (hTc : c.ty = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false)
    (hrl : Eg0.rini l ≤ Eg0.ini l) (hNp : Eg0.ini l ≤ Np) (hNN : Np ≤ N)
    (hF : F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (Cut Eg0 g.i S) (stOf mem pairs th) l F)
    (hFw : Eg0.ini l < Np → (stOf mem pairs th).vs.vWr ≤ F)
    (hhold : ∀ o, InitR (Cut (plant1 Eg0 l F Np) g.i S) c l o → ¬ InitR (Cut Eg0 g.i S) c l o →
      ∀ (t : Nat) (m : Msg), t ∉ th.promises → mem[t]? = some m → m.loc = ⟨l, o⟩ →
      ∃ (t' : Nat) (m' : Msg), t < t' ∧ t' ≤ F ∧ mem[t']? = some m' ∧ m'.loc = ⟨l, o⟩)
    (hinh : ∀ b S' us, SegOf c.ty b S' → accs S' = some us →
      IniSeg (Cut (plant1 Eg0 l F Np) g.i S) c l b → ¬ IniSeg (Cut Eg0 g.i S) c l b →
      ∃ ws, ValOf (Cut (plant1 Eg0 l F Np) g.i S) S' ws ∧ ws.length = nWords us)
    (hcpl : ∀ b S', SegOf c.ty b S' → accs S' ≠ none → TearOK S') (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hf : FlipOK (Cut Eg0 g.i S) (stOf mem pairs th) l) (hfo : FpOK (Cut Eg0 g.i S) (stOf mem pairs th))
    (hR1w : ∀ j, Eg0.ini l ≤ j → j < Np → ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧
      m0.val = .undef ∧ t0 ∉ th.promises ∧ (∃ t, AtA mem ⟨l, j⟩ t0 t = true) ∧
      ∀ t m, mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ th.promises)
    (hval : ∀ j, Eg0.ini l ≤ j → j < Np → ∀ w, LatestNP mem [] ⟨l, j⟩ w →
      ∃ R, ValOfR (Cut (plant1 Eg0 l F Np) g.i S) (.word (.lit n) P) [w] R) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
    obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := ThSysAt_plant1BK A h hpa hc ho hnone hTc hP hrl hNp hNN hF hFw hhold hinh hcpl hcT hnT hrT hf hfo hR1w hval
    exact ⟨x0, x1, x2, x3, h0, h1⟩

/-! ## (L2) The iteration over a list of labels -/

/-- The base `Eg` with the labels of `L` planted (the head last). -/
def plantL (Eg : GEnv) (Fm : AllocLabel → Ts) (Nm : AllocLabel → Nat) : List AllocLabel → GEnv
  | [] => Eg
  | l :: L => plant1 (plantL Eg Fm Nm L) l (Fm l) (Nm l)

theorem plantL_sto (Eg : GEnv) (Fm : AllocLabel → Ts) (Nm : AllocLabel → Nat) :
    ∀ L, (plantL Eg Fm Nm L).sto = Eg.sto
  | [] => rfl
  | _ :: L => plantL_sto Eg Fm Nm L

theorem plantL_rini (Eg : GEnv) (Fm : AllocLabel → Ts) (Nm : AllocLabel → Nat) :
    ∀ L, (plantL Eg Fm Nm L).rini = Eg.rini
  | [] => rfl
  | _ :: L => plantL_rini Eg Fm Nm L

theorem plantL_fp (Eg : GEnv) (Fm : AllocLabel → Ts) (Nm : AllocLabel → Nat) :
    ∀ L, (plantL Eg Fm Nm L).fpOf = Eg.fpOf
  | [] => rfl
  | _ :: L => plantL_fp Eg Fm Nm L

theorem plantL_out {Eg : GEnv} {Fm : AllocLabel → Ts} {Nm : AllocLabel → Nat} {l : AllocLabel} :
    ∀ {L : List AllocLabel}, l ∉ L → (plantL Eg Fm Nm L).ini l = Eg.ini l ∧ (plantL Eg Fm Nm L).pfr l = Eg.pfr l
  | [], _ => ⟨rfl, rfl⟩
  | l' :: L, hl => by
    have hne : l ≠ l' := fun e => hl (e ▸ List.mem_cons_self)
    have ih := plantL_out (Eg := Eg) (Fm := Fm) (Nm := Nm) (fun h => hl (List.mem_cons_of_mem _ h))
    simp only [plantL, plant1, hne, ite_false]
    exact ih

theorem plantL_in {Eg : GEnv} {Fm : AllocLabel → Ts} {Nm : AllocLabel → Nat} {l : AllocLabel} :
    ∀ {L : List AllocLabel}, l ∈ L → (plantL Eg Fm Nm L).pfr l = some (Fm l)
  | [], hl => absurd hl List.not_mem_nil
  | l' :: L, hl => by
    by_cases he : l = l'
    · subst he; simp [plantL, plant1]
    · have hl' : l ∈ L := (List.mem_cons.1 hl).resolve_left he
      simp only [plantL, plant1, he, ite_false]
      exact plantL_in hl'

theorem plantL_csto {Eg : GEnv} {Fm : AllocLabel → Ts} {Nm : AllocLabel → Nat} {j : Nat} :
    ∀ {L : List AllocLabel}, (∀ l ∈ L, ∃ c, Eg.sto l = some c ∧ c.owner = some j) →
      cutSto (plantL Eg Fm Nm L) j = cutSto Eg j
  | [], _ => rfl
  | l :: L, hown => by
    obtain ⟨c, hc, ho⟩ := hown l List.mem_cons_self
    have ih := plantL_csto (Fm := Fm) (Nm := Nm) (fun l' h => hown l' (List.mem_cons_of_mem _ h))
    show cutSto (plant1 (plantL Eg Fm Nm L) l (Fm l) (Nm l)) j = _
    rw [cutSto_plant1 (by rw [plantL_sto]; exact hc) ho, ih]

theorem PAgree_plantL {Eg : GEnv} {Fm : AllocLabel → Ts} {Nm : AllocLabel → Nat} {j : Nat} {l : AllocLabel}
    {L : List AllocLabel} (hown : ∀ l ∈ L, ∃ c, Eg.sto l = some c ∧ c.owner = some j) (hl : l ∉ L) :
    PAgree Eg (plantL Eg Fm Nm L) j l :=
  ⟨plantL_sto Eg Fm Nm L, plantL_csto hown, plantL_rini Eg Fm Nm L, plantL_fp Eg Fm Nm L,
    (plantL_out hl).1, (plantL_out hl).2, fun l' => by
      by_cases h : l' ∈ L
      · exact .inr ⟨_, plantL_in h⟩
      · exact .inl (plantL_out h).2⟩

/-- `ThSysAt_plantL` with `KeepNW` threaded (22 lines; the step hypothesis differs). -/
theorem ThSysAt_plantLK {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg0 : GEnv}
    {Tot : Res} {S : AllocLabel → Prop} {Fm : AllocLabel → Ts} {Nm : AllocLabel → Nat} :
    ∀ {L : List AllocLabel} {HP HS : Res} {cr db : Ts → Res}, L.Nodup →
      (∀ l ∈ L, ∃ c, Eg0.sto l = some c ∧ c.owner = some g.i) →
      (∀ l ∈ L, ∀ {Eg HP HS cr db}, PAgree Eg0 Eg g.i l → ThSysAt p g mem pairs th Eg Tot HP HS cr db S →
        ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l (Fm l) (Nm l)) Tot HP' HS' cr' db' S ∧
          (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
            (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' ∧
          KeepNW (Cut Eg0 g.i S) mem th.promises cr cr') →
      ThSysAt p g mem pairs th Eg0 Tot HP HS cr db S →
      ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plantL Eg0 Fm Nm L) Tot HP' HS' cr' db' S ∧
        (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
          (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' ∧
        KeepNW (Cut Eg0 g.i S) mem th.promises cr cr'
  | [], _, _, _, _, _, _, _, h => ⟨_, _, _, _, h, rfl, KeepNW_refl⟩
  | l :: L, _, _, _, _, hnd, hown, hstep, h => by
    have hown' : ∀ l' ∈ L, ∃ c, Eg0.sto l' = some c ∧ c.owner = some g.i :=
      fun l' h => hown l' (List.mem_cons_of_mem _ h)
    obtain ⟨HP1, HS1, cr1, db1, h1, e1, k1⟩ := ThSysAt_plantLK (List.nodup_cons.1 hnd).2 hown'
      (fun l' h => hstep l' (List.mem_cons_of_mem _ h)) h
    obtain ⟨HP2, HS2, cr2, db2, h2, e2, k2⟩ := hstep l List.mem_cons_self
      (PAgree_plantL hown' (List.nodup_cons.1 hnd).1) h1
    exact ⟨HP2, HS2, cr2, db2, h2, acct_trans e1 e2, KeepNW_trans k1 k2⟩

/-- (L2) **The iteration**: planting the labels of a duplicate-free list of own labels, one at a
time, from per-label steps at partial plants agreeing with the base. -/
theorem ThSysAt_plantL {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg0 : GEnv}
    {Tot : Res} {S : AllocLabel → Prop} {Fm : AllocLabel → Ts} {Nm : AllocLabel → Nat} :
    ∀ {L : List AllocLabel} {HP HS : Res} {cr db : Ts → Res}, L.Nodup →
      (∀ l ∈ L, ∃ c, Eg0.sto l = some c ∧ c.owner = some g.i) →
      (∀ l ∈ L, ∀ {Eg HP HS cr db}, PAgree Eg0 Eg g.i l → ThSysAt p g mem pairs th Eg Tot HP HS cr db S →
        ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l (Fm l) (Nm l)) Tot HP' HS' cr' db' S ∧
          (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
            (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db') →
      ThSysAt p g mem pairs th Eg0 Tot HP HS cr db S →
      ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plantL Eg0 Fm Nm L) Tot HP' HS' cr' db' S ∧
        (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
          (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db'
  | [], _, _, _, _, _, _, _, h => ⟨_, _, _, _, h, rfl⟩
  | l :: L, _, _, _, _, hnd, hown, hstep, h => by
    have hown' : ∀ l' ∈ L, ∃ c, Eg0.sto l' = some c ∧ c.owner = some g.i :=
      fun l' h => hown l' (List.mem_cons_of_mem _ h)
    obtain ⟨HP1, HS1, cr1, db1, h1, e1⟩ := ThSysAt_plantL (List.nodup_cons.1 hnd).2 hown'
      (fun l' h => hstep l' (List.mem_cons_of_mem _ h)) h
    obtain ⟨HP2, HS2, cr2, db2, h2, e2⟩ := hstep l List.mem_cons_self
      (PAgree_plantL hown' (List.nodup_cons.1 hnd).1) h1
    exact ⟨HP2, HS2, cr2, db2, h2, acct_trans e1 e2⟩

theorem plantL_ini_in {Eg : GEnv} {Fm : AllocLabel → Ts} {Nm : AllocLabel → Nat} {l : AllocLabel} :
    ∀ {L : List AllocLabel}, l ∈ L → (plantL Eg Fm Nm L).ini l = Nm l
  | [], hl => absurd hl List.not_mem_nil
  | l' :: L, hl => by
    by_cases he : l = l'
    · subst he; simp [plantL, plant1]
    · have hl' : l ∈ L := (List.mem_cons.1 hl).resolve_left he
      simp only [plantL, plant1, he, ite_false]
      exact plantL_ini_in hl'

theorem plantL_shape (Eg : GEnv) (Fm : AllocLabel → Ts) (Nm : AllocLabel → Nat) :
    ∀ L, plantL Eg Fm Nm L = { Eg with pfr := (plantL Eg Fm Nm L).pfr, ini := (plantL Eg Fm Nm L).ini }
  | [] => rfl
  | l :: L => by
    show plant1 (plantL Eg Fm Nm L) l (Fm l) (Nm l) = _
    have ih := plantL_shape Eg Fm Nm L
    conv => lhs; rw [ih]
    rfl

/-- (L3) The iteration over the planted labels is the ghost plant `plantG`. -/
theorem plantL_eq_plantG {Eg : GEnv} {Fm : AllocLabel → Ts} {Nm : AllocLabel → Nat} {P : AllocLabel → Option Ts}
    {N : AllocLabel → Nat} {L : List AllocLabel} (hL : ∀ l, l ∈ L ↔ P l ≠ none)
    (hF : ∀ l f, P l = some f → Fm l = f) (hN : ∀ l ∈ L, Nm l = max (Eg.ini l) (N l)) :
    plantL Eg Fm Nm L = plantG Eg P N := by
  rw [plantL_shape]
  unfold plantG
  congr 1
  · funext l
    cases e : P l with
    | none => exact (plantL_out (fun h => (hL l).1 h e)).1
    | some f =>
      have hl := (hL l).2 (by rw [e]; exact Option.some_ne_none _)
      rw [plantL_ini_in hl, hN l hl]
  · funext l
    cases e : P l with
    | none => exact (plantL_out (fun h => (hL l).1 h e)).2
    | some f => rw [plantL_in ((hL l).2 (by rw [e]; exact Option.some_ne_none _)), hF l f e]

/-! ## (L4) A plant with no new slots: the flip alone, any cell type -/

/-- (dedup) master of `ThSysAt_flip1`: also exports `KeepNW` (old non-word credits kept). -/
theorem ThSysAt_flip1K {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell}
    {F Np : Ts}
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hc : Eg.sto l = some c) (ho : c.owner = some g.i) (hnone : Eg.pfr l = none)
    (hrl : Eg.rini l ≤ Eg.ini l) (hNp : Np = Eg.ini l)
    (hF : F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (Cut Eg g.i S) (stOf mem pairs th) l F)
    (hcpl : ∀ b S', SegOf c.ty b S' → accs S' ≠ none → TearOK S') (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hf : FlipOK (Cut Eg g.i S) (stOf mem pairs th) l) (hfo : FpOK (Cut Eg g.i S) (stOf mem pairs th)) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' ∧
      KeepNW (Cut Eg g.i S) mem th.promises cr cr' := by
  obtain ⟨hRE, hTE, hm, hHP, hHS, hC⟩ := h
  have hH : MemHeld (Cut Eg g.i S) (stOf mem pairs th) (HP + HS) :=
    MemHeld_join (fun _ _ h1 h2 => Cut_cov h1 h2) hHP hHS
  obtain ⟨ρ, η, cx, Rf, Rs, hE0, hE, hTy, htv, hFI, hsum⟩ := hRE
  have e2 := CE_withSto_Cut (F := F) (Np := Np) hE0 hc ho
  rw [← hE0] at hm hH hC hF hf hfo
  have hsto : η.sto l = some c := by
    show (CE η).sto l = some c
    rw [hE0]; exact cutSto_own hc ho
  have htid : η.tid = g.i := congrArg TEnv.tid hE0
  have hown : c.owner = some η.tid := by rw [htid]; exact ho
  have hnone' : η.pfr l = none := by
    show (CE η).pfr l = none
    rw [hE0]; exact hnone
  have hini : η.ini = Eg.ini := congrArg TEnv.ini hE0
  have hrini : η.rini = Eg.rini := congrArg TEnv.rini hE0
  rw [← hini] at hNp
  rw [← hrini, ← hini] at hrl
  let P1 : AllocLabel → Option Ts := fun l' => if l' = l then some F else η.pfr l'
  let I2 : AllocLabel → Nat := fun l' => if l' = l then Np else η.ini l'
  have hI2e : ∀ l', I2 l' = η.ini l' := fun l' => by
    by_cases he : l' = l
    · subst he; simp [I2, hNp]
    · simp [I2, he]
  have hP1 : ∀ l' f, η.pfr l' = some f → P1 l' = some f := fun l' f h => by
    by_cases he : l' = l
    · subst he; rw [hnone'] at h; cases h
    · simp [P1, he, h]
  have hI2 : ∀ l', η.ini l' ≤ I2 l' := fun l' => by rw [hI2e]; exact Nat.le_refl _
  have hx : Ext η (η.withSto η.sto I2 P1 η.seen) :=
    Ext_withSto hE.2.1 (fun _ _ h => h) hI2 hP1
  have hE' : EnvOK p (η.withSto η.sto I2 P1 η.seen) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
  have hiq : (CE (η.withSto η.sto I2 P1 η.seen)).ini l = (CE η).ini l := by
    show I2 l = η.ini l; exact hI2e l
  have hMI := MemInv_plantFN (E' := CE (η.withSto η.sto I2 P1 η.seen)) (N := Np) hm hsto hown hnone'
    rfl rfl rfl rfl (by rw [hNp]; exact Nat.le_refl _) hrl rfl rfl rfl hF
    (fun h => absurd h (by rw [hNp]; exact Nat.lt_irrefl _))
    (fun o h1 h2 => absurd ((InitR_iff hiq).1 h1) h2)
    (fun b S' us _ _ h1 h2 => absurd ((IniSeg_iff hiq).1 h1) h2) hcpl hcT hnT hrT
  have hV2 : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR (CE η) T vs R →
      ValOfR (CE (η.withSto η.sto I2 P1 η.seen)) T vs R := fun h =>
    ValOfR_mono (η₁ := CE η) (η₂ := CE (η.withSto η.sto I2 P1 η.seen)) rfl rfl
      (fun _ _ h => h) hI2 h hP1 (fun _ _ h => h) (fun _ => Nat.le_refl _)
  have hvisl : ∀ l', l' ≠ l → Vis (CE (η.withSto η.sto I2 P1 η.seen)) l' → Vis (CE η) l' :=
    fun l' hne hv hpr => hv ⟨hpr.1, by simpa [CE, TEnv.withSto, P1, hne] using hpr.2⟩
  obtain ⟨H', cr', db', hH', hC', heq, hKN⟩ := PromCrK_liftK (hsto := fun _ => rfl) (E2 := CE (η.withSto η.sto I2 P1 η.seen)) (l := l) hC
    (fun tw m R hm' hp hla => by
      obtain ⟨-, -, -, -, -, -, -, -, -, hpf, -⟩ := hp
      exact hpf (by rw [hla]; exact hnone'))
    (fun tw m R hm' hla hp => TermPlant.PlantCr_mono (E := CE η) (E' := CE (η.withSto η.sto I2 P1 η.seen)) (s := stOf mem pairs th) (s' := stOf mem pairs th)
      (fun _ _ => rfl) (Nat.le_refl _) rfl (MemInv_promLt hm) rfl rfl
      (fun h => by
        show P1 m.loc.label ≠ none
        simp only [P1, hla, ite_false]; exact h)
      (fun h => (WordUnit_congr rfl).1 h)
      (fun _ _ h => by
        have hvq : Vis (CE (η.withSto η.sto I2 P1 η.seen)) m.loc.label ↔ Vis (CE η) m.loc.label :=
          Vis_congr rfl rfl (by show P1 m.loc.label = η.pfr m.loc.label; simp [P1, hla])
        unfold FpAt at h ⊢; rw [hvq] at h; exact h)
      (fun S ws R0 h => hV2 h) hp)
    (fun cr0 hC0 => by
      obtain ⟨H2, cr2, db2, hH2, hC2, hk, e⟩ := MemHeld_flipLH (E := CE η)
        (E' := CE (η.withSto η.sto I2 P1 η.seen)) (l := l)
        hm hH hC0 hpa (fun _ => rfl) (fun l' => hI2e l')
        (fun l' hv hpr => hv ⟨hpr.1, by
          by_cases he : l' = l
          · subst he; have := hpr.2; simp [CE, TEnv.withSto, P1] at this
          · have := hpr.2; simpa [CE, TEnv.withSto, P1, he] using this⟩)
        hvisl hV2 hf hfo ⟨c, hsto, hown⟩
        (fun l' hne => by
          by_cases he : l' = l
          · subst he; simp [CE, TEnv.withSto, P1]
          · simpa [CE, TEnv.withSto, P1, he] using hne)
        (fun l' hne h1 => by simpa [CE, TEnv.withSto, P1, hne] using h1)
        rfl (fun _ => rfl)
      refine ⟨H2, cr2, db2, hH2, hC2, fun tw m htw hm' hla => hk tw m htw hm' ?_, e⟩
      rintro ⟨h1, h2⟩
      exact h2 ⟨(WordUnit_congr rfl).1 h1.1, hvisl _ hla h1.2⟩)
  -- the plain invariant at the raised environment
  have hTE' : ThInvE p (CE (η.withSto η.sto I2 P1 η.seen)) th := by
    obtain ⟨ρe, ηe, cxe, hEe0, hEe, hTye, htve, hFIe⟩ := hTE
    have hce : CE ηe = CE η := hEe0.trans hE0.symm
    have q1 : ηe.sto = η.sto := (congrArg TEnv.sto hce : (CE ηe).sto = (CE η).sto)
    have q2 : ηe.ini = η.ini := (congrArg TEnv.ini hce : (CE ηe).ini = (CE η).ini)
    have q3 : ηe.pfr = η.pfr := (congrArg TEnv.pfr hce : (CE ηe).pfr = (CE η).pfr)
    have q4 : ηe.seen = η.seen := (congrArg TEnv.seen hce : (CE ηe).seen = (CE η).seen)
    have hxe : Ext ηe (ηe.withSto ηe.sto I2 P1 ηe.seen) :=
      Ext_withSto hEe.2.1 (fun _ _ h => h) (fun l' => by rw [q2]; exact hI2 l')
        (fun l' f h => hP1 l' f (by rw [← q3]; exact h))
    refine ⟨ρe, ηe.withSto ηe.sto I2 P1 ηe.seen, cxe, ?_, ⟨hEe.1, hxe.1, hxe.2.2.2.2.2.2.2.2.2.2.1⟩, hTye, htve, FInv_ext hEe.2.1 hxe hFIe.1, hFIe.2⟩
    have q5 : ηe.prog = η.prog := (congrArg TEnv.prog hce : (CE ηe).prog = (CE η).prog)
    have q6 : ηe.tid = η.tid := (congrArg TEnv.tid hce : (CE ηe).tid = (CE η).tid)
    have q7 : ηe.rini = η.rini := (congrArg TEnv.rini hce : (CE ηe).rini = (CE η).rini)
    have q8 : ηe.box = η.box := (congrArg TEnv.box hce : (CE ηe).box = (CE η).box)
    have q9 : ηe.fp = η.fp := (congrArg TEnv.fp hce : (CE ηe).fp = (CE η).fp)
    simp only [CE, TEnv.withSto, q1, q4, q5, q6, q7, q8, q9]
  have hRE' : ThInvRE p (CE (η.withSto η.sto I2 P1 η.seen)) th Tot :=
    ⟨ρ, _, cx, Rf, Rs, rfl, hE', hTy, htv, FInvR_ext hE.2.1 hE.2.2 hx hFI, hsum⟩
  have e2' : CE (η.withSto η.sto I2 P1 η.seen) = Cut (plant1 Eg l F Np) g.i S := e2
  rw [e2'] at hRE' hTE' hMI hH' hC'
  obtain ⟨HP', HS', rfl, hP', hS'⟩ := MemHeld_split (fun _ _ h1 h2 => Cut_cov h1 h2) hH'
  exact ⟨HP', HS', cr', db', ⟨hRE', hTE', hMI, hP', hS', hC'⟩, heq, by rw [hE0] at hKN; exact hKN⟩

/-- (L4, A′) **The flip of one own label at a count that does not rise** (`Np = Eg.ini l`):
`ThSysAt` survives for any cell type (no new slots, so no value side condition). -/
theorem ThSysAt_flip1 {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell}
    {F Np : Ts}
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hc : Eg.sto l = some c) (ho : c.owner = some g.i) (hnone : Eg.pfr l = none)
    (hrl : Eg.rini l ≤ Eg.ini l) (hNp : Np = Eg.ini l)
    (hF : F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (Cut Eg g.i S) (stOf mem pairs th) l F)
    (hcpl : ∀ b S', SegOf c.ty b S' → accs S' ≠ none → TearOK S') (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hf : FlipOK (Cut Eg g.i S) (stOf mem pairs th) l) (hfo : FpOK (Cut Eg g.i S) (stOf mem pairs th)) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
    obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := ThSysAt_flip1K h hpa hc ho hnone hrl hNp hF hcpl hcT hnT hrT hf hfo
    exact ⟨x0, x1, x2, x3, h0, h1⟩

/-- (dedup) master of `ThSysAt_flip1B`: also exports `KeepNW` (old non-word credits kept). -/
theorem ThSysAt_flip1BK {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg0 Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell}
    {F Np : Ts} (A : PAgree Eg0 Eg g.i l)
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hc : Eg0.sto l = some c) (ho : c.owner = some g.i) (hnone : Eg0.pfr l = none)
    (hrl : Eg0.rini l ≤ Eg0.ini l) (hNp : Np = Eg0.ini l)
    (hF : F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (Cut Eg0 g.i S) (stOf mem pairs th) l F)
    (hcpl : ∀ b S', SegOf c.ty b S' → accs S' ≠ none → TearOK S') (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hf : FlipOK (Cut Eg0 g.i S) (stOf mem pairs th) l) (hfo : FpOK (Cut Eg0 g.i S) (stOf mem pairs th)) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' ∧
      KeepNW (Cut Eg0 g.i S) mem th.promises cr cr' :=
  exK_sto (E := Cut Eg g.i S) A.csto <| ThSysAt_flip1K h hpa (by rw [A.sto]; exact hc) ho (by rw [A.pfr]; exact hnone)
    (by rw [A.rini, A.ini]; exact hrl) (by rw [A.ini]; exact hNp) (hF.imp id (HoldW_agree A))
    hcpl hcT hnT hrT (FlipOK_agree A hf) (FpOK_agree A hfo)

/-- (L4) `ThSysAt_flip1` at a partial plant agreeing with the base at `l`. -/
theorem ThSysAt_flip1B {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg0 Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell}
    {F Np : Ts} (A : PAgree Eg0 Eg g.i l)
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hc : Eg0.sto l = some c) (ho : c.owner = some g.i) (hnone : Eg0.pfr l = none)
    (hrl : Eg0.rini l ≤ Eg0.ini l) (hNp : Np = Eg0.ini l)
    (hF : F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (Cut Eg0 g.i S) (stOf mem pairs th) l F)
    (hcpl : ∀ b S', SegOf c.ty b S' → accs S' ≠ none → TearOK S') (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hf : FlipOK (Cut Eg0 g.i S) (stOf mem pairs th) l) (hfo : FpOK (Cut Eg0 g.i S) (stOf mem pairs th)) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
    obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := ThSysAt_flip1BK A h hpa hc ho hnone hrl hNp hF hcpl hcT hnT hrT hf hfo
    exact ⟨x0, x1, x2, x3, h0, h1⟩

#print axioms ThSysAt_plant1BK
#print axioms ThSysAt_flip1K
#print axioms ThSysAt_flip1BK
#print axioms ThSysAt_plantLK

end TermPlantL

#print axioms TermPlantL.ThSysAt_plant1B
#print axioms TermPlantL.ThSysAt_plantL
#print axioms TermPlantL.plantL_eq_plantG
#print axioms TermPlantL.FlipOK_agree
#print axioms TermPlantL.FpOK_agree
#print axioms TermPlantL.HoldW_agree
#print axioms TermPlantL.ThSysAt_flip1
#print axioms TermPlantL.ThSysAt_flip1B
