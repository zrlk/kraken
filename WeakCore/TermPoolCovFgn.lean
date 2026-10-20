import WeakCore.TermPoolSupp
import WeakCore.PoolCovB

/-! The `fgnCov` share of the (B) pool cover `PoolCovU` (prototype
`PoolCovB`), with `δc`/`δh` testing `QCr`.

The creating case: a foreign step of `i` newly overtakes a unit `⟨l, o⟩` of the owner `j`'s frontier
cell.  The unit's cover item is the stepper's drop entry `g` at its (first) target `Hf`, credited at the
pool part `δh`: `tgtSupp_of` gives `Hf`'s support (`QCr` or the post pool tag); off `QCr` the transfer
goes to `δh` (`δh_eq`, the owner of a `QC` target is unique), so the entry, with any mask `K`
whose pins hold, is a `CrItemQ` at `pl j + δh`.  `QCr` fails at `Hf` when `Hf` is the unit's first
write (`slotFW_of_unit`).

Open (named, the stepper side): the entry/target at the newly overtaken unit with its pin (`K` at the
unit's access word), and `¬ QCr` at `Hf` when `Hf` is not the unit's own first write (piece level). -/

namespace TermPoolCovFgn
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper TermPool TermOverCrW TermPoolStaging TermPoolFgnCov
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The transfer goes to the pool** at a foreign promise `t` of `j` that is not `QCr` there but
post-tagged: no other thread holds a `QC` plant credit at `t` (a plant credit names its cell's owner). -/
theorem δh_eq {δ : Ts → Res} {cr pl : Nat → Ts → Res} {c c' : Cfg} {Eg' : GEnv} {i j : Nat} {thj : TTh}
    {t : Ts} (hji : j ≠ i) (hj : c.ths[j]? = some thj) (hj' : c'.ths[j]? = some thj) (ht : t ∈ thj.promises)
    (hho : ∀ j', j' ≠ i → c'.ths[j']? = c.ths[j']?)
    (hnq : ¬ QCr Eg' c' j t (cr j t + δ t))
    (hP : ∀ thj', c'.ths[j]? = some thj' → PTag Eg' c' j thj' (fun u => pl j u + δ u) t) :
    δh δ cr pl c c' Eg' i t = δ t := by
  classical
  have hC : ¬ ∃ j' thj', j' ≠ i ∧ c.ths[j']? = some thj' ∧ t ∈ thj'.promises ∧
      QCr Eg' c' j' t (cr j' t + δ t) := by
    rintro ⟨j', thj', hj'i, hj'', -, hq⟩
    obtain ⟨⟨m', hm', hall⟩, hns⟩ := hq
    have hj3 : c'.ths[j']? = some thj' := by rw [hho j' hj'i]; exact hj''
    obtain ⟨c1, -, -, -, -, -, -, hs1, ho1, -⟩ := (hall (fun _ => False) thj' hj3).1
    obtain ⟨-, -, m, hm, -, hit⟩ := hP thj hj'
    obtain ⟨cl, -, hcl, hown, -⟩ := hit (fun _ => False)
    have e : m = m' := Option.some.inj (hm.symm.trans hm')
    subst e
    have e1 := (cutSto_some.1 hcl).1
    have e2 := (cutSto_some.1 hs1).1
    rw [e1] at e2
    cases e2
    have e3 : j' = j := by
      rw [hown] at ho1
      exact (Option.some.inj ho1).symm
    subst e3
    exact hnq ⟨⟨_, hm', hall⟩, hns⟩
  have hH : (¬ ∃ j' thj', j' ≠ i ∧ c.ths[j']? = some thj' ∧ t ∈ thj'.promises ∧
      QCr Eg' c' j' t (cr j' t + δ t)) ∧
      ∃ j' thj', j' ≠ i ∧ c.ths[j']? = some thj' ∧ t ∈ thj'.promises ∧ ¬ QCr Eg' c' j' t (cr j' t + δ t) ∧
        ∀ thj'', c'.ths[j']? = some thj'' → PTag Eg' c' j' thj'' (fun u => pl j' u + δ u) t :=
    ⟨hC, j, thj, hji, hj, ht, hnq, hP⟩
  unfold δh
  rw [ite_eq_left hH]

/-- A unit's lowest own promise that is its first write at a predicted unit is `SlotFW`. -/
theorem slotFW_of_unit {Eg' : GEnv} {c' : Cfg} {j : Nat} {S : AllocLabel → Prop} {thj : TTh} {l : AllocLabel}
    {o : Nat} {tw : Ts} (hP : PredU (Cut Eg' j S) ⟨l, o⟩)
    (hlo : TermPlant.LowOwn (stOf c'.mem c'.pairs thj) ⟨l, o⟩ tw) (hfw : FirstW c'.mem ⟨l, o⟩ tw) :
    SlotFW Eg' c' j tw := by
  obtain ⟨-, ⟨m, hm, hml⟩, -⟩ := hlo
  exact ⟨m, hm, by rw [hml]; exact hfw, fun _ => by rw [hml]; exact hP⟩

/-- **The creating case** (explicit form): the drop entry `g` at its target `Hf` (`δ Hf = g.R`), with a
mask `K` whose pins hold after the step (`hIt`, credit bound `g.R`), off `QCr` at `Hf`, is a cover item
at the post pool `pl j + δh` selecting the unit's access word. -/
theorem poolCovU_create {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
    {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (hA : Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F
      cr' db' δ Gd tg j thj Sj l cl)
    {g : TermPiece.GdE} (hg : g ∈ Gd) {Hf : Ts} (htg : tg g = some Hf) (hδg : δ Hf = g.R) {K : Nat → Bool}
    (hIt : TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun _ => g.R) l cl (Hf, g.b, g.S, g.ws, g.R, K))
    (hnq : ¬ QCr (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j Hf (cr j Hf + δ Hf))
    {o : Nat} {usS : List Acc} {ii : Nat} (hus : accs g.S = some usS) (hb : g.b ≤ o)
    (hin : InAcc usS ii (o - g.b)) (hK : K ii = true) :
    ∃ (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) (usS : List Acc) (ii : Nat),
      TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj)
        (fun u => pl j u + δh δ cr pl c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i u) l cl x ∧
      accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS ii (o - x.2.1) ∧ x.2.2.2.2.2 ii = true := by
  have X := hA.1
  have hji := hA.2.2.2.2.2.2.2.2.1
  have hj := hA.2.2.2.2.2.2.2.2.2.1
  obtain ⟨mh, -, hmh, hlab, hlow, hnw, -⟩ := id hIt
  have hj' : c'.ths[j]? = some thj := by rw [X.ho j hji]; exact hj
  obtain ⟨ht, hq | hP⟩ := TermPoolSupp.tgtSupp_of hA hg htg hδg hmh hlab hlow hnw
  · exact absurd hq hnq
  have e := δh_eq hji hj hj' ht (fun j' h => X.ho j' h) hnq hP
  refine ⟨(Hf, g.b, g.S, g.ws, g.R, K), usS, ii, crItemQ_le ?_ hIt, hus, hb, hin, hK⟩
  intro k'
  show g.R k' ≤ (pl j Hf + δh δ cr pl c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Hf) k'
  rw [Res.add_apply, e, hδg]
  exact Nat.le_add_left _ _

/-- **`PredU` is element-wise**: two units of one piece of an own cell are predicted alike (a solid
piece lies inside one array element). -/
theorem predU_piece {E : TEnv} {l : AllocLabel} {cl : Cell} (hsto : E.sto l = some cl) {b : Nat} {U : Ty}
    {vs : List Acc} (hP : TermPiece.Piece cl.ty b U) (hvs : accs U = some vs) {o o' : Nat}
    (ho1 : b ≤ o) (ho2 : o < b + nWords vs) (ho1' : b ≤ o') (ho2' : o' < b + nWords vs)
    (h : PredU E ⟨l, o⟩) : PredU E ⟨l, o'⟩ := by
  -- the element of the piece
  have hel : ∀ N e us, cl.ty = .array (.lit N) e → accs e = some us →
      ∃ jj, jj * nWords us ≤ b ∧ b + nWords vs ≤ jj * nWords us + nWords us := by
    intro N e us hT hu
    rcases AtOff_arr_elem hP.1 hT with e1 | ⟨us', jj, o'', hu', -, hb, hat⟩
    · exact absurd (e1.trans hT) (hP.2.1.2.1 _ _)
    · rw [hu] at hu'
      cases hu'
      have hbd := AtOff_bound hat hu hvs
      exact ⟨jj, by omega, by omega⟩
  obtain ⟨hpf, hiw, hnr⟩ := h
  refine ⟨hpf, fun c N e us hc hT hu => ?_, fun hw => hnr fun c N e us hc hT hu => ?_⟩
  · have hc' : c = cl := Option.some.inj (hc.symm.trans hsto)
    subst hc'
    obtain ⟨jj, h1, h2⟩ := hel N e us hT hu
    have hi := hiw c N e us hc hT hu
    have hlt : jj < E.ini l := Nat.lt_of_not_le fun hle => by
      have := Nat.mul_le_mul_right (nWords us) hle
      change o < E.ini l * nWords us at hi
      omega
    have := Nat.mul_le_mul_right (nWords us) (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    change o' < E.ini l * nWords us
    omega
  · have hc' : c = cl := Option.some.inj (hc.symm.trans hsto)
    subst hc'
    obtain ⟨jj, h1, h2⟩ := hel N e us hT hu
    have hi := hw c N e us hc hT hu
    have hlt : jj < E.rc l := Nat.lt_of_not_le fun hle => by
      have := Nat.mul_le_mul_right (nWords us) hle
      change o' < E.rc l * nWords us at hi
      omega
    have := Nat.mul_le_mul_right (nWords us) (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    change o < E.rc l * nWords us
    omega

/-- **The target is the first write at its own predicted unit** (at a not-yet-published owner cell,
`PredHoldG`): the drop target `Hf`, `j`'s lowest own promise of the entry's piece, sits in the piece of
a predicted unit `o`; its unit is predicted (element-wise), its first write is an own promise
(`PredHoldG`), hence `Hf` (lowest in the piece, and not `undef`). -/
theorem slotFW_of_piece {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
    {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (hA : Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F
      cr' db' δ Gd tg j thj Sj l cl)
    (hnp : ¬ Eg.pubd l) {g : TermPiece.GdE} (hg : g ∈ Gd) {Hf : Ts} (htg : tg g = some Hf)
    (hIl : ∃ mh, c'.mem[Hf]? = some mh ∧ mh.loc.label = l)
    {o : Nat} {usS : List Acc} (hus : accs g.S = some usS) (hb : g.b ≤ o) (ho : o < g.b + nWords usS)
    (hPU : PredU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩) :
    SlotFW (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j Hf := by
  classical
  obtain ⟨X, Y, Z, -, -, hDrop, -, ⟨-, hPd, -, -⟩, hji, hj, hc2, hown, hpf2⟩ := hA
  have hgf := gfoot_of X Y Z
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, hini, hrini, hpfr2⟩ := own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hpreM := tctx_pre X
  have hstoi : (Cut Eg i S).sto l = some cl := cutSto_some.2 ⟨hs, Or.inr ⟨f, hf⟩⟩
  have hDr : TermPiece.Drop (Cut Eg i S) (stOf c.mem c.pairs th) Gd := by rw [← Y.1]; exact hDrop
  obtain ⟨j0, thj0, m, hj0, ht0, hm, hml, us, hus', h1, h2, hlowP, ⟨cl0, hcl0, ho0⟩, -⟩ := hPd g hg Hf htg
  have hgl : g.l = l := by
    obtain ⟨mh, hmh, hmhl⟩ := hIl
    have e : mh = m := Option.some.inj (hmh.symm.trans hm)
    subst e
    exact hml.symm.trans hmhl
  have hj0e : j = j0 := by
    rw [hml, hgl, hs] at hcl0
    cases hcl0
    rw [hown] at ho0
    exact Option.some.inj ho0
  subst hj0e
  have e1 : thj = thj0 := Option.some.inj (hj.symm.trans hj0)
  subst e1
  rw [hus] at hus'
  cases hus'
  obtain ⟨c1, hc1, -, -, hpc, -⟩ := hDr.1 g hg
  rw [hgl, hstoi] at hc1
  cases hc1
  -- the target's unit is predicted, after and before the step
  have hml' : m.loc = ⟨l, m.loc.offset⟩ := by rw [← hgl, ← hml]
  have hPf : PredU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) m.loc := by
    rw [hml']
    exact predU_piece hc2 hpc (vs := usS) hus hb ho h1 h2 hPU
  have hPf0 : PredU (Cut Eg j Sj) m.loc := by
    refine (PredU_congr (E := Cut Eg j Sj) (E' := Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      ?_ rfl ?_ ?_ ?_).1 hPf
    · rw [hml']; exact hc2.trans hpre_c.symm
    · rw [hml']; exact hpfr2
    · rw [hml']; exact hini
    · rw [hml']; simp only [TEnv.rc, Cut_rini, Cut_ini]; exact congr (congrArg min hini) hrini
  -- the first write there is an own promise (`PredHoldG`), so it is `Hf`
  obtain ⟨h, hfw, hh, -⟩ := X.inv.predHold j thj Sj m.loc hj ⟨cl, by rw [hml']; exact hs, hown⟩
    (by rw [hml']; exact hnp) hPf0
  have hHf : Hf < c.mem.size := X.inv.plt j thj Hf hj ht0
  have hm0 : c.mem[Hf]? = some m := by rw [← hpreM Hf hHf]; exact hm
  have hle1 : h ≤ Hf := TermPredHold.holder_min hfw hm0 rfl (X.inv.promNU j thj Hf m hj ht0 hm0)
  obtain ⟨mh, hmh, hmhl, -⟩ := hfw.1
  have hle2 : Hf ≤ h := hlowP h mh hh (by rw [hpreM h (X.inv.plt j thj h hj hh)]; exact hmh)
    (by rw [hmhl]) (by rw [hmhl]; exact h1) (by rw [hmhl]; exact h2)
  have e : h = Hf := Nat.le_antisymm hle1 hle2
  subst e
  refine ⟨m, hm, ⟨⟨m, hm, rfl, X.inv.promNU j thj h m hj ht0 hm0⟩, fun t m' ht hm' hl' => ?_⟩, fun _ => hPf⟩
  have ht' : t < c.mem.size := Nat.lt_trans ht hHf
  rw [hpreM t ht'] at hm'
  exact hfw.2 t m' ht hm' hl'

/-- **The `fgnCov` share of `PoolCovU`** at one owner cell: a unit meeting `PoolCovU`'s premises after
the step that was not overtaken before is covered at the post pool `pl j + δh`, given the stepper's
entry at the unit (named, open: `hN`); the owner cell is not yet published (`hnp`), so the entry's
target is off `QCr` (`slotFW_of_piece`). -/
theorem poolCovU_fgn {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
    {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (hA : Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F
      cr' db' δ Gd tg j thj Sj l cl)
    (hnp : ¬ Eg.pubd l) {o : Nat}
    (hPU : PredU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩)
    (hN : ∃ g ∈ Gd, ∃ (Hf : Ts) (K : Nat → Bool) (usS : List Acc) (ii : Nat), tg g = some Hf ∧ δ Hf = g.R ∧
      TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) (fun _ => g.R) l cl (Hf, g.b, g.S, g.ws, g.R, K) ∧
      accs g.S = some usS ∧ g.b ≤ o ∧ InAcc usS ii (o - g.b) ∧ K ii = true) :
    ∃ (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) (usS : List Acc) (ii : Nat),
      TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj)
        (fun u => pl j u + δh δ cr pl c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i u) l cl x ∧
      accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS ii (o - x.2.1) ∧ x.2.2.2.2.2 ii = true := by
  obtain ⟨g, hg, Hf, K, usS, ii, htg, hδg, hIt, hus, hb, hin, hK⟩ := hN
  have hnq : ¬ QCr (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j Hf (cr j Hf + δ Hf) := by
    obtain ⟨mh, -, hmh, hmhl, -⟩ := hIt
    have ho : o < g.b + nWords usS := by
      have h1 := hin.2
      have h2 := TermOverCr.nWords_take_le usS (ii + 1)
      omega
    exact fun h => h.2 (slotFW_of_piece hA hnp hg htg ⟨mh, hmh, hmhl⟩ hus hb ho hPU)
  exact poolCovU_create hA hg htg hδg hIt hnq hus hb hin hK

end TermPoolCovFgn

#print axioms TermPoolCovFgn.δh_eq
#print axioms TermPoolCovFgn.slotFW_of_unit
#print axioms TermPoolCovFgn.poolCovU_create
#print axioms TermPoolCovFgn.poolCovU_fgn
#print axioms TermPoolCovFgn.predU_piece
#print axioms TermPoolCovFgn.slotFW_of_piece
