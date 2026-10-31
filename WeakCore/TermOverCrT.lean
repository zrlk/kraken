import WeakCore.TermOverCrS
import WeakCore.TermInterf

/-! # TermOverCrT: an idle thread's plant credit after a thread step (H7 htg)

`TermInterf.interfCrTK_holds`'s plant-credit transport, stated alone: along thread `i`'s step,
a plant credit of an idle thread `j ≠ i` stays one, unchanged, at `j`'s post-step cut.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **(H7 htg, transport) An idle thread's plant credit survives a thread step.** -/
theorem plantCr_post {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {m : Msg} {tw : Ts} {R : Res}
    (hpc : PlantCr (Cut Eg j Sj) (stOf c.mem c.pairs thj) m tw R) :
    PlantCr (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) m tw R := by
  have hgf := gfoot_of X Y (Z.toC _ _ _ _ _)
  have hI := (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hPlt : ∀ t, t ∈ thj.promises → t < c.mem.size := fun t ht => X.inv.plt j thj t hj ht
  have hpre := tctx_pre X
  have hsz : c.mem.size ≤ c'.mem.size := by
    apply Nat.le_of_not_lt; intro h
    have e := hpre _ h
    rw [Array.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem h] at e
    cases e
  obtain ⟨cl, hsto, hpne⟩ : ∃ cl, (Cut Eg j Sj).sto m.loc.label = some cl ∧
      (Cut Eg j Sj).pfr m.loc.label ≠ none :=
    let ⟨cl, _, _, _, _, _, _, h1, _, h3, _⟩ := hpc; ⟨cl, h1, h3⟩
  have hsto2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto m.loc.label = some cl :=
    hI.sto _ _ hsto
  have hVis : Vis (Cut Eg j Sj) m.loc.label := fun h => hpne h.2
  refine TermPlant.PlantCr_mono (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj) hpre hsz rfl hPlt
    (hsto2.trans hsto.symm) rfl (fun h hn => ?_) (fun h => ?_) (fun t _ h => ?_)
    (fun S ws R0 hv => ValOfR_mono hI.prog rfl hI.sto hI.ini hv hI.pfr hI.box hI.rini) hpc
  · cases e : (Cut Eg j Sj).pfr m.loc.label with
    | none => exact h e
    | some f => exact absurd ((hI.pfr _ _ e).symm.trans hn) (fun h0 => by cases h0)
  · have hstoEq : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto
        (⟨m.loc.label, m.loc.offset⟩ : Address).label =
        (Cut Eg j Sj).sto (⟨m.loc.label, m.loc.offset⟩ : Address).label := by
      show _ = _; rw [hsto2]; exact hsto.symm
    have h' : WordUnit (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        ⟨m.loc.label, m.loc.offset⟩ := h
    rw [WordUnit_congr hstoEq] at h'; exact h'
  · have h1 := FpAt_sub h
    change t ∈ fpSync Eg c' j at h1
    rw [FpAt_vis (a := ⟨m.loc.label, 0⟩) hVis]
    exact (List.mem_filter.1 h1).1


/-- **(H7 htg) The `Pδ` witness**: the piece-lowest own promise `t` of an idle thread `j`, a
key-free plant credit for the entry's payload on top of its `PromCrK` credit before the step, meets
TermMain's plant-transfer predicate `Pδ g t` (H7 form) after it. -/
theorem pd_witness {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {j : Nat} {thj : TTh} {S0 : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {g : TermPiece.GdE} {us : List Acc} {t : Ts} {m : Msg}
    (hC : TermPlant.PromCrK (Cut Eg j S0) (stOf c.mem c.pairs thj) (cr j) (db j))
    (ht : t ∈ thj.promises) (hm : c.mem[t]? = some m) (hl : m.loc.label = g.l) (hus : accs g.S = some us)
    (hb1 : g.b ≤ m.loc.offset) (hb2 : m.loc.offset < g.b + nWords us)
    (hw : ¬ WordUnit (Cut Eg j S0) m.loc)
    (hpc : PlantCr (Cut Eg j S0) (stOf c.mem c.pairs thj) m t g.R) (hK : TermPlant.CrKeys g.R) :
    t ∉ th.promises ∧ ∃ j' thj' m', j' ≠ i ∧ c.ths[j']? = some thj' ∧ t ∈ thj'.promises ∧
      c'.mem[t]? = some m' ∧ m'.loc.label = g.l ∧
      (∃ us', accs g.S = some us' ∧ g.b ≤ m'.loc.offset ∧ m'.loc.offset < g.b + nWords us') ∧
      ∀ (Sj : AllocLabel → Prop) thj'', c'.ths[j']? = some thj'' →
        PlantCr (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j' Sj) (stOf c'.mem c'.pairs thj'')
          m' t (cr j' t + g.R) ∧ TermPlant.CrKeys (cr j' t + g.R) := by
  have hpre := tctx_pre X
  have hm' : c'.mem[t]? = some m := by rw [hpre t (X.inv.plt j thj t hj ht)]; exact hm
  obtain ⟨hP2, hK2⟩ := plantCrK_add hC ht hm hw hpc hK
  refine ⟨fun hti => X.inv.disj j i thj th t hji hj X.hth ht hti, j, thj, m, hji, hj, ht, hm', hl,
    ⟨us, hus, hb1, hb2⟩, fun Sj thj'' hj'' => ?_⟩
  have e : thj'' = thj := Option.some.inj (hj''.symm.trans ((X.ho _ hji).trans hj))
  subst e
  exact ⟨plantCr_post (Sj := Sj) X Y Z hji hj hP2, hK2⟩

#print axioms pd_witness

end

#print axioms plantCr_post

end TermOverCrW
