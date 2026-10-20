import WeakCore.TermNewCoh
import WeakCore.TermOverCrProm
import WeakCore.TermPlantAtF
import WeakCore.TermTyped

/-! # TermOwnNF: nothing is overtaken at a cell the step newly fronts (shared lemma)

At a thread step that gives a formerly private own cell a frontier (a publish or a plant),
every message above the thread's lowest own promise `tw` at a non-visible unit of that cell
is skipped (`PromAt`).  The reason: a message that is not an outstanding own promise of the
stepper after the step is at or below the stepper's coherence there, and that is below `tw`
(`PromAbove` after the step, from certification).  The coherence bound has three cases:
* a message the step appends: `TermNewCoh.tctx_newCoh`;
* an own promise the step fulfils: `TermPlantAtF.tstep_fulCoh` (with `cfgCoh`);
* any other old message: `TermOverCrProm.priv_le_coh` before the step (`OwnOKSF` with no
  frontier), then coherence monotonicity (`TermLiveProps.tstep_mono`, with `cfgCoh`).
-/

namespace TermOwnNF
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **No overtaking at a newly fronted cell**: after a thread step of `i`, at a unit of a cell
that was private before the step and has a frontier after it, the lowest own promise `tw` is not
overtaken at any environment where the unit is not visible. -/
theorem nf_of
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i)
      (db i) δ)
    (E2 : TEnv) (l : AllocLabel) (o : Nat) (tw : Ts)
    (hpf : (CE η).pfr l = none) (hpf' : E'.pfr l ≠ none) (hsto' : E'.sto l ≠ none)
    (hv : ¬ VisU E2 ⟨l, o⟩) (hlo : TermPlant.LowOwn (stOf c'.mem c'.pairs r.2.2) ⟨l, o⟩ tw) :
    ¬ TermPlant.OverT E2 (stOf c'.mem c'.pairs r.2.2) ⟨l, o⟩ tw := by
  rintro ⟨t, m, hlt, hm, hloc, hnp⟩
  obtain ⟨htw, ⟨mw, hmw, hlw⟩, -⟩ := hlo
  obtain ⟨-, u2, u3, -, -⟩ := TermCert.tstep_appUp X.hr
  have hext : ∀ u mu, c.mem[u]? = some mu → c'.mem[u]? = some mu := fun u mu h => by
    rw [X.e1]; exact u2 u mu h
  have back : ∀ u mu, u < c.mem.size → c'.mem[u]? = some mu → c.mem[u]? = some mu := fun u mu hu h => by
    obtain ⟨m0, hm0⟩ : ∃ m0, c.mem[u]? = some m0 := ⟨_, Array.getElem?_eq_getElem hu⟩
    rw [hext u m0 hm0] at h
    rw [hm0, h]
  have htw0 : tw ∈ th.promises := u3 tw htw
  have hmw0 : c.mem[tw]? = some mw := back tw mw (X.inv.plt i th tw X.hth htw0) hmw
  have hu := X.inv.promNU i th tw mw X.hth htw0 hmw0
  by_cases hin : t ∈ (stOf c'.mem c'.pairs r.2.2).promises ++ FpAt E2 ⟨l, o⟩
  · exact hnp (TermOverCrProm.mem_promAt_above hv hin hlt hmw hlw hu)
  have htp' : t ∉ r.2.2.promises := fun h => hin (List.mem_append_left _ h)
  have hown : OwnAt (CE η) l := by
    rcases Z.1.2.2.2.2.2.1 l with e | ⟨-, F0, -, -, -, hown, -⟩ | ⟨-, -, hn⟩
    · rw [e] at hpf'; exact absurd hpf hpf'
    · exact hown
    · exact absurd hn hsto'
  obtain ⟨cl, hcl, hcown⟩ := hown
  have hclm : (CE η).sto m.loc.label = some cl := by rw [hloc]; exact hcl
  have hcc := X.inv.cfgCoh i th X.hth
  have hcoh : t ≤ r.2.2.vs.coh m.loc := by
    by_cases hnew : c.mem.size ≤ t
    · exact TermNewCoh.tctx_newCoh X Y t m cl hnew (by rw [← X.e1]; exact hm) hclm
    have hm0 : c.mem[t]? = some m := back t m (Nat.lt_of_not_le hnew) hm
    by_cases hth : t ∈ th.promises
    · exact TermPlantAtF.tstep_fulCoh X.hr hcc t hth htp' m hm0
    obtain ⟨S0, -, -, hMI, -⟩ := X.inv.thr i th X.hth
    have e := Y.1
    rw [e] at hcl hpf hcown
    have hle := TermOverCrProm.priv_le_coh (l := l) (cl := cl) hMI hcl hcown
      hpf (X.inv.msgWords t m cl hm0 (by rw [hloc]; exact cutSto_sub hcl)) hth hm0 (by rw [hloc])
    exact Nat.le_trans hle ((TermLiveProps.tstep_mono _ _ _ _ r X.hr hcc).2 m.loc)
  have hpa := TermTyped.certified_promAboveSt X.cert X.e3 tw htw mw hmw
  rw [hlw, ← hloc] at hpa
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hcoh (Nat.lt_trans hpa hlt))

end

end TermOwnNF

#print axioms TermOwnNF.nf_of
