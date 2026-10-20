import WeakCore.TermCohLe

/-!
# TermRmw: T8 `rmw` from the scope and memory's invariant

`NoPlantRMW` asks a `cas`/`fetch` at one of the thread's own **private** cells (no
frontier) to target a slot below the real count.  `TermCohLe.rmwS_core` gives that from
typing except through a non-`own` reference that is a region reference, or a `pub` one at
a label with `rini < ini`.  The region half is excluded by the stepper's scope
(`StepScope ∨ StepScopeR`: a `cas`/`fetch` reference is `own` or `pub`; `StepScopeR` has no
RMW), and `rini < ini` at an own label means a frontier (`OwnHidP`), which a private cell
has not.  An RMW at a planted or published cell is not constrained here: one fulfilling a
designated promise would read the cell's `undef` placeholder, which `rmwPlainAccL` refutes.
-/

namespace TermRmw
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermCohLe
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- In scope, a `cas`/`fetch` reference is `own` or `pub`. -/
theorem rmw_mode {cx : Cx} {σs : List Ty} {th : TTh} {w : At} {tw u : Ty} {μ : Mode}
    (hsc : StepScope cx th.term ∨ StepScopeR σs cx th.term)
    (hrmw : (∃ acq rel e v x ok fail, th.term = .cas acq rel w e v x ok fail) ∨
      (∃ x o acq rel v e, th.term = .let_ x (.fetch o acq rel w v) e))
    (hpk : cx.peek w = .ok tw) (hc : cellOf tw = some (μ, u)) : μ = .own ∨ μ = .pub := by
  rcases hrmw with ⟨acq, rel, e, v, x, ok, fail, ht⟩ | ⟨x, o, acq, rel, v, e, ht⟩ <;> rw [ht] at hsc
  · rcases hsc with hs | hs
    · simp only [StepScope] at hs
      rcases hs tw hpk with ⟨μ', r, P, htw, hμ⟩ | ⟨u', htw, -⟩
      · rcases cellOf_cases hc with rfl | rfl <;> rcases htw with h | h <;> cases h <;> exact hμ
      · rcases cellOf_cases hc with rfl | rfl <;> rcases htw with h | h <;> cases h <;> exact .inr rfl
    · simp [StepScopeR] at hs
  · rcases hsc with hs | hs
    · simp only [StepScope, OpScope] at hs
      obtain ⟨μ', u', htw, hμ⟩ := hs tw hpk
      rcases cellOf_cases hc with rfl | rfl <;> rcases htw with h | h <;> cases h <;> exact hμ
    · simp [StepScopeR, OpScopeR] at hs

/-- The reference of the current `cas`/`fetch` is determined by the term. -/
theorem rmw_ref {th : TTh} {w w' : At}
    (h : (∃ acq rel e v x ok fail, th.term = .cas acq rel w e v x ok fail) ∨
      (∃ x o acq rel v e, th.term = .let_ x (.fetch o acq rel w v) e))
    (h' : (∃ acq rel e v x ok fail, th.term = .cas acq rel w' e v x ok fail) ∨
      (∃ x o acq rel v e, th.term = .let_ x (.fetch o acq rel w' v) e)) : w' = w := by
  rcases h with ⟨_, _, _, _, _, _, _, ht⟩ | ⟨_, _, _, _, _, _, ht⟩ <;>
    rcases h' with ⟨_, _, _, _, _, _, _, ht'⟩ | ⟨_, _, _, _, _, _, ht'⟩ <;>
    rw [ht] at ht' <;> cases ht' <;> rfl

/-- **(N2) `NoPlantRMW` from the scope and memory's invariant**: a `pub` reference at an
own label with `rini < ini` has a frontier (`OwnHidP`), so not at a private cell. -/
theorem noPlantRMW_core {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) : NoPlantRMW (CE η) th := by
  intro w rt pw ad hcase hea had hown hpf
  refine rmwS_core hT hi hE htv hm ?_ w rt pw ad hcase hea had hown
  intro w' rt' pw' ad' tw μ u hcase' hpk hc hne hor hea' had' hown'
  obtain rfl := rmw_ref hcase hcase'
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨-, rfl⟩ := hea'
  rw [had] at had'
  obtain rfl := Option.some.inj had'
  rcases rmw_mode hsc hcase' hpk hc with rfl | rfl
  · exact absurd rfl hne
  · rcases hor with h' | h'
    · exact absurd rfl h'
    · exfalso
      obtain ⟨c, hsto, how⟩ := hown
      have hlt : (CE η).rc ad.label < (CE η).ini ad.label := by
        simp only [TermSound.TEnv.rc]
        omega
      obtain ⟨f, hf, -⟩ := hm.2.2.2.2.2.1.2 ad.label c hsto how hlt
      rw [hpf] at hf; cases hf

/-- `NoPlantRMW` reads only `sto`, `tid`, `ini`, `rini` and `pfr`. -/
theorem noPlantRMW_congr {E E' : TEnv} {th : TTh} (hs : E'.sto = E.sto) (ht : E'.tid = E.tid)
    (hi : E'.ini = E.ini) (hr : E'.rini = E.rini) (hp : E'.pfr = E.pfr) (h : NoPlantRMW E th) :
    NoPlantRMW E' th := by
  unfold NoPlantRMW OwnL IniWr TermSound.TEnv.rc at *
  rw [hs, ht, hi, hr, hp]
  exact h

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **T8 `rmw`** from the stepper's scope: at the stepper's cut in `SysInvN` (stage A, the
PRE-step `MemInv`), transferred to the step's cut. -/
theorem rmw_of
    (hsc : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StepScope cx th.term ∨ StepScopeR th.σs cx th.term) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      NoPlantRMW (CE η) th := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, hE2, hT2, htv2, hi2, hsum2, -⟩ := hRE0
  have Y2 : EnvAt p Eg i th (Tot i) S0 ρ2 η2 cx2 Rf2 Rs2 :=
    ⟨hce2, congrArg (fun E => E.tid) hce2, hE2, hT2, htv2, hi2, hsum2⟩
  have h2 := noPlantRMW_core (hsc X Y2) hT2.1 hi2 hE2 htv2 (by rw [hce2]; exact hm0)
  refine noPlantRMW_congr ?_ ?_ ?_ ?_ ?_ h2 <;> rw [Y.1, hce2] <;> rfl

end

end TermRmw

#print axioms TermRmw.rmw_mode
#print axioms TermRmw.rmw_ref
#print axioms TermRmw.noPlantRMW_core
#print axioms TermRmw.noPlantRMW_congr
#print axioms TermRmw.rmw_of
