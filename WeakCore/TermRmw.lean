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

/-- The target of a `cas`/`fetch` reference (a cell reference `ptr`/`loc` evaluating to an
address): unless the reference is `own`, the target's label has a frontier (`pfr = some`) —
`ModeOK`'s non-`own` clause, the same for `pub` and `rgn` (`VR` of the reference). -/
theorem rmw_mode {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {w : At} {tw u rt : Ty}
    {μ : Mode} {pw : Word} {ad : Address}
    (hv : VarsOK ρ η σs cx.vars env) (hpk : cx.peek w = .ok tw) (hc : cellOf tw = some (μ, u))
    (hea : evalAt env w = some (rt, [pw])) (had : addrOf pw = some ad) :
    μ = .own ∨ ∃ f, η.pfr ad.label = some f := by
  obtain ⟨rt', ws, hea', hvr, -⟩ := peek_VR hv hpk
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨-, rfl⟩ := hea'
  rcases mode_own_or μ with h | hμ
  · exact .inl h
  · refine .inr ?_
    have key : ∀ (a : Address) (c : Cell), [pw].map (·.val) = [.loc a 0] →
        ModeOK η.tid η.pfr η.seen μ a.label c [pw] → ∃ f, η.pfr ad.label = some f := by
      intro a c hws hmode
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
      have e : ad = a := by simp only [addrOf, hws, Option.some.injEq] at had; exact had.symm
      subst e
      rw [ModeOK_eq_pubG hμ] at hmode
      simp only [ModeOK] at hmode
      obtain ⟨f, hf, -⟩ := hmode
      exact ⟨f, hf⟩
    rcases cellOf_cases hc with rfl | rfl
    · simp only [VR] at hvr
      obtain ⟨a, c, hws, -, -, -, hmode, -⟩ := hvr
      exact key a c hws hmode
    · simp only [VR] at hvr
      rcases hvr with ⟨hws, -⟩ | ⟨a, c, U, hws, -, -, -, hmode, -⟩
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
        simp [addrOf, hws] at had
      · exact key a c hws hmode

/-- The reference of the current `cas`/`fetch` is determined by the term. -/
theorem rmw_ref {th : TTh} {w w' : At}
    (h : (∃ acq rel e v x ok fail, th.term = .cas acq rel w e v x ok fail) ∨
      (∃ x o acq rel v e, th.term = .let_ x (.fetch o acq rel w v) e))
    (h' : (∃ acq rel e v x ok fail, th.term = .cas acq rel w' e v x ok fail) ∨
      (∃ x o acq rel v e, th.term = .let_ x (.fetch o acq rel w' v) e)) : w' = w := by
  rcases h with ⟨_, _, _, _, _, _, _, ht⟩ | ⟨_, _, _, _, _, _, ht⟩ <;>
    rcases h' with ⟨_, _, _, _, _, _, _, ht'⟩ | ⟨_, _, _, _, _, _, ht'⟩ <;>
    rw [ht] at ht' <;> cases ht' <;> rfl

/-- **(N2) `NoPlantRMW` from typing and memory's invariant**: a non-`own` reference's target has
a frontier (`rmw_mode`), so it is not a private cell; an `own` one is `rmwS_core`'s. -/
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
  rcases rmw_mode hi.1.2.1 hpk hc hea had with rfl | ⟨f, hf⟩
  · exact absurd rfl hne
  · simp only [CE] at hpf
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
