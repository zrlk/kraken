import WeakCore.TermSpawnMid
import WeakCore.TermSpawnKidMem
/-!
# TermSpawnRunX — L7: the spawn arm of `sysInvO_step`/`sysInvO_run`

`SysInvO` (TermSpawnRun) is `SysInvN ∧ OwnLive ∧ ObsAll` at some witnesses.  Across a spawn
`c' = spawnT c i par kid` the witnesses are `EgK Eg c` and the zero-extended totals/credits; the
`SysInvN` part is the `sysInvN_spawn` (passed here as the hypothesis `hN'`, so this arm stays
sorry-free and independent of the statement's step-shape hypotheses), `OwnLive` and `ObsAll` are
proved here.  `sysInvO_runG` is the run induction over any step relation whose steps preserve
`SysInvO` given the run prefix (the `StepsX` form instantiates it with `StepX`).
-/
namespace TermSpawnRunX
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn TermSpawnMid
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **`OwnLive` after the spawn**: owners stay below the larger size. -/
theorem ownLive_spawnT {Eg : GEnv} {c : Cfg} {i : Nat} {par kid : TTh} (h : OwnLive Eg c) :
    OwnLive (EgK Eg c) (spawnT c i par kid) := by
  refine ⟨fun l cl j hs ho => ?_, fun l B hB => ?_⟩
  · rw [spawnT_size]; exact Nat.lt_succ_of_lt (h.1 l cl j hs ho)
  · rw [spawnT_size]; exact Nat.lt_succ_of_lt (h.2 l B hB)

/-- **`ObsAll` after the spawn** (memory kept, observers only shrink). -/
theorem obsAll_spawnT {Eg : GEnv} {c : Cfg} {i : Nat} {par kid : TTh} (h : ObsAll Eg c) :
    ObsAll (EgK Eg c) (spawnT c i par kid) :=
  TermSpawnKidMem.obsAll_kid _ h rfl rfl (by rw [spawnT_size]; exact Nat.le_succ _)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}

/-- **The spawn arm of `sysInvO_step`**: given the `SysInvN` transfer across the spawn at any
witnesses that carry `OwnLive`/`ObsAll` (the `sysInvN_spawn`), `SysInvO` is preserved. -/
theorem sysInvO_spawnT {c : Cfg} {i : Nat} {par kid : TTh}
    (h : TermSpawn.SysInvO p k arch Init MintOK c)
    (hN' : ∀ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init MintOK c Eg Tot HP HS cr db → OwnLive Eg c → ObsAll Eg c →
      SysInvN p k arch Init MintOK (spawnT c i par kid) (EgK Eg c) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS
        (extZT cr c.ths.size) (extZT db c.ths.size)) :
    TermSpawn.SysInvO p k arch Init MintOK (spawnT c i par kid) := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hOb⟩ := h
  exact ⟨EgK Eg c, extZ Tot c.ths.size, extZ HP c.ths.size, HS, extZT cr c.ths.size, extZT db c.ths.size,
    hN' Eg Tot HP HS cr db hN hOL hOb, ownLive_spawnT hOL, obsAll_spawnT hOb⟩

/-- Runs of a step relation (the shape of `StepsX`). -/
inductive RunsG (S : Cfg → Cfg → Prop) : Cfg → Cfg → Prop
  | refl (c : Cfg) : RunsG S c c
  | step {c c' c'' : Cfg} : S c c' → RunsG S c' c'' → RunsG S c c''

theorem RunsG.snoc {S : Cfg → Cfg → Prop} {c c' c'' : Cfg} (h : RunsG S c c') (h' : S c' c'') : RunsG S c c'' := by
  induction h with
  | refl c => exact .step h' (.refl _)
  | step hs _ ih => exact .step hs (ih h')

/-- **`sysInvO_run` over any step relation** (L7 run induction): preserved by each step given the
run prefix, `SysInvO` holds along every run from a `SysInvO` start. With `S := StepX`, the thread
and promise steps are `sysInvO_step` (prefix retyped to `StepsX`) and the spawn step is
`sysInvO_spawnT`. -/
theorem sysInvO_runG {S : Cfg → Cfg → Prop} {c0 : Cfg}
    (hS : ∀ {c c' : Cfg}, RunsG S c0 c → TermSpawn.SysInvO p k arch Init MintOK c → S c c' →
      TermSpawn.SysInvO p k arch Init MintOK c')
    (h0 : TermSpawn.SysInvO p k arch Init MintOK c0) {c : Cfg} (hr : RunsG S c0 c) :
    TermSpawn.SysInvO p k arch Init MintOK c := by
  have key : ∀ {c1 c2 : Cfg}, RunsG S c1 c2 → RunsG S c0 c1 →
      TermSpawn.SysInvO p k arch Init MintOK c1 → TermSpawn.SysInvO p k arch Init MintOK c2 := by
    intro c1 c2 h12
    induction h12 with
    | refl => exact fun _ h => h
    | step hs _ ih => exact fun hp h => ih (hp.snoc hs) (hS hp h hs)
  exact key hr (.refl _) h0

end

#print axioms TermSpawnRunX.RunsG.snoc
end TermSpawnRunX

#print axioms TermSpawnRunX.ownLive_spawnT
#print axioms TermSpawnRunX.obsAll_spawnT
#print axioms TermSpawnRunX.sysInvO_spawnT
#print axioms TermSpawnRunX.sysInvO_runG
