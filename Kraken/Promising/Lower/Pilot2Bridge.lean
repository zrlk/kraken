/-
**The value-restricted `EnvGCAdj` and the
open bridge `EnvGValsBridge`.** AArch64.

## Why

`pop` loads the link of the node it read from `top` (`ldr x4, [x2, #8]`), and
`main` the payload of the node `pop` returned (`ldr w11, [x10]`). With a
non-empty `dmem` (the private stack), such a load is shared only if its address is
off `dmem`; the private-stack layer's `HeapOff H dmem` gives that for addresses in the heap `H`,
and `PtrsInHeap` says a pointer read from a pointer cell names a heap node. In
the value environment `SharedEnv.inv S G` the load answer carries `G`, so
`PtrsInHeap` applies (`DStack.Treiber2A64.treiber2DWorker_val_heapOff`). In the
ownership environment of the Theorem 1′ chain, `EnvGCAdj`, it does not: the
`ldar` of `top` yields only `Treiber2.Pl` (the value was read from `top`), and
`top`'s release predicate (`Treiber2.predA`) constrains no pop-form value
(`EnvG/Treiber2Ghost.lean`, "Why not a history predicate with pop values").

## What

- `valsEnv E G`: `E` whose load answers at a location `l` satisfy `G l`
  (`ok` unchanged). Reducible, so `E`'s `@[simp]` lemmas apply (with
  `LoadVal`'s equations); the `FenceMono` instance is `E`'s. `Effects.AllEnv.vals`/`Safely.vals`: a judgment of `E`
  is one of `valsEnv E G` (fewer answers).
- `EnvGCAdjV A tid pl G := valsEnv (EnvGCAdjA A tid pl) G`, `QA64CAdjV`.
- **`EnvGValsBridge G`**: the missing link, stated at the whole-program level,
  and its instance `envGValsBridge_true` at `G = ⊤` (the existing chain).
-/
import Kraken.Promising.SLR.EnvG.AdjSpikeA64
import Kraken.Promising.SLR.EnvG.A64RmwFailFinal
import Kraken.Promising.InvLink
import Kraken.Promising.SLR.EnvG.AdjVCGenCommon

namespace Kraken.Promising.Lower.Pilot2

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64
open Kraken.Promising.AArch64.EnvG

/-! ## The value-restricted environment -/

/-- The value condition of an access's answer: a load's value satisfies `G`
at its location; other answers are unconstrained. -/
@[simp] def LoadVal (G : Loc → Val → Prop) : (a : SharedAccess) → a.Ret → Prop
  | .load _ _ addr n, v => G ⟨addr, n⟩ v
  | _, _ => True

/-- **`E` with value-restricted load answers**: the same permissions, and only
the outcomes whose load values satisfy `G`. Reducible, so that `E`'s
`@[simp]` lemmas (typed at `E.State`) apply to its states. -/
@[reducible] def valsEnv (E : SharedEnv) (G : Loc → Val → Prop) : SharedEnv where
  State := E.State
  ok := E.ok
  step a σ r σ' := E.step a σ r σ' ∧ LoadVal G a r

/-- Fences are `E`'s. -/
instance (E : SharedEnv) [E.FenceMono] (G : Loc → Val → Prop) : (valsEnv E G).FenceMono where
  le := SharedEnv.FenceMono.le (env := E)
  refl := SharedEnv.FenceMono.refl (env := E)
  fenceInv σ k g hg :=
    ⟨(SharedEnv.FenceMono.fenceInv (env := E) σ k g hg).1,
      fun g' hs => (SharedEnv.FenceMono.fenceInv (env := E) σ k g hg).2 g' hs.1⟩

@[simp] theorem fenceMono_le_valsEnv (E : SharedEnv) [E.FenceMono] (G : Loc → Val → Prop) :
    (SharedEnv.FenceMono.le (env := valsEnv E G)) = SharedEnv.FenceMono.le (env := E) := rfl

/-- **A judgment of `E` is one of `valsEnv E G`**: same permissions, fewer
outcomes. -/
theorem Effects.AllEnv.vals {E : SharedEnv} {G : Loc → Val → Prop} {post : MachineState → E.State → Prop}
    (ef : Effects) : ∀ g, ef.AllEnv E g post → ef.AllEnv (valsEnv E G) g post := by
  induction ef with
  | done a => exact fun g h => h
  | unimplemented => exact fun _ h => h
  | syscall => exact fun _ h => h
  | unaligned_sp => exact fun _ h => h
  | nonmem_load dmem addr w ret ih => exact fun g h => ⟨h.1, fun v g' h' => ih _ _ g' (h.2 v g' h'.1)⟩
  | nonmem_store dmem addr v ret ih => exact fun g h => ⟨h.1, fun b g' h' => ih _ g' (h.2 b g' h'.1)⟩
  | undefined ret ih => exact fun g h v => ih v g (h v)
  | require_read_access _ _ ok ih => exact fun g h => ih () g h
  | require_write_access _ _ ok ih => exact fun g h => ih () g h
  | require_exec_access _ ok ih => exact fun g h => ih () g h
  | sync_load k xcl dmem addr w ret ih => exact fun g h => ⟨h.1, fun v g' h' => ih _ _ g' (h.2 v g' h'.1)⟩
  | sync_store k xcl dmem addr v ret ih => exact fun g h => ⟨h.1, fun b g' h' => ih _ _ g' (h.2 b g' h'.1)⟩
  | rmw k nr dmem addr w op ret ih => exact fun g h => ⟨h.1, fun v g' h' => ih _ _ g' (h.2 v g' h'.1)⟩
  | fence k ok ih => exact fun g h => ⟨h.1, fun g' h' => ih () g' (h.2 g' h'.1)⟩
  | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih =>
    intro g h succ rev
    have h' := h succ rev
    cases rev with
    | true =>
      exact ⟨h'.1, fun v₂ g₁ h₁ => ⟨(h'.2 v₂ g₁ h₁.1).1,
        fun v₁ g₂ h₂ he => ih _ _ _ g₂ ((h'.2 v₂ g₁ h₁.1).2 v₁ g₂ h₂.1 he)⟩⟩
    | false =>
      exact ⟨h'.1, fun v₁ g₁ h₁ => ⟨(h'.2 v₁ g₁ h₁.1).1,
        fun v₂ g₂ h₂ he => ih _ _ _ g₂ ((h'.2 v₁ g₁ h₁.1).2 v₂ g₂ h₂.1 he)⟩⟩
  | sync_load_pair => exact fun _ h => h
  | sync_store_pair => exact fun _ h => h

/-- **`Safely` of `E` is `Safely` of `valsEnv E G`.** -/
theorem Safely.vals {E : SharedEnv} {G : Loc → Val → Prop} {e : Kraken.Executable Directive}
    {post : MachineState × E.State → Prop} {x : MachineState × E.State}
    (h : Safely (e.instrStepEnv E) post x) : Safely (e.instrStepEnv (valsEnv E G)) post x := by
  obtain ⟨Inv, hx, hInv⟩ := h
  refine ⟨Inv, hx, fun y hy => (hInv y hy).imp id fun ⟨R, hT, hR⟩ => ⟨R, ?_, hR⟩⟩
  obtain ⟨d, z, rest, hcode, hstep⟩ := hT
  exact ⟨d, z, rest, hcode, hstep.imp (Effects.AllEnv.vals _ _) (Effects.AllEnv.vals _ _)⟩

/-- `EnvGCAdj` (AArch64) with value-restricted load answers. -/
abbrev EnvGCAdjV (A : Arch) (tid : Nat) (pl : Plan) (G : Loc → Val → Prop) : SharedEnv :=
  valsEnv (EnvGCAdjA A tid pl) G

/-- `QA64CAdj` with the `Safely` judgment of `EnvGCAdjV`. -/
def QA64CAdjV (A : Arch) (tid : Nat) (pl : Plan) (G : Loc → Val → Prop) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGCAdjV A tid pl G)) post (st.st, σ)

/-! ## The open bridge -/

/-- **The EnvG ↔ value-invariant bridge (open; not provable in EnvG as it
stands).** `final_of_relPureSafelyF` (`EnvG/A64RmwFailFinal.lean`) with the
per-thread `NPSafeF` premise, which `pilot_npSafeF` gets from
`ThreadRuleRXF.ofSafelyEnvGFCAdj`, replaced by

- `hvals`: every configuration reachable from the start keeps the value
  invariant `MemInv G` (a Promising-level fact: `InvLinkAArch64.inv_reachable`
  proves it from value specifications in `SharedEnv.inv S G`), and
- per thread, `ofSafelyEnvGFCAdj`'s premises with the `Safely` judgment in
  `EnvGCAdjV A tid pl G`: the thread may assume its loads at `G`-locations
  return `G`-values.

**Why it is stated for the whole program.** The thread-level form
"`Safely` in `EnvGCAdjV` gives `NPSafeF`" is false in general: `NPSafeF`
quantifies over every environment extension `EnvExt tid c c₁` consistent with
the erasure, and such a `c₁` may hold any value the plan's release predicates
allow (for `treiber2`, `predA`'s pop form allows any value of `top`), so a load
answer outside `G` is possible there. Theorem 1′'s thread rules carry no global
value invariant and no guarantee about other threads' written values, so EnvG
cannot prove the bridge as it stands. Along an actual execution from the
start, every configuration is reachable, so `hvals` restricts the real load
answers to `G`.

**Why it is believed true** (sketch): (1) relativise `NPSafeF` and
`theorem1FChain` to configurations satisfying `Ψ c := MemInv G c.mem`
(`EnvExt tid c c₁ ∧ Ψ c₁`); the adequacy proof instantiates `EnvExt` only along
the virtual execution (reachable, so `Ψ` by `hvals`) and along certification
runs (which keep `MemInv G` exactly as in `InvLink.configInv_reachable`'s
`CertWrite` case); (2) relativise `linkHypsFCAdj_QA64CAdj`: at a `Ψ`
configuration, the link's environment answer to a load is the value of a
message of `c.mem` (or the initial value), which satisfies `G`, so the
`EnvGCAdj` outcome the link builds is an `EnvGCAdjV` outcome. At `G = ⊤` the
statement is the existing chain (`envGValsBridge_true`). -/
def EnvGValsBridge (G : Loc → Val → Prop) : Prop :=
  ∀ (A : Arch) (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val)) (rF : Nat → Res) (g₀ : Ghost)
    (B : Config isa → Res → Ghost → Prop) (Φ : Config isa → Prop) (pl : Nat → Plan)
    (e : Nat → Kraken.Executable Directive) (endPc : Nat → Int64) (post : Nat → MachineState × EStateA → Prop),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g₀ (fun _ => False) (Config.init states initMem) → g₀.pend = [] →
    ∀ (sp : Nat → RelPureSpec A g₀.rel), (∀ tid s, states[tid]? = some s → (sp tid).Holds s) →
    -- the value invariant of every reachable memory
    (∀ c, Reachable A fuel (Config.init states initMem) c → MemInv G c.mem) →
    -- per thread: `ofSafelyEnvGFCAdj`'s premises, the judgment in `EnvGCAdjV`
    (∀ tid, tid < states.length →
      Kraken.Executable.ValidLayout (e tid) ∧ (pl tid).Valid ∧ (e tid).rmwLive = true ∧ Phase1TreeF (e tid) ∧
      (∀ y, post tid y → y.1.2 = endPc tid) ∧
      (∀ x R, x.1.2 = endPc tid → ¬ (e tid).instrStepEnv (EnvGCAdjV A tid (pl tid) G) x R) ∧
      (∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post tid (t.st.st, σ) → t.prom = [] →
        EnvRel tid (pl tid) σ c t r g cl → cl → B c r g) ∧
      ∃ s, states[tid]? = some s ∧
        QA64CAdjV A tid (pl tid) G (e tid) (endPc tid) (post tid) s (σInit (Config.init states initMem) (rF tid) g₀)) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.final = true →
    (∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) →
    Φ c

/-- `valsEnv E ⊤` has `E`'s outcomes. -/
theorem Safely.of_vals_top {E : SharedEnv} {e : Kraken.Executable Directive}
    {post : MachineState × E.State → Prop} {x : MachineState × E.State}
    (h : Safely (e.instrStepEnv (valsEnv E fun _ _ => True)) post x) : Safely (e.instrStepEnv E) post x := by
  have hE : ∀ ef : Effects, ∀ g (P : MachineState → E.State → Prop),
      ef.AllEnv (valsEnv E fun _ _ => True) g P → ef.AllEnv E g P := by
    intro ef
    have hs : ∀ {a : SharedAccess} {g : E.State} {r : a.Ret} {g' : E.State}, E.step a g r g' →
        (valsEnv E fun _ _ => True).step a g r g' := fun {a} _ _ _ h => ⟨h, by cases a <;> trivial⟩
    induction ef with
    | done a => exact fun g _ h => h
    | unimplemented => exact fun _ _ h => h
    | syscall => exact fun _ _ h => h
    | unaligned_sp => exact fun _ _ h => h
    | nonmem_load dmem addr w ret ih => exact fun g _ h => ⟨h.1, fun v g' h' => ih _ _ g' _ (h.2 v g' (hs h'))⟩
    | nonmem_store dmem addr v ret ih => exact fun g _ h => ⟨h.1, fun b g' h' => ih _ g' _ (h.2 b g' (hs h'))⟩
    | undefined ret ih => exact fun g _ h v => ih v g _ (h v)
    | require_read_access _ _ ok ih => exact fun g _ h => ih () g _ h
    | require_write_access _ _ ok ih => exact fun g _ h => ih () g _ h
    | require_exec_access _ ok ih => exact fun g _ h => ih () g _ h
    | sync_load k xcl dmem addr w ret ih => exact fun g _ h => ⟨h.1, fun v g' h' => ih _ _ g' _ (h.2 v g' (hs h'))⟩
    | sync_store k xcl dmem addr v ret ih =>
      exact fun g _ h => ⟨h.1, fun b g' h' => ih _ _ g' _ (h.2 b g' (hs h'))⟩
    | rmw k nr dmem addr w op ret ih => exact fun g _ h => ⟨h.1, fun v g' h' => ih _ _ g' _ (h.2 v g' (hs h'))⟩
    | fence k ok ih => exact fun g _ h => ⟨h.1, fun g' h' => ih () g' _ (h.2 g' (hs h'))⟩
    | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih =>
      intro g _ h succ rev
      have h' := h succ rev
      cases rev with
      | true =>
        exact ⟨h'.1, fun v₂ g₁ h₁ => ⟨(h'.2 v₂ g₁ (hs h₁)).1,
          fun v₁ g₂ h₂ he => ih _ _ _ g₂ _ ((h'.2 v₂ g₁ (hs h₁)).2 v₁ g₂ (hs h₂) he)⟩⟩
      | false =>
        exact ⟨h'.1, fun v₁ g₁ h₁ => ⟨(h'.2 v₁ g₁ (hs h₁)).1,
          fun v₂ g₂ h₂ he => ih _ _ _ g₂ _ ((h'.2 v₁ g₁ (hs h₁)).2 v₂ g₂ (hs h₂) he)⟩⟩
    | sync_load_pair => exact fun _ _ h => h
    | sync_store_pair => exact fun _ _ h => h
  obtain ⟨Inv, hx, hInv⟩ := h
  refine ⟨Inv, hx, fun y hy => (hInv y hy).imp id fun ⟨R, hT, hR⟩ => ⟨R, ?_, hR⟩⟩
  obtain ⟨d, z, rest, hcode, hstep⟩ := hT
  exact ⟨d, z, rest, hcode, hstep.imp (hE _ _ _) (hE _ _ _)⟩

/-- **Shape check: at `G = ⊤` the bridge holds**; it is
`final_of_relPureSafelyF` with `npSafeF_of_safelyEnvGFCAdj` (`hvals` is
trivial and `EnvGCAdjV … ⊤` has `EnvGCAdj`'s outcomes). This checks only that
the statement is well-formed and consistent with the existing chain; the
instance the stack-frame pilot uses is `G = treiber2GA` (the Treiber values), whose truth is
the open question. -/
theorem envGValsBridge_true : EnvGValsBridge fun _ _ => True := by
  intro A fuel states initMem rF g₀ B Φ pl e endPc post hH hE hpend sp h0 _ hthr c hc hf hfin
  refine final_of_relPureSafelyF A fuel (B := B) hH hE (by simp [hpend]) sp h0 ?_ hc hf hfin
  intro tid htid n m
  obtain ⟨hv, hpl, hlive, hshape, hpost, hstuck, hB, s, hs, he, hds, hend, hsafe⟩ := hthr tid htid
  exact NPSafeF.of_ruleRXF (ThreadRuleRXF.ofSafelyEnvGFCAdj (e := e tid) (post := post tid) hpl hlive hshape hpost
      (fun x R hx hR => hstuck x R hx (by
        obtain ⟨d, z, rest, hcode, hstep⟩ := hR
        exact ⟨d, z, rest, hcode, hstep.imp (Effects.AllEnv.vals _ _) (Effects.AllEnv.vals _ _)⟩)) hB) n m _ _ _ _
    (invGFCAdj_init hs hpend ⟨he, hds, hend, Safely.of_vals_top hsafe⟩)

end Kraken.Promising.Lower.Pilot2
