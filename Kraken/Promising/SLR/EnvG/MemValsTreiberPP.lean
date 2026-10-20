/-
**`treiber_pp.kl` never faults at the runner's declarations**: `x64_treiber_pp_envG_runner_faultFree` and its concrete
instance `x64_treiber_pp_envG_runner_faultFree_concrete`, program-level
`Config.FaultFree` from the runner's start states under any architecture
(promises included).

The popper reads `8(%rax)` and `(%rax)` at an address it loaded from `top`;
its purity specification sits at `sAll`, which the runner's declarations do
not agree on. Here both threads get **value specifications**
(`MemValsX64.ValSpecX`) at the pusher's layout `pushS top n1` (`top`, `n1`'s
data word and `n1`'s `next` word), with the value invariant

- `L` (`TreiberValL`): the words `top` and `n1 + 8`;
- `V` (`TreiberValV n1`): `0` or `n1`.

The pusher writes `n1` to `top` and the `top` it read to `n1 + 8`; the
popper writes the `next` it read to `top`; so `MemVals L V` holds at every
reachable configuration, and a non-zero `top` the popper reads is `n1`, so
its loads are at `n1 + 8` and `n1`, inside `pushS`
(`pusherV_memVals`, `popperV_memVals`: the `*V_noNT` scripts in
`(valEnv L V).within (pushS top n1)`). The initial memory must give `top`
and `n1 + 8` the value `0`; at the runner's `treiberInitMemV` this is
`decide`.

Phase-1 limit: single-access trees (`treiberImageV_phase1FX`).
-/
import Kraken.Promising.SLR.EnvG.MemValsX64
import Kraken.Promising.SLR.EnvG.X64TreiberAbsRunner

namespace Kraken.Promising.X64.EnvG.TreiberAbs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.TreiberCommon
open Kraken.Promising.X64.EnvG.TreiberX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The value invariant -/

/-- The locations of the value invariant: `top` and `n1`'s `next` word. -/
def TreiberValL (t n : BitVec 64) : Loc → Prop := fun l => l = ⟨t, 8⟩ ∨ l = ⟨n + 8, 8⟩

/-- The values of the value invariant: the empty stack `0` or the node `n`. -/
def TreiberValV (n : BitVec 64) : Val → Prop := fun v => v.setWidth 64 = 0 ∨ v.setWidth 64 = n

/-- The threads' environment: the value environment at the pusher's layout. -/
abbrev treiberValEnv (t n : BitVec 64) : SharedEnv :=
  (SharedEnv.valEnv (TreiberValL t n) (TreiberValV n)).within (pushS t n)

/-- A load of an `L`-word that is not in the private memory returns a
`V`-value, and ticks the counter. -/
theorem treiberVal_load8 {t n : BitVec 64} {d : DataMem} {σ : BitVec 64} {g g' : (SharedEnv.counted (treiberValEnv t n)).State}
    {a : BitVec 64} (ha : a = t ∨ a = n + 8) (hd : Mem.loadInt d a 8 = none)
    (h : (∃ v, Mem.loadInt d a 8 = some v ∧ σ = BitVec.ofInt 64 v ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ ∃ v, (SharedEnv.counted (treiberValEnv t n)).step (.load .plain false a 8) g v g' ∧
        σ = v.setWidth 64)) :
    (σ = 0 ∨ σ = n) ∧ g.2 < g'.2 := by
  rcases h with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
  · rw [hd] at hm; cases hm
  · refine ⟨hst.1 (by rcases ha with rfl | rfl <;> simp [TreiberValL]), ?_⟩
    have h1 := hst.2
    simp only [SharedAccess.tick] at h1
    omega

/-- A load not in the private memory ticks the counter. -/
theorem treiberVal_loadTick {E : SharedEnv} {d : DataMem} {σ : BitVec 64} {g g' : (SharedEnv.counted E).State}
    {a : BitVec 64} {w : Nat} (hd : Mem.loadInt d a w = none)
    (h : (∃ v, Mem.loadInt d a w = some v ∧ σ = BitVec.ofInt 64 v ∧ g' = g) ∨
      (Mem.loadInt d a w = none ∧ ∃ v, (SharedEnv.counted E).step (.load .plain false a w) g v g' ∧
        σ = v.setWidth 64)) : g.2 < g'.2 := by
  rcases h with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
  · rw [hd] at hm; cases hm
  · have h1 := hst.2
    simp only [SharedAccess.tick] at h1
    omega

/-- The `lock cmpxchgq` with a `V` new value keeps `V`. -/
theorem treiberVal_cmpx {n x y : BitVec 64} (hy : y = 0 ∨ y = n) :
    ∀ old new, cmpxOp64 x y old = some new → TreiberValV n new := by
  intro old new h
  simp only [cmpxOp64, rmwOp128, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  split at ha
  · cases ha
    rcases hy with rfl | rfl <;> simp [TreiberValV]
  · cases ha

/-! ## The threads -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageV)]

local instance treiberImageV.envMemVals : CodeEnv := ⟨layout treiberImageV⟩

/-- **The verbatim popper in the value environment** (counted, partial): its
loads at `8(%rax)` and `(%rax)` are at `n + 8` and `n` (a non-zero `top`
read is `n`), and its `lock cmpxchgq` writes the `next` it read. -/
theorem popperV_memVals (t n : BitVec 64) :
    ∀ s g, QFrameX t s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (treiberValEnv t n)))
        (fun x => (x.1.2 = labT "qdone" ∧ True) ∨ False) ((s, labT "popper"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (treiberValEnv t n)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted (treiberValEnv t n)).State) =>
      QFrameX t s) ?_ rfl (by decide) popperFragV_placedIn popperFragV_last s g hs
  cfg_cases_env [treiberPopperX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64] at hx0
  case vc1 => simp [hx0]; trivial
  case vc2 =>
    rename_i σ v σ1 hld af hz _
    have hl := treiberVal_load8 (Or.inl (by simp [hx0])) (by simpa [hx0] using hd8 _) hld
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have := hl.2
    omega
  case vc3 =>
    rename_i σ v σ1 hld af hz hnz _
    have hl := treiberVal_load8 (Or.inl (by simp [hx0])) (by simpa [hx0] using hd8 _) hld
    simp at hz ⊢
    exact ⟨trivial, Or.inr (hl.1.resolve_left hz)⟩
  case vc4 => simp [hd8]
  case vc5 =>
    rename_i σ v σ1 hld af hz v4 σ4 hld2 _
    have hl := treiberVal_load8 (Or.inl (by simp [hx0])) (by simpa [hx0] using hd8 _) hld
    simp at hz
    obtain rfl := hl.1.resolve_left hz
    have hl2 := treiberVal_load8 (Or.inr (by simp)) (by simpa using hd8 _) hld2
    simp [hx0]
    show ∀ old new, _ → _ → _ → _
    intro old new h _ _
    simp only [rmwOp128, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    split at ha
    · cases ha
      rcases hl2.1 with rfl | rfl <;> simp [TreiberValV]
    · cases ha
  case vc6 =>
    rename_i σ v σ1 hld af hz v4 σ4 hld2 old σ5 hcas heq hz2 _
    have h1 := treiberVal_loadTick (by simpa [hx0] using hd8 _) hld
    have h2 := treiberVal_loadTick (by simpa using hd8 _) hld2
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    omega
  case vc7 =>
    rename_i σ v σ1 hld af hz v4 σ4 hld2 old σ5 hcas heq hz2 hx _
    have hl := treiberVal_load8 (Or.inl (by simp [hx0])) (by simpa [hx0] using hd8 _) hld
    simp at hz
    obtain rfl := hl.1.resolve_left hz
    simp
    trivial
  case vc8 => exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl (by decide)⟩
  case vc9 =>
    rename_i σ v σ1 hld af hz v4 σ4 hld2 old σ5 hcas heq hz2 _
    have h1 := treiberVal_loadTick (by simpa [hx0] using hd8 _) hld
    have h2 := treiberVal_loadTick (by simpa using hd8 _) hld2
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    omega
  case vc10 =>
    rename_i σ v σ1 hld af hz v4 σ4 hld2 old σ5 hcas heq hz2 hx _
    have hl := treiberVal_load8 (Or.inl (by simp [hx0])) (by simpa [hx0] using hd8 _) hld
    simp at hz
    obtain rfl := hl.1.resolve_left hz
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    exact absurd (by bv_omega) heq
  case vc11 => exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl (by decide)⟩

/-- **The verbatim pusher in the value environment** (counted, partial): it
writes the `top` it read to `n + 8` and `n` to `top`. -/
theorem pusherV_memVals (t n : BitVec 64) :
    ∀ s g, PFrameX t n s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (treiberValEnv t n)))
        (fun x => (x.1.2 = labT "pdone" ∧ True) ∨ False) ((s, labT "pusher"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (treiberValEnv t n)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted (treiberValEnv t n)).State) =>
      PFrameX t n s) ?_ rfl (by decide) pusherFragV_placedIn pusherFragV_last s g hs
  cfg_cases_env [treiberPusherX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdt, hdd, hdn⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64] at hx0 hx1
  all_goals have hdn' : Mem.loadInt _ (n + 8#64) 8 = none := hdn
  -- cut `pusher`
  case vc1 => simp [hx1, hdd]
  case vc2 =>
    simp only [SharedEnv.counted_ok]
    simp [hx1]
    show _ → _
    intro h
    simp [TreiberValL] at h
  case vc3 => exact ⟨by simp [hx0], by simp [hx1], hdt, hdd, hdn⟩
  -- cut `push`
  case vc1 =>
    simp only [SharedEnv.counted_ok]
    simp [hx0]
    trivial
  case vc2 =>
    rename_i v σ1 hld _ _
    have hl := treiberVal_load8 (Or.inl (by simp [hx0])) (by simpa [hx0] using hdt) hld
    simp only [SharedEnv.counted_ok]
    simp [hx1]
    show _ → _
    intro _
    simpa [TreiberValV] using hl.1
  case vc3 =>
    rename_i v σ1 hld dm σ2 hst _
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -⟩ := hst
    subst hdm
    simp [hx0, hdt]
  case vc4 =>
    rename_i v σ1 hld dm σ2 hst _
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -⟩ := hst
    subst hdm
    simp only [SharedEnv.counted_ok]
    simp [hx0]
    show ∀ old new, _ → _ → _ → _
    intro old new h _ _
    simp only [rmwOp128, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    split at ha
    · cases ha
      simp [TreiberValV, hx1]
    · cases ha
  case vc5 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by rw [heq]; exact BitVec.sub_self _) hz
  case vc6 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hdt, by simpa using hdd, by simpa using hdn⟩, .inl (by decide)⟩
  case vc7 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hdt, by simpa using hdd, by simpa using hdn⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    omega
  case vc8 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by bv_omega) heq



/-! ## The specifications -/

/-- The verbatim threads' value specifications at `pushS top n1`. -/
noncomputable def treiberValSpec :
    Nat → ValSpecX (TreiberValL (symT "top") (symT "n1")) (TreiberValV (symT "n1"))
  | 0 =>
    { S := pushS (symT "top") (symT "n1")
      le16 := pushS_le16 _ _
      e := layout treiberImageV
      valid := inferInstance
      endPc := labT "pdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labT "pdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }
  | _ + 1 =>
    { S := pushS (symT "top") (symT "n1")
      le16 := pushS_le16 _ _
      e := layout treiberImageV
      valid := inferInstance
      endPc := labT "qdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labT "qdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

set_option maxRecDepth 8000 in
/-- **The value specifications hold at the start states with declarations.** -/
theorem treiberValSpec_initD {ds : Decls} {sP sQ : State} (hP : StartPushVD ds sP) (hQ : StartPopVD ds sQ) :
    ∀ tid s, [sP, sQ][tid]? = some s → (treiberValSpec tid).HoldsD ds s
  | 0, s, hs => by
    cases hs
    refine ⟨hP.exe, hP.endPc, hP.decls, hP.split, ?_⟩
    rw [show sP.st = (sP.st.1, labT "pusher") from Prod.ext rfl hP.pc]
    exact Safely.uncountT (pusherV_memVals _ _ sP.st.1 ((), 0) hP.frame)
  | 1, s, hs => by
    cases hs
    refine ⟨hQ.exe, hQ.endPc, hQ.decls, fun k _ => hQ.dmem k, ?_⟩
    rw [show sQ.st = (sQ.st.1, labT "popper") from Prod.ext rfl hQ.pc]
    exact Safely.uncountT (popperV_memVals _ _ sQ.st.1 ((), 0) hQ.frame)

omit [Executable.ValidLayout (layout treiberImageV)] in
/-- The initial memory of `Config.init` satisfies the value invariant when
`top` and `n + 8` start at `0` (no messages yet). -/
theorem memVals_treiber_init {t n : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hT0 : (Config.init states initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init states initMem).mem.initVal ⟨n + 8, 8⟩ = 0) :
    MemVals (TreiberValL t n) (TreiberValV n) (Config.init states initMem).mem := by
  refine ⟨fun l hl => ?_, fun ts w h _ => ?_⟩
  · rcases hl with rfl | rfl
    · simp only [TreiberValV, hT0]; simp
    · simp only [TreiberValV, hN0]; simp
  · simp [Memory.get?] at h

/-- **No reachable configuration of the verbatim `treiber_pp` threads with
the runner's declarations has a faulting step**, for `ds` agreeing on
`pushS top n1` and an initial memory with `top` and `n1 + 8` at `0`. -/
theorem x64_treiber_pp_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn (pushS (symT "top") (symT "n1"))) {sP sQ : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPushVD ds sP) (hQ : StartPopVD ds sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "top", 8⟩ = 0)
    (hN0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "n1" + 8, 8⟩ = 0) :
    Config.FaultFree A fuel (Config.init [sP, sQ] initMem) :=
  x64_faultFree_of_valSpecs treiberValSpec (fun _ => ds) (fun _ => hsz)
    (fun tid => by rcases tid with _ | _ <;> exact hag)
    (fun tid => by rcases tid with _ | _ <;> exact treiberImageV_noFaultCode)
    (fun tid => by rcases tid with _ | _ <;> exact rootOnlyD_of_phase1TreeFX treiberImageV_phase1FX)
    (memVals_treiber_init hT0 hN0) (init_threads_of (treiberValSpec_initD hP hQ))

end Kraken.Promising.X64.EnvG.TreiberAbs

namespace Kraken.Promising.X64.EnvG.TreiberAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberAbs Kraken.Promising.SLR.EnvG

/-- **`treiber_pp.kl` never faults**, from the runner's exact configuration
(threads `treiberP0D`, `treiberP1D` with the runner's declarations, initial
memory `treiberInitMemV`). -/
theorem x64_treiber_pp_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [treiberP0D, treiberP1D] treiberInitMemV) :=
  x64_treiber_pp_envG_runner_faultFree (layout := treiberLayoutV) treiberDeclsD_sized
    (by rw [symT_top, symT_n1]; decls_agrees_on) treiberP0D_start treiberP1D_start
    (by rw [symT_top]; simp only [Config.init_mem]; decide)
    (by rw [symT_n1]; simp only [Config.init_mem]; decide)

end Kraken.Promising.X64.EnvG.TreiberAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.x64_treiber_pp_envG_runner_faultFree
#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.Concrete.x64_treiber_pp_envG_runner_faultFree_concrete
