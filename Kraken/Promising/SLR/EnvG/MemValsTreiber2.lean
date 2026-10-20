/-
**`treiber2.kl` never faults at the runner's declarations**: `x64_treiber2_envG_runner_faultFree` and its concrete
instance `x64_treiber2_envG_runner_faultFree_concrete`, program-level
`Config.FaultFree` from the runner's start states under any architecture
(promises included).

The worker's `pop` reads `(%rax)` at an address it loaded from `top`; its
purity specification sits at `sAll`. Here both workers get one **value
specification** (`MemValsX64.ValSpecX`) at the declared layout
`[top, n1, n2]` (`treiber2S`), with the value invariant

- `L` (`Treiber2ValL`): the 8-byte words `top`, `n1`, `n2`;
- `V` (`Treiber2ValV n1 n2`): `0`, `n1` or `n2`.

`push` writes the `top` it read to its node (`%rbx`, `n1` or `n2`) and its
node to `top`; `pop` writes the `next` it read to `top`; so `MemVals L V`
holds at every reachable configuration, and a non-zero `top` read is a node,
so `pop`'s load is inside `treiber2S` (`workerV_memVals`: `workerV_noNT`'s
script in `(valEnv L V).within treiber2S`). The initial memory must give
`top`, `n1`, `n2` the value `0`; at the runner's `treiber2InitMemV` this is
`decide`.

Phase-1 limit: single-access trees (`treiber2ImageV_phase1FX`).
-/
import Kraken.Promising.SLR.EnvG.MemValsX64
import Kraken.Promising.SLR.EnvG.X64Treiber2Runner

namespace Kraken.Promising.X64.EnvG.Treiber2X

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The value invariant -/

/-- The locations of the value invariant: `top` and the nodes' `next` words. -/
def Treiber2ValL (t n1 n2 : BitVec 64) : Loc → Prop := fun l => l = ⟨t, 8⟩ ∨ l = ⟨n1, 8⟩ ∨ l = ⟨n2, 8⟩
/-- The values of the value invariant: the empty stack `0` or a node. -/
def Treiber2ValV (n1 n2 : BitVec 64) : Val → Prop := fun v =>
  v.setWidth 64 = 0 ∨ v.setWidth 64 = n1 ∨ v.setWidth 64 = n2
/-- The layout: `top`, `n1`, `n2`, 8-byte words (the runner's declarations). -/
abbrev treiber2S (t n1 n2 : BitVec 64) : SharedEnv.Layout := [(t, 8), (n1, 8), (n2, 8)]
/-- The workers' environment: the value environment at `treiber2S`. -/
abbrev treiber2ValEnv (t n1 n2 : BitVec 64) : SharedEnv :=
  (SharedEnv.valEnv (Treiber2ValL t n1 n2) (Treiber2ValV n1 n2)).within (treiber2S t n1 n2)

/-- A shared 8-byte load at an `L`-word returns a `V`-value and ticks. -/
theorem treiber2Val_load8 {t n1 n2 : BitVec 64} {d : DataMem} {σ : BitVec 64}
    {g g' : (SharedEnv.counted (treiber2ValEnv t n1 n2)).State} {a : BitVec 64} (ha : Treiber2ValL t n1 n2 ⟨a, 8⟩)
    (hd : Mem.loadInt d a 8 = none)
    (h : (∃ v, Mem.loadInt d a 8 = some v ∧ σ = BitVec.ofInt 64 v ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ ∃ v, (SharedEnv.counted (treiber2ValEnv t n1 n2)).step (.load .plain false a 8) g v g' ∧
        σ = v.setWidth 64)) :
    (σ = 0 ∨ σ = n1 ∨ σ = n2) ∧ g.2 < g'.2 := by
  rcases h with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
  · rw [hd] at hm; cases hm
  · refine ⟨hst.1 ha, ?_⟩
    have h1 := hst.2
    simp only [SharedAccess.tick] at h1
    omega

/-- A shared load ticks the counter. -/
theorem treiber2Val_loadTick {E : SharedEnv} {d : DataMem} {σ : BitVec 64} {g g' : (SharedEnv.counted E).State}
    {a : BitVec 64} (hd : Mem.loadInt d a 8 = none)
    (h : (∃ v, Mem.loadInt d a 8 = some v ∧ σ = BitVec.ofInt 64 v ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ ∃ v, (SharedEnv.counted E).step (.load .plain false a 8) g v g' ∧
        σ = v.setWidth 64)) : g.2 < g'.2 := by
  rcases h with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
  · rw [hd] at hm; cases hm
  · have h1 := hst.2
    simp only [SharedAccess.tick] at h1
    omega

/-! ## The worker -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2ImageV)]

local instance treiber2ImageV.envMemVals : CodeEnv := ⟨layout treiber2ImageV⟩

/-- **The verbatim worker in the value environment** (counted, partial): it
writes the `top` it read to its node and its node to `top`, reads `(%rax)`
only at a non-zero `top` (a node), and writes the `next` it read to `top`. -/
theorem workerV_memVals :
    ∀ s g, ((s.regs.get64 .rbx = symT2 "n1" ∨ s.regs.get64 .rbx = symT2 "n2") ∧ ∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted (treiber2ValEnv (symT2 "top") (symT2 "n1") (symT2 "n2"))))
        (fun x => (x.1.2 = labT2 "done" ∧ True) ∨ False) ((s, labT2 "worker"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (treiber2ValEnv (symT2 "top") (symT2 "n1") (symT2 "n2")))
    (Q := fun _ _ => True) (E := fun _ _ _ => False)
    (fun (_ : Label) s (_ : (SharedEnv.counted (treiber2ValEnv (symT2 "top") (symT2 "n1") (symT2 "n2"))).State) =>
      (s.regs.get64 .rbx = symT2 "n1" ∨ s.regs.get64 .rbx = symT2 "n2") ∧ ∀ a, Mem.loadInt s.dmem a 8 = none)
    ?_ rfl (by decide) treiber2CodeV_placedIn treiber2CodeV_last s g hs
  cfg_cases_env [treiber2CodeV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hrb, hd8⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64] at hrb
  -- cut `worker`
  case vc1 => exact ⟨by simpa using hrb, hd8⟩
  -- cut `push`
  case vc1 => exact ⟨trivial, by simp [SharedEnv.AccessIn]⟩
  case vc2 =>
    rename_i v σ1 hld _ _
    have hl := treiber2Val_load8 (Or.inl rfl) (hd8 _) hld
    refine ⟨fun _ => ?_, ?_⟩
    · simpa [Treiber2ValV] using hl.1
    · rcases hrb with h | h <;> simp [SharedEnv.AccessIn, h]
  case vc3 =>
    rename_i v σ1 hld dm σ2 hst _
    simp only [SharedEnv.counted_step, SharedEnv.within_step, SharedEnv.tick_store] at hst
    obtain ⟨rfl, -⟩ := stN hd8 hst
    exact hd8 _
  case vc4 =>
    refine ⟨?_, by simp [SharedEnv.AccessIn]⟩
    show ∀ old new, _ → _ → _ → _
    intro old new h _ _
    simp only [rmwOp128, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    split at ha
    · cases ha
      rcases hrb with h | h <;> simp [Treiber2ValV, h]
    · cases ha
  all_goals try (
    rename_i v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    simp only [SharedEnv.counted_step, SharedEnv.within_step, SharedEnv.tick_store] at hst
    obtain ⟨rfl, h2⟩ := stN hd8 hst
    have h1 := treiber2Val_loadTick (hd8 _) hld
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    first
      | exact ⟨by simpa using hrb, hd8⟩
      | exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hrb, hd8⟩, .inl (by decide)⟩
      | (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hrb, hd8⟩, .inr fun ⟨_, hg⟩ => ?_⟩
         subst hg; omega)
    done)
  -- cut `pop`
  case vc1 => exact ⟨trivial, by simp [SharedEnv.AccessIn]⟩
  case vc2 =>
    rename_i v σ1 hld af hz _
    have h1 := treiber2Val_loadTick (hd8 _) hld
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hrb, hd8⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  case vc3 =>
    rename_i v σ1 hld af hz hnz _
    have hl := treiber2Val_load8 (Or.inl rfl) (hd8 _) hld
    simp at hz
    refine ⟨trivial, ?_⟩
    rcases hl.1 with h | h | h
    · exact absurd h hz
    all_goals simp [SharedEnv.AccessIn, h]
  case vc4 => exact hd8 _
  case vc5 =>
    rename_i v σ1 hld af hz v2 σ2 hld2 _
    have hl := treiber2Val_load8 (Or.inl rfl) (hd8 _) hld
    simp at hz
    have hv : v = symT2 "n1" ∨ v = symT2 "n2" := hl.1.resolve_left hz
    have hl2 := treiber2Val_load8 (by rcases hv with h | h <;> simp [Treiber2ValL, h]) (hd8 _) hld2
    refine ⟨?_, by simp [SharedEnv.AccessIn]⟩
    show ∀ old new, _ → _ → _ → _
    intro old new h _ _
    simp only [rmwOp128, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    split at ha
    · cases ha
      rcases hl2.1 with h | h | h <;> simp [Treiber2ValV, h]
    · cases ha
  all_goals
    rename_i v σ1 hld af hz v2 σ2 hld2 old σ3 hcas heq hz2 _
    have h1 := treiber2Val_loadTick (hd8 _) hld
    have h2 := treiber2Val_loadTick (hd8 _) hld2
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    first
      | exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hrb, hd8⟩, .inl (by decide)⟩
      | (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hrb, hd8⟩, .inr fun ⟨_, hg⟩ => ?_⟩
         subst hg; omega)


/-! ## The specification -/

/-- The verbatim workers' value specification at `treiber2S`. -/
noncomputable def treiber2ValSpec :
    ValSpecX (Treiber2ValL (symT2 "top") (symT2 "n1") (symT2 "n2")) (Treiber2ValV (symT2 "n1") (symT2 "n2")) where
  S := treiber2S (symT2 "top") (symT2 "n1") (symT2 "n2")
  le16 := fun x hx => by
    simp only [treiber2S, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact (by decide : 8 ≤ 16)
  e := layout treiber2ImageV
  valid := inferInstance
  endPc := labT2 "done"
  post := fun x => ∃ _ : Nat, (x.1.2 = labT2 "done" ∧ True) ∨ False
  post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim

/-- **The value specification holds at the start states with
declarations.** -/
theorem treiber2ValSpec_initD {ds : Decls} {s0 s1 : State} (h0 : StartWVD ds (symT2 "n1") s0)
    (h1 : StartWVD ds (symT2 "n2") s1) :
    ∀ (tid : Nat) s, [s0, s1][tid]? = some s → treiber2ValSpec.HoldsD ds s := by
  have H : ∀ {n : BitVec 64} {s : State}, StartWVD ds n s → (n = symT2 "n1" ∨ n = symT2 "n2") →
      treiber2ValSpec.HoldsD ds s := fun {n s} hS hn => by
    refine ⟨hS.exe, hS.endPc, hS.decls, fun k _ => hS.dmem k, ?_⟩
    rw [show s.st = (s.st.1, labT2 "worker") from Prod.ext rfl hS.pc]
    exact TreiberAbs.Safely.uncountT (workerV_memVals _ ((), 0) ⟨hS.rbx ▸ hn, hS.d8⟩)
  intro tid s hs
  rcases tid with _ | _ | i
  · cases hs; exact H h0 (.inl rfl)
  · cases hs; exact H h1 (.inr rfl)
  · simp at hs

omit layout [Executable.ValidLayout (layout treiber2ImageV)] in
/-- The initial memory of `Config.init` satisfies the value invariant when
`top`, `n1`, `n2` start at `0` (no messages yet). -/
theorem memVals_treiber2_init {t n1 n2 : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hT0 : (Config.init states initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN1 : (Config.init states initMem).mem.initVal ⟨n1, 8⟩ = 0)
    (hN2 : (Config.init states initMem).mem.initVal ⟨n2, 8⟩ = 0) :
    MemVals (Treiber2ValL t n1 n2) (Treiber2ValV n1 n2) (Config.init states initMem).mem := by
  refine ⟨fun l hl => ?_, fun ts w h _ => ?_⟩
  · rcases hl with rfl | rfl | rfl
    · simp only [Treiber2ValV, hT0]; simp
    · simp only [Treiber2ValV, hN1]; simp
    · simp only [Treiber2ValV, hN2]; simp
  · simp [Memory.get?] at h

/-- **No reachable configuration of the verbatim `treiber2` workers with the
runner's declarations has a faulting step**, for `ds` agreeing on `top`,
`n1`, `n2` and an initial memory with all three at `0`. -/
theorem x64_treiber2_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn (treiber2S (symT2 "top") (symT2 "n1") (symT2 "n2"))) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartWVD ds (symT2 "n1") s0) (h1 : StartWVD ds (symT2 "n2") s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symT2 "top", 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨symT2 "n1", 8⟩ = 0)
    (hN2 : (Config.init [s0, s1] initMem).mem.initVal ⟨symT2 "n2", 8⟩ = 0) :
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  x64_faultFree_of_valSpecs (fun _ => treiber2ValSpec) (fun _ => ds) (fun _ => hsz) (fun _ => hag)
    (fun _ => treiber2ImageV_noFaultCode) (fun _ => rootOnlyD_of_phase1TreeFX treiber2ImageV_phase1FX)
    (memVals_treiber2_init hT0 hN1 hN2) (init_threads_of (P := fun _ st => treiber2ValSpec.HoldsD ds st) (treiber2ValSpec_initD h0 h1))

end Kraken.Promising.X64.EnvG.Treiber2X

namespace Kraken.Promising.X64.EnvG.Treiber2X.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.Treiber2X Kraken.Promising.SLR.EnvG

/-- **`treiber2.kl` never faults**, from the runner's exact configuration
(threads `treiber2P0D`, `treiber2P1D` with the runner's declarations,
initial memory `treiber2InitMemV`). -/
theorem x64_treiber2_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [treiber2P0D, treiber2P1D] treiber2InitMemV) :=
  x64_treiber2_envG_runner_faultFree (layout := treiber2LayoutV) treiber2DeclsD_sized
    (by rw [symT2_top, symT2_n1, symT2_n2]; decls_agrees_on) treiber2P0D_start treiber2P1D_start
    (by rw [symT2_top]; simp only [Config.init_mem]; decide)
    (by rw [symT2_n1]; simp only [Config.init_mem]; decide)
    (by rw [symT2_n2]; simp only [Config.init_mem]; decide)

end Kraken.Promising.X64.EnvG.Treiber2X.Concrete

#print axioms Kraken.Promising.X64.EnvG.Treiber2X.x64_treiber2_envG_runner_faultFree
#print axioms Kraken.Promising.X64.EnvG.Treiber2X.Concrete.x64_treiber2_envG_runner_faultFree_concrete
