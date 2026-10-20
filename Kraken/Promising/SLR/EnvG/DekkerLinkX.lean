/-
**Dekker's worker as a `ThreadRuleRX`**. The x64 worker on `EnvGX`
(`EnvG/DekkerVCGenX.lean`) through `ThreadRuleRX.ofSafelyEnvGX`
(`EnvG/X64Link.lean`), as `EnvG/X64MpLink.lean` does for the MP reader.

The shared postcondition `DkB F0 F1 C` (`NPSafe`'s `B`, one for both threads)
is a disjunction over the two thread ids: thread `j` with own flag `F_j`, if
its `edx` is `1`, has `DkEnd`: its `Entered` facts in the configuration's
memory and its resource's flag and counter write sets (`D6` read off at
the end through `EnvRel`).
-/
import Kraken.Promising.SLR.EnvG.DekkerVCGenX
import Kraken.Promising.EnvLinkTermX64

namespace Kraken.Promising.X64.EnvG.Dekker

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker
open Kraken.Promising.X64.EnvG

/-! ## The shared postcondition -/

/-- **Thread `j`'s end facts** (own flag `f`, other flag `o`, counter `c`):
`Entered` in `cfg`'s memory, all of `f` and half of `c` with their write sets. -/
def DkEnd (j : Nat) (f o c : BitVec 64) (cfg : Config isa) (r : Res) : Prop :=
  ∃ t rr trc a tc u, Entered cfg.mem j ⟨f, 4⟩ ⟨o, 4⟩ ⟨c, 4⟩ t rr trc a tc u ∧
    (r.wr ⟨f, 4⟩).q = 1 ∧ (∀ p, (r.wr ⟨f, 4⟩).X p → XF2 t u p) ∧
    (r.wr ⟨c, 4⟩).q = 1 / 2 ∧ (∀ p, (r.wr ⟨c, 4⟩).X p → XC1 (inc a, tc) p)

/-- Thread `j`, if its `edx` is `1`, has its end facts. -/
def DkThreadEnd (j : Nat) (f o c : BitVec 64) (cfg : Config isa) (r : Res) : Prop :=
  ∀ th, cfg.threads[j]? = some th → (th.st.st.1.regs.get64 .rdx).setWidth 32 = 1 → DkEnd j f o c cfg r

/-- **Dekker's shared postcondition**: thread `0`'s (own flag `F0`) or
thread `1`'s (own flag `F1`) end facts. -/
def DkB (F0 F1 C : BitVec 64) (cfg : Config isa) (r : Res) (_ : Ghost) : Prop :=
  DkThreadEnd 0 F0 F1 C cfg r ∨ DkThreadEnd 1 F1 F0 C cfg r

/-! ## The rule -/

theorem dkPlan_valid : dkPlan.Valid := by simp [Plan.Valid]

theorem dkS_le16 (f o c : BitVec 64) : Le16 (dkS f o c) := fun x hx => by
  simp only [dkS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact (by decide : 4 ≤ 16)

variable [layout : _root_.Layout]

theorem worker_phase1 [Executable.ValidLayout (layout worker)] : Phase1TreeX Arch.tso (layout worker) := by
  refine phase1TreeX_of_dirs ?_
  dirs_phase1X worker
  -- `jne done`: the branch is inside `toEv`, which the tactic's `split` misses
  -- `jmp done`
  all_goals simp [RelRegOrMem.interp, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS]

theorem worker_noFault : DirsNoFault (layout worker) := by
  dirs_no_fault worker
  all_goals by_cases h : s.status.zf = true <;> simp [h, Kraken.Promising.X64.toEv, EvTree.NoFault]

/-- The worker's postcondition: the end of its text and `edx = 1 → D6` (the
counter of `worker_envG` projected away). -/
abbrev postD (tid : Nat) (f o c : BitVec 64) : MachineState × EStateX → Prop :=
  postOfX worker fun s σ => ∃ _ : Nat, (s.regs.get64 .rdx).setWidth 32 = 1 → D6 tid f o c σ

/-- **`hB` for the worker**: `D6` at the end gives `DkThreadEnd` (the
resource is the env state's, no promise; the snapshot's memory is a prefix
of the configuration's). -/
theorem hB_D (tid : Nat) (f o c : BitVec 64) : ∀ (cfg : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postD tid f o c (t.st.st, σ) → t.prom = [] → EnvRel tid dkPlan σ cfg t r g cl → cl →
      DkThreadEnd tid f o c cfg r := by
  rintro cfg t r g cl σ hpost hp hrel - th hth hrdx
  obtain ⟨-, -, hD⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  obtain rfl : th = t := Option.some.inj (hth.symm.trans hrel.ht)
  obtain ⟨t', rr, trc, a, tc, u, he, hres⟩ := hD hrdx
  exact ⟨t', rr, trc, a, tc, u, (memLe_snap hrel.snap).entered he, hres.qF, hres.xF, hres.qC, hres.xC⟩

/-- **Dekker's worker rule on `EnvG`** (`Arch.tso`), for any shared
postcondition `B` implied by the thread's `DkThreadEnd`. -/
def dkRule [Executable.ValidLayout (layout worker)] (tid : Nat) (f o c : BitVec 64)
    {B : Config isa → Res → Ghost → Prop} (hB : ∀ cfg r g, DkThreadEnd tid f o c cfg r → B cfg r g) :
    ThreadRuleRX (I := isa) Arch.tso B tid :=
  ThreadRuleRX.ofSafelyEnvGX (S := dkS f o c) (post := postD tid f o c) dkPlan_valid (dkS_le16 f o c)
    worker_phase1 postOfX_end (not_instrStepEnv_of_end_labels _ 1)
    (fun cfg t r g cl σ h1 h2 h3 h4 => hB cfg r g (hB_D tid f o c cfg t r g cl σ h1 h2 h3 h4))

/-- **The worker's rule excludes faults.** -/
theorem dkRule_noFault [Executable.ValidLayout (layout worker)] (tid : Nat) (f o c : BitVec 64)
    {B : Config isa → Res → Ghost → Prop} (hB : ∀ cfg r g, DkThreadEnd tid f o c cfg r → B cfg r g) :
    NoFaultRule (dkRule tid f o c hB) :=
  noFaultRule_ofSafelyEnvGX_struct _ _ _ _ _ _ worker_noFault

end Kraken.Promising.X64.EnvG.Dekker
