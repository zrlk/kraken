/-
The one-thread link through the environment for partial-correctness
judgments, AArch64 (design note
`Kraken/Promising/EnvWP.md` §8).

`env_link_halt` (`Kraken.Promising.EnvWPAArch64`) takes an `Eventually`
judgment in `SharedEnv.lastWrite L`. A retry loop with a store-exclusive is
not totally correct even there (`lastWrite` lets `STXR` fail, so the loop may
retry forever), so its judgment is a `Safely` one (`MachineWP.cfgEnv_partial`).
`env_link_halt_safe` is `env_link_halt` for `Safely`: every promise-free
one-thread run that **halts** (reaches `endPc`) ends in `P`. A run that does
not halt is not constrained, which is all partial correctness can say.

The proof composes the simulations directly at the environment level:
`RelEnv` relates a thread state and the Promising memory to a split state
through the merged state (`MergedRel` and `Merged`), `seqSim_env` is the
simulation (`instrStepEnv_step1W`, then `seqSim_merged`), and
`reachablePF_sim_safe` carries `Safely` along the run. At `endPc` the
environment step relation has no step (`hstuck`, which
`not_instrStepEnv_of_end` gives for a laid-out program), so a `Safely`
judgment there is its postcondition (`Safely.post_of_stuck`). `env_link_halt`
used `hstop` (a merged step at `endPc` stutters) for this; a stuttering step
would let `Safely` hold without `P`, so the merged level cannot be used as an
intermediate stop here.
-/
import Kraken.Promising.EnvWPAArch64
import Kraken.Promising.SeqLinkAArch64Prog
import Kraken.Promising.SeqLinkSafe

open Kraken

namespace Kraken.Promising.AArch64

/-! ## No step behind the text -/

/-- Where nothing is laid out from the pc, there is no instruction step in
any environment. -/
theorem not_instrStepEnv_of_directivesFromAddress_nil {e : Kraken.Executable Directive}
    {env : SharedEnv} {x : MachineState × env.State} {R : MachineState × env.State → Prop}
    (h : Kraken.Executable.directivesFromAddress e x.1.2 = []) : ¬ e.instrStepEnv env x R := by
  rintro ⟨d, z, rest, hcode, -⟩
  unfold Kraken.Executable.codeAt at hcode
  rw [h] at hcode
  cases hcode

/-- At the end address of a laid-out program whose last cell is not a label
there is no instruction step in any environment: the `hstuck` premise of
`env_link_halt_safe`. -/
theorem not_instrStepEnv_of_end [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive} (env : SharedEnv)
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    ∀ x R, x.1.2 = (layout p).addrOf p.length → ¬ (layout p).instrStepEnv env x R := by
  intro x R hx
  refine not_instrStepEnv_of_directivesFromAddress_nil ?_
  rw [hx]
  exact Executable.directivesFromAddress_end hlast hd

/-- At the end address of a laid-out program whose last instruction is
followed by `k` labels (`... done:`) there is no instruction step in any
environment: `hstuck` of `env_link_halt_safe` and `env_link_terminates`.
`not_instrStepEnv_of_end` is the case `k = 0`. -/
theorem not_instrStepEnv_of_end_labels [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive} (env : SharedEnv) (k : Nat)
    (hlast : p[p.length - 1 - k]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl)
    (hls : (p.drop (p.length - k)).all Directive.isLabel = true := by rfl) :
    ∀ x R, x.1.2 = (layout p).addrOf p.length → ¬ (layout p).instrStepEnv env x R := by
  rintro x R hx ⟨d, z, rest, hcode, -⟩
  rw [hx, codeAt_of_directivesFromAddress_labels (directivesFromAddress_end_labels k hlast hd hls)] at hcode
  cases hcode

/-! ## The simulation at the environment level -/

/-- The thread state `x` on the Promising memory is the split state `z`: both
are the same merged state. -/
def RelEnv (L : SharedLayout) (e : _root_.Executable) (endPc : Int64) (x : State × Memory)
    (z : MachineState × (SharedEnv.lastWrite L).State) : Prop :=
  ∃ y, MergedRel L e endPc x y ∧ Merged L z y

/-- The environment judgment simulates the sequential runs of the thread. -/
theorem seqSim_env [_root_.Layout] {L : SharedLayout} (hL : L.WF) (e : Kraken.Executable Directive)
    [Kraken.Executable.ValidLayout e] (endPc : Int64) :
    SeqSim isa 0 (RelEnv L e endPc) (e.instrStepEnv (SharedEnv.lastWrite L)) := by
  rintro x z R ⟨y, hxy, hzy⟩ hT tree hex
  exact (seqSim_merged hL e endPc 0 x y _ hxy (instrStepEnv_step1W hL hzy hT) tree hex).mono
    fun _ _ ⟨y', hy', x', hx', hR⟩ => ⟨x', ⟨y', hy', hx'⟩, hR⟩

/-- A related split state is the thread's own state (its `dmem` holds the
private bytes only), with an environment state related to the memory. -/
theorem RelEnv.split {L : SharedLayout} {e : _root_.Executable} {endPc : Int64} {x : State × Memory}
    {z : MachineState × (SharedEnv.lastWrite L).State} (h : RelEnv L e endPc x z) :
    z.1.1 = x.1.st.1 ∧ z.1.2 = x.1.st.2 ∧ envRel L z.2 x.2 := by
  obtain ⟨⟨⟨r, f, D⟩, pc⟩, ⟨-, -, hr, hf, hpc, hrel, -⟩, ⟨hr', hf', hpc', hmr⟩⟩ := h
  obtain ⟨⟨⟨zr, zf, zd⟩, zpc⟩, zg⟩ := z
  obtain ⟨⟨exe, ep, ⟨⟨xr, xf, xd⟩, xpc⟩, sp, decls⟩, m⟩ := x
  simp only at hr hf hpc hrel hr' hf' hpc' hmr ⊢
  subst hr hf hpc hr' hf' hpc'
  have hd : zd = xd := by
    apply Std.ExtHashMap.ext_getElem?
    intro k
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    by_cases hk : L.Covers k
    · rw [hmr.split k hk, hrel.split k hk]
    · rw [← hmr.priv k hk, ← hrel.priv k hk]
  subst hd
  refine ⟨rfl, rfl, fun a n ha => ?_⟩
  have h1 := hmr.shared a n ha
  rw [hrel.shared a n ha, sharedBytes] at h1
  exact (toBytes_eq_iff.mp (Option.some.inj h1)).symm

/-! ## The link -/

/-- **The one-thread link through the environment, partial correctness.** A
`Safely` judgment in the `lastWrite` environment about the thread's own
(split) start state, with the environment state holding the memory's initial
values, holds at the end of every promise-free one-thread run that halts,
with an environment state holding the memory's final values. As
`EnvLinkHalt`, with `Safely` for `Eventually` and `hstuck` (no environment
step at `endPc`) for `hstop`. -/
def EnvLinkHaltSafe : Prop :=
  ∀ [_root_.Layout] (L : SharedLayout) (e : Kraken.Executable Directive) [Kraken.Executable.ValidLayout e],
    L.WF →
    ∀ (A : Arch) (fuel : Nat) (endPc : Int64) (showPc : Int64 → String) (s : MachineData) (pc : Int64)
      (mem : Memory) (g : BitVec 64 → BitVec 128)
      (P : MachineState × (SharedEnv.lastWrite L).State → Prop),
      mem.msgs = #[] → (∀ k, L.Covers k → s.dmem.get? k = none) → envRel L g mem →
      (∀ x, P x → x.1.2 = endPc) →
      (∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (SharedEnv.lastWrite L) x R) →
      Safely (e.instrStepEnv (SharedEnv.lastWrite L)) P ((s, pc), g) →
      ∀ c : Config isa, ReachablePF A fuel ⟨#[Thread.init ({ exe := e, endPc, st := (s, pc), showPc } : State)], mem⟩ c →
        ∀ t' : Thread isa, c.threads = #[t'] → t'.st.st.2 = endPc →
          ∃ g', envRel L g' c.mem ∧ P ((t'.st.st.1, endPc), g')

theorem env_link_halt_safe : EnvLinkHaltSafe := by
  intro _ L e _ hL A fuel endPc showPc s pc mem g P hm hsplit henv hPend hstuck hev c hc t' ht hend
  obtain ⟨D, hpriv, hsh⟩ := exists_merge hL g s.dmem L fun _ h => h
  have hmr : MergeRel L s.dmem g D := ⟨hpriv, hsplit, hsh⟩
  have hrel : MemRel L s.dmem mem D := (memRel_iff_mergeRel L s.dmem D mem g hL henv).mpr hmr
  obtain ⟨r, f, d⟩ := s
  have hxy : RelEnv L e endPc (({ exe := e, endPc, st := (⟨r, f, d⟩, pc), showPc } : State), mem)
      ((⟨r, f, d⟩, pc), g) :=
    ⟨(⟨r, f, D⟩, pc), ⟨rfl, rfl, rfl, rfl, rfl, hrel, rfl⟩, ⟨rfl, rfl, rfl, hmr⟩⟩
  obtain ⟨t'', ht'', hcase⟩ := reachablePF_sim_safe A fuel (seqSim_env hL e endPc) hm hxy hev hc
  rw [ht] at ht''
  have htt : t' = t'' := by simpa using ht''
  subst htt
  have key : ∀ z, RelEnv L e endPc (t'.st, c.mem) z → P z →
      ∃ g', envRel L g' c.mem ∧ P ((t'.st.st.1, endPc), g') := by
    rintro ⟨⟨zs, zpc⟩, zg⟩ hz hP
    obtain ⟨h1, -, h3⟩ := hz.split
    have hpc : zpc = endPc := hPend _ hP
    simp only at h1 h3 hpc
    rw [h1, hpc] at hP
    exact ⟨zg, h3, hP⟩
  rcases hcase with ⟨⟨z₁, z₂⟩, x', -, hz, hzx, hPx⟩ | ⟨x', hx, hev'⟩
  · -- `P` was met at `z`, which is at `endPc`, so the thread halted there
    have hpcz : z₁.st.2 = endPc := hzx.split.2.1.symm.trans (hPend x' hPx)
    have hez : z₁.endPc = endPc := by
      obtain ⟨y, hy, -⟩ := hzx
      exact hy.2.1
    have hhalt : isa.exec z₁ = none := by
      simp [isa, exec, hpcz, hez]
    obtain ⟨h1, h2⟩ := Prod.mk.inj (SeqReach.halted hhalt hz)
    subst h1 h2
    exact key x' hzx hPx
  · have hpx : x'.1.2 = endPc := hx.split.2.1.trans hend
    exact key x' hx (hev'.post_of_stuck fun R => hstuck x' R hpx)

end Kraken.Promising.AArch64
