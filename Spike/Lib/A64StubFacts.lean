/-
**`SFacts` on the overflow abort path** (AArch64): the per-state facts
(`SFacts`, `Spike/Lib/A64SegInst.lean`) at the states of an abort stub,
where the source control is the one about to overflow (`OvfReady`) and its
places hold only in the caller's frame cells (so `CFacts.place`, at every
state, does not apply).

* `SFacts.dt_mono`: a larger write tail;
* `noEnv`, `cfacts_noEnv`: the control with its environment dropped has
  `CFacts` (its places are vacuous, its term an addition);
* `SFacts.ofNoEnv`: `SFacts` at `noEnv c` with `c`'s places at the state and
  `c`'s abort facts is `SFacts` at `c`; with `sfacts_done`, `sfacts_ev`,
  `sfacts_si` at `noEnv c` this gives the stub's instructions;
* `sfacts_svcAt`: `svc #0` with the abort and write facts given (the stub's
  `write`, with the write tail `Dt`, and its `exit_group` at the abort site);
* `abortOk_ovf`: the abort facts at the overflow abort site;
* `sfacts_svcOvf`: `sfacts_svcAt` for the overflow control placed at the
  state, without `CFacts`.
-/
import Spike.Lib.A64SegInst

namespace Spike.Lib.A64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {s : State} {c : Ctl}

/-- **A larger write tail.** -/
theorem SFacts.dt_mono {Dt Dt' : State → Prop} (h : SFacts Λ μ own rS Tk lbl s c Dt) (hD : ∀ s, Dt s → Dt' s) :
    SFacts Λ μ own rS Tk lbl s c Dt' :=
  { h with wrTail := fun ha fd buf n hd => hD s (h.wrTail ha fd buf n hd) }

/-- The control with its environment dropped. -/
def noEnv (c : Ctl) : Ctl := { c with env := [] }

/-- The overflow control's term is no load, store, allocation or return. -/
theorem ovf_cell (hc : OvfReady c) : ∀ x a e ty w,
    (c.term = .let_ x (.load true a) e ∨ ∃ b, c.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c.env a = some (ty, [w]) → OneCellTy ty := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ht, -⟩ := hc
  rintro x a e ty w (h | ⟨b, h⟩) <;> rw [ht] at h <;> cases h

/-- **`CFacts` at the overflow control without its environment**: its term
is an addition, its places are vacuous. -/
theorem cfacts_noEnv (hc : OvfReady c) : CFacts Λ lbl (noEnv c) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ht, -⟩ := hc
  refine ⟨fun a h => ?_, fun x a e ty w h => ?_, fun x a τ e h => ?_, fun _ => ?_⟩
  · simp only [noEnv] at h; rw [ht] at h; cases h
  · simp only [noEnv] at h; rcases h with h | ⟨b, h⟩ <;> rw [ht] at h <;> cases h
  · simp only [noEnv] at h; rw [ht] at h; cases h
  · refine ⟨fun _ _ => none, fun x ty ws h => ?_, fun x _ ty ws h => ?_, fun x k n h => ?_⟩
    · simp [noEnv, TermRun.lookupE] at h
    · simp [noEnv, TermRun.lookupE] at h
    · cases h

/-- **`SFacts` at the overflow control** from `SFacts` at it without its
environment, its places at the state (`hp`) and its abort facts (`hab`). -/
theorem SFacts.ofNoEnv {Dt : State → Prop} (h : SFacts Λ μ own rS Tk lbl s (noEnv c) Dt) (hc : OvfReady c)
    (hp : Placed Λ lbl s c)
    (hab : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .overflow ∧ OvfReady c ∧ EnvSmall c.env ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus) :
    SFacts Λ μ own rS Tk lbl s c Dt :=
  { h with noRet := h.noRet, cell := ovf_cell hc, place := hp, noAlloc := h.noAlloc, abortOk := hab }

/-- **The abort facts at the overflow abort site**: the site is the
overflow one, the control about to overflow in a small environment, and the
`exit_group` status the abort status. -/
theorem abortOk_ovf (hk : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .overflow) (hc : OvfReady c)
    (he : EnvSmall c.env)
    (hv : ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus) :
    ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .overflow ∧ OvfReady c ∧ EnvSmall c.env ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus :=
  fun k a ha hpc => ⟨hk k a ha hpc, hc, he, hv⟩

open Kraken.Promising.Lower.A64 (CellAt after)

/-- **`SFacts` at `svc #0`** off the release and take sites, with the abort
facts (`hab`) and the write tail (`hwr`) given: every state the kernel
resumes in is past it, owning what `s` owns and in the phase iff `s` is. -/
theorem sfacts_svcAt {Dt : State → Prop} (hC : CFacts Λ lbl c)
    (hrel : ∀ a, μ.site .release = some a → pcOf s ≠ a) (htake : ∀ a, μ.site .take = some a → pcOf s ≠ a)
    (hc : CellAt s Spike.Lib.A64.Flow.svcDir 4)
    (hnext : ∀ m, own (after s 4 m) = own s ∧ (Tk (after s 4 m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hab : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .overflow ∧ OvfReady c ∧ EnvSmall c.env ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus)
    (hwr : ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s) :
    SFacts Λ μ own rS Tk lbl s c Dt := by
  have hs : abi.atSys s = true := atSvc_of_cellAt hc
  have hsucc : ∀ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s ∧ (Tk s' ↔ Tk s) := by
    intro call hd s' hs'
    obtain ⟨r, -, rfl⟩ := (mem_certSuccs_svc hc hd).1 hs'
    exact hnext _
  refine ⟨hC.noRet, hC.cell, hrel, fun h => ?_, hC.place s, fun _ => ⟨0, 4, hc⟩, hC.noAlloc,
    fun h => ?_, fun _ call hd s' hs' => (hsucc call hd s' hs').1, fun a ha hpc => (htake a ha hpc).elim,
    fun a ha hpc => (htake a ha hpc).elim, fun a ha hpc => (htake a ha hpc).elim, fun _ h => ?_,
    fun _ call hd s' hs' => (hsucc call hd s' hs').2, hO, hab, fun _ => hwr⟩
  all_goals (rw [hs] at h; cases h)

/-- **`SFacts` at `svc #0` for the overflow control** (`hc`), placed at the
state (`hp`): `sfacts_svcAt` without `CFacts` (a stub's `write` and its
`exit_group` at the abort site, where the abort facts name the control
itself). -/
theorem sfacts_svcOvf {Dt : State → Prop} (hc : OvfReady c) (hp : Placed Λ lbl s c)
    (hrel : ∀ a, μ.site .release = some a → pcOf s ≠ a) (htake : ∀ a, μ.site .take = some a → pcOf s ≠ a)
    (hcell : CellAt s Spike.Lib.A64.Flow.svcDir 4)
    (hnext : ∀ m, own (after s 4 m) = own s ∧ (Tk (after s 4 m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hab : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .overflow ∧ OvfReady c ∧ EnvSmall c.env ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus)
    (hwr : ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s) :
    SFacts Λ μ own rS Tk lbl s c Dt := by
  have hC := cfacts_noEnv (Λ := Λ) (lbl := lbl) hc
  have hs : abi.atSys s = true := atSvc_of_cellAt hcell
  have hsucc : ∀ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s ∧ (Tk s' ↔ Tk s) := by
    intro call hd s' hs'
    obtain ⟨r, -, rfl⟩ := (mem_certSuccs_svc hcell hd).1 hs'
    exact hnext _
  refine ⟨hC.noRet, ovf_cell hc, hrel, fun h => ?_, hp, fun _ => ⟨0, 4, hcell⟩, hC.noAlloc,
    fun h => ?_, fun _ call hd s' hs' => (hsucc call hd s' hs').1, fun a ha hpc => (htake a ha hpc).elim,
    fun a ha hpc => (htake a ha hpc).elim, fun a ha hpc => (htake a ha hpc).elim, fun _ h => ?_,
    fun _ call hd s' hs' => (hsucc call hd s' hs').2, hO, hab, fun _ => hwr⟩
  all_goals (rw [hs] at h; cases h)

end Spike.Lib.A64Consumer

