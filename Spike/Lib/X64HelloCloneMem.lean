/-
**hello.w's source-memory relation at the clone on x86-64** (the twin of `Spike/Lib/A64HelloCloneMem.lean`): the
residual `hm` and `hwf` of `X64HelloSvcFit.r12_fit_clone`.

- `memRelP_preRH`: `PreRH`'s `SpawnPreH.inv1` relation, over the pre-spawn source memory (the spawn keeps it) at the
  record's placement `SR w` (`SpawnPreH.SR`), which is also `ClonePreH`'s `lbl`.
- `wf_LH`: the placed layout `LH hp i` is well formed (`PlaceWX.wf_link_of_placeWX`).
- `r12_fit_preRH`: `r12_fit_clone` at `PreRH.clone`, with no premise left.

## Differences from the AArch64 version

- Over x86-64's `X64HelloSpawnR.PreRH`, `X64HelloAssemblyI.LH` (`PlaceWX`) and `X64HelloSvcFit`.
- The buffer word is main's `%r12` at the clone (AArch64 `x9`), so `x9_fit_preRH` is `r12_fit_preRH`; its
  `ClonePreH` takes no label prefix (AArch64 `".L22_wc_main"`).
-/
import Spike.Lib.X64HelloSpawnR
import Spike.Lib.X64HelloAssemblyI
import Spike.Lib.X64HelloSvcFit

namespace Spike.Lib.X64HelloCloneMem

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64HelloSpawnR (PreRH)
open Spike.Lib.X64HelloAssemblyI (LH)
open Spike.Lib.X64HelloPreA (ClonePreH)

section Pre

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : X64HelloW1.WSideH ι}
  {r0 r1 : ι → Range} {Λ : Scc.Sem.Layout} {w : ι} {d : Cfg} {th : Thread isa} {stack : Nat}
  {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)}
  {l : WeakMem.AllocLabel}

/-- **The source-memory relation at main's clone**, at the record's placement: `inv1`'s, over the spawned
configuration's memory, which is the pre-spawn one. -/
theorem memRelP_preRH
    (h : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l) :
    MemRelP Λ (SR w).lbl (SR w).lsize ts d.1.mem s.mem [] th.prom [] ∧ (SR w).lbl = lbl := by
  have hSR : SR w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ := h.pre.SR
  obtain ⟨th0, ws, -, -, hs'⟩ := h.hsp
  have hmem : s'.mem = s.mem := by rw [hs']; rfl
  have hm := h.pre.inv1.mem
  rw [hmem] at hm
  rw [hSR]
  exact ⟨hm, rfl⟩

end Pre

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **hello's placed layout is well formed.** -/
theorem wf_LH : (LH hp i).Λ.WF := Spike.Lib.PlaceWX.wf_link_of_placeWX i hp

end Inst

section Fit

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : X64HelloW1.WSideH ι}
  {r0 r1 : ι → Range} {w : ι} {d : Cfg} {th : Thread isa} {stack : Nat}
  {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)}
  {l : WeakMem.AllocLabel}

/-- **main's `%r12` at the clone has 13 bytes of room**, at hello's placed layout, from `PreRH` alone. -/
theorem r12_fit_preRH {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    {hp : PlaceWX pcfg Λ0 o} {i : CoreTerm.Expr → String → Nat → Option Nat}
    (h : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l)
    {X : State → Prop} (hc : ClonePreH (LH hp i).Λ (r0 w) (r1 w) X lbl d s) :
    (th.st.st.1.regs.get64 .r12).toNat + 13 < 2 ^ 64 := by
  obtain ⟨hm, hl⟩ := memRelP_preRH h
  rw [hl] at hm
  exact Spike.Lib.X64HelloSvcFit.r12_fit_clone hc h.pre.threads hm (wf_LH hp i)

end Fit

end Spike.Lib.X64HelloCloneMem

/-- info: 'Spike.Lib.X64HelloCloneMem.memRelP_preRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCloneMem.memRelP_preRH

/-- info: 'Spike.Lib.X64HelloCloneMem.wf_LH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCloneMem.wf_LH

/-- info: 'Spike.Lib.X64HelloCloneMem.r12_fit_preRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCloneMem.r12_fit_preRH
