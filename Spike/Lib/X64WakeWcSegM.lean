/-
**`MainSeg` at the clone from `ClonePost`** (x86-64; the `mainSeg_of` half
of `Spike/Lib/A64WakeWcSeg.lean` deferred from `X64WakeWcSeg`): main's thread at the clone in `ClonePost` gives
`X64WakeMainHRD.MainSeg`, `c`'s label placed at the cell `%r12` holds, and
the frame's words above stack 0's guard.

- `mainSeg_of`: `MainSeg L endPc th c Rm F₂ cA fp ra tp`, `lbl l = some
  cA.toNat`, and every word of `⟨Rm.base, -64, 16⟩` at least
  `stacksA + 4096`, from `ClonePost` and `ClonePre` (`c`'s label from main's
  source thread, `hc`).

**Where this differs from AArch64**: `mainSeg_of` is stated at any layout
`L` and end of text `endPc` (as `X64WakeMainHRD.MainSeg`; A64 at
`RuntimeLayout.ofPlaceW hp i` and `WakeSpawnR.endR hp i`, the instance
taking `L := RuntimeLayout.ofPlaceWX hp i`, `endPc := X64WakeH1Inv.endR hp
i`); the frame is `⟨Rm.base, -64, 16⟩` and its guard bound is at every
offset `k ∈ [-64, 16)` (A64: `⟨Rm.base, -96, 16⟩` at `-32` only); `c`'s cell
is in `%r12` (A64 `x9`); there is no `hal`. `hpc_of` (A64's second half:
the same at every `WakeSpawnR.PreR`) is stated over the x86-64 `PreR`/`QG`/
`ιR`, which live in the x86-64 `WakeSpawnR` (on the worker branch), so it
is not here: it is `mainSeg_of` applied to `PreR`'s `clone`, `hc` and
`pre.threads`.
-/
import Spike.Lib.X64WakeWcSeg
import Spike.Lib.X64WakeMainHRD

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range ValRep)
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakePreA (ClonePre)
open Spike.Lib.X64WakeMainHRD (MainSeg)

/-- **`MainSeg`, `c`'s cell and the frame's guard bound at the clone state**
from `ClonePost` and `ClonePre` (`c`'s label from main's source thread,
`hc`). -/
theorem mainSeg_of {L : RuntimeLayout} {endPc : Int64} {th : Thread isa} {c : Ctl} {J : AS → Ctl → Prop}
    {t : UInt64} (h : ClonePost L endPc J t th.st c)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {d : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} {th0 : TermRun.TTh} {l : WeakMem.AllocLabel}
    (hC : ClonePre Λ r0 r1 X lbl d s) (hs : s.ths = #[th0])
    (hc : TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (ht : d.1.threads = #[th]) :
    ∃ Rm F₂ cA fp ra tp, MainSeg L endPc th c Rm F₂ cA fp ra tp ∧ lbl l = some cA.toNat ∧
      ∀ k, -64 ≤ k → k < 16 → L.stacksA.toNat + 4096 ≤ ((⟨Rm.base, -64, 16⟩ : Region).addr k).toNat := by
  obtain ⟨R, F₂, σC, cA, m, fr, hfr, hS, hok, hat, hb, hsp, htp, -⟩ := h
  refine ⟨R, F₂, cA, fr.1, fr.2, t.toBitVec, ⟨hat, hb, hok, hsp, htp, hra_of_frG hfr⟩,
    hA_of_clone hC hs hc ht ?_, fun k h1 h2 => hZ_of hok hb hsp h1 h2⟩
  obtain ⟨-, -, -, -, σ, hA, -, ⟨⟨-, h12, -⟩, -⟩⟩ := hS
  rw [hA.regs]; exact h12

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.mainSeg_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.mainSeg_of
