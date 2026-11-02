/-
**hello's level 1 from rodata's landing at main's thread pointer** (x86-64; the twin of the live part of
`Spike/Lib/A64HelloLevel1T.lean`): the landing's thread pointer `t` carried into `wc_rodata`'s `.x15` invariant, so
that the `.x15` invariant's thread pointer fact (`MainPostT`'s `hJpT`) holds by construction.

`hJpT` asks `Jp σ0 c → σ0.regs.fsBase = t` of the `.x15` invariant; a landing's `Jp` says nothing about the thread
pointer, which is a fact of the concrete state (`KeepTP.TP t s`). At `.x15` the abstract registers are the state's
(`Abs.regs`), so `JpT Jp t` (`Jp` and the thread pointer) holds there whenever `Jp` does and `TP t s`.

- `JpT`: `Jp` at thread pointer `t`.
- `jpT_tp`: `hJpT` at `JpT Jp t`.
- `at_s0_tp`: `wc_rodata`'s `.x15` at `Jp` and `TP t s` is at `JpT Jp t`.

## Differences from the AArch64 version

- The thread pointer is `%fs`'s base (`fsBase`; AArch64: `TPIDR_EL0`), and `wc_rodata`'s node past the allocator's
  return is `.x15` (`HelloRd.pN … .s0`, seven invariants `Jp Jp' J1 J2 J2' J3 J4`; AArch64: `.sp0` with eight,
  the fence's `J5` included).
- AArch64's `land_segWST` and `land_segWSL` are unreachable from the AArch64 root and are not twinned.
-/
import Spike.Lib.X64HelloRodata
import Spike.Lib.X64KeepTP

namespace Spike.Lib.X64.HelloPh.Level1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Region)
open Spike.Lib.X64 (AS At)
open Spike.Lib.X64.Flow.HelloRd (pN)
open Spike.Lib.X64.KeepTP (TP)

/-- **`Jp` at thread pointer `t`**: `wc_rodata`'s `.x15` invariant with `hJpT`'s fact. -/
def JpT (Jp : AS → Ctl → Prop) (t : UInt64) (σ : AS) (c : Ctl) : Prop :=
  Jp σ c ∧ σ.regs.fsBase = t

/-- **`hJpT` at `JpT Jp t`**. -/
theorem jpT_tp {Jp : AS → Ctl → Prop} {t : UInt64} : ∀ σ0 c, JpT Jp t σ0 c → σ0.regs.fsBase = t :=
  fun _ _ h => h.2

/-- **`wc_rodata`'s `.x15` at `Jp` and thread pointer `t` is at `JpT Jp t`** (the abstract registers are the
state's, `Abs.regs`). -/
theorem at_s0_tp {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {lab : Label → Int64} {Jp Jp' J1 J2 J2' J3 J4 Jp'' J1' J2'' J2''' J3' J4' : AS → Ctl → Prop}
    {t : UInt64} {s : State} {c : Ctl}
    (h : At exe endPc R F (pN lab Jp Jp' J1 J2 J2' J3 J4 .s0) s c) (ht : TP t s) :
    At exe endPc R F (pN lab (JpT Jp t) Jp'' J1' J2'' J2''' J3' J4' .s0) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hF, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hF, hJ, by rw [← hA.regs]; exact ht⟩

end Spike.Lib.X64.HelloPh.Level1

/-- info: 'Spike.Lib.X64.HelloPh.Level1.jpT_tp' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1.jpT_tp

/-- info: 'Spike.Lib.X64.HelloPh.Level1.at_s0_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1.at_s0_tp
