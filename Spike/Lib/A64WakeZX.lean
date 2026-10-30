/-
**wake.w's worker fragment, extended** (AArch64): the
fragment `wakeZX` that the worker's segments keep (`seg_childPreNNA`) is
`wakeZE` (`wakePass`, off the end) plus:
- `AbOffL` (off the abort stubs),
- every untagged locative the control accesses is the flag `cS` (`LabPtr`,
  for `WakeLabMapped.labMapped_flagB`),
- the environment placed (`Placed`),
- the instruction's tree has at most one write per path, a release write
  (`RelW1 Arch.armv8`).
It is added alongside `wakeZE`, which stays as it was. The listing is
wake.w's certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `wakeZX`; its projections `toZE`, `abOff`, `labPtr`, `placed`, `relW1`;
  `hhalt1_ofX` (`EndOff.hhalt1_of` through `toZE`); `hW1_ofX` (`WakeConv1`'s
  `hW1` through `relW1`).
- `NodeW.and`, `ProW.and`, `ThrZA.and`: facts at a node's states combine.
-/
import Spike.Lib.A64WakeEndOff
import Spike.Lib.A64WakeChildNNA
import Spike.Lib.WakeMappedRow
import Spike.Lib.RelW1

namespace Spike.Lib.A64.Flow.Worker.Wake.ZX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Labels (ThrZA)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Flow.Worker.Wake.EndOff (wakeZE)
open Spike.Lib.WakeMappedRow (LabPtr)
open Spike.Lib.A64AbOffL (AbOffL)

/-- **The worker's extended fragment**: `wakeZE` (`wakePass`, off the end),
off the abort stubs (`AbOffL`), every untagged locative accessed the flag
`cS`, the environment placed in `Λ` under `lbl`, and the instruction's tree
with at most one write per path, a release write. -/
def wakeZX (Λ : Scc.Sem.Layout) (lbl : WeakMem.AllocLabel → Option Nat) (cS : WeakMem.Address)
    (exe : _root_.Executable) (kp : Nat) : Frag isaLSE2 := fun s c =>
  wakeZE exe kp s c ∧ AbOffL (_root_.Executable.labels exe).label s c ∧ (∀ sa, LabPtr c sa → sa = cS) ∧
    Spike.Lib.A64Consumer.Placed Λ lbl s c ∧ ∀ e, isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e

section Proj

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
  {exe : _root_.Executable} {kp : Nat} {s : State} {c : Ctl}

theorem toZE (h : wakeZX Λ lbl cS exe kp s c) : wakeZE exe kp s c := h.1
theorem abOff (h : wakeZX Λ lbl cS exe kp s c) : AbOffL (_root_.Executable.labels exe).label s c := h.2.1
theorem labPtr (h : wakeZX Λ lbl cS exe kp s c) : ∀ sa, LabPtr c sa → sa = cS := h.2.2.1
theorem placed (h : wakeZX Λ lbl cS exe kp s c) : Spike.Lib.A64Consumer.Placed Λ lbl s c := h.2.2.2.1
theorem relW1 (h : wakeZX Λ lbl cS exe kp s c) : ∀ e, isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e :=
  h.2.2.2.2

end Proj

/-- **`hhalt1`** for a family of states inside `NNZ exe endPc (wakeZX …)`. -/
theorem hhalt1_ofX {ι κ : Type} {Wi : ι → State → κ → Prop} {exe : _root_.Executable}
    [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} (hend : endPc = endOf exe wakeProg kp)
    {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
    {cOf : κ → Ctl} (hW : ∀ w s c, Wi w s c → NNZ exe endPc (wakeZX Λ lbl cS exe kp) s (cOf c)) :
    ∀ w s c, Wi w s c → Scc.Sem.A64.abi.atSys s = true → (isaLSE2.exec s).isSome :=
  EndOff.hhalt1_of hend fun w s c h => ⟨(hW w s c h).1, toZE (hW w s c h).2⟩

/-- **`hW1`** (`WakeConv1`): for a family of states inside `NNZ exe endPc
(wakeZX …)`, the instruction's tree has at most one write per path, a
release write. -/
theorem hW1_ofX {ι κ : Type} {Wi : ι → State → κ → Prop} {exe : _root_.Executable} {endPc : Int64}
    {kp : Nat} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
    {cOf : κ → Ctl} (hW : ∀ w s c, Wi w s c → NNZ exe endPc (wakeZX Λ lbl cS exe kp) s (cOf c)) :
    ∀ w s c e, Wi w s c → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e :=
  fun w s c e h he => relW1 (hW w s c h).2 e he

/-! ## Combining facts at a node's states -/

section And

variable {Z Z' : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- Two facts at a node's states (`NodeW`, no outside moves) combine. -/
theorem NodeW.and {n : ND} (h : NodeW Z (fun _ _ => False) exe endPc R F n)
    (h' : NodeW Z' (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => Z s c ∧ Z' s c) (fun _ _ => False) exe endPc R F n :=
  fun s c hs => ⟨⟨(h s c hs).1, (h' s c hs).1⟩, fun _ h => h⟩

/-- Two facts at a prologue's states combine. -/
theorem ProW.and {ms : MemSide isaLSE2} {pc0 Zr lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : AS → Ctl → Prop} (h : ProW Z (fun _ _ => False) exe endPc R F ms pc0 Zr lim L ps J)
    (h' : ProW Z' (fun _ _ => False) exe endPc R F ms pc0 Zr lim L ps J) :
    ProW (fun s c => Z s c ∧ Z' s c) (fun _ _ => False) exe endPc R F ms pc0 Zr lim L ps J :=
  ⟨NodeZA.and h.w0 h'.w0, NodeW.and h.w1 h'.w1, NodeZA.and h.w2 h'.w2, NodeZA.and h.w3 h'.w3⟩

/-- Two facts at every node's states of the thread worker's run combine. -/
theorem ThrZA.and {ms : MemSide isaLSE2} {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (h : ThrZA Z exe endPc R F ms c0 c1 c2 c3 A B tp sp0) (h' : ThrZA Z' exe endPc R F ms c0 c1 c2 c3 A B tp sp0) :
    ThrZA (fun s c => Z s c ∧ Z' s c) exe endPc R F ms c0 c1 c2 c3 A B tp sp0 where
  pro := ProW.and h.pro h'.pro
  head i := NodeZA.and (h.head i) (h'.head i)
  wpro R' F' hc x29 ra := ProW.and (h.wpro R' F' hc x29 ra) (h'.wpro R' F' hc x29 ra)
  wk R' F' hc x29 ra i := NodeZA.and (h.wk R' F' hc x29 ra i) (h'.wk R' F' hc x29 ra i)
  unpk R' F' hc x29 ra R'' F'' hc' x29' ra' i :=
    NodeZA.and (h.unpk R' F' hc x29 ra R'' F'' hc' x29' ra' i) (h'.unpk R' F' hc x29 ra R'' F'' hc' x29' ra' i)
  tail i := NodeZA.and (h.tail i) (h'.tail i)

end And

end Spike.Lib.A64.Flow.Worker.Wake.ZX
