/-
**wake.w's worker fragment, extended, x86-64** (in the manner of
`Spike/Lib/A64WakeZX.lean`): `wakeZX`, the fragment that the worker's
segments keep (`seg_childPreNNA`), is `wakeZE` (`wakePass`, off the end)
plus:
- `AbOffL` (off the abort stubs),
- `LabPtr`: every untagged locative the control accesses is the flag `cS`
  (for `X64WakeMappedRow`),
- `Placed`: the environment is placed (`X64Consumer.Placed`),
- `RelWS`: the instruction runs and its tree has at most one write per
  path, a release write,
- `OwnW W`: off a system call, no write at the worker's own word `W`.
It sits alongside `wakeZE`, which is unchanged.

- `wakeZX`, with projections `toZE`, `abOff`, `labPtr`, `placed`, `relWS`
  and `ownW`.
- `hhalt1_ofX` (`EndOff.hhalt1_of` through `toZE`) and `hW1_ofX` (the
  `RelW1 tso` half of `RelWS`).
- `ownTree_ofX`: `X64Consumer.Nodes.ownInstr`'s `OwnTree` at a state of
  `wakeZX`, when the owned words are a fixed list at `⟨W, 8⟩`.
- `ThrZA.and`: facts at the thread worker's node states combine (`NodeZA.and`
  and `XProW.and` already exist).

**Unlike AArch64** (forced by the x64 shape):
- The release-write part is the per-state `RelWS` (`Spike/Lib/X64RelWS.lean`,
  which also has `isSome`). AArch64 uses the bare `∀ e, … → RelW1 armv8 e`.
- The extra conjunct `OwnW W` (`Spike/Lib/X64OwnWNodes.lean`) has no AArch64
  counterpart: the AArch64 worker owns no word that the runtime writes.
- There is no `ProW.and`: the x64 prologue is an `XProW`, and `XProW.and` is
  in `Spike/Lib/X64WakeMainR.lean`.
- `NodeW.and` is `Spike/Lib/X64RelWS.lean`'s.
-/
import Spike.Lib.X64WakeAbOffZ
import Spike.Lib.X64WakeChildNNA
import Spike.Lib.X64WakeMappedRow
import Spike.Lib.X64OwnWNodes

namespace Spike.Lib.X64.Flow.Worker.Wake.ZX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (endOf)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker (NNZ NodeZA)
open Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZA)
open Spike.Lib.X64.Flow.Worker.Wake.AbOffZ (wakeZE)
open Spike.Lib.X64.Flow.Worker.Wake.OwnW (OwnW)
open Spike.Lib.X64WakeMappedRow (LabPtr)
open Spike.Lib.X64AbOffL (AbOffL)

/-- **The worker's extended fragment**: `wakeZE` (`wakePass`, off the end),
off the abort stubs (`AbOffL`), every untagged locative accessed the flag
`cS`, the environment placed in `Λ` under `lbl`, the instruction running with
at most one write per path, a release write (`RelWS`), and no write at the
worker's own word `W` (`OwnW`). -/
def wakeZX (Λ : Scc.Sem.Layout) (lbl : WeakMem.AllocLabel → Option Nat) (cS : WeakMem.Address)
    (W : BitVec 64) (exe : _root_.Executable) (kp : Nat) : Frag isa := fun s c =>
  wakeZE exe kp s c ∧ AbOffL (_root_.Executable.labels exe).label s c ∧ (∀ sa, LabPtr c sa → sa = cS) ∧
    Spike.Lib.X64Consumer.Placed Λ lbl s c ∧ RelWS s ∧ OwnW W s c

section Proj

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
  {W : BitVec 64} {exe : _root_.Executable} {kp : Nat} {s : State} {c : Ctl}

theorem toZE (h : wakeZX Λ lbl cS W exe kp s c) : wakeZE exe kp s c := h.1
theorem abOff (h : wakeZX Λ lbl cS W exe kp s c) : AbOffL (_root_.Executable.labels exe).label s c := h.2.1
theorem labPtr (h : wakeZX Λ lbl cS W exe kp s c) : ∀ sa, LabPtr c sa → sa = cS := h.2.2.1
theorem placed (h : wakeZX Λ lbl cS W exe kp s c) : Spike.Lib.X64Consumer.Placed Λ lbl s c := h.2.2.2.1
theorem relWS (h : wakeZX Λ lbl cS W exe kp s c) : RelWS s := h.2.2.2.2.1
theorem ownW (h : wakeZX Λ lbl cS W exe kp s c) : OwnW W s c := h.2.2.2.2.2

/-- **`ownInstr`'s `OwnTree`** at a state of `wakeZX`, when the owned words
are a fixed list `ow`, all at `⟨W, 8⟩`. -/
theorem ownTree_ofX {ow : List (Loc × Val)} (hw : ∀ l v, (l, v) ∈ ow → l = ⟨W, 8⟩)
    (h : wakeZX Λ lbl cS W exe kp s c) (hns : Scc.Sem.X64.abi.atSys s = false) (tree : EvTree State)
    (he : isa.exec s = some tree) : Spike.Lib.Consumer1.OwnTree (fun _ => ow) ow tree :=
  .inl ⟨(Spike.Lib.Consumer1.allInv_true tree).mono fun _ _ => rfl,
    Spike.Lib.Consumer1.writeTree_mono (fun l _ hl w hm => hl (hw l w hm)) (ownW h hns tree he)⟩

end Proj

/-- **`hhalt1`** for a family of states inside `NNZ exe endPc (wakeZX …)`. -/
theorem hhalt1_ofX {ι κ : Type} {Wi : ι → State → κ → Prop} {exe : _root_.Executable}
    [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address} {W : BitVec 64}
    {cOf : κ → Ctl} (hW : ∀ w s c, Wi w s c → NNZ exe endPc (wakeZX Λ lbl cS W exe kp) s (cOf c)) :
    ∀ w s c, Wi w s c → Scc.Sem.X64.abi.atSys s = true → (isa.exec s).isSome :=
  EndOff.hhalt1_of hend fun w s c h => ⟨(hW w s c h).1.1, (hW w s c h).1.2.1, (toZE (hW w s c h).2).2⟩

/-- **`hW1`**: for a family of states inside `NNZ exe endPc (wakeZX …)`, the
instruction's tree has at most one write per path, a release write. -/
theorem hW1_ofX {ι κ : Type} {Wi : ι → State → κ → Prop} {exe : _root_.Executable} {endPc : Int64}
    {kp : Nat} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
    {W : BitVec 64} {cOf : κ → Ctl} (hW : ∀ w s c, Wi w s c → NNZ exe endPc (wakeZX Λ lbl cS W exe kp) s (cOf c)) :
    ∀ w s c e, Wi w s c → isa.exec s = some e → EvTree.RelW1 Arch.tso e :=
  fun w s c e h he => (relWS (hW w s c h).2).2 e he

/-! ## Combining facts at a node's states -/

/-- Two facts at every node's states of the thread worker's run combine. -/
theorem ThrZA.and {Z Z' : Frag isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isa} {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (h : ThrZA Z exe endPc R F ms c0 c1 c2 c3 A B tp sp0) (h' : ThrZA Z' exe endPc R F ms c0 c1 c2 c3 A B tp sp0) :
    ThrZA (fun s c => Z s c ∧ Z' s c) exe endPc R F ms c0 c1 c2 c3 A B tp sp0 where
  pro := Spike.Lib.X64WakeMainR.XProW.and h.pro h'.pro
  head i := NodeZA.and (h.head i) (h'.head i)
  wpro R' F' hc rbp0 ra := Spike.Lib.X64WakeMainR.XProW.and (h.wpro R' F' hc rbp0 ra) (h'.wpro R' F' hc rbp0 ra)
  wk R' F' hc rbp0 ra i := NodeZA.and (h.wk R' F' hc rbp0 ra i) (h'.wk R' F' hc rbp0 ra i)
  unpk R' F' hc rbp0 ra R'' F'' hc' rbp1 ra1 i :=
    NodeZA.and (h.unpk R' F' hc rbp0 ra R'' F'' hc' rbp1 ra1 i) (h'.unpk R' F' hc rbp0 ra R'' F'' hc' rbp1 ra1 i)
  tail i := NodeZA.and (h.tail i) (h'.tail i)

end Spike.Lib.X64.Flow.Worker.Wake.ZX

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.ZX.ThrZA.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.ZX.ThrZA.and
