/-
**Program-level fault freedom from a value-only reachability invariant**
. ISA-neutral.

The x64 pointer programs (treiber, msqueue) access memory at addresses they
read from shared memory. Whether such an access is at a declared footprint
(and so does not fault under the runner's declarations) depends on the
*values* in memory, about which a thread's own `Safely` judgment says
nothing. This file supplies the missing fact without SLR, ghost state or
`AnchorOk`: a value invariant that holds at every reachable configuration of
the full Promising machine, promises included.

- `MemVals L V m`: every message of `m` to a location in `L`, and every
  initial value of such a location, is in `V` (`V` may be infinite);
- `ValX L V P t`: the tree writes only `V`-values to `L`-locations when its
  `L`-reads returned `V`-values (loads and RMW `old` values), and every leaf
  satisfies `P`. It is the tree judgment of the stateless environment
  `SharedEnv.valEnv L V` (`EnvSpike.TreeJ.valX`): `ok` asks the write
  conditions, `step` grants the read conditions;
- **`runTree_valX`**, the key preservation lemma: a run of a `ValX` tree from
  a context whose memory satisfies `MemVals` ends in a memory satisfying
  `MemVals`, at a leaf satisfying `P`; `stepOne_valX`, `threadNP_valX`;
- `certWrite_valX`: every certified promise of a `P`-thread writes a
  `V`-value to an `L`-location, so promise steps keep `MemVals` too;
- `ValInvAt`, **`Reachable.valInv`**: `MemVals` of the memory and `P` of every
  thread state at every reachable configuration;
- **`faultFree_of_valInv`**: if every tree of a `P`-state is structurally
  fault-free (`EvTree.NoFault`), no reachable configuration has a faulting
  step (`Config.FaultFree`). This is program-level, stronger than the
  rule-level `NoFaultRule`s.
- `valX_of_all_empty`: at `L = ∅` the read and write conditions are vacuous,
  so `ValX` is `EvTree.All` (the fixed-layout programs, `MemValsX64`).

The x64 link (value specifications from `vcgen` judgments in
`(valEnv L V).within S`, and the structural no-fault at the runner's
declarations) is `MemValsX64.lean`.

The definitions and the base lemmas (`valEnv`, `MemVals`, `ValX`,
`MemVals.read/append`, `memVals_write`, `ValInvAt`, …) are in
`EnvG/MemValsBase.lean`; the preservation lemmas below are instances of
their generic forms for `ValXA` (`EnvG/MemValsGen.lean`), through
`ValX.toValXA`. Same names and statements.
-/
import Kraken.Promising.SLR.EnvG.MemValsGen

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

variable {L : Loc → Prop} {V : Val → Prop}

/-! ## Preservation by runs, steps and certified promises -/

section Steps

variable {A : Arch} {tid : Nat} {iv : InstrViews}

/-- **The key preservation lemma.** A run of a `ValX` tree from a context
whose memory satisfies `MemVals` ends in a memory satisfying `MemVals`, at a
leaf satisfying `P`. Every read of an `L`-location returns a `V`-value
(`MemVals.read`), so the tree's write conditions apply. -/
theorem runTree_valX (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} {P : σ → Prop} :
    ∀ (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      ValX L V P tree → MemVals L V c.mem → MemVals L V c'.mem ∧ P s :=
  fun tree c s c' h hA hm => runTree_valXA A tid iv tree c s c' h hA.toValXA hm

/-- **One instruction** (`stepOne`): `MemVals` is kept and the next thread
state satisfies `P`. -/
theorem stepOne_valX (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {P : I.State → Prop}
    (hA : ∀ tree, I.exec t.st = some tree → ValX L V P tree) (hm : MemVals L V mem) :
    MemVals L V o.mem ∧ P o.thread.st :=
  stepOne_valXA A hstep ho (fun tree hex => (hA tree hex).toValXA) hm

/-- A promise-free solo run (certification) keeps `MemVals` and the
per-thread invariant. -/
theorem threadNP_valX (A : Arch) {tid : Nat} {P : I.State → Prop}
    (hP : ∀ (st : I.State) tree, P st → I.exec st = some tree → ValX L V P tree) :
    ∀ {p q : Thread I × Memory}, ThreadNP A tid p q → P p.1.st → MemVals L V p.2 →
      P q.1.st ∧ MemVals L V q.2 :=
  fun hr h1 h2 => threadNP_valXA A (fun st tree hst hex => (hP st tree hst hex).toValXA) hr h1 h2

/-- **A certified promise writes a `V`-value to an `L`-location**: the
certifying run keeps `MemVals`, and the promised message is in its final
memory (`stepOne_ext`). -/
theorem certWrite_valX (A : Arch) {tid : Nat} {P : I.State → Prop}
    (hP : ∀ (st : I.State) tree, P st → I.exec st = some tree → ValX L V P tree) {t : Thread I}
    {mem : Memory} {p : Msg × View} (h : CertWrite A tid t mem p) (ht : P t.st) (hm : MemVals L V mem) :
    L p.1.loc → V p.1.val :=
  certWrite_valXA A (fun st tree hst hex => (hP st tree hst hex).toValXA) h ht hm

/-! ## The invariant over `Reachable`, and fault freedom -/

/-- **The value invariant holds at every reachable configuration**, promise
steps included (`certWrite_valX`). -/
theorem Reachable.valInv {A : Arch} [I.LawfulState] {P : I.State → Prop}
    (hP : ∀ (st : I.State) tree, P st → I.exec st = some tree → ValX L V P tree)
    {fuel : Nat} {c c' : Config I} (h : Reachable A fuel c c') (h0 : ValInvAt L V P c) :
    ValInvAt L V P c' :=
  Reachable.valInvA (fun st tree hst hex => (hP st tree hst hex).toValXA) h h0

/-- **Program-level fault freedom from a value invariant.** If every tree of
a `P`-state is `ValX` and structurally fault-free, and the initial
configuration satisfies `ValInvAt`, no reachable configuration has a
faulting step. No SLR, no Theorem 1′. -/
theorem faultFree_of_valInv {A : Arch} [I.LawfulState] {P : I.State → Prop}
    (hP : ∀ (st : I.State) tree, P st → I.exec st = some tree → ValX L V P tree)
    (hnf : ∀ (st : I.State) tree, P st → I.exec st = some tree → tree.NoFault)
    {fuel : Nat} {c₀ : Config I} (h0 : ValInvAt L V P c₀) :
    Config.FaultFree A fuel c₀ :=
  faultFree_of_valInvA (fun st tree hst hex => (hP st tree hst hex).toValXA) hnf h0

end Steps

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvSpike

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvG

/-- **`ValX` as a tree judgment of `valEnv`**: the environment's `ok` is the
tree's write condition, its `step` the read condition. -/
def TreeJ.valX (L : Loc → Prop) (V : Val → Prop) {σ : Type} (Post : σ → Prop) :
    TreeJ (SharedEnv.valEnv L V) σ where
  W t _ := ValX L V Post t
  Post s _ := Post s
  done h := h
  fault := trivial
  choose h := h
  load _ h := fun v hv => h v () hv
  store hok h := ⟨hok, fun b => h b () trivial⟩
  rmw hok h := fun old ho => ⟨fun new hn hl => hok old new hn hl (ho hl), h old () ho⟩
  fence _ h := fun _ => h () trivial

end Kraken.Promising.SLR.EnvSpike

#print axioms Kraken.Promising.SLR.EnvG.runTree_valX
#print axioms Kraken.Promising.SLR.EnvG.Reachable.valInv
#print axioms Kraken.Promising.SLR.EnvG.faultFree_of_valInv
