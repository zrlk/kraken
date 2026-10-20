/-
**The value invariant: memory, tree condition and value environment**
. ISA-neutral.

`SharedEnv.valEnv`, `MemVals`, `ValX`, `MemVals.read`, `MemVals.append`,
`memVals_empty`, `valX_of_all_empty`, `ValX.mono`, `memVals_write` and
`ValInvAt`, moved verbatim. A module of their own so that both tree
conditions, `ValX` (here) and `ValXA` (`EnvG/MemValsGen.lean`), can share
them while keeping their own `match` auxiliaries. The preservation lemmas
are in `MemValsGen.lean` (generic, `ValXA`) and `MemVals.lean` (`ValX`,
their instances). See `MemVals.lean` for the overview.
-/
import Kraken.Promising.SLR.DispenserRun
import Kraken.Promising.SLR.Sim.NoFault
import Kraken.Promising.SLR.EnvSpike

namespace Kraken.SharedEnv

open Kraken.Promising

/-- **The value environment.** Writes to an `L`-location must write a
`V`-value (an RMW's `op` is checked at every `V` old value); reads of an
`L`-location (loads and RMW old values) return `V`-values; every other
access and every fence is unconstrained. The state is trivial. -/
def valEnv (L : Loc → Prop) (V : Val → Prop) : SharedEnv where
  State := Unit
  ok a _ := match a with
    | .load .. => True
    | .store _ _ addr n v => L ⟨addr, n⟩ → V v
    | .rmw _ addr n op => ∀ old new, op old = some new → L ⟨addr, n⟩ → V old → V new
    | .fence _ => True
  step a _ r _ := match a, r with
    | .load _ _ addr n, v => L ⟨addr, n⟩ → V v
    | .store .., _ => True
    | .rmw _ addr n _, old => L ⟨addr, n⟩ → V old
    | .fence _, _ => True

variable {L : Loc → Prop} {V : Val → Prop}

theorem valEnv_fencesSkip (L : Loc → Prop) (V : Val → Prop) : (valEnv L V).FencesSkip :=
  fun _ _ => ⟨trivial, fun _ _ => rfl⟩

instance (L : Loc → Prop) (V : Val → Prop) : (valEnv L V).Skips := ⟨valEnv_fencesSkip L V⟩

@[simp] theorem valEnv_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {g : (valEnv L V).State} : (valEnv L V).ok (.load k xcl addr n) g ↔ True := Iff.rfl

@[simp] theorem valEnv_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : BitVec 128}
    {g : (valEnv L V).State} : (valEnv L V).ok (.store k xcl addr n v) g ↔ (L ⟨addr, n⟩ → V v) := Iff.rfl

@[simp] theorem valEnv_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : BitVec 128 → Option (BitVec 128)} {g : (valEnv L V).State} :
    (valEnv L V).ok (.rmw k addr n op) g ↔
      (∀ old new, op old = some new → L ⟨addr, n⟩ → V old → V new) := Iff.rfl

@[simp] theorem valEnv_ok_fence {k : FenceKind} {g : (valEnv L V).State} :
    (valEnv L V).ok (.fence k) g ↔ True := Iff.rfl

@[simp] theorem valEnv_step_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {g g' : (valEnv L V).State} {v : BitVec 128} :
    (valEnv L V).step (.load k xcl addr n) g v g' ↔ (L ⟨addr, n⟩ → V v) := Iff.rfl

@[simp] theorem valEnv_step_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {v : BitVec 128} {g g' : (valEnv L V).State} {b : Bool} :
    (valEnv L V).step (.store k xcl addr n v) g b g' ↔ True := Iff.rfl

@[simp] theorem valEnv_step_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : BitVec 128 → Option (BitVec 128)} {g g' : (valEnv L V).State} {old : BitVec 128} :
    (valEnv L V).step (.rmw k addr n op) g old g' ↔ (L ⟨addr, n⟩ → V old) := Iff.rfl

@[simp] theorem valEnv_step_fence {k : FenceKind} {g g' : (valEnv L V).State} {u : Unit} :
    (valEnv L V).step (.fence k) g u g' ↔ True := Iff.rfl

end Kraken.SharedEnv

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- **The value invariant of a memory**: every message to an `L`-location,
and every initial value of one, is in `V`. -/
def MemVals (L : Loc → Prop) (V : Val → Prop) (m : Memory) : Prop :=
  (∀ l, L l → V (m.initVal l)) ∧ ∀ ts w, m.get? ts = some w → L w.loc → V w.val

/-- **The tree condition**: `L`-reads assumed in `V` (load values and RMW old
values), `L`-writes in `V` (an RMW's new value from a `V` old value), every
leaf `P`. A fault leaf is unconstrained. -/
def ValX {σ : Type} (L : Loc → Prop) (V : Val → Prop) (P : σ → Prop) : EvTree σ → Prop
  | .done s => P s
  | .fault _ => True
  | .choose _ k => ∀ i, ValX L V P (k i)
  | .load _ _ l ret => ∀ v, (L l → V v) → ValX L V P (ret v)
  | .store _ _ l v ret => (L l → V v) ∧ ∀ b, ValX L V P (ret b)
  | .rmw _ _ l op ret => ∀ old, (L l → V old) →
      (∀ new, op old = some new → L l → V new) ∧ ValX L V P (ret old)
  | .fence _ ret => ∀ u, ValX L V P (ret u)

variable {L : Loc → Prop} {V : Val → Prop}

/-- A read of a `MemVals` memory at an `L`-location returns a `V`-value. -/
theorem MemVals.read {m : Memory} (h : MemVals L V m) {l : Loc} {tr : Time} {v : Val}
    (hr : m.read? l tr = some v) (hl : L l) : V v := by
  unfold Memory.read? at hr
  split at hr
  · cases hr; exact h.1 l hl
  · split at hr
    · next w hw =>
      split at hr
      · next he =>
        cases hr
        have : w.loc = l := by simpa using he
        exact h.2 _ w hw (this ▸ hl)
      · cases hr
    · cases hr

/-- Appending a message with a `V`-value (if at an `L`-location) keeps
`MemVals`. -/
theorem MemVals.append {m : Memory} (h : MemVals L V m) {w : Msg} (hw : L w.loc → V w.val) :
    MemVals L V (m.append w).1 := by
  refine ⟨fun l hl => ?_, fun ts w' hg hl => ?_⟩
  · have : (m.append w).1.init = m.init := by simp [Memory.append]
    simp only [Memory.initVal, this]
    exact h.1 l hl
  · rcases Dispenser.get?_append_cases hg with ⟨-, hg⟩ | ⟨-, rfl⟩
    · exact h.2 ts w' hg hl
    · exact hw hl

/-- **`MemVals` at `L = ∅`** holds of every memory. -/
theorem memVals_empty (V : Val → Prop) (m : Memory) : MemVals (fun _ => False) V m :=
  ⟨fun _ h => h.elim, fun _ _ _ h => h.elim⟩

/-- **At `L = ∅`, `ValX` is `EvTree.All`**: no read or write condition. -/
theorem valX_of_all_empty {σ : Type} {P : σ → Prop} (V : Val → Prop) :
    ∀ {t : EvTree σ}, t.All P → ValX (fun _ => False) V P t
  | .done _, h => h
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => valX_of_all_empty V (h i)
  | .load _ _ _ _, h => fun v _ => valX_of_all_empty V (h v)
  | .store _ _ _ _ _, h => ⟨False.elim, fun b => valX_of_all_empty V (h b)⟩
  | .rmw _ _ _ _ _, h => fun old _ => ⟨fun _ _ h => h.elim, valX_of_all_empty V (h old)⟩
  | .fence _ _, h => fun u => valX_of_all_empty V (h u)

/-- `ValX` is monotone in the leaf condition. -/
theorem ValX.mono {σ : Type} {P P' : σ → Prop} (hP : ∀ s, P s → P' s) :
    ∀ {t : EvTree σ}, ValX L V P t → ValX L V P' t
  | .done s, h => hP s h
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => ValX.mono hP (h i)
  | .load _ _ _ _, h => fun v hv => ValX.mono hP (h v hv)
  | .store _ _ _ _ _, h => ⟨h.1, fun b => ValX.mono hP (h.2 b)⟩
  | .rmw _ _ _ _ _, h => fun old ho => ⟨(h old ho).1, ValX.mono hP (h old ho).2⟩
  | .fence _ _, h => fun u => ValX.mono hP (h u)

/-! ## Preservation by runs, steps and certified promises -/

section Steps

variable {A : Arch} {tid : Nat} {iv : InstrViews}

/-- A write with a `V`-value (if at an `L`-location) keeps `MemVals` of the
context's memory (a fulfilment leaves the memory unchanged). -/
theorem memVals_write {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) (hv : L l → V v)
    (hm : MemVals L V c.mem) : MemVals L V c'.mem := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, w, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · exact hm
  · exact hm.append hv


/-- **The value invariant of a configuration**: `MemVals` of the memory and
`P` of every thread state. -/
def ValInvAt (L : Loc → Prop) (V : Val → Prop) (P : I.State → Prop) (c : Config I) : Prop :=
  MemVals L V c.mem ∧ ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → P t.st

end Steps

end Kraken.Promising.SLR.EnvG
