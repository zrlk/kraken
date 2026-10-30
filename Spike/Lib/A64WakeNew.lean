/-
**The box's initialising store of wake's start segment** (AArch64;
`OpenW.hnew0`, `hctr0`'s `hSt`): the store disjunct of `CtxW` is `StAt`, the
store's premises `NewStM` at the reference memory side `ref` with its
allocation fragment a landing predicate `Lnd` the start admits (`Gs`:
the store node's next node, as `Alloc.newStM_nd` gives it). The store
writes a cell of the arena, above the counter word (`stAt_noWr`); at the
counter add the instruction writes the counter (`ctrAt_wr`); so `hnew0` is
the store's `NewStM` moved to `h0`'s memory side, its landing in `I2`'s
`inv1` disjunct (`hland1`).

- `StAt`: the store's states.
- `stAt_noWr`: the store writes no counter (`hctr0_of`'s `hSt`).
- `ctrAt_wr`: the counter add writes the counter.
- `hnew0_of`: `OpenW.hnew0`'s shape at `Ctx := CtxW … (StAt …)`.
-/
import Spike.Lib.A64WakeCtr
import Spike.Lib.OutNew

namespace Spike.Lib.A64.WakeCtr

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Sem.A64 (abi)
open Spike.Lib (Region FrameRun MemSide Arena FragS Frag)
open Spike.Lib.A64ConsumerA (CtrRow PendA WrAt msOfA I2 ArenaW)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (At)
open Spike.Lib.A64.Alloc (Call Code N)

/-- **The box store's states** of the start (no frames): the store's
premises at `ref` with the allocation fragment a landing `Lnd` that `Gs`
admits. -/
def StAt (ref : MemSide isaLSE2) (p : Prog) (lbl : Lbl)
    (Gs : (WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2) → Prop) : FragS isaLSE2 := fun s c fs =>
  fs = [] ∧ ∃ Lnd, Gs Lnd ∧ NewStM p lbl { ref with xa := Lnd } s c

variable {ref : MemSide isaLSE2} {p : Prog} {lbl : Lbl}
  {Gs : (WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2) → Prop} {ar : Arena}

/-- **The box's store writes no counter**: it writes a cell at or above the
arena's base (`ref.heap`), the counter word below it (`hlt`). -/
theorem stAt_noWr (hlt : ar.ctr + 8 ≤ ref.heap) (h64 : ar.ctr < 2 ^ 64) :
    ∀ s c fs, StAt ref p lbl Gs s c fs → ¬ WrAt s ar.ctrLoc := by
  rintro s c fs ⟨-, Lnd, -, kr, A, V, s', x, a, ty, e, w, wold, old, -, hex, -, -, -, -, -, -, -, hA, -, -⟩ hW
  rcases hW with ⟨kr', V', s'', he⟩ | ⟨k, op, g, he⟩
  · rw [hex] at he
    simp only [Option.some.injEq, EvTree.store.injEq] at he
    have hL := congrArg Loc.addr he.2.2.1
    simp only [Arena.ctrLoc] at hL
    have : A.toNat = ar.ctr := by rw [hL, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
    simp only at hA
    omega
  · rw [hex] at he
    simp at he

variable {exe : _root_.Executable} {endPc : Int64}
  {Gc : MemSide isaLSE2 → Region → (MachineData → Prop) → Call → Prop}

/-- **The counter add writes the counter** (`ctrRow_allocS_n4`'s step), at
a memory side `ref` but for `xa` whose counter is the arena's (`hc`). -/
theorem ctrAt_wr (hcode : ∀ ms0 q, Code ms0 q exe endPc) (hc : ref.ctr = ar.ctr) :
    ∀ s c fs, CtrAt ref exe endPc Gc s c fs → WrAt s ar.ctrLoc := by
  rintro s c fs ⟨-, ms0, R, F, q, hms, -, hok, hAt⟩
  obtain ⟨k, op, g, -, -, -, -, h1, -⟩ := ctrRow_allocS_n4 hok.fst hok.okb.toS (hcode ms0 q) hok.mem hAt
  have e : ms0.ctr = ar.ctr := (congrArg MemSide.ctr hms).trans hc
  refine .inr ⟨k, op, g, ?_⟩
  rw [h1, e]; rfl

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Spike.Lib.A64ConsumerS.OwnS} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isaLSE2}
  {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}

/-- **`OpenW.hnew0` at `Ctx := CtxW ref … (StAt ref …)`** (`ref` the
reference side `msOfA` at no fragment, at `L0`, `ls0`): the counter add
writes the counter (`ctrAt_wr`); at the store the frame run stays put (a
box `new`) and the store's `NewStM` holds at `h0`'s side but for `xa`, its
landings `Lnd` in `h0`'s fragment (`hland1`: in `I2`'s `inv1` disjunct, for
the landings `Gs` admits). `inv0` itself is not used. -/
theorem hnew0_of (hcode : ∀ ms0 q, Code ms0 q exe endPc)
    (hland1 : ∀ Lnd, Gs Lnd → ∀ l A s' c', L0 l = none → Lnd l A 1 s' c' →
      (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 []).xa l A 1 s' c') :
    ∀ s c fs, inv0 s c fs →
      CtxW (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 []) exe endPc Gc
        (StAt (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 []) p L0 Gs) s c fs →
      ¬ WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      ∀ L, WrAt s L → ¬ ArenaW ar L0 ls0 c' L →
        NewStM p L0 (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 fs') s c' := by
  intro s c fs _ hC hW c' fs' hr _ _ _ _
  obtain ⟨rfl, Lnd, hG, kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
    hX⟩ := hC.resolve_left fun h => hW (ctrAt_wr hcode rfl s c fs h)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht)
  exact ⟨kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
    fun l hl => hland1 Lnd hG l _ _ _ hl (hX l hl)⟩

end Spike.Lib.A64.WakeCtr

/-- info: 'Spike.Lib.A64.WakeCtr.stAt_noWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeCtr.stAt_noWr

/-- info: 'Spike.Lib.A64.WakeCtr.ctrAt_wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeCtr.ctrAt_wr

/-- info: 'Spike.Lib.A64.WakeCtr.hnew0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeCtr.hnew0_of
