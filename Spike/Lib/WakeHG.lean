/-
**`WakeHPre.hpre_of`'s `hG` at wake's guarantee** (AArch64):
the pre-spawn data's guarantee `D.G = WakeOG.gW hp i cT` lies below the
clone's record's `wakeG' hp i g`, for every record `g`.

The pre-spawn guarantee's word `cT` (`wakeG G0 cT`: any value at `cT`,
elsewhere `G0 = GOf2 L m0`) is fixed per entry, while the record's flag
word `g.cT` is the run's placed address of `c`'s label. They need not
agree: `G0` already holds of every value at every heap and `.data` word
(`WakeOG.hGpl_ofPlaceW2`; `GOf2` only constrains the runtime's words and
the two limit words, all pinned). So at a heap word `cT`, `wakeG G0 cT`
and `G0` coincide, and `G0` is below `wakeG G0 g.cT` for any `g.cT`.

`cTW hp i`, the root's `cT`, is therefore a **dummy heap word** (the
arena's first word, `Λ.heap.lo`), not the flag's address: no use of the
pre-spawn `D.G` (the relation's `MemInv`, `msOfA`'s values, `SFactsACH`,
`OPrem.hGpl`, the load's `MemInv`) needs the flag's word there.

- `cTW`, `cTW_heap`: the dummy word, in the heap;
- `gW_le`: `gW hp i (wordLoc a)` at a heap or `.data` word `a` is below
  `wakeG G0 cT'` for every `cT'`;
- `memInv_gW`: `MemInv` moved along it to `wakeG' hp i g`, for every `g`.
-/
import Spike.Lib.WakeOG
import Spike.Lib.WakeInst
import Spike.Lib.Rt.A64ArenaOfPlaceW

namespace Spike.Lib.WakeHG

open Kraken Kraken.Promising
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeInst (Gh wakeG')

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **The root's pre-spawn `cT`**: a dummy heap word, the arena's first
(see the module doc). -/
def cTW : Loc := Scc.Sem.wordLoc (Ly).Λ.heap.lo

/-- The dummy word is in the heap. -/
theorem cTW_heap : (Ly).Λ.heap.contains (Ly).Λ.heap.lo := by
  have h := Spike.Lib.A64.Rt.ArenaW.arOf_sub (PlaceW.link i hp)
  simp only [Spike.Lib.A64.Rt.arOf, Spike.Lib.Arena.ofWords, Scc.Sem.Range.Sub] at h
  change Λ0.heap.contains Λ0.heap.lo
  simp only [Scc.Sem.Range.contains]
  have : 0 < Scc.Cert.PlaceOK.allocCells := by decide
  constructor <;> omega

/-- **The pre-spawn guarantee at a heap or `.data` word is below every
flag word's.** -/
theorem gW_le (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) {a : Nat}
    (ha : (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a) (cT' : Loc) :
    ∀ L v, WakeOG.gW hp i (Scc.Sem.wordLoc a) L v →
      WakeG.wakeG (WakeGOf2.GOf2 (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ o.prog o.secs)) cT' L v := by
  rintro L v (rfl | h)
  · exact .inr (WakeOG.hGpl_ofPlaceW2 hp i hpin2 a v ha)
  · exact .inr h

/-- **`hpre_of`'s `hG`**: `MemInv` of the pre-spawn guarantee at the dummy
word gives `MemInv` of every record's `wakeG'`. -/
theorem memInv_gW (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (g : Gh)
    {m : Memory} (h : MemInv (WakeOG.gW hp i (cTW hp i)) m) : MemInv (wakeG' hp i g) m :=
  ⟨fun l => gW_le hp i hpin2 (.inl (cTW_heap hp i)) g.cT _ _ (h.1 l),
    fun w hw => gW_le hp i hpin2 (.inl (cTW_heap hp i)) g.cT _ _ (h.2 w hw)⟩

end Spike.Lib.WakeHG

/-- info: 'Spike.Lib.WakeHG.memInv_gW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeHG.memInv_gW
