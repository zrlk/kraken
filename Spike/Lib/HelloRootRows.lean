/-
**hello.w's spawn rows at the root records** (`HelloW1StoreX.wstoreX_IR`'s
and `HelloCompatI`'s per-record premises at `ι := {g : Gh // HelloOkHR.okHR
L.Λ lB g}`, with the instance's field choices `cS w = w.1.cS`, `cT w =
w.1.cT`, `cw w = w.1.cwW` / `w.1.cwM`, `SR w = wakeSR w.1` and
`G w = wakeG G0 (cT w)`): each row is `GhOK`'s, or holds by definition of
hello's location data `helloP abi μ (helloLocs …)` (as wake's
`WakeInst.cTfoot_I`, `cSfrz_I`, `footLab_I`, `WakeInstFields.Gc_I`).

- `cwv_okHR`: the worker's pointer word is a locative to `cS w`
  (`WCompat.cwv`, `hC_IR`'s / `hC_IP`'s `cwv`); `hcw_okHR`: the same for
  main's (`HelloMs.hC0Ms`'s / `HelloCompatI.hC0P`'s `hcw`); `hcwE_okHR`:
  `wstoreX_IR`'s `hcw` (`∃ cS`).
- `cT_okHR`, `cTin_okHR`: `GhOK`'s `cS` placement and `cT` shared.
- `cTfoot_okHR`, `cSfrz_okHR`, `footLab_okHR`: `WakeP.wakeP_foot_c`,
  `wakeP_not_frzS_c`, `wakeP_footLab` at `HelloMs.helloLocs_ok`.
- `Gc_okHR`: `WCompatX.Gc` (`HelloWorkerRR.hx_IR`'s), `WakeG.wakeG_cT`.
-/
import Spike.Lib.HelloW1StoreX
import Spike.Lib.HelloOkHR

namespace Spike.Lib.HelloRootRows

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.WakeInst Spike.Lib.WakeP Spike.Lib.Inv2Core
open Spike.Lib.HelloOkHR (okHR)
open Spike.Lib.HelloInst (helloP)
open Spike.Lib.HelloMs (helloLocs helloLocs_ok)
open Spike.Lib.A64.Rt (RuntimeLayout)

variable {L : RuntimeLayout} {lB : WeakMem.AllocLabel}

section Ghost

variable {cS : {g : Gh // okHR L.Λ lB g} → WeakMem.Address} {cT : {g : Gh // okHR L.Λ lB g} → Loc}
  {SR : {g : Gh // okHR L.Λ lB g} → SpawnRec} {cw : {g : Gh // okHR L.Λ lB g} → TermRun.Word}
  (hcS : ∀ w, cS w = w.1.cS)

include hcS in
/-- **The worker's pointer word** (`WCompat.cwv`) at `cw w = w.1.cwW`. -/
theorem cwv_okHR (hcw : ∀ w, cw w = w.1.cwW) : ∀ w, (cw w).val = .loc (cS w) 0 := fun w => by
  rw [hcw, hcS]; exact w.2.1.2.1

include hcS in
/-- **main's pointer word** (`WCompat0.cw0`) at `cw w = w.1.cwM`. -/
theorem hcw_okHR (hcw : ∀ w, cw w = w.1.cwM) : ∀ w, (cw w).val = .loc (cS w) 0 := fun w => by
  rw [hcw, hcS]; exact w.2.1.1

/-- `wstoreX_IR`'s `hcw`: the worker's word is an untagged locative. -/
theorem hcwE_okHR (hcw : ∀ w, cw w = w.1.cwW) : ∀ w, ∃ c, (cw w).val = .loc c 0 := fun w =>
  ⟨w.1.cS, by rw [hcw]; exact w.2.1.2.1⟩

include hcS in
/-- **`WCompat.cT`**: `cS w` placed, `cT w` its word. -/
theorem cT_okHR (hcT : ∀ w, cT w = w.1.cT) (hSR : ∀ w, SR w = wakeSR w.1) :
    ∀ w, ∃ a, cT w = wordLoc a ∧ wordAddr (SR w).lbl (cS w) = some a ∧
      (cS w).offset < (SR w).lsize (cS w).label := fun w => by
  rw [hcT, hcS, hSR]; exact HelloOkHR.okHR_cT w

/-- **`WCompat.cTin`**: `cT w` shared. -/
theorem cTin_okHR (hcT : ∀ w, cT w = w.1.cT) : ∀ w, Consumer1.LocIn L.Λ.shared (cT w) := fun w => by
  rw [hcT]; exact w.2.1.2.2.2.2

end Ghost

section Locs

variable {ι : Type} {μ : Marks} {SR : ι → SpawnRec} {cT : ι → Loc} {cS : ι → WeakMem.Address}

/-- **`WCompat.cTfoot`** at hello's location data. -/
theorem cTfoot_okHR : ∀ w, (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 1 (cT w) :=
  fun _ => wakeP_foot_c

/-- **`WCompat.cSfrz`** at hello's location data. -/
theorem cSfrz_okHR : ∀ w, ¬ (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).frzS (cS w) :=
  fun _ => wakeP_not_frzS_c

/-- **`WCompat.footLab`** at hello's location data. -/
theorem footLab_okHR : ∀ w Lc, (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 1 Lc →
    InLabel (SR w).lbl (SR w).lsize Lc → Lc = cT w :=
  fun w _ hf hl => wakeP_footLab (helloLocs_ok L (SR w).lbl (SR w).lsize (cT w) (cS w)) hf hl

/-- **`WCompatX.Gc`** at a value invariant `wakeG G0 (cT w)`. -/
theorem Gc_okHR {G : ι → Loc → Val → Prop} {G0 : ι → Loc → Val → Prop}
    (hG : ∀ w, G w = WakeG.wakeG (G0 w) (cT w)) : ∀ w, G w (cT w) 1 := fun w => by
  rw [hG]; exact WakeG.wakeG_cT _

end Locs

end Spike.Lib.HelloRootRows

/-- info: 'Spike.Lib.HelloRootRows.cwv_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootRows.cwv_okHR

/-- info: 'Spike.Lib.HelloRootRows.hcw_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootRows.hcw_okHR

/-- info: 'Spike.Lib.HelloRootRows.cT_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootRows.cT_okHR

/-- info: 'Spike.Lib.HelloRootRows.footLab_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootRows.footLab_okHR

/-- info: 'Spike.Lib.HelloRootRows.Gc_okHR' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.HelloRootRows.Gc_okHR
