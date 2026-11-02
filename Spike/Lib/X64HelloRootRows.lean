/-
**hello.w's spawn rows at the root records, x86-64** (the twin of `Spike/Lib/HelloRootRows.lean`):
`X64HelloW1Store.wstoreX_IR`'s and `X64HelloCompatI`'s per-record premises at
`ι := {g : Gh // X64HelloOkHR.okHR L.Λ lB T W g}`, with the instance's field choices `cS w = w.1.cS`, `cT w = w.1.cT`,
`cw w = w.1.cwW` / `w.1.cwM`, `SR w = wakeSR w.1` and `G w = wakeG G0 (cT w)`: each row is `GhOK`'s, or holds by
definition of hello's location data `helloP abi μ (helloLocs …)`.

- `cwv_okHR`: the worker's pointer word is a locative to `cS w` (`WCompat.cwv`, `hC_IR`'s `cwv`); `hcw_okHR`: the
  same for main's (`X64HelloMs.hC0Ms`'s `hcw`); `hcwE_okHR`: `wstoreX_IR`'s `hcw` (`∃ cS`).
- `cT_okHR`, `cTin_okHR`: `GhOK`'s `cS` placement and `cT` shared.
- `cTfoot_okHR`, `cSfrz_okHR`, `footLab_okHR`: `WakeP.wakeP_foot_c`, `wakeP_not_frzS_c`, `wakeP_footLab` at
  `helloLocs`' separation facts `hok` (`X64HelloMs.helloLocs_okG` at a record's `SelfOK`).
- `Gc_okHR`: `WCompatX.Gc` (`X64HelloWorkerRR.hx_IR`'s), `WakeG.wakeG_cT`.

Unlike AArch64: the records are x86-64 wake's (`X64WakeInst`, `X64WakeInstFields.GhOK`), the layout is
`X64.Rt.RuntimeLayout`, and the location data's ABI is `Scc.Sem.X64.abi`; the rows' proofs are unchanged.
-/
import Spike.Lib.X64HelloW1StoreX
import Spike.Lib.X64HelloOkHR
import Spike.Lib.X64HelloMs

namespace Spike.Lib.X64HelloRootRows

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64WakeInst Spike.Lib.WakeP Spike.Lib.Inv2Core
open Spike.Lib.X64HelloOkHR (okHR)
open Spike.Lib.X64HelloInst (helloP)
open Spike.Lib.X64HelloMs (helloLocs)
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {L : RuntimeLayout} {lB : WeakMem.AllocLabel} {T W : BitVec 64}

section Ghost

variable {cS : {g : Gh // okHR L.Λ lB T W g} → WeakMem.Address} {cT : {g : Gh // okHR L.Λ lB T W g} → Loc}
  {SR : {g : Gh // okHR L.Λ lB T W g} → SpawnRec} {cw : {g : Gh // okHR L.Λ lB T W g} → TermRun.Word}
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
  rw [hcT, hcS, hSR]; exact X64HelloOkHR.okHR_cT w

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
theorem footLab_okHR (hok : ∀ w, (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w)).OK) :
    ∀ w Lc, (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 1 Lc →
    InLabel (SR w).lbl (SR w).lsize Lc → Lc = cT w :=
  fun w _ hf hl => wakeP_footLab (hok w) hf hl

/-- **`WCompatX.Gc`** at a value invariant `wakeG G0 (cT w)`. -/
theorem Gc_okHR {G : ι → Loc → Val → Prop} {G0 : ι → Loc → Val → Prop}
    (hG : ∀ w, G w = WakeG.wakeG (G0 w) (cT w)) : ∀ w, G w (cT w) 1 := fun w => by
  rw [hG]; exact WakeG.wakeG_cT _

end Locs

end Spike.Lib.X64HelloRootRows

/-- info: 'Spike.Lib.X64HelloRootRows.hcwE_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootRows.hcwE_okHR

/-- info: 'Spike.Lib.X64HelloRootRows.cTin_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootRows.cTin_okHR

/-- info: 'Spike.Lib.X64HelloRootRows.cTfoot_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootRows.cTfoot_okHR

/-- info: 'Spike.Lib.X64HelloRootRows.cSfrz_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootRows.cSfrz_okHR


/-- info: 'Spike.Lib.X64HelloRootRows.cwv_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootRows.cwv_okHR

/-- info: 'Spike.Lib.X64HelloRootRows.hcw_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootRows.hcw_okHR

/-- info: 'Spike.Lib.X64HelloRootRows.cT_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootRows.cT_okHR

/-- info: 'Spike.Lib.X64HelloRootRows.footLab_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootRows.footLab_okHR

/-- info: 'Spike.Lib.X64HelloRootRows.Gc_okHR' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootRows.Gc_okHR
