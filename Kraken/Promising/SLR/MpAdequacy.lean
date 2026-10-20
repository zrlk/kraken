/-
**Message passing under `Arch.armv8`**: at every reachable final
configuration the reader has loaded `1` and the data word's final value is
`1` (`mp_armv8`).

Assembly (`theorem1IIPure_of_relWrites`, through the generic
`final_of_relWrites`):

- scope (`NTFree`): `Config.ntFree_armv8`;
- initial erasure: `erase_mpInit` (`SLR/MpInit.lean`);
- the per-instruction purity condition: `mpReach_reachable`, `mp_cell`
  (`SLR/MpPure.lean`);
- `NPSafe`: `mpW_npsafe` (writer, `ThreadRuleRX`) and `mpR_npsafe` (reader,
  `ThreadRuleR`) from the initial invariants (`SLR/MpRule.lean`).

At the final configuration both threads are done, so both satisfy `MpPost`.
They cannot both hold all of `W` (validity, `Erase.q_add_le_one`), so one
gives the reader's disjunct: `W4 = 1`, a seen non-zero flag message and an
acquire id `ι` of `Fl` with predicate `φ`. The total then holds `ι` exactly
once, so the flag message carries a slot for `ι` with all of `Dt` and maximal
write `(1, ts)` (`slot_of_seen`); that is the total's maximal write of `Dt`
(`total_max_of_slot`), hence its final value (`Erase.finalVal_of_max`).

The spin loop needs no bound: Theorem 1′ speaks about final configurations.

`mp_final` is in `SLR/MpSpec.lean` (moved unchanged).
-/
import Kraken.Promising.SLR.MpPure
import Kraken.Promising.SLR.Theorem1Final

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.Spinlock

variable (lW lR : _root_.Layout) [hw : Executable.ValidLayout (lW mpWriter)]
  [hr : Executable.ValidLayout (lR mpReader)]

/-- **Message passing under `Arch.armv8`**: the writer (thread `0`, laid out
by `lW`) and the reader (thread `1`, laid out by `lR`) started at their
programs with `X0 = f`, `X1 = d` (`FrameW`, `FrameR`), from an initial memory
with the flag at `0`: at every reachable final configuration the reader's
`W4` is `1` and the data word's final value is `1`. -/
theorem mp_armv8 {fuel : Nat} (P : Params) (hL : MpLocs P) {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : FrameW (layout := lW) P sW ∧ AtPos (layout := lW) mpWriter sW 0)
    (hR : FrameR (layout := lR) P sR ∧ AtPos (layout := lR) mpReader sR 0)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal P.Fl = 0)
    {c : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sR] initMem) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal P.Dt = 1#128 := by
  have hsafe : ∀ tid, tid < [sW, sR].length → ∀ n m, NPSafe (model isa) Arch.armv8 (MpPost P 1) tid n m True
      (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem P tid) (mpGhost P) := by
    intro tid htid n m
    rcases tid with _ | _ | k
    · exact mpW_npsafe (layout := lW) P Arch.armv8 0 1 hL (by decide) (by decide) n m
        (invXW_init (layout := lW) hL hW.1 hW.2)
    · exact mpR_npsafe (layout := lR) P Arch.armv8 1 (by decide) (by decide) n m
        (invR_init (layout := lR) hR.1 hR.2)
    · simp only [List.length_cons, List.length_nil] at htid; omega
  exact final_of_relWrites (I := isa) Arch.armv8 fuel (B := MpPost P 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal P.Dt = 1#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_mpInit P _ hF0) pend_mpGhost
    (MpReach lW lR P) (fun _ hc' _ _ ht => mpReach_reachable lW lR P hW hR hc' ht) (mp_cell lW lR P hL Arch.armv8)
    hsafe hc hf fun _ _ E' hle hsize hB => mp_final E' hf hsize (by rw [hle.rel]; exact mpGhost_rel_Fl) hB

end Kraken.Promising.SLR.Mp
