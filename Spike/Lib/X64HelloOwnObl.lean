/-
**`ZObl` at `X := OwnW W`** (x86-64; `X64HelloAbOblZ`'s recipe at the worker's own word): the spawned child's run
writes nothing at `⟨W, 8⟩` off a system call at every node, assembled from the stub and the thread worker
(`child_ownH`, `thrPro_ownH`, `thrHead_ownH`, `thrTail_ownH`), `wc_worker` (`wcPro_ownH`, `wE_ownH`, `wCall_ownH`,
`tail_ownH`, `unpk_ownH`), `print` and the write abort (`print_ownH`, `abortObl_ownH`). The three shared writes
are premises: `wc_worker`'s flag at `w.w4` (`hA`), `scc_rt_unpark`'s exchange at `w.w5 + 16` (`hB`), the thread
tail's store at `tp + 24` (`htp`).

- `wcObl_own`: `WcObl (OwnW W)` in every `wc_worker` sub-region.
- `zObl_own`: `ZObl (OwnW W)` in a region of the child's stub's frame.

Unlike `zObl_abX`, no marks, labels or count bound are asked (`OwnW` is a fact of the instruction alone), and
`wcObl_own` takes no return address.
-/
import Spike.Lib.X64HelloOwnZP
import Spike.Lib.X64HelloWorkerSegRP

namespace Spike.Lib.X64.Flow.Worker.Hello.OwnZH

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib (Region FragS)
open Spike.Lib.X64.Flow.Worker.Hello.SegRP (WcObl ZObl)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.X64.Flow.Worker.Wake.Child (thrR thrR_ok)
open Spike.Lib.X64.Flow.Worker.Wake.OwnW (OwnW)

variable {W : BitVec 64} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
include hp hend

/-- **`WcObl` at `OwnW W`**: `wc_worker` in a region of its frame and its calls' (`R'.lo ≤ -176`), its flag's
store off `W` (`hA`), `scc_rt_unpark`'s exchange off `W` (`hB`). -/
theorem wcObl_own {ms : List TermRun.Frame → MemSide isa} {R' : Region} {F' : MachineData → Prop}
    (hR : R'.OK) (hlo : R'.lo ≤ -176) (hhi : 8 ≤ R'.hi) {rbp ra : BitVec 64}
    {w : Words} {tp sp0 : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hA : w.w4 ≠ W) (hB : w.w5 + 16#64 ≠ W) :
    WcObl (fun s c _ => OwnW W s c) exe endPc ms R' F' rbp ra w tp sp0 w0 w1 w2 w3 w4 n m where
  hz := wcPro_ownH hp hend hR (by omega) (by omega)
  hZE := wE_ownH hp hend hR (by omega) hhi
  hZC := wCall_ownH hp hend hR (by omega) hhi
  hZP _ _ _ hR'' hlo'' hhi'' _ _ _ σC _ _ _ _ i := by
    cases i
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .e
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .n1
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .loop
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .n3
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .write
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .sys
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .n5
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .n6
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .chk2
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .n8
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .chk3
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .n10
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .adv
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .fail
    · exact print_ownH hp hend hR'' hlo'' hhi'' (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := σC.regs.rbp.toBitVec)
        (ra := σC.slot (-96)) .done
  hZA _ _ _ hRA hloA hhiA _ _ _ _ _ _ _ _ _ _ _ := abortObl_ownH hp hend hRA hloA hhiA
  hZW i := tail_ownH hp hend hR (by omega) hhi hA i
  hZU _ _ hC _ _ _ i := unpk_ownH hp hend hC.ok hC.lo hC.hi hB i

/-- **`ZObl` at `OwnW W`**: the spawned child's run in a region of the stub's frame (`R.lo ≤ -128`), the thread
worker in `thrR R`, the three shared writes off `W` (`hA`, `hB`, `htp`). -/
theorem zObl_own {ms : List TermRun.Frame → MemSide isa} {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    {w : Words} {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hA : w.w4 ≠ W) (hB : w.w5 + 16#64 ≠ W) (htp : tp + 24#64 ≠ W) :
    ZObl (fun s c _ => OwnW W s c) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m := by
  have hRt := thrR_ok hR (by omega : R.lo ≤ -8) (by omega : -8 < R.hi)
  have hlot : (thrR R).lo ≤ -120 := show R.lo + 8 ≤ -120 by omega
  have hhit : 8 ≤ (thrR R).hi := show 8 ≤ R.hi + 8 by omega
  exact
    { hZc := fun i => child_ownH hp hend hR hlo hhi i
      hzT := thrPro_ownH hp hend hRt (by omega) (by omega)
      hZEt := thrHead_ownH hp hend hRt (by omega) hhit .e
      hZT := fun i => thrTail_ownH hp hend hRt (by omega) hhit htp i
      hwc := fun _ _ hR' hlo' hhi' _ _ _ _ _ => wcObl_own hp hend hR' hlo' hhi' hA hB }

end Spike.Lib.X64.Flow.Worker.Hello.OwnZH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.OwnZH.wcObl_own' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.OwnZH.wcObl_own

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.OwnZH.zObl_own' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.OwnZH.zObl_own
