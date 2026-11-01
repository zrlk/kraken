/-
**`ZObl` at `X := AbX μ lab`** (row 5i-hab1, P5, AArch64; `A64HelloAbObl`'s recipe): the
spawned child's run keeps the worker's abort facts at every node, assembled from P2 (`child_abX`,
`thrPro_abX`, `thrHead_abX`, `thrTail_abX`), P3 (`wcPro_abX`, `wE_abX`, `wCall_abX`, `tail_abX`, `unpk_abX`),
P4 (`wcPrint_abX`, `abortObl_abXH`), the slice's words below `2^60` (`hm`, `ChildPrem.hm`).

- `wcObl_abX`: `WcObl (AbX μ lab)` in every `wc_worker` sub-region at the return address `.sp0`.
- `zObl_abX`: `ZObl (AbX μ lab)` in a region of the child's stub's frame.
-/
import Spike.Lib.A64HelloAbOblP
import Spike.Lib.A64HelloAbOblU
import Spike.Lib.A64HelloAbOblAb

namespace Spike.Lib.A64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Region FragS)
open Spike.Lib.A64.Flow (AS)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (WcObl ZObl)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open SccCode (helloProg)

/-- **`print`'s count at `wc_worker`'s call is below `2^63`**: `x1` is the slice's words times 8 (`wkC_x1_lt`),
the words the frame's `-80` cell (`wkJ`). -/
theorem wcLen_lt {lab : Label → Int64} {c0 : Ctl} {w : Words} {x29 ra tp : BitVec 64} {Kc : AS → Ctl → Prop}
    {σC : AS} {c : Ctl} (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hJ : (Body.wCall lab (Spike.Lib.A64.Flow.Worker.Hello.Wk.wkJ c0 w x29 ra tp) Kc).J σC c) :
    σC.regs.X1.toBitVec.toNat < 2 ^ 63 := by
  obtain ⟨⟨σ0, c0', ⟨-, -, -, h80, -⟩, rfl⟩, -⟩ := hJ
  exact Body.wkC_x1_lt lab σ0 (by rw [h80]; exact hm)

section P5

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

/-- **`WcObl` at `AbX`**: `wc_worker` in a region of its frame and its calls' (`R'.lo ≤ -192`), the return
address `.sp0` (`hra`), the slice's words below `2^60` (`hm`). -/
theorem wcObl_abX {ms : List TermRun.Frame → MemSide isaLSE2} {R' : Region} {F' : MachineData → Prop}
    (hR : R'.OK) (hal : R'.base.toNat % 16 = 0) (hlo : R'.lo ≤ -192) (hhi : 0 ≤ R'.hi)
    {x29 ra : BitVec 64} (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0"))
    {w : Words} {tp sp0 : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hm : w.w2.toNat * 8 < 2 ^ 63) :
    WcObl (AbX μ (_root_.Executable.labels exe).label) exe endPc ms R' F' x29 ra w tp sp0 w0 w1 w2 w3 w4 n m where
  hz := wcPro_abX hp hend hlab hμ hR hal (by omega) hhi
  hZE := wE_abX hp hend hlab hμ hR hal (by omega) hhi
  hZC := wCall_abX hp hend hlab hμ hR hal hlo hhi
  hZP _ _ _ hR'' hal'' hlo'' hhi'' hF'' _ _ _ _ _ hJ _ i :=
    print_abX hlab hp hend hμ hF'' hR'' hal'' hlo'' hhi'' (wcLen_lt hm hJ) (wcRet_abX hlab hJ) i
  hZA _ _ _ _ _ hloA hhiA _ _ _ _ _ _ _ _ _ _ _ := abortObl_abXH hp hμ hloA hhiA
  hZW i := tail_abX hp hend hlab hμ hR hal (by omega) hhi hra i
  hZU _ _ hR'' hal'' hlo'' hhi'' _ _ _ _ hra' i := unpk_abX hp hend hlab hμ hR'' hal'' hlo'' hhi'' hra' i

/-- **`ZObl` at `AbX`**: the spawned child's run in a region of the stub's frame (`R.lo ≤ -224`), the slice's
words below `2^60` (`hm`). -/
theorem zObl_abX {ms : List TermRun.Frame → MemSide isaLSE2} {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi)
    {w : Words} {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hm : w.w2.toNat * 8 < 2 ^ 63) :
    ZObl (AbX μ (_root_.Executable.labels exe).label) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m where
  hZc i := child_abX hp hend hlab hμ hR hal hlo hhi i
  hzT := thrPro_abX hp hend hlab hμ hR hal (by omega) hhi
  hZEt := thrHead_abX hp hend hlab hμ hR hal hlo hhi .e
  hZT i := thrTail_abX hp hend hlab hμ hR hal (by omega) hhi i
  hwc _ _ hR' hal' hlo' hhi' _ _ _ _ hra := wcObl_abX hp hend hlab hμ hR' hal' hlo' hhi' hra hm

end P5

end Spike.Lib.A64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.zObl_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.zObl_abX
