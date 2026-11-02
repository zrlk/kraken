/-
**`ZObl` at `X := AbX μ lab`** (x86-64; the twin of `Spike/Lib/A64HelloAbOblZ.lean`, `X64HelloAbObl`'s recipe):
the spawned child's run keeps the worker's abort facts at every node, assembled from the stub and the thread
worker (`child_abX`, `thrPro_abX`, `thrHead_abX`, `thrTail_abX`), `wc_worker` (`wcPro_abX`, `wE_abX`,
`wCall_abX`, `tail_abX`, `unpk_abX`), `print` and the write abort (`print_abX`, `abortObl_abXH`), the slice's
words times 8 below `2^63` (`hm`, `ChildPrem.hm`).

- `wcLen_lt`: `print`'s count at `wc_worker`'s call below `2^63`.
- `wcObl_abX`: `WcObl (AbX μ lab)` in every `wc_worker` sub-region at the return address `.x13`.
- `zObl_abX`: `ZObl (AbX μ lab)` in a region of the child's stub's frame.

Unlike AArch64 (a 16-aligned region, the worker's sub-regions from `-192` and the stub's from `-224`, the count in
`x1`, `print`'s nodes from the caller's `x30`, the return address `.sp0`), the regions need no alignment and reach
`8` above the base, the worker's sub-regions are from `-176` and the stub's from `-128` (the thread worker's in
`thrR R`, `8` bytes up), the count is `%rsi`, `print`'s return address is the caller's cell `-96`, and the thread
worker's return address is `.x13`.
-/
import Spike.Lib.X64HelloAbOblP
import Spike.Lib.X64HelloAbOblAb

namespace Spike.Lib.X64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib (Region FragS)
open Spike.Lib.X64 (AS)
open Spike.Lib.X64.Flow.Worker.Hello.SegRP (WcObl ZObl)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.X64.Flow.Worker.Wake.Child (thrR thrR_ok)
open SccCode (helloCells)

/-- **`print`'s count at `wc_worker`'s call is below `2^63`**: `%rsi` is at most the slice's words times 8
(`Body.wkC_rsi_lt`), the words the frame's `-32` cell (`wkJ`). -/
theorem wcLen_lt {lab : Label → Int64} {c0 : Ctl} {w : Words} {rbp ra tp sp : BitVec 64} {Kc : AS → Ctl → Prop}
    {σC : AS} {c : Ctl} (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hJ : (Body.wCall lab (wkJ c0 w rbp ra tp sp) Kc).J σC c) :
    (σC.regs.get64 .rsi).toNat < 2 ^ 63 := by
  obtain ⟨⟨σ0, c0', fl, hJ0, rfl⟩, -⟩ := hJ
  exact Body.wkC_rsi_lt lab σ0 fl (by rw [hJ0.2.2.2.1]; exact hm)

section Z

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
  (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

/-- **`WcObl` at `AbX`**: `wc_worker` in a region of its frame and its calls' (`R'.lo ≤ -176`), the return
address `.x13` (`hra`), the slice's words times 8 below `2^63` (`hm`). -/
theorem wcObl_abX {ms : List TermRun.Frame → MemSide isa} {R' : Region} {F' : MachineData → Prop}
    (hR : R'.OK) (hlo : R'.lo ≤ -176) (hhi : 8 ≤ R'.hi) {rbp ra : BitVec 64}
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13")
    {w : Words} {tp sp0 : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hm : w.w2.toNat * 8 < 2 ^ 63) :
    WcObl (AbX μ (_root_.Executable.labels exe).label) exe endPc ms R' F' rbp ra w tp sp0 w0 w1 w2 w3 w4 n m where
  hz := wcPro_abX hp hend hlab hμ hR (by omega) (by omega)
  hZE := wE_abX hp hend hlab hμ hR (by omega) hhi
  hZC := wCall_abX hp hend hlab hμ hR (by omega) hhi
  hZP _ _ _ hR'' hlo'' hhi'' hF'' _ _ _ _ _ hJ _ i :=
    print_abX hlab hp hend hμ hF'' hR'' hlo'' hhi'' (wcLen_lt hm hJ) (wcRet_abX hlab hp hJ) i
  hZA _ _ _ _ hloA hhiA _ _ _ _ _ _ _ _ _ _ _ := abortObl_abXH hp hμ hloA hhiA
  hZW i := tail_abX hp hend hlab hμ hR (by omega) hhi hra i
  hZU _ _ hC _ _ hra' i := unpk_abX hp hend hlab hμ hC.ok hC.lo hC.hi hra' i

/-- **`ZObl` at `AbX`**: the spawned child's run in a region of the stub's frame (`R.lo ≤ -128`), the thread
worker in `thrR R`, the slice's words times 8 below `2^63` (`hm`). -/
theorem zObl_abX {ms : List TermRun.Frame → MemSide isa} {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    {w : Words} {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hm : w.w2.toNat * 8 < 2 ^ 63) :
    ZObl (AbX μ (_root_.Executable.labels exe).label) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m := by
  have hRt := thrR_ok hR (by omega : R.lo ≤ -8) (by omega : -8 < R.hi)
  have hlot : (thrR R).lo ≤ -120 := show R.lo + 8 ≤ -120 by omega
  have hhit : 8 ≤ (thrR R).hi := show 8 ≤ R.hi + 8 by omega
  exact
    { hZc := fun i => child_abX hp hend hlab hμ hR hlo hhi i
      hzT := thrPro_abX hp hend hlab hμ hRt (by omega) (by omega)
      hZEt := thrHead_abX hp hend hlab hμ hRt (by omega) hhit .e
      hZT := fun i => thrTail_abX hp hend hlab hμ hRt (by omega) hhit i
      hwc := fun _ _ hR' hlo' hhi' _ _ _ _ hra => wcObl_abX hp hend hlab hμ hR' hlo' hhi' hra hm }

end Z

end Spike.Lib.X64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcLen_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcLen_lt

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcObl_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcObl_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.zObl_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.zObl_abX
