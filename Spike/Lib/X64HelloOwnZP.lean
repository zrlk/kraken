/-
**No write to the worker's own word at `print` and the write abort, x86-64** (the `print`/abort part of
`Spike/Lib/X64HelloOwnZ.lean`, in the manner of `Spike/Lib/X64HelloRelZP.lean`): the fact `OwnW W s c` at every
node of `scc_rt_print` and of the write abort's path, in the `NodeZA`/`AbortObl` form `X64HelloWorkerSegRP`'s
`WcObl` takes. Every block is covered (it runs to `.done`: its stack accesses hit the private memory; neither
writes to shared memory), the abort stub's `leaq` runs to `.done`, and the `syscall`s fault.

- `print_ownH`: at a node with `Print.N`'s pc and offsets and any invariant `J`, in a region covering `print`'s
  frame (`RelZH.print_relH`'s nodes and region).
- `abortObl_ownH`: `AbortObl (OwnW W)` at hello's cells for any source control, in the stub's region
  (`AbortObl.ofPc`'s premises, less its `hZ` and `hF`).

Unlike `AbortObl.ofPc` (a pc-only `Z` from `RelWS`), the nodes' facts are proved directly (`blkZA_done` with
`ownW_done`, `ownW_syscall`), so no fact of the pc in `abortRuns` and no frame stability is asked.
-/
import Spike.Lib.X64HelloOwnZ
import Spike.Lib.X64HelloPrintNN
import Spike.Lib.X64HelloAbortObl

namespace Spike.Lib.X64.Flow.Worker.Hello.OwnZH

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker (NodeZA AbortObl)
open Spike.Lib.X64.Flow.Worker.Wake.RelZW (blkZA_done nodeZA_cell)
open Spike.Lib.X64.Flow.Worker.Wake.OwnW (OwnW ownW_done ownW_syscall)

variable {W : BitVec 64} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
include hp hend

set_option hygiene false in
/-- A covered block of `print`'s, its code from `Wk.printCode`. -/
local macro "rp " ok:term:max f:ident : tactic =>
  `(tactic| exact blkZA_done (fun _ _ _ h => ownW_done h) $ok hR (by omega) (by omega)
    (fun s he hn => hc.$f s he hn))

/-- **`OwnW` at `scc_rt_print`'s nodes**: at a node with `Print.N`'s pc and offsets and any invariant `J`, in a
region covering `print`'s frame (`-40 … 16` from its entry). -/
theorem print_ownH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} {rbp0 ra : BitVec 64} {J : AS → Ctl → Prop} (i : Print.PN) :
    NodeZA (OwnW W) exe endPc R F
      ⟨(Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).pc,
        (Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).o, J⟩ (PrintF.FA.blkN i) := by
  have hc := Wk.printCode hp hend (c0 := c0) (rbp0 := rbp0) (ra := ra)
  cases i
  · rp Print.x0_ok e
  · rp Print.x1_ok n1
  · rp Print.x2_ok loop
  · rp Print.x3_ok n3
  · rp Print.x4_ok write
  · exact nodeZA_cell (fun s he hn => hc.sys s he hn) fun _ _ _ hc _ _ _ => ownW_syscall hc
  · rp Print.x5_ok n5
  · rp Print.x6_ok n6
  · rp Print.x7_ok chk2
  · rp Print.x8_ok n8
  · rp Print.x9_ok chk3
  · rp Print.x10_ok n10
  · rp Print.x11_ok adv
  · rp Print.x12_ok fail
  · rp Print.x13_ok done

set_option hygiene false in
/-- A covered block of the write abort's path, its code `f s he hn`. -/
local macro "ra " ok:term:max f:term:max : tactic =>
  `(tactic| exact blkZA_done (fun _ _ _ h => ownW_done h) $ok hR (by omega) (by omega)
    (fun s he hn => $f s he hn))

/-- **`OwnW` at the write abort's path** (`AbortObl`), at hello's cells (`SccCode.hello_abort`), for any source
control `c0`: the stub's region holds its frame (`hlo`, `hhi`), as `AbortObl.ofPc`'s. -/
theorem abortObl_ownH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} : AbortObl (fun s c => OwnW W s c) exe endPc R F c0 := by
  have hpr := SccCode.hello_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hpr
  have dc : Abort.Disp.Code c0 exe endPc := Scc.Cert.Rt.X64.Abort.code_disp hp hend hpr.2
  have sc : Abort.Code Abort.write c0 Abort.x1Write exe endPc :=
    Scc.Cert.Rt.X64.Abort.code_stubs hp hend SccCode.hello_abort .write
  refine
    { de := ?_, dt1 := ?_, dj1 := ?_, dt2 := ?_, dj2 := ?_, dt3 := ?_, dj3 := ?_, dt4 := ?_, dg4 := ?_,
      se := ?_, sn1 := ?_, sn2 := ?_, sys := ?_, sn5 := ?_, sex := ?_ }
  · ra Abort.Disp.d0_ok dc.e
  · ra Abort.Disp.t1_ok dc.t1
  · ra Abort.Disp.j1_ok dc.j1
  · ra Abort.Disp.t2_ok dc.t2
  · ra Abort.Disp.j2_ok dc.j2
  · ra Abort.Disp.t3_ok dc.t3
  · ra Abort.Disp.j3_ok dc.j3
  · ra Abort.Disp.t4_ok dc.t4
  · ra Abort.Disp.g4_ok dc.g4
  · ra Abort.x0_ok sc.e
  · rintro s c ⟨he, hn, -, hpc, -⟩
    exact ⟨ownW_done (exec_si ((sc.n1 s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [cellOff]))),
      fun _ h => h⟩
  · ra Abort.x1Write_ok sc.n2
  · rintro s c ⟨he, hn, -, hpc, -⟩
    exact ⟨ownW_syscall ((sc.sys s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [cellOff])),
      fun _ h => h⟩
  · ra Abort.x2_ok sc.n5
  · rintro s c ⟨he, hn, -, hpc, -⟩
    exact ⟨ownW_syscall ((sc.ex s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [cellOff])),
      fun _ h => h⟩

end Spike.Lib.X64.Flow.Worker.Hello.OwnZH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.OwnZH.print_ownH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.OwnZH.print_ownH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.OwnZH.abortObl_ownH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.OwnZH.abortObl_ownH
