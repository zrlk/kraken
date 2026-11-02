/-
**hello.w's `print` writes at most once per instruction** (x86-64; the `print_relH` part of
`Spike/Lib/A64HelloRelZ.lean`): `RelWS` (`RelZW.RZ`) at every node of `scc_rt_print`, in the `NodeZA` form over
its per-node blocks (`PrintF.FA.blkN`, `X64HelloPrintNN`). Every block is covered (it runs to `.done`: its stack
accesses hit the private memory; `print` loads nothing from the shared buffer), and the `write`'s `syscall` faults.

- `print_relH`: at a node with `Print.N`'s pc and offsets and any invariant `J` (so at `Print.N`, `PrintA.N`, the
  call-pinned `PrintCall.pN` and their thread-pointer variants alike), in a region covering `print`'s frame.

Unlike AArch64 (one module, `print`'s nodes `PrintF.cN` at the call state, a `dmb ish` fence node), `print`'s nodes
are stated by their pc and offsets with the invariant left free, `print` has no fence (15 nodes, the system call
`.sys` a single cell), and the fact is `RelWS` under `Arch.tso`.
-/
import Spike.Lib.X64HelloRelZ
import Spike.Lib.X64HelloPrintNN

namespace Spike.Lib.X64.Flow.Worker.Hello.RelZH

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker (NodeZA)
open Spike.Lib.X64.Flow.Worker.Wake.RelZW (RZ blkZA_done nodeZA_cell)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
include hp hend

set_option hygiene false in
/-- A covered block of `print`'s, its code from `Wk.printCode`. -/
local macro "rp " ok:term:max f:ident : tactic =>
  `(tactic| exact blkZA_done (fun _ _ _ h => relWS_done ⟨_, h⟩) $ok hR (by omega) (by omega)
    (fun s he hn => hc.$f s he hn))

/-- **`RelWS` at `scc_rt_print`'s nodes**: at a node with `Print.N`'s pc and offsets and any invariant `J`, in a
region covering `print`'s frame (`-40 … 16` from its entry). -/
theorem print_relH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} {rbp0 ra : BitVec 64} {J : AS → Ctl → Prop} (i : Print.PN) :
    NodeZA RZ exe endPc R F
      ⟨(Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).pc,
        (Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).o, J⟩ (PrintF.FA.blkN i) := by
  have hc := Wk.printCode hp hend (c0 := c0) (rbp0 := rbp0) (ra := ra)
  cases i
  · rp Print.x0_ok e
  · rp Print.x1_ok n1
  · rp Print.x2_ok loop
  · rp Print.x3_ok n3
  · rp Print.x4_ok write
  · exact nodeZA_cell (fun s he hn => hc.sys s he hn) fun _ _ _ hc _ _ _ => relWS_syscall hc
  · rp Print.x5_ok n5
  · rp Print.x6_ok n6
  · rp Print.x7_ok chk2
  · rp Print.x8_ok n8
  · rp Print.x9_ok chk3
  · rp Print.x10_ok n10
  · rp Print.x11_ok adv
  · rp Print.x12_ok fail
  · rp Print.x13_ok done

end Spike.Lib.X64.Flow.Worker.Hello.RelZH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.RelZH.print_relH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.RelZH.print_relH
