/-
**hello.w's child print `write` at the placed layout** (ChildPrem row `hsvc`, at `PI`'s memory side `HelloMsW.msWH`):
`msWH`'s byte
step is `print`'s (`msWH_bo`) and its abort justification is the write
abort's phase `WriteAb.Ab` (`msWH_we`), so `HelloChildSvc.hsvc_IW` closes
`hsvc` with no premise on the memory side.

- `msWH_we_svc` (non-vacuity of `msWH.we`): at hello's placed layout every
  state at `print`'s `write` node (`PrintF.FA.N … .svc`, any region with
  `print`'s frame) satisfies `msWH`'s abort justification
  (`printSvcWeF`). The child reaches that node at the clone's words through
  `seg_childR`'s use of `hsvc` (`Wk.seg_wcWorkerS`'s `print` call), and the
  `example` below instantiates it at the child's call (`printN 13 2 = 13`
  bytes).
- `hsvc_I`: `ChildPrem.hsvc` at `PI`'s memory side.
-/
import Spike.Lib.HelloChildSvc
import Spike.Lib.HelloSegI

namespace Spike.Lib.HelloAssemblyI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.HelloMsW (msWH)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (wcP)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.HelloByteOutP (ByteOutP)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZR)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- hello's text is laid out in the placed executable. -/
theorem lays_H (ho : o.prog = helloProg) : Scc.Cert.Rt.A64.Lays (LH hp i).exe helloProg (LH hp i).pfx := by
  rw [← ho]; exact (LH hp i).lays

/-- **Non-vacuity of `msWH.we`**: at hello's placed layout, every state at
`print`'s `write` node (a region with `print`'s 48-byte frame, the count
below `2^63`) satisfies `msWH`'s abort justification, for every record. -/
theorem msWH_we_svc (ho : o.prog = helloProg) (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i)
    {R : Region} {F : MachineData → Prop} {c0 : Ctl} {x29 ra buf0 : BitVec 64} {len0 : Nat}
    {P Q : Nat → Ctl → Prop} {tp : UInt64} (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hlen : len0 < 2 ^ 63) :
    ∀ s c, At (LH hp i).exe (endH hp i) R F
      ((PrintF.FA.N (_root_.Executable.labels (LH hp i).exe).label x29 ra buf0 len0 P Q .svc).withTp tp) s c →
      (msWH (LH hp i) (GH hp i G0) (SRH hp i) w).we s c := by
  haveI := (LH hp i).valid
  exact fun _ _ hAt => Hello.SegR.printSvcWeF (Hello.Wk.printCode (c0 := c0) (lays_H hp i ho) rfl) hlo hhi hlen hAt

/-- `msWH_we_svc` at the child's `print` call: the call state `σC` of the
worker's call node on the clone's words, `13` bytes in `2` words. -/
example (ho : o.prog = helloProg) (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i)
    {R : Region} {F : MachineData → Prop} {σC : AS} {w0 w2 : TermRun.Word} (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hx1 : σC.regs.X1.toBitVec.toNat = printN 13 2) :
    ∀ s c, At (LH hp i).exe (endH hp i) R F
      (PrintF.cN (_root_.Executable.labels (LH hp i).exe).label (fun _ => PrW w0 w2 13 2) (fun _ => PrW w0 w2 13 2)
        σC .svc) s c →
      (msWH (LH hp i) (GH hp i G0) (SRH hp i) w).we s c :=
  msWH_we_svc hp i ho G0 w (c0 := wcP w0 w0 w2 w0 w0) hlo hhi (by rw [hx1]; decide)

/-- **`ChildPrem.hsvc` at `PI`'s memory side** (`hsvc_IW` with `msWH`'s
byte step and abort justification exactly the ones it asks). -/
theorem hsvc_I (ho : o.prog = helloProg) (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i) {F : MachineData → Prop}
    {w' : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} {l : WeakMem.AllocLabel}
    (hpw : w0.val = .loc ⟨l, 0⟩ 0)
    (hl : (SRH hp i w).lbl l = some (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat) (hwn : w2.val = .num n)
    (hfit : (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat + printN n m < 2 ^ 64)
    (hlen : printN n m < 2 ^ 63) :
    Hello.SegR.SvcX (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
      (fun _ => msWH (LH hp i) (GH hp i G0) (SRH hp i) w) F w' tp w0 w1 w2 w3 w4 n m := by
  haveI := (LH hp i).valid
  exact Hello.SegR.hsvc_IW (F := F) (ms := fun _ => msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (lays_H hp i ho) rfl (fun _ => HelloMs.K_H (LH hp i) (GH hp i G0) (SRH hp i) w) hpw hl hwn hfit hlen
    (fun _ _ _ _ _ h => h) (fun _ _ _ h => h)

end Inst

/-- info: 'Spike.Lib.HelloAssemblyI.msWH_we_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msWH_we_svc

/-- info: 'Spike.Lib.HelloAssemblyI.hsvc_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hsvc_I

end Spike.Lib.HelloAssemblyI
