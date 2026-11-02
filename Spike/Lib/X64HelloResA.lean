/-
**hello.w's `hres`: `scc_rt_thread_reserve`'s counter owned at its add, x86-64** (the twin of
`Spike/Lib/A64HelloResA.lean`; the program half of x86-64 wake's `H1Rt.resA_W` at `helloCells`): at any memory
side whose owned words are hello's global map `ownGH L (ntA L.lab)` (`hown`), the reserve's counter
`scc_rt_nthreads` at old value `0` is `ResOkA` in any region, given the counter's store `StOk` (`hnext`).

The reserve's locked add (`Reserve.rmwPc`, `entryL + 22`, byte `4199514` of hello's cells) is at a free pc
(`freeNH`: `ownGH` picks `ownH`) before `scc_rt_nthreads`' add (bit `4` of `phH` clear), a decided check
(`res_phH`).

- `res_phH`: the phase fact at the reserve's add.
- `resA_H`: `hres` (`ResOkA … ⟨g.1, 0, g.2⟩`) at any region.

Unlike AArch64: the add's pc is a byte offset from `entryL` resolved through `X64HelloPh.pc_eq` and `resLabs`
(AArch64: a label-relative check `phAtH` at `entryL + 4·5`, which is therefore not stated), the add is the locked
`xaddq`, and `StOk` takes no executable or end.
-/
import Spike.Lib.X64HelloWcPreW
import Spike.Lib.X64HelloOwnGEq
import Spike.Lib.Rt.X64RtReserveA

namespace Spike.Lib.X64.HelloPh.ResA

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA ResOkA)
open Spike.Lib.X64.Flow.Ret0 (StOk)
open Spike.Lib.X64.HelloPh.WcW (freeNH inCvH cvH goodW_of_freeNH)

/-- **The phase fact at the reserve's add** (byte `4199514`): free (`ownGH` picks `ownH`) and before
`scc_rt_nthreads`' add. -/
theorem res_phH : freeNH 4199514 = true ∧ phH 4199514 / 16 % 2 = 0 := by
  rw [phH_eq]; unfold freeNH inCvH cvH; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-- **`hres`**: at a memory side owning `ownGH L (ntA L.lab)` (`hown`), the reserve's counter at old value `0` is
`ResOkA` in any region `R` under any frame `F`, its store `StOk` given (`hnext`). -/
theorem resA_H {L : RuntimeLayout} {ms : MemSide isa} {F0 F : MachineData → Prop} {endPc : Int64}
    {R : Spike.Lib.Region}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hown : ∀ s, ms.own s = ownGH L (ntA L.lab) s)
    (hnext : StOk ms F0 (ntA (_root_.Executable.labels L.exe).label) (0#64 + 1#64)) :
    ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Ctl, ResOkA ms F0 L.exe endPc R F ⟨g.1, 0#64, g.2⟩ := by
  refine fun g => ⟨hnext, fun s c hAt => ?_⟩
  have hs : s.st.2 = Spike.Lib.X64.Flow.Reserve.rmwPc L.lab := hAt.2.2.2.1
  have hpc : pcOf s = 4199514 := by
    unfold pcOf; rw [hs]; exact pc_eq hlab resLabs.2.1 22
  have hf := res_phH
  rw [← hpc] at hf
  show _ ∈ ms.own s
  rw [hown, ownGH_W hlab (goodW_of_freeNH hlab hf.1)]
  show _ ∈ Spike.Lib.X64.WakePh.ownW L (ntA L.lab) _
  rw [Spike.Lib.X64.WakePh.ownW_eq]
  simp [Spike.Lib.X64.WakePh.ownV, hf.2]

end Spike.Lib.X64.HelloPh.ResA

/-- info: 'Spike.Lib.X64.HelloPh.ResA.res_phH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ResA.res_phH

/-- info: 'Spike.Lib.X64.HelloPh.ResA.resA_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ResA.resA_H
