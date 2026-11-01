/-
**hello.w's `hres`: `scc_rt_thread_reserve`'s counter owned at its add**
(AArch64 row 5d; the program half of wake's `H1Rt.resA_W` at
helloProg): at any memory side whose owned words are hello's global map
`ownGH L (ntA L.lab)` (`hown`), the reserve's counter `scc_rt_nthreads` at
old value `0` is `ResOkA` in any region, given the counter's store `StOk`
(`hnext`, the instance's: `H1Rt.stOk_W`'s twin at hello's memory side).

The reserve's `ldadd` (`entryL + 4·5`) is at a free pc (`freeNH`: `ownGH`
picks `ownH`) before `scc_rt_nthreads`' add (bit `4` of `phH` clear), a
decided check (`ph_rmwH`).

- `phAtH`, `phAtH_pc`: a label-relative pc check of helloProg, read through
  `L.lab`.
- `ph_rmwH`: the phase fact at the reserve's add.
- `resA_H`: `WcMid`'s `hres` (`ResOkA … (rARH R) …`) at any region.
-/
import Spike.Lib.A64HelloWcPreW
import Spike.Lib.A64HelloOwnGEq
import Spike.Lib.Rt.A64RtReserveA

namespace Spike.Lib.A64.HelloPh.ResA

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA ResOkA)
open Spike.Lib.A64.HelloPh.WcW (freeNH inCvH cvH goodW_of_freeNH)

/-- **A label-relative pc check**: `f` at `l + 4 k` of helloProg. -/
def phAtH (f : Nat → Bool) (l : Label) (k : Nat) : Bool :=
  match Scc.Cert.Rt.A64.pcAt (codeOf lo SccCode.helloProg) l k with
  | some t => f t
  | none => false

theorem phAtH_pc {L : RuntimeLayout}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {f : Nat → Bool} {l : Label} {k : Nat} (h : phAtH f l k = true) {s : State}
    (hs : s.st.2 = L.lab l + Int64.ofNat (4 * k)) : f (pcOf s) = true := by
  unfold phAtH at h
  split at h
  · next t ht => unfold pcOf; rw [hs, Spike.Lib.A64.Rt.PhOfTab.pcAt_eq hlab ht]; exact h
  · cases h

/-- **The phase fact at the reserve's add**: free (`ownGH` picks `ownH`)
and before `scc_rt_nthreads`' add. -/
theorem ph_rmwH : phAtH (fun t => freeNH t && phH t / 16 % 2 == 0) Spike.Lib.A64.Flow.Reserve.entryL 5 = true := by
  unfold phAtH freeNH inCvH cvH; rw [phH_eq, ← codeT_eq]; decide +kernel

/-- **`hres`**: at a memory side owning `ownGH L (ntA L.lab)` (`hown`), the
reserve's counter at old value `0` is `ResOkA` in any region `R` under any
frame `F`, its store `StOk` given (`hnext`). -/
theorem resA_H {L : RuntimeLayout} {ms : MemSide isaLSE2} {F0 F : MachineData → Prop} {endPc : Int64}
    {R : Spike.Lib.Region}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hown : ∀ s, ms.own s = ownGH L (ntA L.lab) s)
    (hnext : Spike.Lib.A64.Flow.Ret0.StOk ms F0 L.exe endPc (ntA (_root_.Executable.labels L.exe).label)
      (0#64 + 1#64)) :
    ∀ g : Spike.Lib.A64.Flow.Reserve.G × Ctl, ResOkA ms F0 L.exe endPc R F ⟨g.1, 0#64, g.2⟩ := by
  refine fun g => ⟨hnext, fun s c hAt => ?_⟩
  have hf := phAtH_pc hlab ph_rmwH hAt.2.2.2.1
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  show _ ∈ ms.own s
  rw [hown, ownGH_W hlab (goodW_of_freeNH hlab hf.1)]
  show _ ∈ Spike.Lib.A64.WakePh.ownW L (ntA L.lab) _
  rw [Spike.Lib.A64.WakePh.ownW_eq]
  simp [Spike.Lib.A64.WakePh.ownV, hf.2]

end Spike.Lib.A64.HelloPh.ResA

/-- info: 'Spike.Lib.A64.HelloPh.ResA.phAtH_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ResA.phAtH_pc

/-- info: 'Spike.Lib.A64.HelloPh.ResA.ph_rmwH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ResA.ph_rmwH

/-- info: 'Spike.Lib.A64.HelloPh.ResA.resA_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ResA.resA_H
