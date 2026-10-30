/-
**The second thread's `scc_rt_thread_init` inside `W`** (AArch64, wake's
spawn; R-c): the same function as main's own setup, called a second time,
taking the next 16 KiB of `scc_rt_stacks` (`r1Of`). Inside the call `W` is
`SFacts` at `r1Of lab` and the second take's phase `Tk2` (an instance's
facts `InstOk` at `Tk2`); outside it, main's `r0Of lab` and `Tk`. Main's
ownership of `r0` across the call is not `W`'s: it is the held predicate's
(`A64Consumer.HeldOk2`, kept off the transfer sites by `owned_mono`).

- `r0Of`: main's take's range, the first 16 KiB of `scc_rt_stacks`.
- `r0Of_eq`, `r1Of_eq`: their bounds, the stacks not wrapping.
- `r01_disj`: the two ranges are disjoint (the second take's
  `HeldPathS.site` clause against the held `[(0, r0)]`).
- `tiW2_gen`: `tiW_gen` at the second take (`q.k0 = 16384`): the range is
  `r1Of lab`, no other premise changes.
-/
import Spike.Lib.Rt.A64RtTi
import Spike.Lib.Rt.A64RtPreChild

namespace Spike.Lib.A64.Rt.Ti2

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (TI TiG TiW lockA freeNA nextA stacksA StackM)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.Rt Spike.Lib.A64.Rt.Ti Spike.Lib.A64.Rt.Take Spike.Lib.A64.Flow.Ret0.ThreadInit

/-- **Main's take's range**: the first 16 KiB of `scc_rt_stacks`. -/
def r0Of (lab : Label → Int64) : Range := ⟨(stacksA lab + 0#64).toNat, 16384⟩

theorem r0Of_eq (lab : Label → Int64) : (r0Of lab).lo = (stacksA lab).toNat ∧ (r0Of lab).size = 16384 := by
  refine ⟨?_, rfl⟩
  show (stacksA lab + 0#64).toNat = _
  rw [BitVec.add_zero]

theorem r1Of_eq {lab : Label → Int64} (hbd : (stacksA lab).toNat + 32768 < 2 ^ 64) :
    (r1Of lab).lo = (stacksA lab).toNat + 16384 ∧ (r1Of lab).size = 16384 := by
  refine ⟨?_, rfl⟩
  show (stacksA lab + 16384#64).toNat = _
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl

/-- **The two takes' ranges are disjoint.** -/
theorem r01_disj {lab : Label → Int64} (hbd : (stacksA lab).toNat + 32768 < 2 ^ 64) :
    (r1Of lab).Disjoint (r0Of lab) := by
  have h0 := r0Of_eq lab
  have h1 := r1Of_eq hbd
  right; omega

/-- **The second `scc_rt_thread_init`'s states are inside `SFacts` at
`r1Of lab`**: `tiW_gen` at the instance `hI` of the second take's phase,
`q.k0 = 16384`. -/
theorem tiW2_gen {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk2 : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F P : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk2 K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : threadInitIn prog = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi) (q : TiG)
    (hk0 : q.k0 = 16384#64)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra spL).toBitVec) (hph : TiPh okPc ph Tk2 lab ra)
    (hmF : ∀ a ∈ tiAddrs q.tcb, Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hunF : ∀ a ∈ tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoF : ∀ a ∈ tiAddrs q.tcb, ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hsub : (r1Of lab).Sub Λ.stackPool) (hSM : FStable R (StackM (r1Of lab)))
    (hSM' : FStable (R.callee oI.sp (-208) 0) (StackM (r1Of lab)))
    (hin' : Ret0.StackTake.stackTakeIn prog = true)
    (hphT : TakePh okPc ph Tk2 ownOf μ lab fun _ => lab spL)
    (hmL : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨lockA lab, 8⟩ = true)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨freeNA lab, 8⟩ = true)
    (hmX : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨nextA lab, 8⟩ = true)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hdisj : Λ.rodata.Disjoint Λ.stackPool) :
    ∀ i, TiW (fun s c => SFacts Λ μ own (r1Of lab) Tk2 lbl s c) K exe endPc R F (StackM (r1Of lab)) q i P :=
  tiW_gen hI hown hin hC0 hR hal hlo hhi q hq hra hph hmF hunF hnoF hsub hSM hSM' hin' hphT hmL hmN hmX
    hunL hunN hunX (by rw [hk0]; rfl) hdisj

/-- info: 'Spike.Lib.A64.Rt.Ti2.tiW2_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.Ti2.tiW2_gen

end Spike.Lib.A64.Rt.Ti2
