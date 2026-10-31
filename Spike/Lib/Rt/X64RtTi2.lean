/-
**The second thread's `scc_rt_thread_init` inside `W`** (x86-64; twin of
`Spike/Lib/Rt/A64RtTi2.lean`, wake's spawn; R-c): the same function as
main's own setup, called a second time, taking the next 16 KiB of
`scc_rt_stacks` (`r1Of`). Inside the call `W` is `SFacts` at `r1Of lab` and
the second take's phase `Tk2` (an instance's facts `InstOk` at `Tk2`);
outside it, main's `r0Of lab` and `Tk`. Main's ownership of `r0` across the
call is not `W`'s: it is the held predicate's (`X64Consumer.HeldOk2`, kept
off the transfer sites by `owned_mono`).

- `r0Of`: main's take's range, the first 16 KiB of `scc_rt_stacks`.
- `r0Of_eq`, `r1Of_eq`: their bounds, the stacks not wrapping.
- `r01_disj`: the two ranges are disjoint (the second take's
  `HeldPathS.site` clause against the held `[(0, r0)]`).
- `tiW2_gen`: `tiW_gen` at the second take (`q.k0 = 16384`): the range is
  `r1Of lab`, no other premise changes.

**Unlike AArch64**: no `hal`; the region bounds are x86-64's `tiW_gen`'s
(`R.lo ≤ -248`, `8 ≤ R.hi`; A64's `-256`, `0`), the take's callee region
`R.callee (-48 - 0) (-200) 8` (A64's `R.callee oI.sp (-208) 0`), the return
label `x7L` (A64's `spL`); x86-64's `tiW_gen` takes the range equation
`hrS` explicitly, discharged here from `hk0`.
-/
import Spike.Lib.Rt.X64RtTi
import Spike.Lib.Rt.X64RtPreChild

namespace Spike.Lib.X64.Rt.Ti2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (TI TiG TiW lockA freeNA nextA stacksA StackM)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.Rt Spike.Lib.X64.Rt.Ti Spike.Lib.X64.Rt.Take Spike.Lib.X64.Flow.Ret0.ThreadInit

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
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk2 : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk2 K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : threadInitIn cells = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi) (q : TiG)
    (hk0 : q.k0 = 16384#64)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra x7L).toBitVec) (hph : TiPh okPc ph Tk2 lab ra)
    (hmF : ∀ a ∈ tiAddrs q.tcb, Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hunF : ∀ a ∈ tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoF : ∀ a ∈ tiAddrs q.tcb, ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hsub : (r1Of lab).Sub Λ.stackPool) (hSM : FStable R (StackM (r1Of lab)))
    (hSM' : FStable (R.callee (-48 - 0) (-200) 8) (StackM (r1Of lab)))
    (hin' : Spike.Lib.X64.Flow.Ret0.StackTake.stackTakeIn cells = true)
    (hphT : TakePh okPc ph Tk2 ownOf μ lab fun _ => lab x7L)
    (hmL : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨lockA lab, 8⟩ = true)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨freeNA lab, 8⟩ = true)
    (hmX : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨nextA lab, 8⟩ = true)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hdisj : Λ.rodata.Disjoint Λ.stackPool) :
    ∀ i, TiW (fun s c => SFacts Λ μ own (r1Of lab) Tk2 lbl s c) K exe endPc R F (StackM (r1Of lab)) q i :=
  tiW_gen hI hown hin hC0 hR hlo hhi q hq hra hph hmF hunF hnoF hsub hSM hSM' hin' hphT hmL hmN hmX
    hunL hunN hunX (by rw [hk0]; rfl) hdisj

end Spike.Lib.X64.Rt.Ti2

/-- info: 'Spike.Lib.X64.Rt.Ti2.r0Of_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Ti2.r0Of_eq

/-- info: 'Spike.Lib.X64.Rt.Ti2.r1Of_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Ti2.r1Of_eq

/-- info: 'Spike.Lib.X64.Rt.Ti2.r01_disj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Ti2.r01_disj

/-- info: 'Spike.Lib.X64.Rt.Ti2.tiW2_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Ti2.tiW2_gen
