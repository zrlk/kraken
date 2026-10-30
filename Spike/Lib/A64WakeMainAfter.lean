/-
**wake.w on AArch64: main's invariant after its `clone`** (main's rows after the spawn): from main's state at its `clone`
(`Spike.Lib.WakePreA.ClonePre`), the parent the kernel returns to is at
`Parent.pN … .cb` (`Parent.parent_at_preR`) in main's post-spawn region
(base `sp + 80`, offsets `[-96, 16)`: the wait loop's and the park's frames
below `wc_main`'s, `scc_rt_main`'s spill cell above), which lies in main's
stack range `r0` (`WakeCloneSp.clone_sp_in_r0` from `ClonePre.spTop`); from
there main's path to its `exit_group` is one `SegL` to nothing
(`MainPost.seg_mainPost`, `hseg`), so `WakeM0.closed_of_segL` gives an
invariant closed under the rows holding at the parent.

- `main_closed_of_clone`: the above, for any frame condition containing the
  parent's memory outside the region (`hF`).
- `main_closed_wake`: with `hseg` from `seg_mainPost` at the ghost `g0`
  (`Rg g0 = R`, `fp g0 = x29`, `Fg g0` containing the parent's memory outside
  `R`), its code and labels decided (`LoopCode.waitCode_wake`,
  `parkCode_wake`, `loopLabs_wake`).
-/
import Spike.Lib.A64WakeParentAt
import Spike.Lib.WakeCloneSp
import Spike.Lib.WakeM0
import Spike.Lib.A64WakeMainPost
import Spike.Lib.A64WakeLoopCode

namespace Spike.Lib.A64.Flow.Worker.Wake.MainAfter

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (pN parent_at_preR JS oP)
open Spike.Lib.WakePreA (cloneAt)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-- **main's invariant after its `clone`**: from main's state at the clone
(`h`, its thread in `At` of the clone's node with `JS`: `hat`), main's
post-spawn region `R` (base `sp + 80`: `hRb`; offsets `[-96, 16)`), the
kernel returning the child's id `0 < r < pidMax`, and main's path from
`pN .cb` to nothing in a frame condition `F` containing the parent's memory
outside `R` (`hseg`, `hF`; `MainPost.seg_mainPost`), an invariant closed
under the rows holds at the parent. -/
theorem main_closed_of_clone {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isaLSE2}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F F0 : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 80)
    (hRlo : R.lo = -96) (hRhi : R.hi = 16) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    (hF : ∀ th : Thread isaLSE2, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m)
    (hseg : SegL Spike.Lib.WakeT1.wakeSrc lbl ms
      (At exe endPc R F (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb)) (fun _ _ => False)) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧ ∃ inv : Frag isaLSE2,
      inv (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP ∧
      ∀ s c, inv s c → OutL Spike.Lib.WakeT1.wakeSrc lbl ms inv s c := by
  obtain ⟨th', hth', hsp⟩ := Spike.Lib.WakeCloneSp.clone_sp_in_r0 h.spTop
  have hb := hRb th' hth'
  obtain ⟨th, hth, hAt⟩ := parent_at_preR hp hend h hat
    (by refine ⟨?_, ?_⟩ <;> omega) (by omega) hR htop hr0 hrm
  obtain ⟨inv, hP, hi⟩ := Spike.Lib.WakeM0.closed_of_segL hseg
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  exact ⟨th, hth, inv, hP _ _ ⟨he, hn, hdc, hpc, σ, hA, hF th hth _ hD, hJ⟩, hi⟩

open Spike.Lib.A64.Flow.Worker.Wake.MainPost (seg_mainPost mainSp0)
open Scc.Sem (ValRep)

/-- **main's invariant after its `clone` in wake's program**:
`main_closed_of_clone` with `hseg` from `seg_mainPost` at the ghost `g0`
whose region is `R` (`hRg`), frame pointer `x29` (`hfp`) and frame condition
contains the parent's memory outside `R` (`hFg`); the loop's and the park's
code and labels decided. What stays: `seg_mainPost`'s regions, source, memory
side, thread-pointer load (`htls`), return address and exit facts. -/
theorem main_closed_wake {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isaLSE2}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F0 : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 80)
    (hRlo : R.lo = -96) (hRhi : R.hi = 16) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    {γ : Sort _} {Rg : γ → Spike.Lib.Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64} (g0 : γ)
    (hRg : Rg g0 = R) (hfp : fp g0 = x29)
    (hFg : ∀ th : Thread isaLSE2, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → Fg g0 m)
    (hF : ∀ g, FStable (Rg g) (Fg g)) (hRo : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -96) (hhi : ∀ g, 16 ≤ (Rg g).hi)
    (hrun : LocalRun Spike.Lib.WakeT1.wakeSrc cP c0)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0)
    (htls : ∀ g,
      SegW (Spike.Lib.A64AbOffL.TlsW (_root_.Executable.labels exe).label A c0) (fun _ _ => False) Spike.Lib.WakeT1.wakeSrc lbl ms (At exe endPc (Rg g) (Fg g)
          (WaitLoop.N (_root_.Executable.labels exe).label WakeLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (WaitLoop.N (_root_.Executable.labels exe).label WakeLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0)
    (hexit : ∀ g s c, WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp0 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit Spike.Lib.WakeT1.wakeSrc ms s c 0) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧ ∃ inv : Frag isaLSE2,
      inv (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP ∧
      ∀ s c, inv s c → OutL Spike.Lib.WakeT1.wakeSrc lbl ms inv s c := by
  obtain ⟨he, -, hs3, hpe⟩ := LoopCode.loopLabs_wake hp
  have hseg := seg_mainPost (exe := exe) (Rg := Rg) (Fg := Fg) (fp := fp) hp hend (cP := cP) g0 hF hRo hal hlo hhi
    hrun hterm hev hval htag hdm (fun _ => LoopCode.waitCode_wake hp hend) he hK hS htp4
    (LoopCode.parkCode_wake hp hend (c0 := cP) (x29 := 0) (ra := 0) (tp := 0)) hpe hs3 htls hra hexit
  rw [hRg, hfp] at hseg
  exact main_closed_of_clone hp hend h hat hRb hRlo hRhi hR htop hr0 hrm hFg hseg

/-- info: 'Spike.Lib.A64.Flow.Worker.Wake.MainAfter.main_closed_wake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms main_closed_wake

/-- info: 'Spike.Lib.A64.Flow.Worker.Wake.MainAfter.main_closed_of_clone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms main_closed_of_clone

end Spike.Lib.A64.Flow.Worker.Wake.MainAfter
