/-
**The abort exits inside `W2` at the write abort's phase** (AArch64):
`stubON_w2` and `stubHN_w2` (`Spike/Lib/LowerA64/AbortW2.lean`) at
`Ab := WriteAb.Ab lab`, their per-node bundles (`hab`) discharged by
`stubOAb`, `stubHAb` (`Spike/Lib/LowerA64/StubAbW2.lean`), and then at the
record of an output passing `placeOK` (`RuntimeLayout.ofPlaceOK`), the
instance, the code, the exit calls' site premises and both paths' phase
checks discharged (the heap's by `abortPhHeapOk_ofPlaceOK`,
`Spike/Lib/Rt/A64AbNoSite.lean`). The twin of
`Spike/Lib/LowerX64/AbortW2Ab.lean`.

- `stubON_w2Ab`, `stubHN_w2Ab`: `StubON`, `StubHN` inside `W2` at
  `WriteAb.Ab lab`, from `printIn` in place of the bundle.
- `heap_toNat`, `hrelH_ofPlaceOK`, `htkH_ofPlaceOK`, `hkH_ofPlaceOK`,
  `hKexH_ofPlaceOK`, `hmsH_ofPlaceOK`, `hmsO_ofPlaceOK`: the heap exit call's
  site premises from the placement (the twins of the overflow's in
  `Spike/Lib/LowerA64/AbortOfPlaceOK.lean`), and both exit calls' `hms` for
  any memory side aborting at the record's abort sites.
- `stubON_w2_ofPlaceOK`, `stubHN_w2_ofPlaceOK`: the two at the record.
-/
import Spike.Lib.LowerA64.StubAbW2
import Spike.Lib.LowerA64.AbortOfPlaceOK
import Spike.Lib.Rt.A64AbNoSite

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun OvfReady EnvSmall)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable KStable)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff TakeK)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.A64.StubW (abortPhOk abortPhHeapOk NbCtl)

/-! ## At the write abort's phase -/

section Ab

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {c0 : Ctl}

/-- **`StubON` inside `W2` at the write abort's phase** (`stubON_w2` with
its bundle `stubOAb`, from the `print` code). -/
theorem stubON_w2Ab {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hp : ProgNoS ZBad p)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hphs : abortPhOk okPc ph lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0) (hsm : EnvSmall c0.env)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0)
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', pcOf s = (lab A64.Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    {ms : MemSide isaLSE2} (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At exe endPc R F (A64.Abort.N lab A64.Abort.overflow c0 .svc) s c → Dt s)
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs) (hcw : CtlW2 c0 fs) :
    StubON (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs) K ms
      exe endPc R F c0 :=
  stubON_w2 hI hp hprog hphs hR hal hlo hhi hl hh hF hsub hfit hFO hc hsm hpl hrel htk hk hKex hms hK hwr
    hfp hcw (stubOAb hI hpr hprog hphs hR hal hlo hhi htk)

/-- **`StubHN` inside `W2` at the write abort's phase** (`stubHN_w2` with
its bundle `stubHAb`, from the `print` code). -/
theorem stubHN_w2Ab {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hphs : abortPhHeapOk okPc ph lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : NbCtl Λ p (fun s _ => own s) lbl F c0 fs)
    (hobl : HeapAbortObl ar.cells ar.ctr c0)
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.heap.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.heap.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.heap.exit).toBitVec.toNat = a → k = .heap)
    (hKex : ∀ s s', pcOf s = (lab A64.Abort.heap.exit).toBitVec.toNat → ¬ K s s')
    {ms : MemSide isaLSE2} (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.heap.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At exe endPc R F (A64.Abort.N lab A64.Abort.heap c0 .svc) s c → Dt s) :
    StubHN (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs) K ms
      exe endPc R F c0 :=
  stubHN_w2 hI hprog hphs hR hal hlo hhi hl hh hF hsub hfit hFO hc hobl hrel htk hk hKex hms hK hwr
    (stubHAb hI hpr hprog hphs hR hal hlo hhi htk)

end Ab

/-! ## At the record of an output passing `placeOK` -/

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ K)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- The heap exit call's address is its `codeOf` address. -/
theorem heap_toNat {a : Nat}
    (ha : codeOf Λ.code.lo o.prog "scc_rt_abort_heap_exit" = some a) :
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap.exit).toBitVec.toNat = a :=
  lab_toNat h i ha

/-- **`hrel`** (heap): the heap exit call is off the release site. -/
theorem hrelH_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .release = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, -, hr, -, hhe, -, -, -, hnd⟩ := sites7 h
  intro a ha
  change codeOf Λ.code.lo o.prog "scc_rt_release_site" = some a at ha
  rw [hr] at ha
  cases ha
  rw [heap_toNat h i hhe]
  rintro rfl
  simp at hnd

/-- **`htk`** (heap): the heap exit call is off the take site. -/
theorem htkH_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .take = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, -, hhe, -, -, -, hnd⟩ := sites7 h
  intro a ha
  change codeOf Λ.code.lo o.prog "scc_rt_take_site" = some a at ha
  rw [ht] at ha
  cases ha
  rw [heap_toNat h i hhe]
  rintro rfl
  simp at hnd

/-- **`hk`** (heap): the heap exit call is no other abort kind's site. -/
theorem hkH_ofPlaceOK : ∀ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap.exit).toBitVec.toNat = a → k = .heap := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, hov, hhe, hst, hwr, hth, hnd⟩ := sites7 h
  intro k a ha hx
  rw [heap_toNat h i hhe] at hx
  subst hx
  cases k with
  | heap => rfl
  | overflow =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_overflow_exit" = some he at ha
    rw [hov] at ha; cases ha; simp at hnd
  | stack =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_stack_exit" = some he at ha
    rw [hst] at ha; cases ha; simp at hnd
  | threads =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_threads_exit" = some he at ha
    rw [hth] at ha; cases ha; simp at hnd
  | writeErr =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_write_exit" = some he at ha
    rw [hwr] at ha; cases ha; simp at hnd

/-- **`hKex`** (heap): no outside move (the take, at the take site) at the
heap exit call. -/
theorem hKexH_ofPlaceOK {rS : Scc.Sem.Range} : ∀ s s', Scc.Sem.A64.pcOf s =
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap.exit).toBitVec.toNat →
    ¬ K (RuntimeLayout.ofPlaceOK h i) rS s s' := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, -, hhe, -, -, -, hnd⟩ := sites7 h
  intro s s' hpc hK
  rw [Scc.Sem.A64.pcOf, Spike.Lib.A64.Flow.Ret0.TakeK.pc hK, lab_toNat h i (l := "scc_rt_take_site") ht,
    heap_toNat h i hhe] at hpc
  subst hpc
  simp at hnd

/-- **`hms`** (heap): a memory side aborting at every abort site of the
record aborts at the heap exit call. -/
theorem hmsH_ofPlaceOK {ms : MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s) :
    ∀ s : State, s.exe = (RuntimeLayout.ofPlaceOK h i).exe →
      s.st.2 = (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap.exit → ms.abortAt s := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, -, hhe, -, -, -, -⟩ := sites7 h
  intro s _ hs
  refine hma s ⟨.heap, he, (abortAt_eq h i _).trans hhe, ?_⟩
  rw [Scc.Sem.A64.pcOf, hs, heap_toNat h i hhe]

/-- **`hms`** (overflow) for a memory side aborting at every abort site of
the record (`hms_ofPlaceOK` is `msOf`'s). -/
theorem hmsO_ofPlaceOK {ms : MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s) :
    ∀ s : State, s.exe = (RuntimeLayout.ofPlaceOK h i).exe →
      s.st.2 = (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow.exit → ms.abortAt s := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, hov, -, -, -, -, -⟩ := sites7 h
  intro s _ hs
  refine hma s ⟨.overflow, ov, (abortAt_eq h i _).trans hov, ?_⟩
  rw [Scc.Sem.A64.pcOf, hs, ovf_toNat h i hov]

variable {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {c0 : Ctl} {rS : Range}

/-- **`stubON_w2Ab` at the record of an output passing `placeOK`**: the
instance (`instOk_ofPlaceOK`), the abort and `print` code, the overflow
path's phase check and the exit call's site premises discharged; the memory
side any aborting at the record's abort sites with the ABI's kernel. -/
theorem stubON_w2_ofPlaceOK (hp : ProgNoS ZBad p)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0) (hsm : EnvSmall c0.env)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0)
    {ms : MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
      (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow c0 .svc) s c → Dt s)
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs) (hcw : CtlW2 c0 fs) :
    StubON (fun s c => W2 Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R F c0 :=
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  stubON_w2Ab (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i) hp (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i)
    (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h i) hR hal hlo hhi hl hh hF hsub hfit hFO
    hc hsm hpl (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i) (hk_ofPlaceOK h i) (hKex_ofPlaceOK h i)
    (hmsO_ofPlaceOK h i hma) hK hwr hfp hcw

/-- **`stubHN_w2Ab` at the record of an output passing `placeOK`**: as
`stubON_w2_ofPlaceOK`, the heap path's phase check from
`abortPhHeapOk_ofPlaceOK`. -/
theorem stubHN_w2_ofPlaceOK
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hc : NbCtl Λ p (fun s _ => Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl F c0 fs)
    (hobl : HeapAbortObl ar.cells ar.ctr c0)
    {ms : MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
      (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap c0 .svc) s c → Dt s) :
    StubHN (fun s c => W2 Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R F c0 :=
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  stubHN_w2Ab (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i) (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i)
    (Spike.Lib.A64.Rt.abortPhHeapOk_ofPlaceOK h i)
    hR hal hlo hhi hl hh hF hsub hfit hFO hc hobl (hrelH_ofPlaceOK h i) (htkH_ofPlaceOK h i)
    (hkH_ofPlaceOK h i) (hKexH_ofPlaceOK h i) (hmsH_ofPlaceOK h i hma) hK hwr

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.stubON_w2Ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubON_w2Ab

/-- info: 'Spike.Lib.LowerA64.stubHN_w2Ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_w2Ab

/-- info: 'Spike.Lib.LowerA64.hkH_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hkH_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.stubON_w2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubON_w2_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.stubHN_w2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_w2_ofPlaceOK

end Spike.Lib.LowerA64
