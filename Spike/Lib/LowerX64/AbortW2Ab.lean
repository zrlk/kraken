/-
**The abort exits inside `W2` at the write abort's phase** (x86-64):
`stubON_w2` and `stubHN_w2` (`Spike/Lib/LowerX64/AbortW2.lean`) at
`Ab := WriteAb.Ab lab`, their per-node bundles (`hab`) discharged by
`stubOAb`, `stubHAb` (`Spike/Lib/LowerX64/StubAbW2.lean`), and then at the
record of an output passing `placeOK` (`RuntimeLayout.ofPlaceOK`), the
instance, the code, the exit calls' site premises and both paths' phase
checks discharged (the heap's by `abortPhHeapOk_ofPlaceOK`, from A7's
`tailOffC`).

- `stubON_w2Ab`, `stubHN_w2Ab`: `StubON`, `StubHN` inside `W2` at
  `WriteAb.Ab lab`, from `printIn` in place of the bundle.
- `heap_codeLabel`, `heap_toNat`, `hrelH_ofPlaceOK`, `htkH_ofPlaceOK`,
  `hkH_ofPlaceOK`, `hKexH_ofPlaceOK`, `hmsH_ofPlaceOK`: the heap exit
  call's site premises from the placement (the twins of the overflow's in
  `Spike/Lib/LowerX64/AbortOfPlaceOK.lean`).
- `stubON_w2_ofPlaceOK`, `stubHN_w2_ofPlaceOK`: the two at the record.
-/
import Spike.Lib.LowerX64.StubAbW2
import Spike.Lib.LowerX64.AbortOfPlaceOK
import Spike.Lib.X64AbortPhHPlace

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun OvfReady EnvSmall)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At okBlk FStable KStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff TakeK)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Scc.Cert.Rt.X64 (blockAt blockAtB)
open Kraken.Promising.Lower.X64 (op64)
open Spike.Lib.X64.StubW (abortPhOk abortPhHeapOk NbCtl)
open Spike.Lib.X64

/-! ## At the write abort's phase -/

section Ab

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {c0 : Ctl}

/-- **`StubON` inside `W2` at the write abort's phase** (`stubON_w2` with
its bundle `stubOAb`, from the `print` code). -/
theorem stubON_w2Ab {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hp : ProgNoS ZBad p)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hsysIn : blockAtB cells Abort.overflow.entry 34 [(op64 .syscall, 2)] = true)
    (hphs : abortPhOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0) (hsm : EnvSmall c0.env)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', pcOf s = (lab Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    {ms : MemSide isa} (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.N lab Abort.overflow c0 .sys) s c → Dt s)
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs) (hcw : CtlW2 c0 fs) :
    StubON (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize s c fs) K ms
      exe endPc R F c0 :=
  stubON_w2 hI hp hprog hsysIn hphs hR hR8 hlo hhi hl hh hF hsub hfit hFO hc hsm hpl hrel htk hk hKex hms hK hwr
    hfp hcw (stubOAb hI hpr hprog hphs hR hlo hhi htk)

/-- **`StubHN` inside `W2` at the write abort's phase** (`stubHN_w2` with
its bundle `stubHAb`, from the `print` code). -/
theorem stubHN_w2Ab {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hphs : abortPhHeapOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : NbCtl Λ p (fun s _ => own s) lbl F c0 fs)
    (hobl : HeapAbortObl ar.cells ar.ctr c0)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.heap.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.heap.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.heap.exit).toBitVec.toNat = a → k = .heap)
    (hKex : ∀ s s', pcOf s = (lab Abort.heap.exit).toBitVec.toNat → ¬ K s s')
    {ms : MemSide isa} (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.heap.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.N lab Abort.heap c0 .sys) s c → Dt s) :
    StubHN (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize s c fs) K ms
      exe endPc R F c0 :=
  stubHN_w2 hI hprog hphs hR hR8 hlo hhi hl hh hF hsub hfit hFO hc hobl hrel htk hk hKex hms hK hwr
    (stubHAb hI hpr hprog hphs hR hlo hhi htk)

end Ab

/-! ## At the record of an output passing `placeOK` -/

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (μ K)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- The heap exit call's label resolves (A6's sites). -/
theorem heap_codeLabel : ∃ a, codeLabel (Λ).code.lo o.prog Abort.heap.exit = some a := by
  obtain ⟨-, -, -, he, -, -, -, -, -, -, hhe, -, -, -, -⟩ := sites7 h
  exact ⟨he, hhe⟩

/-- The heap exit call's address is its `codeLabel` address. -/
theorem heap_toNat {a : Nat}
    (ha : codeLabel (Λ).code.lo o.prog "scc_rt_abort_heap_exit" = some a) :
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.heap.exit).toBitVec.toNat = a :=
  lab_toNat h i ha

/-- **`hrel`** (heap): the heap exit call is off the release site. -/
theorem hrelH_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .release = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.heap.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, -, hr, -, hhe, -, -, -, hnd⟩ := sites7 h
  intro a ha
  change codeLabel (Λ).code.lo o.prog "scc_rt_release_site" = some a at ha
  rw [hr] at ha
  cases ha
  rw [heap_toNat h i hhe]
  rintro rfl
  simp at hnd

/-- **`htk`** (heap): the heap exit call is off the take site. -/
theorem htkH_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .take = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.heap.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, -, hhe, -, -, -, hnd⟩ := sites7 h
  intro a ha
  change codeLabel (Λ).code.lo o.prog "scc_rt_take_site" = some a at ha
  rw [ht] at ha
  cases ha
  rw [heap_toNat h i hhe]
  rintro rfl
  simp at hnd

/-- **`hk`** (heap): the heap exit call is no other abort kind's site. -/
theorem hkH_ofPlaceOK : ∀ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.heap.exit).toBitVec.toNat = a → k = .heap := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, hov, hhe, hst, hwr, hth, hnd⟩ := sites7 h
  intro k a ha hx
  rw [heap_toNat h i hhe] at hx
  subst hx
  cases k with
  | heap => rfl
  | overflow =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_overflow_exit" = some he at ha
    rw [hov] at ha; cases ha; simp at hnd
  | stack =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_stack_exit" = some he at ha
    rw [hst] at ha; cases ha; simp at hnd
  | threads =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_threads_exit" = some he at ha
    rw [hth] at ha; cases ha; simp at hnd
  | writeErr =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_write_exit" = some he at ha
    rw [hwr] at ha; cases ha; simp at hnd

/-- **`hKex`** (heap): no outside move (the take, at the take site) at the
heap exit call. -/
theorem hKexH_ofPlaceOK {rS : Scc.Sem.Range} : ∀ s s', Scc.Sem.X64.pcOf s =
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.heap.exit).toBitVec.toNat →
    ¬ K (RuntimeLayout.ofPlaceOK h i) rS s s' := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, -, hhe, -, -, -, hnd⟩ := sites7 h
  intro s s' hpc hK
  rw [Scc.Sem.X64.pcOf, Spike.Lib.X64.Flow.Ret0.TakeK.pc hK, lab_toNat h i (l := "scc_rt_take_site") ht,
    heap_toNat h i hhe] at hpc
  subst hpc
  simp at hnd

/-- **`hms`** (heap): a memory side aborting at every abort site of the
record (`msOf`'s, `msOfA`'s) aborts at the heap exit call. -/
theorem hmsH_ofPlaceOK {ms : MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s) :
    ∀ s : State, s.exe = (RuntimeLayout.ofPlaceOK h i).exe →
      s.st.2 = (RuntimeLayout.ofPlaceOK h i).lab Abort.heap.exit → ms.abortAt s := by
  obtain ⟨a, ha⟩ := heap_codeLabel h
  intro s _ hs
  refine hma s ⟨.heap, a, (abortAt_eq h i _).trans ha, ?_⟩
  rw [Scc.Sem.X64.pcOf, hs, lab_toNat h i ha]

/-- **`hms`** (overflow) for a memory side aborting at every abort site of
the record (`hms_ofPlaceOK` is `msOf`'s). -/
theorem hmsO_ofPlaceOK {ms : MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s) :
    ∀ s : State, s.exe = (RuntimeLayout.ofPlaceOK h i).exe →
      s.st.2 = (RuntimeLayout.ofPlaceOK h i).lab Abort.overflow.exit → ms.abortAt s := by
  obtain ⟨a, ha⟩ := ovf_codeLabel h
  intro s _ hs
  refine hma s ⟨.overflow, a, (abortAt_eq h i _).trans ha, ?_⟩
  rw [Scc.Sem.X64.pcOf, hs, lab_toNat h i ha]

variable {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {c0 : Ctl} {rS : Range}

/-- **`stubON_w2Ab` at the record of an output passing `placeOK`**: the
instance (`instOk_ofPlaceOK`), the abort and `print` code, the stub's
`write` call, the overflow path's phase check and the exit call's site
premises discharged; the memory side any aborting at the record's abort
sites with the ABI's kernel. -/
theorem stubON_w2_ofPlaceOK (hp : ProgNoS ZBad p)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0) (hsm : EnvSmall c0.env)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0)
    {ms : MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
      (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.overflow c0 .sys) s c → Dt s)
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs) (hcw : CtlW2 c0 fs) :
    StubON (fun s c => W2 Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R F c0 :=
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  stubON_w2Ab (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i) hp (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i)
    (hsysIn_ofPlaceOK h i) (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h i) hR hR8 hlo hhi hl hh hF hsub hfit hFO
    hc hsm hpl (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i) (hk_ofPlaceOK h i) (hKex_ofPlaceOK h i)
    (hmsO_ofPlaceOK h i hma) hK hwr hfp hcw

/-- **`stubHN_w2Ab` at the record of an output passing `placeOK`**: as
`stubON_w2_ofPlaceOK`, the heap path's phase check from
`abortPhHeapOk_ofPlaceOK`. -/
theorem stubHN_w2_ofPlaceOK
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hc : NbCtl Λ p (fun s _ => Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl F c0 fs)
    (hobl : HeapAbortObl ar.cells ar.ctr c0)
    {ms : MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
      (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.heap c0 .sys) s c → Dt s) :
    StubHN (fun s c => W2 Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R F c0 :=
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  stubHN_w2Ab (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i) (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i)
    (Spike.Lib.X64.PhRec.abortPhHeapOk_ofPlaceOK h i)
    hR hR8 hlo hhi hl hh hF hsub hfit hFO hc hobl (hrelH_ofPlaceOK h i) (htkH_ofPlaceOK h i)
    (hkH_ofPlaceOK h i) (hKexH_ofPlaceOK h i) (hmsH_ofPlaceOK h i hma) hK hwr

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.stubON_w2Ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubON_w2Ab

/-- info: 'Spike.Lib.LowerX64.stubHN_w2Ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_w2Ab

/-- info: 'Spike.Lib.LowerX64.hkH_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hkH_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.stubON_w2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubON_w2_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.stubHN_w2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_w2_ofPlaceOK

end Spike.Lib.LowerX64
