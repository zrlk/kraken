/-
**hello's root immediate table on x86-64**: the twin of `A64.HelloPh.C0S.immsH`, `A64.HelloPh.ImmsH.iH`,
`A64.HelloPh.ImmsRd.i0Rd`/`iRd` and `A64.HelloPh.ImmsMe.i0M`/`iRdM` over x86-64's `SccCode.helloImms`
(`Spike/Lib/X64HelloCode.lean`). The certificate's table keeps only `z`, `m` and `two` at
`helloImm_t0/t1/t2`. The root's table `iRdM Λ0 := immsH Λ0 (i0M Λ0)` adds, overriding nothing:
- `me` at main's control block `tcb0 Λ0 = Λ0.pinned.lo + 8` at the setup start's term `setupTerm` (`immsH`);
- the same word at the setup continuation `SrcCalls.setupCont` (`i0M`);
- rodata's immediates past its allocation (`i0Rd`): `m`'s word `2` at the six terms `eW0` … `eN`, the lane
  words `rdK1` at `eO0`'s `w0` and `rdK2` at `eO1`'s `w1`, and `sl`'s words `2` and `13` at `eRet`.

Soundness of the extra entries, as for AArch64: the table only permits immediates, and the placement checks
`ValRep` at every state, so a control whose word differs fails to be placed rather than being wrongly placed.
`ofPlaceWX hp i` accepts any `i`.

Unlike AArch64, the runtime layout is `X64.Rt.RuntimeLayout.ofPlaceWX` at `PlaceWX` (A64 `ofPlaceW` at
`PlaceW`), and the definitions sit in one module: the AArch64 ones live in `A64HelloC0S`/`A64HelloImmsH`/
`A64HelloImmsRd`/`A64HelloImmsMe`, which import AArch64's consumer and syntax and so cannot be imported here.
`tcb0` is `X64WakeLoadT.tcb0`; the rodata terms are `X64HelloRodataSrc`'s.

- `immsH`, `immsH_start`; `iH`, `helloImms_setup_me`, `iH_of_ne`.
- `i0Rd`, `iRd`, `i0Rd_helloImms`; `i0M`, `iRdM`, `i0M_i0Rd`.
- `hme_iRdM`, `hmeC_iRdM`, `hm_iRdM`, `rdImms_iRdM`: the root's layout facts at `ofPlaceWX hp (iRdM Λ0)`.
-/
import Spike.Lib.X64WakeLoadT
import Spike.Lib.X64HelloCode
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64HelloRodataSrc
import Spike.Lib.SrcCalls

namespace Spike.Lib.X64.HelloImms

open CoreLang CoreTerm
open Spike.Lib.X64WakeLoadT (tcb0)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64HelloRodataSrc (eB eW0 eO0 eW1 eO1 eS eN eRet)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2)

open Classical in
/-- **hello's immediate table** at the placement input `Λ0`: at the setup start's term, word 0 of `me` is
main's control block `Λ0.pinned.lo + 8`; elsewhere the base table `i0` (`A64.HelloPh.C0S.immsH`). -/
noncomputable def immsH (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) (e : Expr) (x : String)
    (k : Nat) : Option Nat :=
  if e = Scc.Sem.SrcSem.setupTerm ∧ x = "me" ∧ k = 0 then some (Λ0.pinned.lo + 8) else i0 e x k

/-- At the setup start's term, word 0 of `me` is main's control block. -/
theorem immsH_start (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) :
    immsH Λ0 i0 Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ0) := by
  simp [immsH, tcb0]

/-- **The certificate's table plus `me` at the start** (`A64.HelloPh.ImmsH.iH`). -/
noncomputable abbrev iH (Λ0 : Scc.Sem.Layout) : Expr → String → Nat → Option Nat :=
  immsH Λ0 SccCode.helloImms

/-- **`helloImms` has no entry at the setup start's `me`**: `iH` overrides nothing. -/
theorem helloImms_setup_me : SccCode.helloImms Scc.Sem.SrcSem.setupTerm "me" 0 = none := by
  simp [SccCode.helloImms, Scc.Sem.SrcSem.setupTerm, SccCode.helloImm_t0, SccCode.helloImm_t1,
    SccCode.helloImm_t2]

/-- **Off the start's `me`, `iH` is the certificate's table.** -/
theorem iH_of_ne {Λ0 : Scc.Sem.Layout} {e : Expr} {x : String} {k : Nat}
    (h : ¬ (e = Scc.Sem.SrcSem.setupTerm ∧ x = "me" ∧ k = 0)) : iH Λ0 e x k = SccCode.helloImms e x k := by
  simp only [iH, immsH, h, ite_false]

open Classical in
/-- **The certificate's table plus rodata's immediates** past the allocation (`A64.HelloPh.ImmsRd.i0Rd`). -/
noncomputable def i0Rd (e : Expr) (x : String) (k : Nat) : Option Nat :=
  if (e = eW0 ∨ e = eO0 ∨ e = eW1 ∨ e = eO1 ∨ e = eS ∨ e = eN) ∧ x = "m" ∧ k = 0 then some 2
  else if e = eO0 ∧ x = "w0" ∧ k = 0 then some rdK1
  else if e = eO1 ∧ x = "w1" ∧ k = 0 then some rdK2
  else if e = eRet ∧ x = "sl" ∧ k = 1 then some 2
  else if e = eRet ∧ x = "sl" ∧ k = 2 then some 13
  else SccCode.helloImms e x k

/-- **`i0Rd` plus `me` at the start** (`A64.HelloPh.ImmsRd.iRd`). -/
noncomputable abbrev iRd (Λ0 : Scc.Sem.Layout) : Expr → String → Nat → Option Nat :=
  immsH Λ0 i0Rd

/-- **`i0Rd` extends `helloImms`**: the added keys are off `helloImms`'s three terms. -/
theorem i0Rd_helloImms {e : Expr} {x : String} {k : Nat} {n : Nat} (h : SccCode.helloImms e x k = some n) :
    i0Rd e x k = some n := by
  have he : e = SccCode.helloImm_t2 ∨ e = SccCode.helloImm_t1 ∨ e = SccCode.helloImm_t0 := by
    unfold SccCode.helloImms at h
    by_cases h2 : e = SccCode.helloImm_t2
    · exact .inl h2
    by_cases h1 : e = SccCode.helloImm_t1
    · exact .inr (.inl h1)
    by_cases h0 : e = SccCode.helloImm_t0
    · exact .inr (.inr h0)
    simp [h2, h1, h0] at h
  have hne : ¬ (e = eW0 ∨ e = eO0 ∨ e = eW1 ∨ e = eO1 ∨ e = eS ∨ e = eN) ∧ ¬ e = eRet := by
    rcases he with rfl | rfl | rfl <;>
      simp [eW0, eO0, eW1, eO1, eS, eN, eRet, Spike.Lib.X64HelloRodataSrc.eSm, Spike.Lib.X64HelloRodataSrc.eSl0,
        Spike.Lib.X64HelloRodataSrc.ePack, SccCode.helloImm_t2, SccCode.helloImm_t1, SccCode.helloImm_t0]
  have hO0 : ¬ e = eO0 := fun h' => hne.1 (.inr (.inl h'))
  have hO1 : ¬ e = eO1 := fun h' => hne.1 (.inr (.inr (.inr (.inl h'))))
  unfold i0Rd
  have hm : ¬ ((e = eW0 ∨ e = eO0 ∨ e = eW1 ∨ e = eO1 ∨ e = eS ∨ e = eN) ∧ x = "m" ∧ k = 0) :=
    fun h' => hne.1 h'.1
  simp only [hne.2, hO0, hO1, false_and, ite_false]
  split
  · exact absurd ‹_› hm
  · exact h

open Classical in
/-- **`i0Rd` plus `me` at `tcb0 Λ0` at the setup continuation** (`A64.HelloPh.ImmsMe.i0M`). -/
noncomputable def i0M (Λ0 : Scc.Sem.Layout) (e : Expr) (x : String) (k : Nat) : Option Nat :=
  if e = Spike.Lib.SrcCalls.setupCont ∧ x = "me" ∧ k = 0 then some (tcb0 Λ0) else i0Rd e x k

/-- **The root's immediate table with `me` at both setup terms** (`A64.HelloPh.ImmsMe.iRdM`). -/
noncomputable abbrev iRdM (Λ0 : Scc.Sem.Layout) : Expr → String → Nat → Option Nat :=
  immsH Λ0 (i0M Λ0)

/-- **`i0M` is `i0Rd` off the added key**. -/
theorem i0M_i0Rd {Λ0 : Scc.Sem.Layout} {e : Expr} {x : String} {k : Nat}
    (h : ¬ (e = Spike.Lib.SrcCalls.setupCont ∧ x = "me" ∧ k = 0)) : i0M Λ0 e x k = i0Rd e x k := by
  simp only [i0M, h, ite_false]

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o)

/-- **The start's `hme` at the root's layout**: `me` at `tcb0` at `setupTerm`. -/
theorem hme_iRdM :
    let Λ := (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ
    Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ) :=
  immsH_start Λ0 _

/-- **`me` at `tcb0` at the setup continuation** at the root's layout. -/
theorem hmeC_iRdM :
    let Λ := (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ
    Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 Λ) := by
  show iRdM Λ0 Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 Λ0)
  have hne : Spike.Lib.SrcCalls.setupCont ≠ Scc.Sem.SrcSem.setupTerm := by
    simp [Spike.Lib.SrcCalls.setupCont, Scc.Sem.SrcSem.setupTerm]
  simp [iRdM, immsH, i0M, hne]

/-- **rodata's `m` at `eB`** at the root's layout. -/
theorem hm_iRdM : (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ.imms eB "m" 0 = some 2 := by
  show iRdM Λ0 eB "m" 0 = some 2
  have h1 : eB ≠ Scc.Sem.SrcSem.setupTerm := by simp [eB, Scc.Sem.SrcSem.setupTerm]
  have h2 : eB ≠ Spike.Lib.SrcCalls.setupCont := by simp [eB, Spike.Lib.SrcCalls.setupCont]
  have h3 : SccCode.helloImms eB "m" 0 = some 2 := by
    have : eB = SccCode.helloImm_t2 := rfl
    rw [this]; simp [SccCode.helloImms]
  simp only [iRdM, immsH, i0M, h1, h2, false_and, ite_false]
  exact i0Rd_helloImms h3

/-- **rodata's immediates at the root's layout** (`m`, `w0`, `w1`, `sl1`, `sl2`, in that order). -/
theorem rdImms_iRdM :
    let Λ := (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ
    (∀ e ∈ [eW0, eO0, eW1, eO1, eS, eN], Λ.imms e "m" 0 = some 2) ∧
      Λ.imms eO0 "w0" 0 = some rdK1 ∧ Λ.imms eO1 "w1" 0 = some rdK2 ∧
      Λ.imms eRet "sl" 1 = some 2 ∧ Λ.imms eRet "sl" 2 = some 13 := by
  show (∀ e ∈ [eW0, eO0, eW1, eO1, eS, eN], iRdM Λ0 e "m" 0 = some 2) ∧
      iRdM Λ0 eO0 "w0" 0 = some rdK1 ∧ iRdM Λ0 eO1 "w1" 0 = some rdK2 ∧
      iRdM Λ0 eRet "sl" 1 = some 2 ∧ iRdM Λ0 eRet "sl" 2 = some 13
  simp only [iRdM, immsH, i0M, i0Rd]
  refine ⟨fun e he => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [eW0, eO0, eW1, eO1, eS, eN, eRet, Scc.Sem.SrcSem.setupTerm, Spike.Lib.SrcCalls.setupCont]

end Root

/-- At any `Λ0` the table has `me` at both setup terms and rodata's `m` at `eW0`, while the certificate's
`two` at `helloImm_t2` survives. -/
example (Λ0 : Scc.Sem.Layout) :
    iRdM Λ0 Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ0) ∧
      iRdM Λ0 Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 Λ0) ∧
      iRdM Λ0 eW0 "m" 0 = some 2 ∧ iRdM Λ0 SccCode.helloImm_t2 "two" 0 = some 2 := by
  refine ⟨immsH_start _ _, ?_, ?_, ?_⟩
  · simp [immsH, i0M, Spike.Lib.SrcCalls.setupCont, Scc.Sem.SrcSem.setupTerm]
  · simp [immsH, i0M, i0Rd, eW0, Scc.Sem.SrcSem.setupTerm, Spike.Lib.SrcCalls.setupCont]
  · have h1 : SccCode.helloImm_t2 ≠ Scc.Sem.SrcSem.setupTerm := by
      simp [SccCode.helloImm_t2, Scc.Sem.SrcSem.setupTerm]
    have h2 : SccCode.helloImm_t2 ≠ Spike.Lib.SrcCalls.setupCont := by
      simp [SccCode.helloImm_t2, Spike.Lib.SrcCalls.setupCont]
    simp only [immsH, i0M, h1, h2, false_and, ite_false]
    exact i0Rd_helloImms (by simp [SccCode.helloImms])

end Spike.Lib.X64.HelloImms

/-- info: 'Spike.Lib.X64.HelloImms.immsH_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.immsH_start

/-- info: 'Spike.Lib.X64.HelloImms.helloImms_setup_me' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.helloImms_setup_me

/-- info: 'Spike.Lib.X64.HelloImms.i0Rd_helloImms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.i0Rd_helloImms

/-- info: 'Spike.Lib.X64.HelloImms.hmeC_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.hmeC_iRdM

/-- info: 'Spike.Lib.X64.HelloImms.hm_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.hm_iRdM

/-- info: 'Spike.Lib.X64.HelloImms.rdImms_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloImms.rdImms_iRdM
