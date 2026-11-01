/-
**hello's root immediate table with `me` at the setup continuation** (AArch64;
extends `A64HelloImmsRd`'s `iRd`): `HabCtlRdI.placedS_rdCN` places `rdCN` under
the setup call's frame `frH c0S.env` at every state with every word at an immediate, and the frame still reads
`me` (`SrcCalls.setupCont`'s free variables less `r`). So the root's table needs `me`'s word at `tcb0` at
`setupCont` as well as at `setupTerm` (`C0S.immsH`'s). The table `i0M Λ0` adds it to `ImmsRd.i0Rd`, overriding
nothing, and the root's table is `iRdM Λ0 := immsH Λ0 (i0M Λ0)` (a `C0S.immsH Λ0 i0` table, so `StartH0R0` /
`StartH0U0` apply at `i0 := i0M Λ0`).

Soundness of the extra entry as `ImmsH`'s note: the table only permits immediates, and `Components.env_rep`
checks `ValRep` at every state, so a control whose `me` differs fails to be placed rather than being wrongly
placed; `me`'s word is main's `ThreadId` box at `tcb0` (`WakeImmsW.valRep_me`), as at `setupTerm`.

- `i0M`, `iRdM`: the tables.
- `i0M_i0Rd`: `i0M` is `i0Rd` off `(setupCont, "me", 0)`.
- `hme_iRdM`, `hmeC_iRdM`: `me` at `tcb0` at `setupTerm` and at `setupCont` at `ofPlaceW hp (iRdM Λ0)`.
- `hm_iRdM`: `rdCN`'s `m` (word `2`) at `eB` (`HabCtlRdI.placedS_rdCN`'s `hm`).
- `rdImms_iRdM`: `ImmsRd.rdImms_iRd`'s five fields at `ofPlaceW hp (iRdM Λ0)`.
-/
import Spike.Lib.A64HelloImmsRd

namespace Spike.Lib.A64.HelloPh.ImmsMe

open CoreLang CoreTerm
open Spike.Lib.WakeLoadT (tcb0)
open Spike.Lib.A64.HelloPh.C0S (immsH immsH_start)
open Spike.Lib.A64.HelloPh.ImmsRd (i0Rd)
open Spike.Lib.HelloRodataSrc (eB eW0 eO0 eW1 eO1 eS eN eRet)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2)

open Classical in
/-- **`i0Rd` plus `me` at `tcb0 Λ0` at the setup continuation** (module doc). -/
noncomputable def i0M (Λ0 : Scc.Sem.Layout) (e : Expr) (x : String) (k : Nat) : Option Nat :=
  if e = Spike.Lib.SrcCalls.setupCont ∧ x = "me" ∧ k = 0 then some (tcb0 Λ0) else i0Rd e x k

/-- **The root's immediate table with `me` at both setup terms** (`immsH`'s `setupTerm` entry, `i0M`'s
`setupCont` entry, rodata's immediates). -/
noncomputable abbrev iRdM (Λ0 : Scc.Sem.Layout) : Expr → String → Nat → Option Nat :=
  immsH Λ0 (i0M Λ0)

/-- **`i0M` is `i0Rd` off the added key**. -/
theorem i0M_i0Rd {Λ0 : Scc.Sem.Layout} {e : Expr} {x : String} {k : Nat}
    (h : ¬ (e = Spike.Lib.SrcCalls.setupCont ∧ x = "me" ∧ k = 0)) : i0M Λ0 e x k = i0Rd e x k := by
  simp only [i0M, h, ite_false]

/-- **The start's `hme` at the root's layout**: `me` at `tcb0` at `setupTerm`. -/
theorem hme_iRdM {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ
    Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ) :=
  immsH_start Λ0 _

/-- **`me` at `tcb0` at the setup continuation** at the root's layout (`HabCtlRdI.placedS_rdCN`'s `hme`). -/
theorem hmeC_iRdM {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ
    Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 Λ) := by
  show iRdM Λ0 Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 Λ0)
  have hne : Spike.Lib.SrcCalls.setupCont ≠ Scc.Sem.SrcSem.setupTerm := by
    simp [Spike.Lib.SrcCalls.setupCont, Scc.Sem.SrcSem.setupTerm]
  simp [iRdM, immsH, i0M, hne]

/-- **`rdCN`'s `m` at `eB`** at the root's layout (`HabCtlRdI.placedS_rdCN`'s `hm`). -/
theorem hm_iRdM {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) :
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ.imms eB "m" 0 = some 2 := by
  show iRdM Λ0 eB "m" 0 = some 2
  have h1 : eB ≠ Scc.Sem.SrcSem.setupTerm := by simp [eB, Scc.Sem.SrcSem.setupTerm]
  have h2 : eB ≠ Spike.Lib.SrcCalls.setupCont := by simp [eB, Spike.Lib.SrcCalls.setupCont]
  have h3 : SccCode.helloImms eB "m" 0 = some 2 := by
    have : eB = SccCode.helloImm_t2 := rfl
    rw [this]; simp [SccCode.helloImms]
  simp only [iRdM, immsH, i0M, h1, h2, false_and, ite_false]
  exact Spike.Lib.A64.HelloPh.ImmsRd.i0Rd_helloImms h3

/-- **`RdImms`'s fields at the root's layout** (`m`, `w0`, `w1`, `sl1`, `sl2`; `ImmsRd.rdImms_iRd`'s). -/
theorem rdImms_iRdM {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ
    (∀ e ∈ [eW0, eO0, eW1, eO1, eS, eN], Λ.imms e "m" 0 = some 2) ∧
      Λ.imms eO0 "w0" 0 = some rdK1 ∧ Λ.imms eO1 "w1" 0 = some rdK2 ∧
      Λ.imms eRet "sl" 1 = some 2 ∧ Λ.imms eRet "sl" 2 = some 13 := by
  show (∀ e ∈ [eW0, eO0, eW1, eO1, eS, eN], iRdM Λ0 e "m" 0 = some 2) ∧
      iRdM Λ0 eO0 "w0" 0 = some rdK1 ∧ iRdM Λ0 eO1 "w1" 0 = some rdK2 ∧
      iRdM Λ0 eRet "sl" 1 = some 2 ∧ iRdM Λ0 eRet "sl" 2 = some 13
  simp only [iRdM, immsH, i0M, i0Rd]
  refine ⟨fun e he => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [eW0, eO0, eW1, eO1, eS, eN, eRet, Scc.Sem.SrcSem.setupTerm, Spike.Lib.SrcCalls.setupCont]

end Spike.Lib.A64.HelloPh.ImmsMe

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.i0M_i0Rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.i0M_i0Rd

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.hme_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.hme_iRdM

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.hmeC_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.hmeC_iRdM

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.hm_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.hm_iRdM

/-- info: 'Spike.Lib.A64.HelloPh.ImmsMe.rdImms_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsMe.rdImms_iRdM
