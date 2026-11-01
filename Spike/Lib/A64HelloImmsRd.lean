/-
**hello's root immediate table with rodata's immediates** (AArch64;
extends `A64HelloImmsH`'s `iH`): `SccCode.helloImms` keeps `m`/`two` only at `helloImm_t2` (`let b`, rodata's
allocation), so `HelloRdPlS.placed_rd`'s immediates past the allocation are missing. The table `i0Rd` adds them,
overriding nothing, and the root's table `iRd Λ0 := immsH Λ0 i0Rd` adds `me` at `tcb0` at `setupTerm` as `iH`.

The entries (`HelloRdPlS.RdImms`, hello-b4): `m`'s word `2` at the six terms `eW0` … `eN` (from `let w0` up to
`let n`), the lane words `rdK1` at `eO0`'s `w0` and `rdK2` at `eO1`'s `w1`, and `sl`'s constant words `2` and `13`
(words 1 and 2) at `eRet`.

Soundness of the extra entries as `ImmsH`'s note: the table only permits immediates (`Components.env_imm`), while
`Components.env_rep` checks `WordPlaceRep … (.imm n) w = ValRep lbl w n` at every state, so a control whose word
differs fails to be placed rather than being wrongly placed. `ofPlaceW hp i` accepts any `i`.

- `i0Rd`, `iRd`: the tables.
- `i0Rd_helloImms`: `i0Rd` extends `helloImms` (every entry of `helloImms` is `i0Rd`'s).
- `hme_iRd`: the start's `hme` at `ofPlaceW hp (iRd Λ0)`.
- `rdImms_iRd`: `RdImms`'s five fields at `ofPlaceW hp (iRd Λ0)`, as a conjunction in their order (`m`, `w0`,
  `w1`, `sl1`, `sl2`), so `⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ : RdImms _`.
-/
import Spike.Lib.A64HelloImmsH
import Spike.Lib.HelloRodataSrc

namespace Spike.Lib.A64.HelloPh.ImmsRd

open CoreLang CoreTerm
open Spike.Lib.WakeLoadT (tcb0)
open Spike.Lib.A64.HelloPh.C0S (immsH immsH_start)
open Spike.Lib.HelloRodataSrc (eW0 eO0 eW1 eO1 eS eN eRet)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2)

open Classical in
/-- **The certificate's table plus rodata's immediates** past the allocation (module doc). -/
noncomputable def i0Rd (e : Expr) (x : String) (k : Nat) : Option Nat :=
  if (e = eW0 ∨ e = eO0 ∨ e = eW1 ∨ e = eO1 ∨ e = eS ∨ e = eN) ∧ x = "m" ∧ k = 0 then some 2
  else if e = eO0 ∧ x = "w0" ∧ k = 0 then some rdK1
  else if e = eO1 ∧ x = "w1" ∧ k = 0 then some rdK2
  else if e = eRet ∧ x = "sl" ∧ k = 1 then some 2
  else if e = eRet ∧ x = "sl" ∧ k = 2 then some 13
  else SccCode.helloImms e x k

/-- **The root's immediate table with rodata's immediates**: `i0Rd` plus `me` at `tcb0 Λ0` at `setupTerm`
(`iH`'s extension). -/
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
      simp [eW0, eO0, eW1, eO1, eS, eN, eRet, Spike.Lib.HelloRodataSrc.eSm, Spike.Lib.HelloRodataSrc.eSl0,
        Spike.Lib.HelloRodataSrc.ePack, SccCode.helloImm_t2, SccCode.helloImm_t1, SccCode.helloImm_t0]
  have hO0 : ¬ e = eO0 := fun h' => hne.1 (.inr (.inl h'))
  have hO1 : ¬ e = eO1 := fun h' => hne.1 (.inr (.inr (.inr (.inl h'))))
  unfold i0Rd
  have hm : ¬ ((e = eW0 ∨ e = eO0 ∨ e = eW1 ∨ e = eO1 ∨ e = eS ∨ e = eN) ∧ x = "m" ∧ k = 0) :=
    fun h' => hne.1 h'.1
  simp only [hne.2, hO0, hO1, false_and, ite_false]
  split
  · exact absurd ‹_› hm
  · exact h

/-- **The start's `hme` at the root's layout**: at `ofPlaceW hp (iRd Λ0)`, `me` at `tcb0` at `setupTerm`. -/
theorem hme_iRd {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRd Λ0)).Λ
    Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ) :=
  immsH_start Λ0 _

/-- **`RdImms`'s fields at the root's layout** (`m`, `w0`, `w1`, `sl1`, `sl2`; module doc). -/
theorem rdImms_iRd {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRd Λ0)).Λ
    (∀ e ∈ [eW0, eO0, eW1, eO1, eS, eN], Λ.imms e "m" 0 = some 2) ∧
      Λ.imms eO0 "w0" 0 = some rdK1 ∧ Λ.imms eO1 "w1" 0 = some rdK2 ∧
      Λ.imms eRet "sl" 1 = some 2 ∧ Λ.imms eRet "sl" 2 = some 13 := by
  show (∀ e ∈ [eW0, eO0, eW1, eO1, eS, eN], iRd Λ0 e "m" 0 = some 2) ∧
      iRd Λ0 eO0 "w0" 0 = some rdK1 ∧ iRd Λ0 eO1 "w1" 0 = some rdK2 ∧
      iRd Λ0 eRet "sl" 1 = some 2 ∧ iRd Λ0 eRet "sl" 2 = some 13
  simp only [iRd, immsH, i0Rd]
  refine ⟨fun e he => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [eW0, eO0, eW1, eO1, eS, eN, eRet, Scc.Sem.SrcSem.setupTerm]

end Spike.Lib.A64.HelloPh.ImmsRd

/-- info: 'Spike.Lib.A64.HelloPh.ImmsRd.i0Rd_helloImms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsRd.i0Rd_helloImms

/-- info: 'Spike.Lib.A64.HelloPh.ImmsRd.hme_iRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsRd.hme_iRd

/-- info: 'Spike.Lib.A64.HelloPh.ImmsRd.rdImms_iRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsRd.rdImms_iRd
