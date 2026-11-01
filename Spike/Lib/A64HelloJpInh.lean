/-
**Non-vacuity of level 1's `wc_rodata` invariants along the source's own steps** (AArch64;
non-vacuity): `MainWcL1R.hW_L1` and `MainWcPS`'s source fields are proved at `.sp0`'s
`JpT (JpL …) TV` and `RdSrcL1`'s `jP'` … `jRet` (`J5`), and `MainWcL1R.rdPostW_of_inh` drops `RdPostW`'s premises
at an empty `Jp`. `MainWcL1P.jpT_of_rdLandH` shows `JpT (JpL …) TV` is inhabited at every landing level 1
starts from; here every later invariant is inhabited too, by states the source's own steps reach from it (the
`asLanes` steps `hr0_rd`/`hr2_rd`, the exchanges' stores `h2_rd`/`h4_rd`, the publication's fence `hfen_rd`), all at
the same `.sp0` abstract state, so `J5` (`jRet`, `hedge`'s antecedent) is not empty either.

- `chain_of_jpT`: from a `.sp0` state of `JpT (JpL …) t` below `rdCN`, the eight invariants chained by the source's
  steps.
- `chain_of_rdLandH`: at the root's choices, from every state of level 0's landing `RdLandH` (`Level1I.hB_land`'s
  precondition).

No new invariant is introduced here. No absolute address appears in a statement here.
-/
import Spike.Lib.A64HelloMainWcL1P

namespace Spike.Lib.A64.HelloPh.JpInh

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib (MemSide Region Ctl LocalRun FenceRun)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Hello1 (mRdJ0)
open Spike.Lib.A64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.WakePh.MainGlue (JS)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.A64.HelloPh.RdSrcL1 (jP' jX1 jC2 jC2' jX3 jC4 jRet)
open Spike.Lib.HelloRodataSrc (rdCN)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- **The eight invariants chained by the source's steps** (module doc): from `.sp0` at `JpT (JpL …) t` below
`rdCN` (`hJ1`), the `asLanes` step to `jP'`, a held first word `jX1`, its store's successor `jC2` (`h2_rd`), the
second `asLanes` step to `jC2'`, a held second word `jX3`, its store's successor `jC4` (`h4_rd`), the publication's
fence to `jRet`, all at `.sp0`'s abstract state `σ` and the placement `upd L0 l b`. -/
theorem chain_of_jpT {p : Prog} {P : Prop} (hP : P) {R : Region} {ms₀ : MemSide isaLSE2} {lab : Label → Int64}
    {J0 J1 : FAS → Ctl → Prop} {L0 : Lbl} {l : WeakMem.AllocLabel} {b w : Nat} {t : UInt64}
    (hJ1 : ∀ σ c, J1 σ c → c = rdCN) {σ : FAS} {c0 : Ctl}
    (h : JpT (JpL (R := R) ms₀ lab J0 J1 l b w) t σ c0) :
    ∃ c1 c2 c3 c4 c5 c6 c7 : Ctl,
      LocalRun p c0 c1 ∧ jP' (Spike.Lib.A64ConsumerA.upd L0 l b) l σ c1 ∧
      jX1 (Spike.Lib.A64ConsumerA.upd L0 l b) l σ c2 ∧ jC2 (Spike.Lib.A64ConsumerA.upd L0 l b) l σ c3 ∧
      LocalRun p c3 c4 ∧ jC2' (Spike.Lib.A64ConsumerA.upd L0 l b) l σ c4 ∧
      jX3 (Spike.Lib.A64ConsumerA.upd L0 l b) l σ c5 ∧ jC4 (Spike.Lib.A64ConsumerA.upd L0 l b) l σ c6 ∧
      FenceRun p P .st c6 c7 ∧ jRet (Spike.Lib.A64ConsumerA.upd L0 l b) l σ c7 := by
  have hJp := Spike.Lib.A64.HelloPh.RdJpL.jpT_rb (R := R) (ms₀ := ms₀) (lab := lab) (J0 := J0) (L0 := L0) (l := l)
    (b := b) (w := w) (t := t) hJ1
  obtain ⟨c1, hr1, hj1⟩ := Spike.Lib.A64.HelloPh.RdSrcL1.hr0_rd (p := p) hJp σ c0 h
  obtain ⟨hB, ini, -⟩ := id hj1
  have hx1 : jX1 (Spike.Lib.A64ConsumerA.upd L0 l b) l σ
      { Spike.Lib.HelloRodataSrc.rdC1 l ini with
        hold := some ((Spike.Lib.A64.Flow.rAddr σ.regs .X0 0).toNat, TermRun.cst (.num 0)) } :=
    ⟨hB, ini, _, rfl⟩
  obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, hc2⟩ := Spike.Lib.A64.HelloPh.RdSrcL1.h2_rd _ _ hx1
  obtain ⟨c4, hr4, hj4⟩ := Spike.Lib.A64.HelloPh.RdSrcL1.hr2_rd (p := p) _ _ hc2
  obtain ⟨-, ini2, wo0, -⟩ := id hj4
  have hx3 : jX3 (Spike.Lib.A64ConsumerA.upd L0 l b) l σ
      { Spike.Lib.HelloRodataSrc.rdC3 l ini2 wo0 with
        hold := some ((Spike.Lib.A64.Flow.rAddr σ.regs .X0 8).toNat, TermRun.cst (.num 0)) } :=
    ⟨hB, ini2, wo0, _, rfl⟩
  obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, hc6⟩ := Spike.Lib.A64.HelloPh.RdSrcL1.h4_rd _ _ hx3
  obtain ⟨c7, hf7, hj7⟩ := Spike.Lib.A64.HelloPh.RdSrcL1.hfen_rd (p := p) hP _ _ hc6
  exact ⟨c1, _, _, c4, _, _, c7, hr1, hj1, hx1, hc2, hr4, hj4, hx3, hc6, hf7, hj7⟩

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  {E : Entry} {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls [FR]

set_option hygiene false in
local notation "LBL" => Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b

/-- **Level 1's `wc_rodata` invariants inhabited at every landing it starts from** (module doc): at the root's
choices (`Level1I`'s `.sp0` invariant, `hW_L1`'s `jP'` … `jRet` at `upd (L0T Λ) l b`), chained by the source's
steps from `.sp0`. -/
theorem chain_of_rdLandH {p : Prog} {P : Prop} (hP : P) {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl}
    (h : RdLandH (asm := asm) hpw i0 E rd I ls (fun σC => mRdJ0 (J') σC) l b n s c) :
    ∃ (σC σ : FAS) (c0 c1 c2 c3 c4 c5 c6 c7 : Ctl),
      JpT (JpL (R := swR (TOP) (-helloLsw) 0) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ c0 ∧
      LocalRun p c0 c1 ∧ jP' (LBL) l σ c1 ∧ jX1 (LBL) l σ c2 ∧ jC2 (LBL) l σ c3 ∧ LocalRun p c3 c4 ∧
      jC2' (LBL) l σ c4 ∧ jX3 (LBL) l σ c5 ∧ jC4 (LBL) l σ c6 ∧ FenceRun p P .st c6 c7 ∧ jRet (LBL) l σ c7 := by
  obtain ⟨σC, σ, c0, hj⟩ := Spike.Lib.A64.HelloPh.MainWcL1P.jpT_of_rdLandH hpw i0 h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, h⟩ :=
    chain_of_jpT (p := p) (L0 := Spike.Lib.WakeLoadT.L0T (Ly).Λ) hP
      Spike.Lib.A64.HelloPh.RdJpL.rdJH_rdCN hj
  exact ⟨σC, σ, c0, c1, c2, c3, c4, c5, c6, c7, hj, h⟩

end Root

end Spike.Lib.A64.HelloPh.JpInh

/-- info: 'Spike.Lib.A64.HelloPh.JpInh.chain_of_jpT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.JpInh.chain_of_jpT

/-- info: 'Spike.Lib.A64.HelloPh.JpInh.chain_of_rdLandH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.JpInh.chain_of_rdLandH
