/-
**hello.w's level 1 at the root with the child's stack unmapped** (AArch64; the root wiring): the root's level 1 is
`W1H … (CtxU ∘ CtxR1H) …` with invariant `inv ∧ U r1Of`, lifted from a
level-1 instance at `CtxR1H` (`Level1I`) by `LandR1U.segInv1_U`, so `HelloRootO.oPremH_R`'s `hW1` is
`LandR1U.hW1_RUμ` with `RootHP.hland2_boxMRU` (no run-level `hUn1`; the box's ghost `RootHP.GJ1RH`).

`U r1Of` enters level 1 at its entry, rodata's landing (`RdLandH`, `h1`'s `Rd`): `rdLand_U` reads it off the
landing, where `LandRd.hlandRd_U` puts it from `HLandRdU`'s `U` at `n4`, itself kept by `RootUL.ctrRow_ofFTU`
from level 0's context `LandRU.CtxRdU` (`U` there from the start's witness, `RootUL.hst0_UH`).

- `W1RU`, `inv1RU`: the root's level 1 and its invariant.
- `rdLand_U`: `U r1Of` at level 1's entry (non-vacuity of the lift: a lemma, no premise).
- `h1StmtHF_U`: `HelloPreA.H1StmtHF` at `W1H … CtxR1H …` gives it at `W1RU`/`inv ∧ U` for an `Rd` with `U`.
- `h1t_U`: `H1TakeH` at `inv` gives it at `inv ∧ U`.
- `h1_rootU`: `oPremH_R`'s `h1` at `W1RU`/`inv1RU` from the level's segments at `CtxR1H`.
- `hW1_rootU`: `oPremH_R`'s `hW1` at `W1RU` (`hW1_RUμ`, `RootHP.hland2_boxMRU`).
-/
import Spike.Lib.A64HelloRootHP
import Spike.Lib.HelloRootO

namespace Spike.Lib.A64.HelloPh.RootL1U

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SFactsACH SegInvS TakeCKS msOfA I3)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib (FragS MemSide Arena)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.HelloM (wcF)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.KeepUn (U)
open Spike.Lib.A64.HelloPh.Land (ref1H CtxR1H)
open Spike.Lib.A64.HelloPh.RootUL (CtxU)
open Spike.Lib.A64.HelloPh.LandR1U (HLandM1U segInv1_U hW1_RUμ)
open Spike.Lib.A64.HelloPh.RootHP (GJ1RH hland2_boxMRU)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.A64.HelloWf (W1H)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.HelloHMid (BoxMH slWsH)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloO (IH)
open Spike.Lib.HelloRootO (helloDR)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "TI" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw TI

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- The take site's label. -/
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

/-! ## The root's level 1 -/

/-- **The root's level 1** (`HelloWf.W1H` at the root's data `helloDR`, the context `CtxU (CtxR1H l b n)`). -/
abbrev W1RU (E : Entry) (ls : Lsize) (frM : TermRun.Frame) : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2 :=
  W1H (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly))
    (fun l b n => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E (fun _ => True) ls l b n)) (LB) (ls0T ls) frM (X0WH (Ly)
        (AX))

/-- **The root's level-1 invariant**: a level-1 invariant `inv` with the child's stack unmapped. -/
abbrev inv1RU (inv : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) :
    WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2 :=
  fun l b n s c fs => inv l b n s c fs ∧ U (R1) s

/-! ## `U r1Of` at level 1's entry -/

/-- **rodata's landing has `r1Of` unmapped** (level 1's entry, `h1`'s `Rd`): `RdLandH`'s `U` conjunct, put there by
`LandRd.hlandRd_U` from `HLandRdU`'s `U` at `n4`, which `RootUL.ctrRow_ofFTU` keeps from `LandRU.CtxRdU`. -/
theorem rdLand_U {E : Entry} {rd : TermRun.Word → Prop} {I : InvS} {ls : Lsize}
    {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    {s : State} {c : Spike.Lib.Ctl} (h : RdLandH (asm := asm) hpw i0 E rd I ls J1 l b w s c) : U (R1) s := by
  obtain ⟨-, -, -, -, -, -, -, -, hu, -⟩ := h
  exact hu

/-! ## The level-1 statement and take fact with `U` -/

/-- **`H1StmtHF` at `W1H … CtxR1H …` gives it at `CtxU CtxR1H`, `inv ∧ U r1Of`** (`segInv1_U` per label), for an
entry `Rd` with `r1Of` unmapped (`hRd`, as `rdLand_U`); the clone clause from `inv`'s. -/
theorem h1StmtHF_U (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) {E : Entry}
    {rd : TermRun.Word → Prop} {ls : Lsize} {a : BitVec 64} {ar ar' : Arena} {Dt Cl : State → Prop}
    {L0 L0' : Lbl} {ls0 : Lsize} {frM : TermRun.Frame}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    {Rd : WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop}
    {inv : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {fr : List TermRun.Frame}
    (hK : ∀ l b n fs, (ms1 l b n fs).K = some abi) (hRd : ∀ l b n s c, Rd l b n s c → U (R1) s)
    (h : Spike.Lib.HelloPreA.H1StmtHF (W1H (Ly) a ar helloSrc Dt Cl (CtxR1H (asm := asm) hpw i0 E rd ls) L0 ls0 frM
      (X0WH (Ly) (AX))) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) ar' L0' ms1 (Ly) Rd inv fr) :
    Spike.Lib.HelloPreA.H1StmtHF (W1H (Ly) a ar helloSrc Dt Cl
      (fun l b n => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E rd ls l b n)) L0 ls0 frM (X0WH (Ly) (AX)))
      (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) ar' L0' ms1 (Ly) Rd (inv1RU hpw i0 inv) fr := by
  intro l b n hl hb
  obtain ⟨hS, hR, hpc⟩ := h l b n hl hb
  exact ⟨segInv1_U hpw i0 E rd ls l b n hA13 (hK l b n) hS, fun s c hr => ⟨hR s c hr, hRd l b n s c hr⟩,
    fun s c fs hi => hpc s c fs hi.1⟩

/-- **`H1TakeH` at `inv ∧ U r1Of`** from `inv`'s. -/
theorem h1t_U {a : Int64} {inv : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h : Spike.Lib.HelloPreA.H1TakeH a inv) : Spike.Lib.HelloPreA.H1TakeH a (inv1RU hpw i0 inv) :=
  fun l b n s c fs hi => h l b n s c fs hi.1

/-! ## `oPremH_R`'s level-1 premises -/

variable (E : Entry) (Ctx : FragS isaLSE2) (ls : Lsize) (frM : TermRun.Frame)
  (inv : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
  (W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)

set_option hygiene false in
local notation "D" => helloDR (asm := asm) hpw TI E Ctx ls frM (W1RU (asm := asm) hpw i0 E ls frM) (inv1RU hpw i0
    inv) W2 inv2

set_option hygiene false in
local notation "μE" => (Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ

/-- **`oPremH_R`'s `h1` at `W1RU`/`inv1RU`** from the level's segments at `CtxR1H` (`hL`, `Level1I` at
`I := IH D`) by `segInv1_U`. -/
theorem h1_rootU (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hL : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      SegInvS (W1H (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly))
        (CtxR1H (asm := asm) hpw i0 E (fun _ => True) ls) (LB) (ls0T ls) frM (X0WH (Ly) (AX)) l b n)
        (TakeCKS (D).a (D).Cl) helloSrc (Spike.Lib.A64ConsumerA.upd (D).L0 l b)
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (Spike.Lib.A64ConsumerA.upd (D).L0 l b)
          (Spike.Lib.A64ConsumerA.updN (D).ls0 l n)) (inv l b n)) :
    ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      SegInvS ((D).W1 l b n) (TakeCKS (D).a (D).Cl) helloSrc (Spike.Lib.A64ConsumerA.upd (D).L0 l b)
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (Spike.Lib.A64ConsumerA.upd (D).L0 l b)
          (Spike.Lib.A64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n) :=
  fun l b n hl hb => segInv1_U hpw i0 E (fun _ => True) ls l b n hA13 (fun _ => rfl) (hL l b n hl hb)

/-- **`oPremH_R`'s `hW1` at `W1RU`** (`hW1_RUμ` at `J := IH D`, the store's landings by `hland2_boxMRU` from the
box clause `h2` of `H2StmtH` at the root's box `BoxMH … (GJ1RH …) … ∧ U r1`): the box counter add's tails `hM` with
`U r1Of` (`HLandM1U`), `wc_main`'s frame condition inside `F0` (`hF0`). `Ab`/`Ac` are `W1H`'s. -/
theorem hW1_rootU (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hc : Spike.Lib.A64.Rt.CtrZ o)
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    {L : RuntimeLayout} {endPc : Int64} {F0 : MachineData → Prop}
    (hM : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      HLandM1U (asm := asm) hpw i0 E (fun _ => True) ls l b n
        (IH (D) (Spike.Lib.A64ConsumerA.upd (D).L0 l b) (Spike.Lib.A64ConsumerA.updN (D).ls0 l n)))
    (h2 : Spike.Lib.HelloPreA.H2StmtH W2 K (AR) (LB) ms2 L endPc
      (fun l b n l' A n' s c => BoxMH (Ly) (ref1H (asm := asm) hpw i0 E (fun _ => True) ls l b n []) F0
        (GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l) l' A (slWsH l) n' s c ∧ U (R1) s) inv2)
    (hF0 : ∀ v m1 σ1 m, wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) helloLsw 0#64 v) m1 σ1 m →
      F0 m) :
    ∀ l b n s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n → (D).W1 l b n s c fs →
      SFactsACH (Ly).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (Spike.Lib.A64ConsumerA.upd (D).L0 l b) (Spike.Lib.A64ConsumerA.updN (D).ls0 l n) s c fs (D).Dt
        (Spike.Lib.A64.WriteAb.Ab (Ly).lab) (D).Cl
        (Spike.Lib.A64.HelloWf.AcH (Ly).lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM) := by
  intro l b n s c fs hl hb hW
  have hμ : (μE) = Spike.Lib.A64.PhRec.μ (Ly) := by
    have hr := Scc.Sem.A64.resolve_of_parsed (Scc.Sem.A64.kernel 2) E (Ly).Λ (prog := (Ly).prog) hpa
    unfold Scc.Sem.Target.marks Spike.Lib.A64.PhRec.μ
    congr 1
    · funext k; exact hr _
    · funext k; exact hr _
  rw [hμ]
  exact hW1_RUμ hpw i0 E (fun _ => True) ls l b n hpa hhp hc (P := fun _ _ _ => True) (hM l b n hl hb)
    (hland2_boxMRU hpw i0 E (fun _ => True) ls h2 hl hb hF0) s c fs trivial hW

end Spike.Lib.A64.HelloPh.RootL1U

/-- info: 'Spike.Lib.A64.HelloPh.RootL1U.rdLand_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootL1U.rdLand_U

/-- info: 'Spike.Lib.A64.HelloPh.RootL1U.h1StmtHF_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootL1U.h1StmtHF_U

/-- info: 'Spike.Lib.A64.HelloPh.RootL1U.h1t_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootL1U.h1t_U

/-- info: 'Spike.Lib.A64.HelloPh.RootL1U.h1_rootU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootL1U.h1_rootU

/-- info: 'Spike.Lib.A64.HelloPh.RootL1U.hW1_rootU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootL1U.hW1_rootU
