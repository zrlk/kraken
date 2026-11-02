/-
**hello.w's level 1 at the root with the child's stack unmapped** (x86-64; the twin of
`Spike/Lib/A64HelloRootL1U.lean`'s live part): the root's level 1 is `W1H … (CtxU ∘ CtxR1H) …` with invariant
`inv ∧ U r1Of`, lifted from a level-1 instance at `CtxR1H` by `segInv1_UP` (`LandR1U.segInv1_U` at publication
rows).

`U r1Of` enters level 1 at its entry, rodata's landing (`RdLandH`, `h1`'s `Rd`): `rdLand_U` reads it off the
landing, where `LandRd.hlandRd_U` puts it from `HLandRdU`'s `U` at `c2`, itself kept by `RootUL.ctrRow_ofFTU`
from level 0's context (`U` there from the start's witness, `RootUL.hst0_UH`).

- `W1RU`, `inv1RU`: the root's level 1 and its invariant; `W1RUg`: the level at the owned words `own`
  (`HelloWf.W1Hg own`), `W1RU` its instance at `ownGH`.
- `rdLand_U`: `U r1Of` at level 1's entry (non-vacuity of the lift: a lemma, no premise); `rdLand_Ug` at
  `RdLandHg own`.
- `segInvSP_keepUn`: a segment invariant with publication rows carries `U r` (`WakePh.RootUL.SegInvS.keepUn` at
  `SegInvSP`: the publication changes the control only, so `U r` holds at its row's state).
- `segInv1_UP`: `LandR1U.segInv1_U` at `SegInvSP`; `segInv1_UPg` at `W1Hg own`.
- `h1StmtHF_U`: `HelloPreA.H1StmtHF` at `W1H … CtxR1H …` gives it at `W1RU`/`inv ∧ U` for an `Rd` with `U`;
  `h1StmtHF_Ug` at `W1Hg own`.
- `hW1_rootU`: `oPremH_R`'s `hW1` at `W1RU` (`hW1_RUμ`, `RootHP.hland2_boxMRUg`); `hW1_rootUg`: `oPremH_Rg`'s at
  `W1RUg own` and `helloDRg own` (`LandR1U.hW1_RUμg`, `RootHP.hland2_boxMRUg`, `own` containing `ownGH`),
  `hW1_rootU` its instance.

## Differences from the AArch64 version

- `H1StmtHF`'s segment is a `SegInvSP` (rows may start after the source's publication, `X64SegWPub`; AArch64
  `SegInvS`), so `h1StmtHF_U` lifts by `segInv1_UP`, through `segInvSP_keepUn` (stated here; AArch64 needs only
  `LandR1U.segInv1_U`).
- `rdLand_U`'s `U` is put at the allocator's `c2` (AArch64 `n4`).
- `h1StmtHF_U` takes no `a13data` premise (`LandR1U.takeU_X`'s bound is `X64WakeHClC.hbd_W`).
- `hW1_rootU` reads `W1H` as `W0` by `HelloWf.w1H_def`; the marks are rewritten by
  `Worker.Wake.AbOffW.marks_target` (AArch64 by `resolve_of_parsed`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `h1t_U`, `h1_rootU`.
-/
import Spike.Lib.X64HelloLandR1U
import Spike.Lib.X64HelloStartH0H1
import Spike.Lib.X64HelloWcInv3F
import Spike.Lib.X64SegWPub
import Spike.Lib.X64HelloRootHPL
import Spike.Lib.X64HelloRootO

namespace Spike.Lib.X64.HelloPh.RootL1U

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Scc.Sem.X64 (abi)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib (FragS MemSide Arena PlaceWX OutS)
open Spike.Lib.X64SegWPub (SegInvSP)
open Spike.Lib.X64.KeepUn (U unXa out_un exec_un)
open Spike.Lib.X64.HelloPh.Land (CtxR1H)
open Spike.Lib.X64.HelloPh.RootUL (CtxU)
open Spike.Lib.X64.HelloPh.LandR1U (takeU_X)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartH0H1 (RdLandH RdLandHg)
open Spike.Lib.X64.HelloWf (W1H W1Hg)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.WakePh.RootUL (w0_mono)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64ConsumerA (SFactsACH)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64.Flow.HelloM (wcF)
open Spike.Lib.X64.WakePh.MainGlue (FS RS)
open Spike.Lib.X64.HelloPh.Land (ref1H)
open Spike.Lib.X64.HelloPh.LandR1U (HLandM1U hW1_RUμg)
open Spike.Lib.X64.HelloPh.RootHP (GJ1RH hland2_boxMRUg)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64HelloHMid (BoxMH slWsH)
open Spike.Lib.X64HelloO (IH)
open Spike.Lib.X64HelloRootO (helloDR helloDRg)

/-! ## `U r` at publication rows -/

/-- **A segment invariant with publication rows carries `U r`** (`WakePh.RootUL.SegInvS.keepUn` at `SegInvSP`):
under `ms` with `U r` at its pairs, given outside moves keeping it. A publication row's `OutS` row is at the same
state (the publication moves the control only), so `out_un`/`exec_un` apply to both disjuncts. -/
theorem segInvSP_keepUn {W inv : FragS isa} {K : State → State → Prop} {p : Prog} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isa} {r : Scc.Sem.Range} (hK : ∀ fs, (ms fs).K = some abi)
    (h : SegInvSP W K p lbl ms inv) (hKu : ∀ s c fs, W s c fs → ∀ s', K s s' → U r s → U r s') :
    SegInvSP (fun s c fs => W s c fs ∧ U r s) K p lbl ms (fun s c fs => inv s c fs ∧ U r s) := by
  rintro s c fs ⟨hi, hu⟩
  obtain ⟨hw, ho, hk⟩ := h s c fs hi
  have hO : ∀ c₀, OutS p lbl ms (Spike.Lib.Pend p inv) s c₀ fs →
      OutS p lbl ms (Spike.Lib.Pend p fun s c fs => inv s c fs ∧ U r s) s c₀ fs := fun c₀ h => by
    cases h with
    | pre c₁ fs₁ hr h =>
      exact .pre c₁ fs₁ hr ((out_un (hK fs₁) hu (Spike.Lib.X64ConsumerA.Out.mono_xa (ms' := unXa (ms fs₁) r) h rfl
        fun _ _ _ _ _ h _ => h)).mono fun _ _ ⟨⟨c₂, fs₂, hr₂, hi⟩, hu⟩ => ⟨c₂, fs₂, hr₂, hi, hu⟩)
    | frame s' c' fs' he hr hx =>
      obtain ⟨c₂, fs₂, hr₂, hi⟩ := hx
      exact .frame s' c' fs' he hr ⟨c₂, fs₂, hr₂, hi, exec_un hu he⟩
  refine ⟨⟨hw, hu⟩, fun hn => ?_, fun s' hks => ?_⟩
  · rcases ho hn with h | ⟨hs, hp, c₁, hps, hY, h⟩
    · exact .inl (hO c h)
    · exact .inr ⟨hs, hp, c₁, hps, ⟨hY, hu⟩, hO c₁ h⟩
  · obtain ⟨c', fs', hr, hx⟩ := hk s' hks
    exact ⟨c', fs', hr, hx, hKu s c fs hw s' hks hu⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "TI" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw TI

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- The take site's label. -/
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

/-! ## The root's level 1 -/

/-- **The root's level 1 at the owned words `own`** (`HelloWf.W1Hg own` at the root's data `helloDRg own`, the
context `CtxU (CtxR1H l b n)`). -/
abbrev W1RUg (own : Spike.Lib.X64Consumer.Own) (E : Entry) (ls : Lsize) (frM : TermRun.Frame) :
    WeakMem.AllocLabel → Nat → Nat → FragS isa :=
  W1Hg own (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly))
    (fun l b n => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E (fun _ => True) ls l b n)) (LB) (ls0T ls) frM
    (X0WH (Ly) (AX))

/-- **The root's level 1** (`HelloWf.W1H` at the root's data `helloDR`, the context `CtxU (CtxR1H l b n)`):
`W1RUg` at `ownGH`. -/
abbrev W1RU (E : Entry) (ls : Lsize) (frM : TermRun.Frame) : WeakMem.AllocLabel → Nat → Nat → FragS isa :=
  W1RUg (asm := asm) hpw i0 (Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)) E ls frM

/-- **The root's level-1 invariant**: a level-1 invariant `inv` with the child's stack unmapped. -/
abbrev inv1RU (inv : WeakMem.AllocLabel → Nat → Nat → FragS isa) :
    WeakMem.AllocLabel → Nat → Nat → FragS isa :=
  fun l b n s c fs => inv l b n s c fs ∧ U (R1) s

/-! ## `U r1Of` at level 1's entry -/

/-- **rodata's landing at the owned words `own` has `r1Of` unmapped** (level 1's entry, `h1`'s `Rd`): `RdLandHg`'s
`U` conjunct. -/
theorem rdLand_Ug {own : Spike.Lib.X64Consumer.Own} {E : Entry} {rd : TermRun.Word → Prop} {I : InvS} {ls : Lsize}
    {J1 : Spike.Lib.X64.AS → Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    {s : State} {c : Spike.Lib.Ctl} (h : RdLandHg (asm := asm) hpw i0 own E rd I ls J1 l b w s c) : U (R1) s := by
  obtain ⟨-, -, -, -, -, -, -, -, hu, -⟩ := h
  exact hu

/-- **rodata's landing has `r1Of` unmapped** (level 1's entry, `h1`'s `Rd`): `RdLandH`'s `U` conjunct, put there by
`LandRd.hlandRd_U` from `HLandRdU`'s `U` at `c2`, which `RootUL.ctrRow_ofFTU` keeps from level 0's context
(`rdLand_Ug` at `ownGH`). -/
theorem rdLand_U {E : Entry} {rd : TermRun.Word → Prop} {I : InvS} {ls : Lsize}
    {J1 : Spike.Lib.X64.AS → Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    {s : State} {c : Spike.Lib.Ctl} (h : RdLandH (asm := asm) hpw i0 E rd I ls J1 l b w s c) : U (R1) s :=
  rdLand_Ug hpw i0 h

/-! ## The level-1 statement with `U` -/

/-- **`LandR1U.segInv1_U` at publication rows, at the owned words `own`**: a level-1 segment invariant (`SegInvSP`)
at `W1Hg own … CtxR1H` carries `U r1Of` to one at `CtxU CtxR1H` (`segInvSP_keepUn` with `LandR1U.takeU_X` at
`W1Hg`'s `X0WH` states, the fragment weakened by `w0_mono`). -/
theorem segInv1_UPg {own : Spike.Lib.X64Consumer.Own} {E : Entry} {rd : TermRun.Word → Prop} {ls : Lsize}
    {l : WeakMem.AllocLabel} {b n : Nat} {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {lbl : Lbl} {ms : List TermRun.Frame → MemSide isa} {inv : FragS isa}
    (hK : ∀ fs, (ms fs).K = some abi)
    (h : SegInvSP (W1Hg own (Ly) ar p Dt Cl (CtxR1H (asm := asm) hpw i0 E rd ls) L0 ls0 frM (X0WH (Ly) (AX)) l b n)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) p lbl ms inv) :
    SegInvSP (W1Hg own (Ly) ar p Dt Cl (fun l b n => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E rd ls l b n)) L0
        ls0 frM (X0WH (Ly) (AX)) l b n)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) p lbl ms (fun s c fs => inv s c fs ∧ U (R1) s) :=
  (segInvSP_keepUn hK h fun s _ _ hW s' hk hu => takeU_X hpw i0 s s' hW.2.1 hk hu).weakW
    fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩

/-- **`LandR1U.segInv1_U` at publication rows**: a level-1 segment invariant (`SegInvSP`) at `CtxR1H` carries
`U r1Of` to one at `CtxU CtxR1H` (`segInv1_UPg` at `ownGH`). -/
theorem segInv1_UP {E : Entry} {rd : TermRun.Word → Prop} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {lbl : Lbl} {ms : List TermRun.Frame → MemSide isa} {inv : FragS isa}
    (hK : ∀ fs, (ms fs).K = some abi)
    (h : SegInvSP (W1H (Ly) a ar p Dt Cl (CtxR1H (asm := asm) hpw i0 E rd ls) L0 ls0 frM (X0WH (Ly) (AX)) l b n)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) p lbl ms inv) :
    SegInvSP (W1H (Ly) a ar p Dt Cl (fun l b n => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E rd ls l b n)) L0 ls0
        frM (X0WH (Ly) (AX)) l b n)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) p lbl ms (fun s c fs => inv s c fs ∧ U (R1) s) :=
  segInv1_UPg hpw i0 hK h

/-- **`H1StmtHF` at `W1Hg own … CtxR1H …` gives it at `CtxU CtxR1H`, `inv ∧ U r1Of`** (`segInv1_UPg` per label),
for an entry `Rd` with `r1Of` unmapped (`hRd`, as `rdLand_Ug`); the clone clause from `inv`'s. -/
theorem h1StmtHF_Ug {own : Spike.Lib.X64Consumer.Own} {E : Entry} {rd : TermRun.Word → Prop} {ls : Lsize}
    {ar ar' : Arena} {Dt Cl : State → Prop} {L0 L0' : Lbl} {ls0 : Lsize} {frM : TermRun.Frame}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {Rd : WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop}
    {inv : WeakMem.AllocLabel → Nat → Nat → FragS isa} {fr : List TermRun.Frame}
    (hK : ∀ l b n fs, (ms1 l b n fs).K = some abi) (hRd : ∀ l b n s c, Rd l b n s c → U (R1) s)
    (h : Spike.Lib.X64HelloPreA.H1StmtHF (W1Hg own (Ly) ar helloSrc Dt Cl (CtxR1H (asm := asm) hpw i0 E rd ls) L0
      ls0 frM (X0WH (Ly) (AX))) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) ar' L0' ms1 (Ly) Rd inv fr) :
    Spike.Lib.X64HelloPreA.H1StmtHF (W1Hg own (Ly) ar helloSrc Dt Cl
      (fun l b n => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E rd ls l b n)) L0 ls0 frM (X0WH (Ly) (AX)))
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) ar' L0' ms1 (Ly) Rd (inv1RU hpw i0 inv) fr := by
  intro l b n hl hb
  obtain ⟨hS, hR, hpc⟩ := h l b n hl hb
  exact ⟨segInv1_UPg hpw i0 (hK l b n) hS, fun s c hr => ⟨hR s c hr, hRd l b n s c hr⟩,
    fun s c fs hi => hpc s c fs hi.1⟩

/-- **`H1StmtHF` at `W1H … CtxR1H …` gives it at `CtxU CtxR1H`, `inv ∧ U r1Of`** (`h1StmtHF_Ug` at `ownGH`), for an
entry `Rd` with `r1Of` unmapped (`hRd`, as `rdLand_U`); the clone clause from `inv`'s. -/
theorem h1StmtHF_U {E : Entry} {rd : TermRun.Word → Prop} {ls : Lsize} {a : BitVec 64} {ar ar' : Arena}
    {Dt Cl : State → Prop} {L0 L0' : Lbl} {ls0 : Lsize} {frM : TermRun.Frame}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {Rd : WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop}
    {inv : WeakMem.AllocLabel → Nat → Nat → FragS isa} {fr : List TermRun.Frame}
    (hK : ∀ l b n fs, (ms1 l b n fs).K = some abi) (hRd : ∀ l b n s c, Rd l b n s c → U (R1) s)
    (h : Spike.Lib.X64HelloPreA.H1StmtHF (W1H (Ly) a ar helloSrc Dt Cl (CtxR1H (asm := asm) hpw i0 E rd ls) L0
      ls0 frM (X0WH (Ly) (AX))) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) ar' L0' ms1 (Ly) Rd inv fr) :
    Spike.Lib.X64HelloPreA.H1StmtHF (W1H (Ly) a ar helloSrc Dt Cl
      (fun l b n => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E rd ls l b n)) L0 ls0 frM (X0WH (Ly) (AX)))
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) ar' L0' ms1 (Ly) Rd (inv1RU hpw i0 inv) fr :=
  h1StmtHF_Ug hpw i0 hK hRd h

/-! ## `oPremH_R`'s level-1 premises -/

variable (E : Entry) (Ctx : FragS isa) (ls : Lsize) (frM : TermRun.Frame)
  (inv : WeakMem.AllocLabel → Nat → Nat → FragS isa)
  (W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa)

set_option hygiene false in
local notation "D" => helloDR (asm := asm) hpw TI E Ctx ls frM (W1RU (asm := asm) hpw i0 E ls frM)
    (inv1RU hpw i0 inv) W2 inv2

set_option hygiene false in
local notation "DG" => helloDRg (asm := asm) hpw TI own E Ctx ls frM (W1RUg (asm := asm) hpw i0 own E ls frM)
    (inv1RU hpw i0 inv) W2 inv2

set_option hygiene false in
local notation "μE" => (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ

/-- **`oPremH_Rg`'s `hW1` at `W1RUg own`** (`hW1_RUμg` at `J := IH DG`, the store's landings by `hland2_boxMRUg`
from the box clause `h2` of `H2StmtH` at the root's box `BoxMH … (GJ1RH …) … ∧ U r1`): the box counter add's
tails `hM` with `U r1Of` (`HLandM1U`), `wc_main`'s frame condition inside `F0` (`hF0`), `own` containing `ownGH`
(`hown`). `Ab`/`Ac` are `W1Hg`'s. -/
theorem hW1_rootUg {own : Spike.Lib.X64Consumer.Own} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hc : Spike.Lib.X64.Rt.CtrZ o)
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {L : RuntimeLayout} {endPc : Int64} {F0 : MachineData → Prop}
    (hown : ∀ s x, x ∈ Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s → x ∈ own s)
    (hM : ∀ l b n, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n →
      HLandM1U (asm := asm) hpw i0 E (fun _ => True) ls l b n
        (IH (DG) (Spike.Lib.X64ConsumerA.upd (DG).L0 l b) (Spike.Lib.X64ConsumerA.updN (DG).ls0 l n)))
    (h2 : Spike.Lib.X64HelloPreA.H2StmtH W2 K (AR) (LB) ms2 L endPc
      (fun l b n l' A n' s c => BoxMH (Ly) (ref1H (asm := asm) hpw i0 E (fun _ => True) ls l b n []) F0
        (GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l) l' A (slWsH l) n' s c ∧ U (R1) s) inv2)
    (hF0 : ∀ v m1 σ1 m, wcF (RS helloLsw v) helloD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) helloLsw 0#64 v) m1 σ1 m →
      F0 m) :
    ∀ l b n s c fs, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n → (DG).W1 l b n s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG))
        (Spike.Lib.X64ConsumerA.upd (DG).L0 l b) (Spike.Lib.X64ConsumerA.updN (DG).ls0 l n) s c fs (DG).Dt
        (Spike.Lib.X64.WriteAb.Ab (Ly).lab) (DG).Cl
        (Spike.Lib.X64.Hello.ThreadsAb.AcH (Ly).lab Spike.Lib.X64.HelloPh.StartWf.pfxM) := by
  intro l b n s c fs hl hb hW
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
  exact hW1_RUμg hpw i0 E (fun _ => True) ls l b n hpa hhp hc (P := fun _ _ _ => True) hown (hM l b n hl hb)
    (hland2_boxMRUg hpw i0 E (fun _ => True) ls h2 hl hb hF0) s c fs trivial
    ((Spike.Lib.X64.HelloWf.w1Hg_def l b n s c fs).1
      (show W1RUg (asm := asm) hpw i0 own E ls frM l b n s c fs from hW))

/-- **`oPremH_R`'s `hW1` at `W1RU`** (`hW1_rootUg` at `ownGH`: `hW1_RUμ` at `J := IH D`, the store's landings by
`hland2_boxMRUg` from the box clause `h2` of `H2StmtH` at the root's box `BoxMH … (GJ1RH …) … ∧ U r1`): the box
counter add's tails `hM` with `U r1Of` (`HLandM1U`), `wc_main`'s frame condition inside `F0` (`hF0`). `Ab`/`Ac`
are `W1H`'s. -/
theorem hW1_rootU (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hc : Spike.Lib.X64.Rt.CtrZ o)
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {L : RuntimeLayout} {endPc : Int64} {F0 : MachineData → Prop}
    (hM : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      HLandM1U (asm := asm) hpw i0 E (fun _ => True) ls l b n
        (IH (D) (Spike.Lib.X64ConsumerA.upd (D).L0 l b) (Spike.Lib.X64ConsumerA.updN (D).ls0 l n)))
    (h2 : Spike.Lib.X64HelloPreA.H2StmtH W2 K (AR) (LB) ms2 L endPc
      (fun l b n l' A n' s c => BoxMH (Ly) (ref1H (asm := asm) hpw i0 E (fun _ => True) ls l b n []) F0
        (GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l) l' A (slWsH l) n' s c ∧ U (R1) s) inv2)
    (hF0 : ∀ v m1 σ1 m, wcF (RS helloLsw v) helloD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) helloLsw 0#64 v) m1 σ1 m →
      F0 m) :
    ∀ l b n s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n → (D).W1 l b n s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (Spike.Lib.X64ConsumerA.upd (D).L0 l b) (Spike.Lib.X64ConsumerA.updN (D).ls0 l n) s c fs (D).Dt
        (Spike.Lib.X64.WriteAb.Ab (Ly).lab) (D).Cl
        (Spike.Lib.X64.Hello.ThreadsAb.AcH (Ly).lab Spike.Lib.X64.HelloPh.StartWf.pfxM) :=
  hW1_rootUg hpw i0 E Ctx ls frM inv W2 inv2 hpa hhp hc (fun _ _ h => h) hM h2 hF0

end Spike.Lib.X64.HelloPh.RootL1U

/-- info: 'Spike.Lib.X64.HelloPh.RootL1U.segInvSP_keepUn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1U.segInvSP_keepUn

/-- info: 'Spike.Lib.X64.HelloPh.RootL1U.rdLand_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1U.rdLand_U

/-- info: 'Spike.Lib.X64.HelloPh.RootL1U.segInv1_UP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1U.segInv1_UP

/-- info: 'Spike.Lib.X64.HelloPh.RootL1U.h1StmtHF_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1U.h1StmtHF_U

/-- info: 'Spike.Lib.X64.HelloPh.RootL1U.hW1_rootU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1U.hW1_rootU

/-- info: 'Spike.Lib.X64.HelloPh.RootL1U.rdLand_Ug' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1U.rdLand_Ug

/-- info: 'Spike.Lib.X64.HelloPh.RootL1U.segInv1_UPg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1U.segInv1_UPg

/-- info: 'Spike.Lib.X64.HelloPh.RootL1U.h1StmtHF_Ug' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1U.h1StmtHF_Ug

/-- info: 'Spike.Lib.X64.HelloPh.RootL1U.hW1_rootUg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1U.hW1_rootUg
