/-
**hello.w's level 1 with the child's stack unmapped** (x86-64; the twin of `Spike/Lib/A64HelloLandR1U.lean`'s live
part): the level-1 twin of `RootUL`/`LandRU`. The level's context carries `U r1Of` (`CtxU (CtxR1H l b n)`), so the
box store's landing state does too (`KeepUn.exec_un` from the store's pre-state, as wake's `RootUL.hnew0_U`), and
no run-level premise (the child's stack unmapped at every pinned landing) is needed: the landings `HLand2U` asks for
are those with `U r1Of`.

- `HLand2U`, `HLandM1U`: the box store's landings and `wc_main`'s box counter add's tail at states with `U r1Of`.
- `ctrRow_own_mono`: `CtrRow` at `msOfA` keeps under a larger own map.
- `hctr1_RUg`, `hnew1_RUg`: `WakeWf.hW0`'s `hctr`/`hnew` at `CtxU (CtxR1H l b n)` (`h2 : HLand2U`) at an own map
  `own` (`hctr1_RUg`: one containing `ownGH`'s); `hctr1_RU`, `hnew1_RU`: them at `ownGH`.
- `hW1_RUg`, `hW1_RUμg`: `OPremH.hW1`'s `SFactsACH` at `CtxU (CtxR1H l b n)` at an own map containing `ownGH`'s,
  the second at `PhRec.μ`; `hW1_RU`, `hW1_RUμ`: them at `ownGH`.
- `hland2_ofUg`: `HLand2U` from `H2StmtH`'s box clause, for a `Box` holding at the landings with `U r1Of`, at the
  level's memory sides at any own map; `hland2_ofU`: it at `ownGH`.
- `takeU_X`: the outside move at an `X0WH` state keeps `r1Of` unmapped (`RootUL.takeU_H`'s core).
- `segInv1_U`: a level-1 segment invariant at `W1H … CtxR1H …` carries `U r1Of` into one at
  `W1H … (CtxU ∘ CtxR1H) …` (`SegInvS.keepUn`, `takeU_X`; the level-1 `inv0_upH`/`hst0_UH` core).

## Differences from the AArch64 version

- `HLandM1U`'s tail starts at the allocator's `c2` (AArch64 `n4`), as `RootUL.ctrRow_ofFTU`'s `hland`; the thread
  pointer is `tpOf (tcbS Ly)` (AArch64 `pinA + 8`).
- The allocator's code comes from `LandR.hcode_H`'s three facts (`Lays`, `endOf`, `allocIn`; AArch64's
  `Alloc.Code`), under `(Ly).valid`; the loader's facts are the two parses `cellsOf asm` (AArch64 `textProgram`).
- `hW1_RUμ`'s marks are `Worker.Wake.AbOffW.marks_target`'s (AArch64 `resolve_of_parsed` inline).
- `takeU_X` and `segInv1_U` take no `a13data` premise: the stacks' bound is `X64WakeHClC.hbd_W` (AArch64 through
  `StartPlaceLy.hsub1_W`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hLandM1U_of` (and so
  `LandR.HLandM1`, which only it reads).
-/
import Spike.Lib.X64HelloRootUL
import Spike.Lib.X64HelloLand1
import Spike.Lib.X64HelloW1H
import Spike.Lib.X64HelloWcInv3
import Spike.Lib.X64SegInstA3
import Spike.Lib.X64WakeWf
import Spike.Lib.X64SFactsACH
import Spike.Lib.X64HelloHrdArena

namespace Spike.Lib.X64.HelloPh.LandR1U

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Scc.Sem.X64 (abi)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (CtrRow PendA WrAt ArenaW SFactsACH SegInvS TakeCKS)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib (FragS Frag MemSide FrameRun Arena NewStM PlaceWX)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.WakePh.MainGlue (tcbS)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.KeepUn (U exec_un)
open Spike.Lib.X64.HelloPh.Land (ref1H GsH1 CtxR1H)
open Spike.Lib.X64.HelloPh.RootUL (CtxU)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.WakeH1Inv (segInvS_weakW)
open Spike.Lib.X64.WakePh.RootUL (w0_mono)
open Spike.Lib.X64HelloSrc (helloSrc)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize) (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
local notation "TI" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw TI

set_option hygiene false in
local notation "RS" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The level's labels. -/
local notation "L1" => Spike.Lib.X64ConsumerA.upd (LB) l b

set_option hygiene false in
/-- The level's sizes. -/
local notation "S1" => Spike.Lib.X64ConsumerA.updN (ls0T ls) l n

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- The take site's label. -/
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "μE" => (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
/-- The level's memory sides at a fragment `J`, the frames `fs`. -/
local notation "MS1" => fun (J : InvS) (fs : List TermRun.Frame) => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ (μE) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw TI (Spike.Lib.X64WakeHG.cTW hpw TI))
    (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (AR) J (L1) (S1) fs

set_option hygiene false in
/-- The level's memory sides at an own map `own`, a fragment `J`, the frames `fs`. -/
local notation "MS1g" => fun (own : Spike.Lib.X64Consumer.Own) (J : InvS) (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ (μE) rd (Spike.Lib.X64HelloGOf2H.gWH hpw TI (Spike.Lib.X64WakeHG.cTW hpw TI))
    (fun s _ => own s) (AR) J (L1) (S1) fs

set_option hygiene false in
/-- The start's own map. -/
local notation "OG" => Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)

set_option hygiene false in
/-- The level-1 context with the child's stack unmapped. -/
local notation "C1U" => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E rd ls l b n)

/-! ## The carried landings with `r1Of` unmapped -/

/-- **The box store's landings at level 1 with `r1Of` unmapped** (at landing states with `U r1Of`):
every landing `GsH1` admits, at a state with the child's stack unmapped, is in `X`, for labels fresh at the
level. -/
def HLand2U (X : WeakMem.AllocLabel → Nat → Nat → Frag isa) : Prop :=
  ∀ Lnd, GsH1 (asm := asm) hpw i0 E rd ls l b n Lnd → ∀ l' A s' c', (L1) l' = none → Lnd l' A 1 s' c' → U (R1) s' →
    X l' A 1 s' c'

/-- **`wc_main`'s box counter add's tail at level 1 with `r1Of` unmapped** (at `c2`, at the pinned call
`Land.GcM1H`, `RootUL.ctrRow_ofFTU`'s `hland`): the add keeps `U r1Of` from the context into the allocator's next
node. -/
def HLandM1U (Q : FragS isa) : Prop :=
  ∀ fs (ms0 : MemSide isa) R F q, ms0 = { ref1H (asm := asm) hpw i0 E rd ls l b n fs with xa := ms0.xa } →
    Spike.Lib.X64.HelloPh.Land.GcM1H hpw i0 l b fs ms0 R F q →
    Spike.Lib.X64.HelloPh.Land.CtrOkS ms0 (_root_.Executable.labels (Ly).exe).label R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (Spike.Lib.X64.Alloc.N (_root_.Executable.labels (Ly).exe).label ms0 q .c2) s c →
      TP (TV) s → U (R1) s → Q s c fs

/-! ## The counter row and the store's premises at `CtxU CtxR1H` -/

/-- **`CtrRow` at an own map containing another's**: the row reads the own map only in an antecedent (the counter's
old value at every owned copy), so a larger own map keeps it. -/
theorem ctrRow_own_mono {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
    {L0 : Lbl} {ls0 : Lsize} {fs : List TermRun.Frame} {own own' : Spike.Lib.X64Consumer.Own}
    (hown : ∀ s x, x ∈ own s → x ∈ own' s) {X : Frag isa} {s : State} {c : Spike.Lib.Ctl}
    (h : CtrRow (Spike.Lib.X64ConsumerA.msOfA Λ μ rd G (fun s _ => own s) ar J L0 ls0 fs) X s c) :
    CtrRow (Spike.Lib.X64ConsumerA.msOfA Λ μ rd G (fun s _ => own' s) ar J L0 ls0 fs) X s c := by
  obtain ⟨k, op, g, x, τ, e, n', h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨k, op, g, x, τ, e, n', h1, h2, h3, h4, h5, h6, fun old hG hw => h7 old hG fun w hm => hw w (hown s _ hm)⟩

variable {J : InvS} {P : FragS isa}

/-- **`WakeWf.hW0`'s `hctr` at `CtxU (CtxR1H l b n)` at an own map `own` containing `ownGH`'s** (at level 1): the
box counter add by `RootUL.ctrRow_ofFTU`, keeping `U r1Of` into the tail (`hM : HLandM1U`), at `ownGH`, then
`ctrRow_own_mono`; the store writing no counter (`stAt_noWr`). -/
theorem hctr1_RUg {own : Spike.Lib.X64Consumer.Own} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hown : ∀ s x, x ∈ (OG) s → x ∈ own s)
    (hM : HLandM1U (asm := asm) hpw i0 E rd ls l b n (J (L1) (S1))) :
    ∀ s c fs, P s c fs → (C1U) s c fs → WrAt s (AR).ctrLoc → ∀ c' fs',
      FrameRun helloSrc (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow ((MS1g) own J fs') (fun s' c'' => PendA helloSrc J (L1) (S1) s' c'' fs') s c' := by
  haveI := (Ly).valid
  obtain ⟨hp, hend, hin⟩ := Spike.Lib.X64.HelloPh.LandR.hcode_H hpw i0 hpa hhp
  intro s c fs _ hC hW c' fs' hr _
  rcases hC with ⟨⟨h, htp⟩ | h, hu⟩
  · exact ctrRow_own_mono rd hown
      (Spike.Lib.X64.HelloPh.RootUL.ctrRow_ofFTU (M := (MS1) J) hp hend hin (fun _ => rfl) hM h htp hu hr)
  · exact (Spike.Lib.X64.WakeCtr.stAt_noWr (Spike.Lib.X64.HelloPh.HrdArena.hlt_U hpw i0 hc)
      (Spike.Lib.X64.HelloPh.HrdArena.h64_U hpw i0 hc) s c fs h hW).elim

/-- **`WakeWf.hW0`'s `hctr` at `CtxU (CtxR1H l b n)`** (at level 1): `hctr1_RUg` at `ownGH`. -/
theorem hctr1_RU (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hM : HLandM1U (asm := asm) hpw i0 E rd ls l b n (J (L1) (S1))) :
    ∀ s c fs, P s c fs → (C1U) s c fs → WrAt s (AR).ctrLoc → ∀ c' fs',
      FrameRun helloSrc (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow ((MS1) J fs') (fun s' c'' => PendA helloSrc J (L1) (S1) s' c'' fs') s c' :=
  hctr1_RUg hpw i0 E rd ls l b n hpa hhp hc (fun _ _ h => h) hM

/-- **`WakeWf.hW0`'s `hnew` at `CtxU (CtxR1H l b n)` at any own map `own`** (with `HLand2U`): the counter add
writes the counter (`ctrAtF_wr`); at the box's store the frame run stays put (`eq_of_new`) and the landing state
keeps `U r1Of` from the store's pre-state (`exec_un`, as wake's `RootUL.hnew0_U`), so `h2` applies (`NewStM` reads
no own map). -/
theorem hnew1_RUg {own : Spike.Lib.X64Consumer.Own} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (h2 : HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1g) own J []).xa) :
    ∀ s c fs, P s c fs → (C1U) s c fs → ¬ WrAt s (AR).ctrLoc → ∀ c' fs',
      FrameRun helloSrc (c, fs) (c', fs') → abi.atSys s = false → ∀ L, WrAt s L → ¬ ArenaW (AR) (L1) (S1) c' L →
        NewStM helloSrc (L1) ((MS1g) own J fs') s c' := by
  haveI := (Ly).valid
  obtain ⟨hp, hend, hin⟩ := Spike.Lib.X64.HelloPh.LandR.hcode_H hpw i0 hpa hhp
  intro s c fs _ hC hW c' fs' hr _ _ _ _
  rcases hC with ⟨⟨h, -⟩ | h, hu⟩
  · exact (hW (Spike.Lib.X64.HelloPh.CtrF.ctrAtF_wr hp hend hin (fun _ => rfl) s c fs h)).elim
  · obtain ⟨rfl, Lnd, hG, kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA,
      hcl, hX⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht.choose_spec)
    have hU : U (R1) s' := exec_un hu hex true
    exact ⟨kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
      fun l' hl => h2 Lnd hG l' _ _ _ hl (hX l' hl) hU⟩

/-- **`WakeWf.hW0`'s `hnew` at `CtxU (CtxR1H l b n)`** (with `HLand2U`): `hnew1_RUg` at `ownGH`. -/
theorem hnew1_RU (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (h2 : HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) J []).xa) :
    ∀ s c fs, P s c fs → (C1U) s c fs → ¬ WrAt s (AR).ctrLoc → ∀ c' fs',
      FrameRun helloSrc (c, fs) (c', fs') → abi.atSys s = false → ∀ L, WrAt s L → ¬ ArenaW (AR) (L1) (S1) c' L →
        NewStM helloSrc (L1) ((MS1) J fs') s c' :=
  hnew1_RUg hpw i0 E rd ls l b n hpa hhp h2

/-! ## The level's per-state facts -/

/-- **`HelloO.OPremH.hW1`'s `SFactsACH` at `Ctx1 := CtxU CtxR1H` at an own map `own` containing `ownGH`'s**
(`WakeWf.hW0` with `hctr1_RUg`/`hnew1_RUg`): the store's landings only at states with `r1Of` unmapped
(`h2 : HLand2U`). -/
theorem hW1_RUg {own : Spike.Lib.X64Consumer.Own} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hc : Spike.Lib.X64.Rt.CtrZ o)
    {Dt Ab Cl Ac : State → Prop} {frM : TermRun.Frame} {X1 : State → Prop}
    (hown : ∀ s x, x ∈ (OG) s → x ∈ own s)
    (hM : HLandM1U (asm := asm) hpw i0 E rd ls l b n (J (L1) (S1)))
    (h2 : HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1g) own J []).xa) :
    ∀ s c fs, P s c fs →
      Spike.Lib.X64.WakeWf.W0 (Ly).Λ (μE) own (AR) helloSrc Dt Ab Cl Ac (C1U) (L1) (S1) frM X1 s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc rd (Spike.Lib.X64HelloGOf2H.gWH hpw TI (Spike.Lib.X64WakeHG.cTW hpw TI))
        (fun s _ => own s) (AR) J (L1) (S1) s c fs Dt Ab Cl Ac :=
  Spike.Lib.X64.WakeWf.hW0 (hctr1_RUg hpw i0 E rd ls l b n hpa hhp hc hown hM)
    (hnew1_RUg hpw i0 E rd ls l b n hpa hhp h2)

/-- **`HelloO.OPremH.hW1`'s `SFactsACH` at `Ctx1 := CtxU CtxR1H`** (`WakeWf.hW0` with
`hctr1_RU`/`hnew1_RU`): `hW1_RUg` at `ownGH`. -/
theorem hW1_RU (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hc : Spike.Lib.X64.Rt.CtrZ o)
    {Dt Ab Cl Ac : State → Prop} {frM : TermRun.Frame} {X1 : State → Prop}
    (hM : HLandM1U (asm := asm) hpw i0 E rd ls l b n (J (L1) (S1)))
    (h2 : HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) J []).xa) :
    ∀ s c fs, P s c fs →
      Spike.Lib.X64.WakeWf.W0 (Ly).Λ (μE) (Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab))
        (AR) helloSrc Dt Ab Cl Ac (C1U) (L1) (S1) frM X1 s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc rd (Spike.Lib.X64HelloGOf2H.gWH hpw TI (Spike.Lib.X64WakeHG.cTW hpw TI))
        (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (AR) J (L1) (S1)
        s c fs Dt Ab Cl Ac :=
  hW1_RUg hpw i0 E rd ls l b n hpa hhp hc (fun _ _ h => h) hM h2

/-- **`hW1_RUg` at `PhRec.μ`** (`HelloWf.W1H`'s marks): the entry's marks are `PhRec.μ (Ly)`
(`Worker.Wake.AbOffW.marks_target`, from the loader's parse `hpa`). -/
theorem hW1_RUμg {own : Spike.Lib.X64Consumer.Own} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hc : Spike.Lib.X64.Rt.CtrZ o)
    {Dt Ab Cl Ac : State → Prop} {frM : TermRun.Frame} {X1 : State → Prop}
    (hown : ∀ s x, x ∈ (OG) s → x ∈ own s)
    (hM : HLandM1U (asm := asm) hpw i0 E rd ls l b n (J (L1) (S1)))
    (h2 : HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1g) own J []).xa) :
    ∀ s c fs, P s c fs →
      Spike.Lib.X64.WakeWf.W0 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) own (AR) helloSrc Dt Ab Cl Ac (C1U) (L1) (S1) frM
        X1 s c fs →
      SFactsACH (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) helloSrc rd
        (Spike.Lib.X64HelloGOf2H.gWH hpw TI (Spike.Lib.X64WakeHG.cTW hpw TI)) (fun s _ => own s) (AR) J (L1) (S1)
        s c fs Dt Ab Cl Ac := by
  have hμ : (μE) = Spike.Lib.X64.PhRec.μ (Ly) := Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa
  rw [← hμ]
  exact hW1_RUg hpw i0 E rd ls l b n hpa hhp hc hown hM h2

/-- **`hW1_RU` at `PhRec.μ`** (`HelloWf.W1H`'s marks): `hW1_RUμg` at `ownGH`. -/
theorem hW1_RUμ (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hc : Spike.Lib.X64.Rt.CtrZ o)
    {Dt Ab Cl Ac : State → Prop} {frM : TermRun.Frame} {X1 : State → Prop}
    (hM : HLandM1U (asm := asm) hpw i0 E rd ls l b n (J (L1) (S1)))
    (h2 : HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) J []).xa) :
    ∀ s c fs, P s c fs →
      Spike.Lib.X64.WakeWf.W0 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly))
        (Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab))
        (AR) helloSrc Dt Ab Cl Ac (C1U) (L1) (S1) frM X1 s c fs →
      SFactsACH (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) helloSrc rd
        (Spike.Lib.X64HelloGOf2H.gWH hpw TI (Spike.Lib.X64WakeHG.cTW hpw TI))
        (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (AR) J (L1) (S1)
        s c fs Dt Ab Cl Ac :=
  hW1_RUμg hpw i0 E rd ls l b n hpa hhp hc (fun _ _ h => h) hM h2

/-! ## The box store's landings from `h2`'s statement -/

/-- **`HLand2U` from `H2StmtH`'s box clause at any own map `own`** at the root's `I3` (`land_I3b`): `hB` need
only give the `Box` at landings with `r1Of` unmapped (the allocation fragment `xa` reads no own map). -/
theorem hland2_ofUg {own : Spike.Lib.X64Consumer.Own}
    {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {L : RuntimeLayout} {endPc : Int64}
    {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop}
    {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    (h2 : Spike.Lib.X64HelloPreA.H2StmtH W2 K (AR) (LB) ms2 L endPc Box inv2) (hl : (LB) l = none)
    (hb : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n)
    (hB : ∀ Lnd, GsH1 (asm := asm) hpw i0 E rd ls l b n Lnd → ∀ l' A s c, (L1) l' = none → Lnd l' A 1 s c → U (R1) s →
      Box l b n l' A 1 s c) :
    HLand2U (asm := asm) hpw i0 E rd ls l b n
      ((MS1g) own (Spike.Lib.X64ConsumerA.I3 (AR) (LB) (ls0T ls) inv0 inv1 inv2) []).xa := by
  intro Lnd hG l' A s c hl' hL hu
  have hBx := hB Lnd hG l' A s c hl' hL hu
  obtain ⟨v, σC, m1, σ1, -, rfl⟩ := hG
  obtain ⟨-, ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩, -⟩ := hL
  have hf : (ref1H (asm := asm) hpw i0 E rd ls l b n []).off 1 q.1.τ = 8 :=
    Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) q.2.toS.accs
  have hu : 1 ≤ (ref1H (asm := asm) hpw i0 E rd ls l b n []).units 1 q.1.τ :=
    Spike.Lib.LowerX64.arOf_units_pos (Λ := (Ly).Λ) q.2.toS.accs
  have hcl : 2 ≤ (ref1H (asm := asm) hpw i0 E rd ls l b n []).cells :=
    show 2 ≤ Scc.Cert.PlaceOK.allocCells by decide
  have hAL : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells A 1 := by
    show (ref1H (asm := asm) hpw i0 E rd ls l b n []).heap + 8 ≤ A ∧
      A + 8 * 1 ≤ (ref1H (asm := asm) hpw i0 E rd ls l b n []).heap +
        16 * (ref1H (asm := asm) hpw i0 E rd ls l b n []).cells ∧
      1 + 1 ≤ (ref1H (asm := asm) hpw i0 E rd ls l b n []).cells
    rw [hf] at hAo; omega
  exact ⟨hAL, Spike.Lib.X64ConsumerA.land_I3b hl hb hl' hAL ((h2 l b n l' A 1 hl hb hl' hAL).2.1 s c hBx)⟩

/-- **`HLand2U` from `H2StmtH`'s box clause** at the root's `I3` (`land_I3b`): `hland2_ofUg` at `ownGH`. -/
theorem hland2_ofU {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {L : RuntimeLayout} {endPc : Int64}
    {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop}
    {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    (h2 : Spike.Lib.X64HelloPreA.H2StmtH W2 K (AR) (LB) ms2 L endPc Box inv2) (hl : (LB) l = none)
    (hb : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n)
    (hB : ∀ Lnd, GsH1 (asm := asm) hpw i0 E rd ls l b n Lnd → ∀ l' A s c, (L1) l' = none → Lnd l' A 1 s c → U (R1) s →
      Box l b n l' A 1 s c) :
    HLand2U (asm := asm) hpw i0 E rd ls l b n
      ((MS1) (Spike.Lib.X64ConsumerA.I3 (AR) (LB) (ls0T ls) inv0 inv1 inv2) []).xa :=
  hland2_ofUg hpw i0 E rd ls l b n h2 hl hb hB

/-! ## The level's segment invariant with `r1Of` unmapped -/

/-- **The outside move at an `X0WH` state keeps `r1Of` unmapped** (`RootUL.takeU_H`'s core, at any fragment whose
states are `X0WH`'s): the take at the site label is `PhRec.K`, the take of `rS0` (`StartH0B.takeCKS_iffH`),
disjoint from `r1Of` (`KeepUn.take_un`). -/
theorem takeU_X :
    ∀ s s', X0WH (Ly) (AX) s → TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly)) s s' → U (R1) s → U (R1) s' := by
  have hbd' : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 :=
    Spike.Lib.X64WakeHClC.hbd_W hpw TI
  obtain ⟨h1l, h1s⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS).size = 16384 := rfl
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS).lo + (RS).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS) := by unfold Scc.Sem.Range.Disjoint; omega
  intro s s' hx hk hu
  obtain ⟨-, pm, rfl⟩ := (Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH hpw TI hx).1 hk
  exact Spike.Lib.X64.KeepUn.take_un pm hd hw1 hwS hu

/-- **A level-1 segment invariant at `CtxR1H` carries `U r1Of` to one at `CtxU CtxR1H`** (the level-1 core of
`RootUL.inv0_upH`/`hst0_UH`): `SegInvS.keepUn` with `takeU_X` at `W1H`'s `X0WH` states, the fragment weakened by
`w0_mono` (`W1H` is `W0`, `w1H_def`). -/
theorem segInv1_U {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {lbl : Lbl} {ms : List TermRun.Frame → MemSide isa} {inv : FragS isa}
    (hK : ∀ fs, (ms fs).K = some abi)
    (h : SegInvS (Spike.Lib.X64.HelloWf.W1H (Ly) a ar p Dt Cl (CtxR1H (asm := asm) hpw i0 E rd ls) L0 ls0 frM
      (X0WH (Ly) (AX)) l b n) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) p lbl ms inv) :
    SegInvS (Spike.Lib.X64.HelloWf.W1H (Ly) a ar p Dt Cl
        (fun l b n => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E rd ls l b n)) L0 ls0 frM (X0WH (Ly) (AX)) l b n)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) p lbl ms (fun s c fs => inv s c fs ∧ U (R1) s) :=
  segInvS_weakW (Spike.Lib.X64.WakePh.RootUL.SegInvS.keepUn hK h
      fun s _ _ hW s' hk hu => takeU_X hpw i0 s s' hW.2.1 hk hu)
    fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩

end Spike.Lib.X64.HelloPh.LandR1U

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.ctrRow_own_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.ctrRow_own_mono

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hctr1_RUg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hctr1_RUg

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hnew1_RUg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hnew1_RUg

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hW1_RUg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hW1_RUg

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hW1_RUμg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hW1_RUμg

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hctr1_RU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hctr1_RU

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hnew1_RU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hnew1_RU

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hW1_RU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hW1_RU

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hW1_RUμ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hW1_RUμ

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hland2_ofUg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hland2_ofUg

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.hland2_ofU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.hland2_ofU

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.takeU_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.takeU_X

/-- info: 'Spike.Lib.X64.HelloPh.LandR1U.segInv1_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR1U.segInv1_U
