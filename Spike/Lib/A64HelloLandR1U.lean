/-
**hello.w's level 1 with the child's stack unmapped** (AArch64): the level-1
twin of `RootUL`/`LandRU`. The level's context carries `U r1Of` (`CtxU (CtxR1H l b n)`), so the box store's landing
state does too (`KeepUn.exec_un` from the store's pre-state, as wake's `RootUL.rootOpen_U`'s `hnew0`), and no
run-level premise `hUn1` (the child's stack unmapped at every pinned landing) is needed: the landings `HLand2U`
asks for are those with `U r1Of`.

- `HLand2U`, `HLandM1U`: the box store's landings and `LandR.HLandM1` at states with `U r1Of` (`hLandM1U_of`:
  `HLandM1` gives it).
- `hctr1_RU`, `hnew1_RU`: `WakeWf.hW0`'s `hctr`/`hnew` at `CtxU (CtxR1H l b n)` (`h2 : HLand2U`).
- `hW1_RU`, `hW1_RUμ`: `OPremH.hW1`'s `SFactsACH` at `CtxU (CtxR1H l b n)`, the second at `PhRec.μ`.
- `hland2_ofU`: `HLand2U` from `H2StmtH`'s box clause, for a `Box` holding at the landings with `U r1Of`.
- `takeU_X`: the outside move at an `X0WH` state keeps `r1Of` unmapped (`RootUL.takeU_H`'s core).
- `segInv1_U`: a level-1 segment invariant at `W1H … CtxR1H …` carries `U r1Of` into one at
  `W1H … (CtxU ∘ CtxR1H) …` (`SegInvS.keepUn`, `takeU_X`; the level-1 `inv0_upH`/`hst0_UH` core).
-/
import Spike.Lib.A64HelloBoxM
import Spike.Lib.A64HelloRootUL
import Spike.Lib.A64HelloW1H
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.LandR1U

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (CtrRow PendA WrAt ArenaW SFactsACH SegInvS TakeCKS)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib (FragS Frag MemSide FrameRun Arena NewStM)
open Spike.Lib.A64.Flow (At swR)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.KeepUn (U exec_un)
open Spike.Lib.A64.HelloPh.Land (ref1H GsH1 CtxR1H)
open Spike.Lib.A64.HelloPh.LandR (HLandM1)
open Spike.Lib.A64.HelloPh.RootUL (CtxU)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.HelloHMid (BoxMH slWsH)
open Spike.Lib.HelloH2G (GJ1H)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeH1Inv (segInvS_weakW)
open Spike.Lib.A64.WakePh.RootUL (w0_mono)
open Spike.Lib.HelloSrc (helloSrc)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize) (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
local notation "TI" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw TI

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The level's labels. -/
local notation "L1" => Spike.Lib.A64ConsumerA.upd (LB) l b

set_option hygiene false in
/-- The level's sizes. -/
local notation "S1" => Spike.Lib.A64ConsumerA.updN (ls0T ls) l n

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- The take site's label. -/
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "μE" => (Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
/-- The level's memory sides at a fragment `J`, the frames `fs`. -/
local notation "MS1" => fun (J : InvS) (fs : List TermRun.Frame) => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ (μE) rd
    (Spike.Lib.HelloGOf2H.gWH hpw TI (Spike.Lib.WakeHG.cTW hpw TI))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AR) J (L1) (S1) fs

set_option hygiene false in
/-- The level-1 context with the child's stack unmapped. -/
local notation "C1U" => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E rd ls l b n)

/-! ## The carried landings with `r1Of` unmapped -/

/-- **The box store's landings at level 1 with `r1Of` unmapped** (at landing states with `U r1Of`):
every landing `GsH1` admits, at a state with the child's stack unmapped, is in `X`, for labels fresh at the
level. -/
def HLand2U (X : WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2) : Prop :=
  ∀ Lnd, GsH1 (asm := asm) hpw i0 E rd ls l b n Lnd → ∀ l' A s' c', (L1) l' = none → Lnd l' A 1 s' c' → U (R1) s' →
    X l' A 1 s' c'

/-- **`wc_main`'s box counter add's tail at level 1 with `r1Of` unmapped** (`LandR.HLandM1` with `U r1Of` at `n4`,
at the pinned call `Land.GcM1H`, `RootUL.ctrRow_ofFTU`'s `hland`): the add keeps `U r1Of` from the context into the
allocator's next node. -/
def HLandM1U (Q : FragS isaLSE2) : Prop :=
  ∀ fs (ms0 : MemSide isaLSE2) R F q, ms0 = { ref1H (asm := asm) hpw i0 E rd ls l b n fs with xa := ms0.xa } →
    Spike.Lib.A64.HelloPh.Land.GcM1H hpw i0 l b fs ms0 R F q →
    Spike.Lib.A64.HelloPh.Land.CtrOkS ms0 (_root_.Executable.labels (Ly).exe).label R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (Spike.Lib.A64.Alloc.N (_root_.Executable.labels (Ly).exe).label ms0 q .n4) s c →
      TP (TV) s → U (R1) s → Q s c fs

/-- **`HLandM1` gives `HLandM1U`** (the `U` premise dropped, the call pinned: `Land.GcM1H.gcMH`). -/
theorem hLandM1U_of {Q : FragS isaLSE2} (h : HLandM1 (asm := asm) hpw i0 E rd ls l b n Q) : HLandM1U (asm :=
    asm) hpw i0 E rd ls l b n Q :=
  fun fs ms0 R F q hms hG hok s c hAt htp _ => h fs ms0 R F q hms (hG.gcMH hpw i0) hok s c hAt htp

/-! ## The counter row and the store's premises at `CtxU CtxR1H` -/

variable {J : InvS} {P : FragS isaLSE2}

/-- **`WakeWf.hW0`'s `hctr` at `CtxU (CtxR1H l b n)`** (at level 1): the box counter add by
`RootUL.ctrRow_ofFTU`, keeping `U r1Of` into the tail (`hM : HLandM1U`), the store writing no counter
(`stAt_noWr`). -/
theorem hctr1_RU (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hM : HLandM1U (asm := asm) hpw i0 E rd ls l b n (J (L1) (S1))) :
    ∀ s c fs, P s c fs → (C1U) s c fs → WrAt s (AR).ctrLoc → ∀ c' fs',
      FrameRun helloSrc (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow ((MS1) J fs') (fun s' c'' => PendA helloSrc J (L1) (S1) s' c'' fs') s c' :=
  by
  intro s c fs _ hC hW c' fs' hr _
  rcases hC with ⟨⟨h, htp⟩ | h, hu⟩
  · exact Spike.Lib.A64.HelloPh.RootUL.ctrRow_ofFTU (Spike.Lib.A64.HelloPh.LandR.hcode_H hpw i0 hpa hhp)
      (fun _ => rfl) hM h htp hu hr
  · exact (Spike.Lib.A64.WakeCtr.stAt_noWr (Spike.Lib.A64.HelloPh.HrdArena.hlt_U hpw i0 hc)
      (Spike.Lib.A64.HelloPh.HrdArena.h64_U hpw i0 hc) s c fs h hW).elim

/-- **`WakeWf.hW0`'s `hnew` at `CtxU (CtxR1H l b n)`** (with `HLand2U`): the counter add writes
the counter (`ctrAtF_wr`); at the box's store the frame run stays put (`eq_of_new`) and the landing state keeps
`U r1Of` from the store's pre-state (`exec_un`, as wake's `RootUL.rootOpen_U`'s `hnew0`), so `h2` applies. -/
theorem hnew1_RU (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (h2 : HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) J []).xa) :
    ∀ s c fs, P s c fs → (C1U) s c fs → ¬ WrAt s (AR).ctrLoc → ∀ c' fs',
      FrameRun helloSrc (c, fs) (c', fs') → abi.atSys s = false → ∀ L, WrAt s L → ¬ ArenaW (AR) (L1) (S1) c' L →
        NewStM helloSrc (L1) ((MS1) J fs') s c' := by
  intro s c fs _ hC hW c' fs' hr _ _ _ _
  rcases hC with ⟨⟨h, -⟩ | h, hu⟩
  · exact (hW (Spike.Lib.A64.HelloPh.CtrF.ctrAtF_wr (Spike.Lib.A64.HelloPh.LandR.hcode_H hpw i0 hpa hhp)
      (fun _ => rfl) s c fs h)).elim
  · obtain ⟨rfl, Lnd, hG, kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA,
      hcl, hX⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (let ⟨_, ht'⟩ := ht; Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht')
    have hU : U (R1) s' := exec_un hu hex true
    exact ⟨kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
      fun l' hl => h2 Lnd hG l' _ _ _ hl (hX l' hl) hU⟩

/-! ## The level's per-state facts -/

/-- **`HelloO.OPremH.hW1`'s `SFactsACH` at `Ctx1 := CtxU CtxR1H`** (`WakeWf.hW0` with
`hctr1_RU`/`hnew1_RU`): the store's landings only at states with `r1Of` unmapped (`h2 : HLand2U`). -/
theorem hW1_RU (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hc : Spike.Lib.A64.Rt.CtrZ o)
    {Dt Ab Cl Ac : State → Prop} {frM : TermRun.Frame} {X1 : State → Prop}
    (hM : HLandM1U (asm := asm) hpw i0 E rd ls l b n (J (L1) (S1))) (h2 : HLand2U (asm := asm) hpw i0 E rd ls l b n
        ((MS1) J []).xa) :
    ∀ s c fs, P s c fs →
      Spike.Lib.A64.WakeWf.W0 (Ly).Λ (μE) (Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab))
        (AR) helloSrc Dt Ab Cl Ac (C1U) (L1) (S1) frM X1 s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc rd (Spike.Lib.HelloGOf2H.gWH hpw TI (Spike.Lib.WakeHG.cTW hpw TI))
        (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AR) J (L1) (S1)
        s c fs Dt Ab Cl Ac :=
  Spike.Lib.A64.WakeWf.hW0 (hctr1_RU hpw i0 E rd ls l b n hpa hhp hc hM)
    (hnew1_RU hpw i0 E rd ls l b n hpa hhp h2)

/-- **`hW1_RU` at `PhRec.μ`** (`HelloWf.W1H`'s marks): the entry's marks are `PhRec.μ (Ly)` (`resolve_of_parsed`
from the loader's parse `hpa`). -/
theorem hW1_RUμ (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hc : Spike.Lib.A64.Rt.CtrZ o)
    {Dt Ab Cl Ac : State → Prop} {frM : TermRun.Frame} {X1 : State → Prop}
    (hM : HLandM1U (asm := asm) hpw i0 E rd ls l b n (J (L1) (S1))) (h2 : HLand2U (asm := asm) hpw i0 E rd ls l b n
        ((MS1) J []).xa) :
    ∀ s c fs, P s c fs →
      Spike.Lib.A64.WakeWf.W0 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly))
        (Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab))
        (AR) helloSrc Dt Ab Cl Ac (C1U) (L1) (S1) frM X1 s c fs →
      SFactsACH (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) helloSrc rd
        (Spike.Lib.HelloGOf2H.gWH hpw TI (Spike.Lib.WakeHG.cTW hpw TI))
        (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AR) J (L1) (S1)
        s c fs Dt Ab Cl Ac := by
  have hμ : (μE) = Spike.Lib.A64.PhRec.μ (Ly) := by
    have hr := Scc.Sem.A64.resolve_of_parsed (Scc.Sem.A64.kernel 2) E (Ly).Λ (prog := (Ly).prog) hpa
    unfold Scc.Sem.Target.marks Spike.Lib.A64.PhRec.μ
    congr 1
    · funext k; exact hr _
    · funext k; exact hr _
  rw [← hμ]
  exact hW1_RU hpw i0 E rd ls l b n hpa hhp hc hM h2

/-! ## The box store's landings from `h2`'s statement -/

/-- **`HLand2U` from `H2StmtH`'s box clause** at the root's `I3` (`land_I3b`): `hB` need only give
the `Box` at landings with `r1Of` unmapped. -/
theorem hland2_ofU {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    {L : RuntimeLayout} {endPc : Int64}
    {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop}
    {inv0 : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h2 : Spike.Lib.HelloPreA.H2StmtH W2 K (AR) (LB) ms2 L endPc Box inv2) (hl : (LB) l = none)
    (hb : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n)
    (hB : ∀ Lnd, GsH1 (asm := asm) hpw i0 E rd ls l b n Lnd → ∀ l' A s c, (L1) l' = none → Lnd l' A 1 s c → U (R1) s →
      Box l b n l' A 1 s c) :
    HLand2U (asm := asm) hpw i0 E rd ls l b n
      ((MS1) (Spike.Lib.A64ConsumerA.I3 (AR) (LB) (ls0T ls) inv0 inv1 inv2) []).xa := by
  intro Lnd hG l' A s c hl' hL hu
  have hBx := hB Lnd hG l' A s c hl' hL hu
  obtain ⟨v, σC, m1, σ1, -, rfl⟩ := hG
  obtain ⟨-, ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩, -⟩ := hL
  have hf : (ref1H (asm := asm) hpw i0 E rd ls l b n []).off 1 q.1.τ = 8 :=
    Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) q.2.toS.accs
  have hu : 1 ≤ (ref1H (asm := asm) hpw i0 E rd ls l b n []).units 1 q.1.τ :=
    Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) q.2.toS.accs
  have hcl : 2 ≤ (ref1H (asm := asm) hpw i0 E rd ls l b n []).cells := show 2 ≤ Scc.Cert.PlaceOK.allocCells by decide
  have hAL : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells A 1 := by
    show (ref1H (asm := asm) hpw i0 E rd ls l b n []).heap + 8 ≤ A ∧
      A + 8 * 1 ≤ (ref1H (asm := asm) hpw i0 E rd ls l b n []).heap + 16 * (ref1H (asm := asm) hpw i0 E rd ls l b n
          []).cells ∧
      1 + 1 ≤ (ref1H (asm := asm) hpw i0 E rd ls l b n []).cells
    rw [hf] at hAo; omega
  exact ⟨hAL, Spike.Lib.A64ConsumerA.land_I3b hl hb hl' hAL ((h2 l b n l' A 1 hl hb hl' hAL).2.1 s c hBx)⟩

/-! ## The level's segment invariant with `r1Of` unmapped -/

/-- **The outside move at an `X0WH` state keeps `r1Of` unmapped** (`RootUL.takeU_H`'s core, at any fragment whose
states are `X0WH`'s): the take at the site label is `PhRec.K`, the take of `rS0` (`StartH0B.takeCKS_iffH`),
disjoint from `r1Of` (`KeepUn.take_un`). -/
theorem takeU_X (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ s s', X0WH (Ly) (AX) s → TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly)) s s' → U (R1) s → U (R1) s' := by
  have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hpw TI hA13
  have hbd' : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by
    rw [(Ly).lab_stacks]; exact Spike.Lib.WakeHClW.hbd_W hpw TI hsub1
  obtain ⟨h1l, h1s⟩ := Spike.Lib.A64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS).size = 16384 := rfl
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS).lo + (RS).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS) := by unfold Scc.Sem.Range.Disjoint; omega
  intro s s' hx hk hu
  obtain ⟨-, pm, rfl⟩ := (Spike.Lib.A64.HelloPh.StartH0B.takeCKS_iffH hpw TI hx).1 hk
  exact Spike.Lib.A64.KeepUn.take_un pm hd hw1 hwS hu

/-- **A level-1 segment invariant at `CtxR1H` carries `U r1Of` to one at `CtxU CtxR1H`** (the level-1 core of
`RootUL.inv0_upH`/`hst0_UH`): `SegInvS.keepUn` with `takeU_X` at `W1H`'s `X0WH` states, the fragment weakened by
`w0_mono` (`W1H` is `W0`, `w1H_def`). -/
theorem segInv1_U (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64} {ar : Arena}
    {p : Prog} {Dt Cl : State → Prop} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isaLSE2} {inv : FragS isaLSE2} (hK : ∀ fs, (ms fs).K = some abi)
    (h : SegInvS (Spike.Lib.A64.HelloWf.W1H (Ly) a ar p Dt Cl (CtxR1H (asm := asm) hpw i0 E rd ls) L0 ls0 frM (X0WH
        (Ly) (AX))
      l b n) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) p lbl ms inv) :
    SegInvS (Spike.Lib.A64.HelloWf.W1H (Ly) a ar p Dt Cl (fun l b n => CtxU hpw i0 (CtxR1H (asm := asm) hpw i0 E rd ls
        l b n)) L0
      ls0 frM (X0WH (Ly) (AX)) l b n) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) p lbl ms
      (fun s c fs => inv s c fs ∧ U (R1) s) :=
  segInvS_weakW (Spike.Lib.A64.WakePh.RootUL.SegInvS.keepUn hK h
      fun s _ _ hW s' hk hu => takeU_X hpw i0 hA13 s s' hW.2.1 hk hu)
    fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩

end Spike.Lib.A64.HelloPh.LandR1U

/-- info: 'Spike.Lib.A64.HelloPh.LandR1U.hctr1_RU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR1U.hctr1_RU

/-- info: 'Spike.Lib.A64.HelloPh.LandR1U.hLandM1U_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR1U.hLandM1U_of

/-- info: 'Spike.Lib.A64.HelloPh.LandR1U.hnew1_RU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR1U.hnew1_RU

/-- info: 'Spike.Lib.A64.HelloPh.LandR1U.hW1_RU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR1U.hW1_RU

/-- info: 'Spike.Lib.A64.HelloPh.LandR1U.hW1_RUμ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR1U.hW1_RUμ

/-- info: 'Spike.Lib.A64.HelloPh.LandR1U.hland2_ofU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR1U.hland2_ofU

/-- info: 'Spike.Lib.A64.HelloPh.LandR1U.takeU_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR1U.takeU_X

/-- info: 'Spike.Lib.A64.HelloPh.LandR1U.segInv1_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR1U.segInv1_U
