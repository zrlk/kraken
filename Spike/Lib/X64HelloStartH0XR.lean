/-
**`RootH0.hstHg`'s `hst0` at `ownGHXW` with `wc_rodata`'s level obligations discharged** (x86-64 only):
`StartH0X.hst0_X` at the allocator's caller's invariant at the first stack's top (`J1 := mRdJ0 (J' TOP)`), its
`hrd` by `HrdRootX.hrd_RXT` and `hloc` by the empty local run.

Left as premises: `hst0_X`'s minus `hrd` and `hloc`, plus `hrd_RXT`'s `hm` (rodata's immediate) and `hctx` (the
context at the counter add, under main's thread pointer, at `msUHg (ownGHXW Ly ntA)`).

- `hst0_XR`: the `hst0` premise of `RootH0.hstHg` at `ownGHXW`, any context `Ctx` (given `hctx`).
- `hst0_XRc`: the same at the root's context `LandRU.CtxRdHg … (ownGHXW Ly ntA)`, `hrd` by `HrdRootX.hrd_RdHX`
  (no `hctx`).

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there (`A64HelloStartH0U1` discharges `hrd` at `ownGH`). Against
x86-64 at `ownGH`: `hctx` stays a premise, `LandRU.CtxRdH`'s reference side being `msUH` (at `ownGH`).
-/
import Spike.Lib.X64HelloStartH0X
import Spike.Lib.X64HelloHrdRootX

namespace Spike.Lib.X64.HelloPh.StartH0XR

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS I3)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (WSg rdJH)
open Spike.Lib.X64 (At enter CKept Abs)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mRdJ0 mNC aR)
open Spike.Lib.X64.Flow.HelloRd (rN rX RdPreW)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64.Alloc (Call Ea)
open Spike.Lib.X64.HelloPh.StartH0U (invUH msUHg)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0B (StartPH W0Hg)
open Spike.Lib.X64.HelloPh.RootH0 (msBotHg)
open Spike.Lib.X64.HelloPh.StartH0H1 (RdLandHg hRdU_of_h1Fg)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib (FragS Frag SegWS LocalRun PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0`. -/
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
/-- main's owned words before the spawn, at `scc_rt_nthreads`. -/
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) NT

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The root's memory sides at the frames `fs`, the entry's marks. -/
local notation "MSF" => fun fs : List TermRun.Frame => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
  (fun s _ => (OX) s) (AR) I (LB) (ls0T ls) fs

set_option hygiene false in
/-- The root's memory sides at `invUH I`, owning `OX`. -/
local notation "MSU" => msUHg (asm := asm) hpw i0 (OX) E rd I ls

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
/-- The start's level at the root's choices, at `OX`. -/
local notation "WP" => WSg (OX) (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
local notation "JW" => JS (Ly) 0#64 c0S

set_option hygiene false in
/-- `scc_rt_main`'s region at the new stack's base `v`. -/
local notation "RM" v => RS helloLsw v

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at `scc_rt_main`'s region `RM v`. -/
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RM v) (JW)

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- The root's fragment with `I3`'s `inv0` disjunct `⊥` (`RootH0.msBotHg`'s). -/
local notation "IB" => I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2

set_option hygiene false in
/-- The root's memory sides at `invUH IB`, owning `OX`. -/
local notation "MSUB" => msUHg (asm := asm) hpw i0 (OX) E rd (IB) ls

set_option maxHeartbeats 1600000 in
/-- **`RootH0.hstHg`'s `hst0` at `OX`, `hrd` discharged**: `StartH0X.hst0_X` at `J1 := mRdJ0 (J' TOP)`, `hrd` by
`HrdRootX.hrd_RXT` (given `hm`, `hctx`), `hloc` by `LocalRun.refl`. -/
theorem hst0_XR (E : Entry) (hE : E.Ok (Ly).Λ)
    {Ctx : FragS isa} {ls0 : Lsize} {rd : TermRun.Word → Prop} {ls : Lsize}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → Spike.Lib.MemSide isa}
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo)
    (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.X64HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) (mNC (Ly).lab (RM v) (JW)) s c →
      WP s c [])
    (hctx : ∀ (v : BitVec 64) (m0 : MachineData) (σC : FAS), ∀ q : Call, q.OK ((MSUB) [FR]) (Ly).lab →
      q.ra = ((Ly).lab ".Lwc_rodata.x0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (RM v)))
        (fun m => mF (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m ∧
          Spike.Lib.X64.Flow.Ret0.CallerCells (mR (RM v)) (-48) (-160) 8 m ∧
          Spike.Lib.X64.Flow.HelloRd.RdCtx ((MSUB) [FR]) (Ly).lab (mR (RM v)) (mRdJ0 ((J') v) σC)
            (mRdJ0 ((J') v) σC) q m)
        (Spike.Lib.X64.Alloc.N (Ly).lab ((MSUB) [FR]) q .rmw) s c → TP (TV) s → Ctx s c [FR])
    (hq : ∀ σC σ c, mRdJ0 ((J') (TOP)) σC σ c → ∃ q : Call, q.OK ((MSUB) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSUB) [FR]) = 3#64)
    /- level 1's statement: rodata's landing at `OX` is in `inv1 … [FR]` -/
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandHg (asm := asm) hpw i0 (OX) E rd (IB) ls fun σC => mRdJ0 ((J') (TOP)) σC) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH
      (msBotHg (asm := asm) hpw IH E rd ls inv1 inv2 (OX) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (mR (RM (TOP))) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    SegWS (W0Hg (asm := asm) hpw IH (OX) E DtW Ctx (ls0T ls0) (FR))
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB)
      (msBotHg (asm := asm) hpw IH E rd ls inv1 inv2 (OX)) (StartPH hpw IH E) (fun _ _ _ => False) :=
  Spike.Lib.X64.HelloPh.StartH0X.hst0_X (asm := asm) hpw i0 E hE hpa hhp hlo0 hstat hA13 hctr2 hc hWe
    (Spike.Lib.X64.HelloPh.HrdRootX.hrd_RXT hpw i0 E rd (IB) ls hpa hhp hlo0 hc hA13 hm (Ctx := Ctx)
      (ls0 := ls0) hctx)
    (fun _ _ c h => ⟨c, .refl _, h⟩) hq h1 hhabctlRd

set_option maxHeartbeats 1600000 in
/-- **`RootH0.hstHg`'s `hst0` at `OX` at the root's context, `hrd` closed**: `hst0_XR`'s at
`Ctx := LandRU.CtxRdHg … OX`, `hrd` by `HrdRootX.hrd_RdHX` (no `hctx`). -/
theorem hst0_XRc (E : Entry) (hE : E.Ok (Ly).Λ)
    {ls0 : Lsize} {rd : TermRun.Word → Prop} {ls : Lsize}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → Spike.Lib.MemSide isa}
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo)
    (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.X64HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) (mNC (Ly).lab (RM v) (JW)) s c →
      WSg (OX) (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly))
        (Spike.Lib.X64.HelloPh.LandRU.CtxRdHg (asm := asm) hpw i0 E rd ls (OX)) (LB) (ls0T ls0) (FR) (X0WH (Ly) (AX))
        s c [])
    (hq : ∀ σC σ c, mRdJ0 ((J') (TOP)) σC σ c → ∃ q : Call, q.OK ((MSUB) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSUB) [FR]) = 3#64)
    /- level 1's statement: rodata's landing at `OX` is in `inv1 … [FR]` -/
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandHg (asm := asm) hpw i0 (OX) E rd (IB) ls fun σC => mRdJ0 ((J') (TOP)) σC) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH
      (msBotHg (asm := asm) hpw IH E rd ls inv1 inv2 (OX) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (mR (RM (TOP))) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    SegWS (W0Hg (asm := asm) hpw IH (OX) E DtW (Spike.Lib.X64.HelloPh.LandRU.CtxRdHg (asm := asm) hpw i0 E rd ls (OX))
        (ls0T ls0) (FR))
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB)
      (msBotHg (asm := asm) hpw IH E rd ls inv1 inv2 (OX)) (StartPH hpw IH E) (fun _ _ _ => False) :=
  Spike.Lib.X64.HelloPh.StartH0X.hst0_X (asm := asm) hpw i0 E hE hpa hhp hlo0 hstat hA13 hctr2 hc hWe
    (Spike.Lib.X64.HelloPh.HrdRootX.hrd_RdHX hpw i0 E rd (IB) ls hpa hhp hlo0 hc hA13 hm (ls0 := ls0))
    (fun _ _ c h => ⟨c, .refl _, h⟩) hq h1 hhabctlRd

end Spike.Lib.X64.HelloPh.StartH0XR

/-- info: 'Spike.Lib.X64.HelloPh.StartH0XR.hst0_XR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0XR.hst0_XR

/-- info: 'Spike.Lib.X64.HelloPh.StartH0XR.hst0_XRc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0XR.hst0_XRc
