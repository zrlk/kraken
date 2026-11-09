/-
**`OpenW.hW0` at hello's level-0 root context, the child's stack unmapped** (x86-64; the twin of
`Spike/Lib/A64HelloLandRU.lean`): level 0 ends at `wc_rodata`'s landing, so its only counter add is
`wc_rodata`'s, under main's frame and thread pointer (`CtxRdH`; `wc_main`'s add and the box's store are level
1's). The root's context is `RootUL.CtxU CtxRdHg` (`r1Of` unmapped; `CtxRdU` at `ownGH`).

At it the counter row is `RootUL.ctrRow_ofFTU` (the add keeps `TP` and `U r1Of` into `c2`) and the add writes the
counter (`CtrF.ctrAtF_wr`), so `hnew` is vacuous; the root's `hW0` at the self words is
`X64HelloRootL0X.hW0_RdUX`.

- `refHg`, `CtxRdHg`: the reference side and the level-0 context at an own map `own` (`refH`, `CtxRdH` at `ownGH`).
- `CtxRdH`, `CtxRdU`: the level-0 context, with `r1Of` unmapped.
- `hctx_rdRHg`, `hctx_rdRH`: a counter add of `wc_rodata`'s buffer call under main's frame and thread pointer is in
  `CtxRdHg own` (`CtxRdH`).

## Differences from the AArch64 version

- The layout is `RuntimeLayout.ofPlaceWX` at `X64.HelloImms.immsH`; the loader's facts are the two parses
  `cellsOf asm` (AArch64 `textProgram`), and the allocator's code is `LandR.hcode_H`'s three facts (`Lays`,
  `endOf`, `allocIn`) under `(Ly).valid`.
- main's thread pointer is `tpOf (tcbS Ly)` (`%fs`'s base; AArch64 `pinA + 8` in `TPIDR_EL0`).
- `wc_rodata`'s call is in `scc_rt_main`'s region `RS helloLsw v` (AArch64 `swR v (-helloLsw) 0`), its caller's
  invariant `rdJH` at that region, returning to `.Lwc_rodata.x0` with `CallerCells` reaching `8` (AArch64
  `.L19_wc_rodata.sp0`, `0`); the regions' stability is `Land.fstable_FS`, `Hello1.mR_ok`, `Land.fstable_aRH` (`Land3`)
  with no alignment.
- The counter add's tail starts at `c2` (AArch64 `n4`).
- AArch64's `hW0_RdU` (at `ownGH`) is at `ownGHXW` here: `X64HelloRootL0X.hW0_RdUX`.
-/
import Spike.Lib.X64HelloRootUL
import Spike.Lib.X64HelloRootO
import Spike.Lib.X64HelloLand3

namespace Spike.Lib.X64.HelloPh.LandRU

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib (FragS MemSide PlaceWX)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.Flow.Hello1 (mR mF mRdJ0 aR)
open Spike.Lib.X64.Flow.HelloRd (RdCtx)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.Alloc (Call N)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.HelloPh.Land (CtrAtF refH GcRdH)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.RootUL (CtxU)
open Spike.Lib.X64.HelloPh.C0S (c0S)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "TI" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw TI

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at `scc_rt_main`'s region `RS helloLsw v`. -/
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

/-- **The root's reference memory side at an own map `own`** (`Land.refH` at `own`: `StartH0U.msUHg own` with no
allocation fragment). `refH` is it at `ownGH`. -/
noncomputable abbrev refHg (own : State → List (Loc × Val)) (fs : List TermRun.Frame) : MemSide isa :=
  Spike.Lib.X64.HelloPh.StartH0U.msUHg (asm := asm) hpw i0 own E rd (fun _ _ _ _ _ => False) ls fs

/-- **The root's level-0 context at an own map `own`**: `wc_rodata`'s counter add (`GcRdH`, under main's frame) at
the reference side `refHg own`, under main's thread pointer. `CtxRdH` is it at `ownGH`. -/
def CtxRdHg (own : State → List (Loc × Val)) : FragS isa := fun s c fs =>
  CtrAtF (refHg (asm := asm) hpw i0 E rd ls own) (Ly).exe (Ly).endPc (GcRdH hpw i0) s c fs ∧ TP (TV) s

/-- **The root's level-0 context**: `wc_rodata`'s counter add (`GcRdH`, under main's frame) under main's thread
pointer. -/
def CtxRdH : FragS isa := fun s c fs =>
  CtrAtF (refH (asm := asm) hpw i0 E rd ls) (Ly).exe (Ly).endPc (GcRdH hpw i0) s c fs ∧ TP (TV) s

/-- **The root's level-0 context with the child's stack unmapped.** -/
abbrev CtxRdU : FragS isa := CtxU hpw i0 (CtxRdH (asm := asm) hpw i0 E rd ls)

/-- `CtxRdH` is `CtxRdHg` at `ownGH`, by definition. -/
example : CtxRdH (asm := asm) hpw i0 E rd ls =
    CtxRdHg (asm := asm) hpw i0 E rd ls (Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)) :=
  rfl

/-- **A counter add of `wc_rodata`'s buffer call is in `CtxRdHg own`**: a buffer allocation from `wc_rodata`
returning to `.Lwc_rodata.x0`, under main's frame and thread pointer, at a memory side that is `refHg own` but for
`xa`. -/
theorem hctx_rdRHg (own : State → List (Loc × Val)) (hc : Spike.Lib.X64.Rt.CtrZ o) {ms : MemSide isa}
    (hms : ms = { refHg (asm := asm) hpw i0 E rd ls own [FR] with xa := ms.xa }) (v : BitVec 64)
    (m0 : MachineData) (σC : FAS) :
    ∀ q : Call, q.OK ms (Ly).lab → q.ra = ((Ly).lab ".Lwc_rodata.x0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (RS helloLsw v)))
        (fun m => mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (RS helloLsw v)) (-48) (-160) 8 m ∧
          RdCtx ms (Ly).lab (mR (RS helloLsw v)) (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC) q m)
        (N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxRdHg (asm := asm) hpw i0 E rd ls own s c [FR] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { refHg (asm := asm) hpw i0 E rd ls own [FR] with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt htp
  refine ⟨⟨_, _, _, q, rfl, ⟨rfl, hq, v, m0, σC, rfl, rfl, hra⟩, ⟨hq.toS, ?_, fun m hm => ?_⟩, hAt⟩, htp⟩
  · by_cases hv : v = topS (Ly) 0#64
    case neg => exact fun m _ hm => (hv hm.1.1.1.2.1.1).elim
    subst hv
    obtain ⟨-, hok0, hF0⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
    obtain ⟨hmR, hFm⟩ := Spike.Lib.X64.Flow.Hello1.mR_ok hok0 hF0
      (by show (8 - helloLsw : Int) ≤ -288; decide) (by show (8 : Int) ≤ 8; decide) m0 σC
    exact Spike.Lib.X64.HelloPh.Land.fstable_aRH hmR hFm (by show (-208 : Int) ≤ -208; decide)
      (by show (8 : Int) ≤ 8; decide)
  · -- the counter word is `own`-independent: `Land.ctr_none_FS` at `refH`
    exact Spike.Lib.X64.HelloPh.Land.ctr_none_FS (asm := asm) hpw i0 E rd ls hc (fs := [FR]) (X := X) m hm.1.1

/-- **A counter add of `wc_rodata`'s buffer call is in `CtxRdH`**: a buffer allocation from `wc_rodata`
returning to `.Lwc_rodata.x0`, under main's frame and thread pointer (`hctx_rdRHg` at `ownGH`). -/
theorem hctx_rdRH (hc : Spike.Lib.X64.Rt.CtrZ o) {ms : MemSide isa}
    (hms : ms = { refH (asm := asm) hpw i0 E rd ls [FR] with xa := ms.xa }) (v : BitVec 64) (m0 : MachineData)
    (σC : FAS) :
    ∀ q : Call, q.OK ms (Ly).lab → q.ra = ((Ly).lab ".Lwc_rodata.x0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (RS helloLsw v)))
        (fun m => mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (RS helloLsw v)) (-48) (-160) 8 m ∧
          RdCtx ms (Ly).lab (mR (RS helloLsw v)) (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC) q m)
        (N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxRdH (asm := asm) hpw i0 E rd ls s c [FR] :=
  hctx_rdRHg hpw i0 E rd ls _ hc hms v m0 σC

end Spike.Lib.X64.HelloPh.LandRU

/-- info: 'Spike.Lib.X64.HelloPh.LandRU.hctx_rdRHg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandRU.hctx_rdRHg

/-- info: 'Spike.Lib.X64.HelloPh.LandRU.hctx_rdRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandRU.hctx_rdRH
