/-
**`OpenW.hW0` at hello's level-0 root context, the child's stack unmapped** (x86-64; the twin of
`Spike/Lib/A64HelloLandRU.lean`): level 0 ends at `wc_rodata`'s landing, so its only counter add is
`wc_rodata`'s, under main's frame and thread pointer (`CtxRdH`; `wc_main`'s add and the box's store are level
1's). The root's context is `CtxRdU := RootUL.CtxU CtxRdH` (`r1Of` unmapped).

At `CtxRdU` the counter row is `RootUL.ctrRow_ofFTU` (the add keeps `TP` and `U r1Of` into `c2`), its tail
`LandRd.HLandRdU` (in `inv0H` at `CtxRdH`) moved up by `RootUL.inv0_upH`; the add writes the counter
(`CtrF.ctrAtF_wr`), so `hnew` is vacuous.

- `refHg`, `CtxRdHg`: the reference side and the level-0 context at an own map `own` (`refH`, `CtxRdH` at `ownGH`).
- `CtxRdH`, `CtxRdU`: the level-0 context, with `r1Of` unmapped.
- `hctx_rdRHg`, `hctx_rdRH`: a counter add of `wc_rodata`'s buffer call under main's frame and thread pointer is in
  `CtxRdHg own` (`CtxRdH`).
- `hW0_RdU`: `hW0` at `helloDR` with `Ctx := CtxRdU`, given `HLandRdU` at `inv0H … CtxRdH …`.

## Differences from the AArch64 version

- The layout is `RuntimeLayout.ofPlaceWX` at `X64.HelloImms.immsH`; the loader's facts are the two parses
  `cellsOf asm` (AArch64 `textProgram`), and the allocator's code is `LandR.hcode_H`'s three facts (`Lays`,
  `endOf`, `allocIn`) under `(Ly).valid`.
- main's thread pointer is `tpOf (tcbS Ly)` (`%fs`'s base; AArch64 `pinA + 8` in `TPIDR_EL0`).
- `wc_rodata`'s call is in `scc_rt_main`'s region `RS helloLsw v` (AArch64 `swR v (-helloLsw) 0`), its caller's
  invariant `rdJH` at that region, returning to `.Lwc_rodata.x15` with `CallerCells` reaching `8` (AArch64
  `.L19_wc_rodata.sp0`, `0`); the regions' stability is `Land.fstable_FS`, `Hello1.mR_ok`, `Land.fstable_aRH` (`Land3`)
  with no alignment.
- The counter add's tail starts at `c2` (AArch64 `n4`); `inv0_upH` takes no `a13data` premise, so neither does
  `hW0_RdU`.
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
open Spike.Lib.X64ConsumerA (SFactsACH)
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
open Spike.Lib.X64.HelloPh.RootH0 (inv0H)
open Spike.Lib.X64.HelloPh.RootUL (CtxU)
open Spike.Lib.X64.HelloPh.LandRd (HLandRdU)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloRootO (helloDR)

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
returning to `.Lwc_rodata.x15`, under main's frame and thread pointer, at a memory side that is `refHg own` but for
`xa`. -/
theorem hctx_rdRHg (own : State → List (Loc × Val)) (hc : Spike.Lib.X64.Rt.CtrZ o) {ms : MemSide isa}
    (hms : ms = { refHg (asm := asm) hpw i0 E rd ls own [FR] with xa := ms.xa }) (v : BitVec 64)
    (m0 : MachineData) (σC : FAS) :
    ∀ q : Call, q.OK ms (Ly).lab → q.ra = ((Ly).lab ".Lwc_rodata.x15").toBitVec →
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
returning to `.Lwc_rodata.x15`, under main's frame and thread pointer (`hctx_rdRHg` at `ownGH`). -/
theorem hctx_rdRH (hc : Spike.Lib.X64.Rt.CtrZ o) {ms : MemSide isa}
    (hms : ms = { refH (asm := asm) hpw i0 E rd ls [FR] with xa := ms.xa }) (v : BitVec 64) (m0 : MachineData)
    (σC : FAS) :
    ∀ q : Call, q.OK ms (Ly).lab → q.ra = ((Ly).lab ".Lwc_rodata.x15").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (RS helloLsw v)))
        (fun m => mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (RS helloLsw v)) (-48) (-160) 8 m ∧
          RdCtx ms (Ly).lab (mR (RS helloLsw v)) (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC) q m)
        (N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxRdH (asm := asm) hpw i0 E rd ls s c [FR] :=
  hctx_rdRHg hpw i0 E rd ls _ hc hms v m0 σC

variable {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}

set_option hygiene false in
/-- The root's instance data at `Ctx := CtxRdU`, `frM := frH c0S.env`, both levels at `ls`. -/
local notation "D" => helloDR (asm := asm) hpw TI E (CtxRdU (asm := asm) hpw i0 E (fun _ => True)
    ls) ls (FR) W1 inv1 W2 inv2

set_option hygiene false in
local notation "μE" => (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ

/-- **`hW0` at `Ctx := CtxRdU`** (`WakeWf.hW0`): the counter row by `ctrRow_ofFTU`, its tail `hR` (`HLandRdU` in
`inv0H` at `CtxRdH`) lifted by `inv0_upH` with `U r1Of` kept by the add; `hnew` vacuous (the add writes the
counter, `ctrAtF_wr`). -/
theorem hW0_RdU (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hR : HLandRdU (asm := asm) hpw i0 E (fun _ => True) ls
      (inv0H (asm := asm) hpw TI E (fun _ => True) (CtxRdH (asm := asm) hpw i0 E (fun _ => True) ls) ls ls (FR)
        inv1 inv2)) :
    ∀ s c fs, (D).inv0 s c fs → (D).W0 s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc (D).rd (D).G (D).own (D).ar (Spike.Lib.X64HelloO.IH (D)) (D).L0 (D).ls0 s c fs
        (D).Dt (Spike.Lib.X64.WriteAb.Ab (Ly).lab) (D).Cl
        (Spike.Lib.X64.Hello.ThreadsAb.AcH (Ly).lab Spike.Lib.X64.HelloPh.StartWf.pfxM) := by
  haveI := (Ly).valid
  obtain ⟨hp, hend, hin⟩ := Spike.Lib.X64.HelloPh.LandR.hcode_H hpw i0 hpa hhp
  exact Spike.Lib.X64.WakeWf.hW0
    (fun _ _ _ _ hC _ _ _ hr _ =>
      Spike.Lib.X64.HelloPh.RootUL.ctrRow_ofFTU hp hend hin (fun _ => rfl)
        (fun fs ms0 R F q hms hG hok s c hA ht hu => .inl ⟨rfl, rfl,
          Spike.Lib.X64.HelloPh.RootUL.inv0_upH hpw i0 E (fun _ => True)
            (CtxRdH (asm := asm) hpw i0 E (fun _ => True) ls) ls (FR) inv1 inv2 s c fs
            (hR fs ms0 R F q hms hG hok s c hA hu ht) hu⟩)
        hC.1.1 hC.1.2 hC.2 hr)
    (fun s c fs _ hC hW _ _ _ _ _ _ _ =>
      (hW (Spike.Lib.X64.HelloPh.CtrF.ctrAtF_wr hp hend hin (fun _ => rfl) s c fs hC.1.1)).elim)

end Spike.Lib.X64.HelloPh.LandRU

/-- info: 'Spike.Lib.X64.HelloPh.LandRU.hctx_rdRHg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandRU.hctx_rdRHg

/-- info: 'Spike.Lib.X64.HelloPh.LandRU.hctx_rdRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandRU.hctx_rdRH

/-- info: 'Spike.Lib.X64.HelloPh.LandRU.hW0_RdU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandRU.hW0_RdU
