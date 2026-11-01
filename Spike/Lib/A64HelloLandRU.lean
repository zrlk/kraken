/-
**`OpenW.hW0` at hello's level-0 root context, the child's stack unmapped** (AArch64; the
twin of `Spike/Lib/A64WakeRootUL.lean`'s `rootOpen_U` `hctr0`/`hnew0` at `LandR.hW0_RH`): level 0 ends at
`wc_rodata`'s landing (`StartH0U0`), so its only counter add is `wc_rodata`'s, under main's frame and thread pointer
(`CtxRdH`, `Land.CtxRH`'s first disjunct; `wc_main`'s add and the box's store are level 1's). The root's context is
`CtxRdU := RootUL.CtxU CtxRdH` (`r1Of` unmapped, `RootUL.hst0_UH` from the start segment at `CtxRdH`).

At `CtxRdU` the counter row is `RootUL.ctrRow_ofFTU` (the add keeps `TP` and `U r1Of` into `n4`), its tail
`LandRd.hlandRd_U` (`HLandRdU`, in `inv0H` at `CtxRdH`) moved up by `RootUL.inv0_upH`; the add writes the counter
(`CtrF.ctrAtF_wr`), so `hnew` is vacuous. No `LandR.HLandM`/`HLand1` is consumed.

- `CtxRdH`, `CtxRdU`: the level-0 context, with `r1Of` unmapped.
- `hctx_rdRH`: `HrdS.hrd_WSHF`'s `hctx` at `CtxRdH` (as `Land.hctx_rdH`).
- `hW0_RdU`: `oPremH_R`'s `hW0` at `helloDR` with `Ctx := CtxRdU`, given `HLandRdU` at `inv0H … CtxRdH …`.
-/
import Spike.Lib.A64HelloRootUL

namespace Spike.Lib.A64.HelloPh.LandRU

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.A64ConsumerA (SFactsACH)
open Spike.Lib (FragS MemSide)
open Spike.Lib.A64.Flow (At swR)
open Spike.Lib.A64.Flow.Ret0 (CallerCells pinA)
open Spike.Lib.A64.Flow.Hello1 (mR mF mRdJ0 aR)
open Spike.Lib.A64.Flow.HelloRd (RdCtx)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Alloc (Call N)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.HelloPh.Land (CtrAtF refH GcRdH)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.HelloPh.RootH0 (inv0H)
open Spike.Lib.A64.HelloPh.RootUL (CtxU)
open Spike.Lib.A64.HelloPh.LandRd (HLandRdU)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloRootO (helloDR)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "TI" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw TI

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

/-- **The root's level-0 context**: `wc_rodata`'s counter add (`GcRdH`, under main's frame) under main's thread
pointer (`Land.CtxRH`'s first disjunct). -/
def CtxRdH : FragS isaLSE2 := fun s c fs =>
  CtrAtF (refH (asm := asm) hpw i0 E rd ls) (Ly).exe (Ly).endPc (GcRdH hpw i0) s c fs ∧ TP (TV) s

/-- **The root's level-0 context with the child's stack unmapped.** -/
abbrev CtxRdU : FragS isaLSE2 := CtxU hpw i0 (CtxRdH (asm := asm) hpw i0 E rd ls)

/-- **`HrdS.hrd_WSHF`'s `hctx` at `CtxRdH`** (`Land.hctx_rdH`, its disjunct): a counter add of a buffer call from
`wc_rodata` returning to `.sp0`, under main's frame and thread pointer. -/
theorem hctx_rdRH (hc : Spike.Lib.A64.Rt.CtrZ o) {ms : MemSide isaLSE2}
    (hms : ms = { refH (asm := asm) hpw i0 E rd ls [FR] with xa := ms.xa }) (v : BitVec 64) (m0 : MachineData) (σC :
        FAS) :
    ∀ q : Call, q.OK ms (Ly).lab → q.ra = ((Ly).lab ".L19_wc_rodata.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0)))
        (fun m => mF (swR v (-helloLsw) 0) (FS (Ly) (RS) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 m ∧
          RdCtx ms (Ly).lab (mR (swR v (-helloLsw) 0)) (mRdJ0 (J') σC) (mRdJ0 (J') σC) q m)
        (N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxRdH (asm := asm) hpw i0 E rd ls s c [FR] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { refH (asm := asm) hpw i0 E rd ls [FR] with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt htp
  refine ⟨⟨_, _, _, q, rfl, ⟨rfl, hq, v, m0, σC, rfl, rfl, hra⟩, ⟨hq.toS, ?_, fun m hm => ?_⟩, hAt⟩, htp⟩
  · by_cases hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64
    case neg => exact fun m _ hm => (hv hm.1.1.2.1.1).elim
    subst hv
    obtain ⟨hok, hal, hF0⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
    obtain ⟨hR, -, hF⟩ := Spike.Lib.A64.Flow.Hello1.mR_ok hok hal hF0
      (by show (-helloLsw : Int) ≤ -288; decide) (by show (0 : Int) ≤ 0; decide) m0 σC
    exact Spike.Lib.A64.HelloPh.Land.fstable_aRH hR hF (by show (-208 : Int) ≤ -208; decide)
      (by show (0 : Int) ≤ 0; decide)
  · exact Spike.Lib.A64.HelloPh.Land.ctr_none_FS (asm := asm) hpw i0 E rd ls hc m hm.1.1

variable {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}

set_option hygiene false in
/-- The root's instance data at `Ctx := CtxRdU`, `frM := frH c0S.env`, both levels at `ls`. -/
local notation "D" => helloDR (asm := asm) hpw TI E (CtxRdU (asm := asm) hpw i0 E (fun _ => True)
    ls) ls (FR) W1 inv1 W2 inv2

set_option hygiene false in
local notation "μE" => (Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ

/-- **`oPremH_R`'s `hW0` at `Ctx := CtxRdU`** (`WakeWf.hW0`; wake's `rootOpen_U` `hctr0`/`hnew0`): the counter row
by `ctrRow_ofFTU`, its tail `hR` (`HLandRdU` in `inv0H` at `CtxRdH`) lifted by `inv0_upH` with `U r1Of` kept by the
add; `hnew` vacuous (the add writes the counter, `ctrAtF_wr`). -/
theorem hW0_RdU (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hR : HLandRdU (asm := asm) hpw i0 E (fun _ => True) ls
      (inv0H (asm := asm) hpw TI E (fun _ => True) (CtxRdH (asm := asm) hpw i0 E (fun _ => True) ls) ls ls (FR) inv1
          inv2)) :
    ∀ s c fs, (D).inv0 s c fs → (D).W0 s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc (D).rd (D).G (D).own (D).ar (Spike.Lib.HelloO.IH (D)) (D).L0 (D).ls0 s c fs
        (D).Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab) (D).Cl
        (Spike.Lib.A64.HelloWf.AcH (Ly).lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM) :=
  Spike.Lib.A64.WakeWf.hW0
    (fun _ _ _ _ hC _ _ _ hr _ =>
      Spike.Lib.A64.HelloPh.RootUL.ctrRow_ofFTU (Spike.Lib.A64.HelloPh.LandR.hcode_H hpw i0 hpa hhp) (fun _ => rfl)
        (fun fs ms0 R F q hms hG hok s c hA ht hu => .inl ⟨rfl, rfl,
          Spike.Lib.A64.HelloPh.RootUL.inv0_upH hpw i0 E (fun _ => True) (CtxRdH (asm := asm) hpw i0 E (fun _ => True)
              ls) ls
            (FR) inv1 inv2 hA13 s c fs (hR fs ms0 R F q hms hG hok s c hA hu ht) hu⟩)
        hC.1.1 hC.1.2 hC.2 hr)
    (fun s c fs _ hC hW _ _ _ _ _ _ _ =>
      (hW (Spike.Lib.A64.HelloPh.CtrF.ctrAtF_wr (Spike.Lib.A64.HelloPh.LandR.hcode_H hpw i0 hpa hhp) (fun _ => rfl)
        s c fs hC.1.1)).elim)

end Spike.Lib.A64.HelloPh.LandRU

/-- info: 'Spike.Lib.A64.HelloPh.LandRU.hctx_rdRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandRU.hctx_rdRH

/-- info: 'Spike.Lib.A64.HelloPh.LandRU.hW0_RdU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandRU.hW0_RdU
