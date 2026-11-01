/-
**The root's level-0 premises at `LandRU.CtxRdU`** (AArch64): the root's context
`Ctx` (`helloDR`'s, `RootInv`'s `CR`) moves from `Land.CtxRH` to `LandRU.CtxRdU` (`wc_rodata`'s counter add under
main's frame and thread pointer, the child's stack unmapped), the context the level-0 route is proved at
(`LandRU.hW0_RdU`, `RootUL.hst0_UH`); `CtxRH`'s `wc_main` and store disjuncts are level 1's (`Land1.CtxR1H`), and
no root statement reads them. Of the root's premises only `hst0` and `hW0` see the context's content; the rest
(`H0Stmt.h0Stmt_root`, `RootPlug.RootRest`, `W2I`, `inv2H`, `RootL1U.hW1_rootU`, `HelloHClW.hClH_ofRI`,
`HelloSegEnd.hpc_ofR`, `HelloXOk.hX_ofR`, `HelloAssemblyRS.hello_obligations_RS`) are generic in it. Here are the
two at `CtxRdU`, with the context's one obligation (`HrdS.hrd_WSHF`'s `hctx`) discharged by `HrdRoot.hrd_RdH`
and level 1's statement taken in the root's form (at level 1's fragment `RootL1F.I0H`, its entry moved by
`rdLandH_xa`).

- `h1StmtHF_mono_rd`, `h1_rdLand_xa`: `H1StmtHF` is antitone in its entry `Rd`; at `RdLandH` the fragment is free.
- `hlandRdU_root`: `LandRd.HLandRdU` at `inv0H … CtxRdH …` from level 1's statement at any fragment and the level-0
  controls' facts `hhabctlRd` (`LandRd.hlandRd_U` at `hrd_RdH`).
- `hW0_RdU'`: `oPremH_R`'s `hW0` at `Ctx := CtxRdU` from the same (`LandRU.hW0_RdU`).
- `hst0_RdH`, `hst0_RdU`: the start segment at `CtxRdH` (`StartH0U1.hst0_ofHU1_i0` at `hrd_RdH`, `J1 := mRdJ0 J'`,
  `hloc` by reflexivity) and at `CtxRdU` (`RootUL.hst0_UH`). The premises left are level 0's source and frame
  facts `hWe`, `hq` and `hhabctlRd`, the loader's, and level 1's statement.
-/
import Spike.Lib.A64HelloHrdRoot
import Spike.Lib.A64HelloRootL1F
import Spike.Lib.A64HelloStartH0U1

namespace Spike.Lib.A64.HelloPh.CtxRdU

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS I3)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.A64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.A64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.RootH0 (msBotH inv0H)
open Spike.Lib.A64.HelloPh.RootUL (CtxU)
open Spike.Lib.A64.HelloPh.LandRU (CtxRdH CtxRdU)
open Spike.Lib.A64.HelloPh.LandRd (HLandRdU)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.A64.Flow (At swR)
open Spike.Lib.A64.Flow.Hello1 (mNC mRdJ0)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib (FragS SegWS MemSide)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloRootO (helloDR)
open Spike.Lib.HelloPreA (H1StmtHF)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## Level 1's statement at another entry -/

/-- **`H1StmtHF` is antitone in its entry `Rd`** (the entry is asked into `inv1` only). -/
theorem h1StmtHF_mono_rd {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {K : State → State → Prop}
    {ar : Spike.Lib.Arena} {L0 : Lbl} {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    {L : RuntimeLayout} {Rd Rd' : WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {fr : List TermRun.Frame}
    (h : ∀ l b n s c, Rd' l b n s c → Rd l b n s c) (hs : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr) :
    H1StmtHF W1 K ar L0 ms1 L Rd' inv1 fr :=
  fun l b n hl hb => ⟨(hs l b n hl hb).1, fun s c hr => (hs l b n hl hb).2.1 s c (h l b n s c hr),
    (hs l b n hl hb).2.2⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

/-- **Level 1's statement at `RdLandH` is at any fragment** (`RootL1F.rdLandH_xa`: the root proves it at level 1's
fragment `I0H`, level 0 asks it at `msBotH`'s). -/
theorem h1_rdLand_xa {E : Entry} {rd : TermRun.Word → Prop} {I I' : InvS} {ls : Lsize}
    {J1 : FAS → FAS → Spike.Lib.Ctl → Prop} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {K : State → State → Prop} {ar : Spike.Lib.Arena} {L0 : Lbl}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2} {L : RuntimeLayout}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {fr : List TermRun.Frame}
    (hs : H1StmtHF W1 K ar L0 ms1 L (RdLandH (asm := asm) hpw i0 E rd I ls J1) inv1 fr) :
    H1StmtHF W1 K ar L0 ms1 L (RdLandH (asm := asm) hpw i0 E rd I' ls J1) inv1 fr :=
  h1StmtHF_mono_rd (fun _ _ _ _ _ h => Spike.Lib.A64.HelloPh.RootL1F.rdLandH_xa hpw i0 h) hs

/-! ## The root's level 0 at `CtxRdU` -/

variable (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "TI" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw TI

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- main's frame at the root (`StartH0U`'s `FR`). -/
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at the root (`StartH0U`'s `J'`). -/
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- `msBotH`'s fragment: `I3` with its `inv0` disjunct `⊥`. -/
local notation "IB" => I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2

set_option hygiene false in
local notation "MSB" => msBotH (asm := asm) hpw TI E rd ls inv1 inv2

set_option hygiene false in
/-- The start's level at `CtxRdH`. -/
local notation "WPRd" => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly))
  (CtxRdH (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls) (FR) (X0WH (Ly) (AX))

variable {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}

/-- **`HLandRdU` at the root's level-0 invariant at `CtxRdH`** (`LandRd.hlandRd_U`, its `hrd` the root's
`HrdRoot.hrd_RdH`): from level 1's statement at any fragment `I` (`h1_rdLand_xa`) and the level-0 controls' facts
at `rX .abort` (`hhabctlRd`, row `5h-S-habctl`). -/
theorem hlandRdU_root (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2)
    {I : InvS} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    (h1 : H1StmtHF W1 K (AR) (LB) ms1 (Ly) (RdLandH (asm := asm) hpw i0 E rd I ls (fun σC => mRdJ0 (J') σC)) inv1
      [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH ((MSB) [FR]) (Ly).lab helloSrc (Ly).Λ (LB) (AR)
      [FR] (mRdJ0 (J') σC)) :
    HLandRdU (asm := asm) hpw i0 E rd ls
      (inv0H (asm := asm) hpw TI E rd (CtxRdH (asm := asm) hpw i0 E rd ls) ls ls (FR) inv1 inv2) :=
  Spike.Lib.A64.HelloPh.LandRd.hlandRd_U hpw i0 E rd ls (CtxRdH (asm := asm) hpw i0 E rd ls) ls inv1 inv2 hpa hhp
    hlo0 hc hA13 (Spike.Lib.A64.HelloPh.HrdRoot.hrd_RdH hpw i0 E rd (IB) ls hpa hhp hlo0 hc hA13 hm)
    (h1_rdLand_xa hpw i0 h1) hhabctlRd

variable {W1' : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}

set_option hygiene false in
/-- The root's instance data at `Ctx := CtxRdU`, `rd := True`, `frM := frH c0S.env`, both levels at `ls`
(`RootInv`'s `D` after the switch). -/
local notation "DU" => helloDR (asm := asm) hpw TI E (CtxRdU (asm := asm) hpw i0 E (fun _ => True) ls) ls (FR) W1'
  inv1 W2 inv2

/-- **`oPremH_R`'s `hW0` at `Ctx := CtxRdU`** (`LandRU.hW0_RdU` at `hlandRdU_root`; `rd := True`, both levels at
`ls`, as the root's): from level 1's statement at any fragment and `hhabctlRd`. -/
theorem hW0_RdU' (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2)
    {I : InvS} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    (h1 : H1StmtHF W1 K (AR) (LB) ms1 (Ly) (RdLandH (asm := asm) hpw i0 E (fun _ => True) I ls
      (fun σC => mRdJ0 (J') σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH
      (msBotH (asm := asm) hpw TI E (fun _ => True) ls inv1 inv2 [FR]) (Ly).lab helloSrc (Ly).Λ (LB) (AR)
      [FR] (mRdJ0 (J') σC)) :
    ∀ s c fs, (DU).inv0 s c fs → (DU).W0 s c fs →
      Spike.Lib.A64ConsumerA.SFactsACH (Ly).Λ ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ)
        helloSrc (DU).rd (DU).G (DU).own (DU).ar (Spike.Lib.HelloO.IH (DU)) (DU).L0 (DU).ls0 s c fs (DU).Dt
        (Spike.Lib.A64.WriteAb.Ab (Ly).lab) (DU).Cl
        (Spike.Lib.A64.HelloWf.AcH (Ly).lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM) :=
  Spike.Lib.A64.HelloPh.LandRU.hW0_RdU hpw i0 E ls hpa hhp hA13
    (hlandRdU_root hpw i0 E (fun _ => True) ls hpa hhp hlo0 hc hA13 hm h1 hhabctlRd)

/-- **The start segment at `CtxRdH`** (`StartH0U1.hst0_ofHU1_i0` at `msBotH`'s fragment, `J1 := mRdJ0 J'`): its
`hrd` is `HrdRoot.hrd_RdH`, `hloc` reflexivity, level 1's statement at any fragment. Left: the loader's facts, the
entry's admissibility, `wc_rodata`'s entry states inside the level (`hWe`), its buffer call's site facts (`hq`) and
the level-0 controls' facts (`hhabctlRd`). -/
theorem hst0_RdH (hE : E.Ok (Ly).Λ) (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2)
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v)
      (mNC (Ly).lab (JS (Ly) 0#64 c0S)) s c → WPRd s c [])
    (hq : ∀ σC σ c, mRdJ0 (J') σC σ c → ∃ q : Call, q.OK (msUH (asm := asm) hpw i0 E rd (IB) ls [FR]) (Ly).lab ∧
      q.c0 = c ∧ q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (msUH (asm := asm) hpw i0 E rd (IB) ls [FR]) = 3#64)
    {I : InvS} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    (h1 : H1StmtHF W1 K (AR) (LB) ms1 (Ly) (RdLandH (asm := asm) hpw i0 E rd I ls (fun σC => mRdJ0 (J') σC)) inv1
      [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH ((MSB) [FR]) (Ly).lab helloSrc (Ly).Λ (LB) (AR)
      [FR] (mRdJ0 (J') σC)) :
    SegWS (W0H (asm := asm) hpw TI E DtW (CtxRdH (asm := asm) hpw i0 E rd ls) (ls0T ls) (FR))
      (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) helloSrc (LB) (MSB) (StartPH hpw TI E)
      (fun _ _ _ => False) :=
  Spike.Lib.A64.HelloPh.StartH0U1.hst0_ofHU1_i0 (asm := asm) hpw i0 E hE (inv0 := fun _ _ _ => False)
    hpa hhp hlo0 hstat hA13 hctr2 hc hWe
    (Spike.Lib.A64.HelloPh.HrdRoot.hrd_RdH hpw i0 E rd (IB) ls hpa hhp hlo0 hc hA13 hm)
    (fun _ _ c h => ⟨c, .refl _, h⟩) hq (h1_rdLand_xa hpw i0 h1) hhabctlRd

/-- **The start segment at `CtxRdU`** (`RootUL.hst0_UH` at `hst0_RdH`): `RootInv`'s `hst0` at `CR := CtxRdU`. -/
theorem hst0_RdU (hE : E.Ok (Ly).Λ) (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2)
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v)
      (mNC (Ly).lab (JS (Ly) 0#64 c0S)) s c → WPRd s c [])
    (hq : ∀ σC σ c, mRdJ0 (J') σC σ c → ∃ q : Call, q.OK (msUH (asm := asm) hpw i0 E rd (IB) ls [FR]) (Ly).lab ∧
      q.c0 = c ∧ q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (msUH (asm := asm) hpw i0 E rd (IB) ls [FR]) = 3#64)
    {I : InvS} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    (h1 : H1StmtHF W1 K (AR) (LB) ms1 (Ly) (RdLandH (asm := asm) hpw i0 E rd I ls (fun σC => mRdJ0 (J') σC)) inv1
      [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH ((MSB) [FR]) (Ly).lab helloSrc (Ly).Λ (LB) (AR)
      [FR] (mRdJ0 (J') σC)) :
    SegWS (W0H (asm := asm) hpw TI E DtW (CtxRdU (asm := asm) hpw i0 E rd ls) (ls0T ls) (FR))
      (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) helloSrc (LB) (MSB) (StartPH hpw TI E)
      (fun _ _ _ => False) :=
  Spike.Lib.A64.HelloPh.RootUL.hst0_UH hpw i0 E rd (CtxRdH (asm := asm) hpw i0 E rd ls) ls (FR) inv1 inv2 hE hA13
    (hst0_RdH hpw i0 E rd ls hE hpa hhp hlo0 hstat hA13 hctr2 hc hm hWe hq h1 hhabctlRd)

end Spike.Lib.A64.HelloPh.CtxRdU

/-- info: 'Spike.Lib.A64.HelloPh.CtxRdU.h1StmtHF_mono_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtxRdU.h1StmtHF_mono_rd

/-- info: 'Spike.Lib.A64.HelloPh.CtxRdU.h1_rdLand_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtxRdU.h1_rdLand_xa

/-- info: 'Spike.Lib.A64.HelloPh.CtxRdU.hlandRdU_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtxRdU.hlandRdU_root

/-- info: 'Spike.Lib.A64.HelloPh.CtxRdU.hW0_RdU'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtxRdU.hW0_RdU'

/-- info: 'Spike.Lib.A64.HelloPh.CtxRdU.hst0_RdH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtxRdU.hst0_RdH

/-- info: 'Spike.Lib.A64.HelloPh.CtxRdU.hst0_RdU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtxRdU.hst0_RdU
