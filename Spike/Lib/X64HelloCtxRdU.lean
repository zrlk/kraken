/-
**The root's level-0 premises at `LandRU.CtxRdU`** (x86-64; the twin of `Spike/Lib/HelloCtxRdU.lean`): the root's
context `Ctx` (`helloDR`'s, `RootInv`'s `CR`) is `LandRU.CtxRdU` (`wc_rodata`'s counter add under main's frame and
thread pointer, the child's stack unmapped), the context the level-0 route is proved at (`LandRU.hW0_RdU`). Here
is `hW0` at `CtxRdU`, with the context's one obligation (`HrdS.hrd_WSHF`'s `hctx`) discharged by
`HrdRoot.hrd_RdH` and level 1's statement taken in the root's form (at any fragment, its entry moved by
`RootL1F.rdLandH_xa`).

- `h1StmtHF_mono_rd`, `h1_rdLand_xa`: `H1StmtHF` is antitone in its entry `Rd`; at `RdLandH` the fragment is free.
- `hlandRdU_root`: `LandRd.HLandRdU` at `inv0H … CtxRdH …` from level 1's statement at any fragment and the level-0
  controls' facts `hhabctlRd` (`LandRd.hlandRd_U` at `hrd_RdH`).
- `hW0_RdU'`: `oPremH_R`'s `hW0` at `Ctx := CtxRdU` from the same (`LandRU.hW0_RdU`).

## Differences from the AArch64 version

- `scc_rt_main`'s region at the new stack's base `v` is `MainGlue.RS helloLsw v` (AArch64 `swR v (-helloLsw) 0`),
  and `wc_rodata`'s caller's entry invariant `rdJH` takes it, so `J'` depends on `v`; level 1's statement and
  `hhabctlRd` are at the first stack's top `topS Ly 0` (`LandRd.hlandRd_U`'s), and `HabCtlRdH` takes `wc_rodata`'s
  region `mR (RS helloLsw (topS Ly 0))`.
- The loader's facts are `cellsOf asm = some …` (AArch64 `textProgram asm = .ok …`); `LandRU.hW0_RdU` asks no
  `hA13`.
- `hst0_RdH`'s `J1` is `mRdJ0 (J' (topS Ly 0))` (AArch64 `mRdJ0 J'`): `StartH0U1.hst0_ofHU1_i0`'s `hloc` is asked
  at the first stack's top only, so it is reflexivity there; its `hrd` (at `J' v`, `J1`) is `HrdRoot.hrd_RdH` at
  `v = topS Ly 0` and `HrdRoot.rdPreW_vac` elsewhere (the frame condition pins `v`), and `hq` is at
  `J' (topS Ly 0)`.
-/
import Spike.Lib.X64HelloHrdRoot
import Spike.Lib.X64HelloRootL1F
import Spike.Lib.X64HelloLandRd
import Spike.Lib.X64HelloLandRU
import Spike.Lib.X64HelloStartH0U1
import Spike.Lib.X64HelloRootUL

namespace Spike.Lib.X64.HelloPh.CtxRdU

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (I3 SFactsACH)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.RootH0 (msBotH inv0H)
open Spike.Lib.X64.HelloPh.LandRU (CtxRdH CtxRdU)
open Spike.Lib.X64.HelloPh.LandRd (HLandRdU)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64.Flow.Hello1 (mR mRdJ0)
open Spike.Lib.X64.WakePh.MainGlue (JS RS topS)
open Spike.Lib (FragS MemSide PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloRootO (helloDR)
open Spike.Lib.X64HelloPreA (H1StmtHF)

/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## Level 1's statement at another entry -/

/-- **`H1StmtHF` is antitone in its entry `Rd`** (the entry is asked into `inv1` only). -/
theorem h1StmtHF_mono_rd {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ar : Spike.Lib.Arena} {L0 : Lbl} {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {L : RuntimeLayout} {Rd Rd' : WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {fr : List TermRun.Frame}
    (h : ∀ l b n s c, Rd' l b n s c → Rd l b n s c) (hs : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr) :
    H1StmtHF W1 K ar L0 ms1 L Rd' inv1 fr :=
  fun l b n hl hb => ⟨(hs l b n hl hb).1, fun s c hr => (hs l b n hl hb).2.1 s c (h l b n s c hr),
    (hs l b n hl hb).2.2⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

/-- **Level 1's statement at `RdLandH` is at any fragment** (`RootL1F.rdLandH_xa`: the root proves it at level 1's
fragment `I0H`, level 0 asks it at `msBotH`'s). -/
theorem h1_rdLand_xa {E : Entry} {rd : TermRun.Word → Prop} {I I' : InvS} {ls : Lsize}
    {J1 : FAS → FAS → Spike.Lib.Ctl → Prop} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {K : State → State → Prop} {ar : Spike.Lib.Arena} {L0 : Lbl}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa} {L : RuntimeLayout}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {fr : List TermRun.Frame}
    (hs : H1StmtHF W1 K ar L0 ms1 L (RdLandH (asm := asm) hpw i0 E rd I ls J1) inv1 fr) :
    H1StmtHF W1 K ar L0 ms1 L (RdLandH (asm := asm) hpw i0 E rd I' ls J1) inv1 fr :=
  h1StmtHF_mono_rd (fun _ _ _ _ _ h => Spike.Lib.X64.HelloPh.RootL1F.rdLandH_xa hpw i0 h) hs

/-! ## The root's level 0 at `CtxRdU` -/

variable (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "TI" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw TI

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- main's frame at the root (`StartH0U`'s `FR`). -/
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at the root, at `scc_rt_main`'s region `RS helloLsw v`. -/
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `wc_rodata`'s region at the first stack's top. -/
local notation "MT" => mR (RS helloLsw (TOP))

set_option hygiene false in
/-- `msBotH`'s fragment: `I3` with its `inv0` disjunct `⊥`. -/
local notation "IB" => I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2

set_option hygiene false in
local notation "MSB" => msBotH (asm := asm) hpw TI E rd ls inv1 inv2

variable {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}

/-- **`HLandRdU` at the root's level-0 invariant at `CtxRdH`** (`LandRd.hlandRd_U`, its `hrd` the root's
`HrdRoot.hrd_RdH`): from level 1's statement at any fragment `I` (`h1_rdLand_xa`) and the level-0 controls' facts
at `rX .abort` (`hhabctlRd`). -/
theorem hlandRdU_root (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    {I : InvS} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    (h1 : H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandH (asm := asm) hpw i0 E rd I ls (fun σC => mRdJ0 ((J') (TOP)) σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSB) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (MT) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    HLandRdU (asm := asm) hpw i0 E rd ls
      (inv0H (asm := asm) hpw TI E rd (CtxRdH (asm := asm) hpw i0 E rd ls) ls ls (FR) inv1 inv2) :=
  Spike.Lib.X64.HelloPh.LandRd.hlandRd_U hpw i0 E rd ls (CtxRdH (asm := asm) hpw i0 E rd ls) ls inv1 inv2 hpa hhp
    hlo0 hc (Spike.Lib.X64.HelloPh.HrdRoot.hrd_RdH hpw i0 E rd (IB) ls hpa hhp hlo0 hc hA13 hm)
    (h1_rdLand_xa hpw i0 h1) hhabctlRd

variable {W1' : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}

set_option hygiene false in
/-- The root's instance data at `Ctx := CtxRdU`, `rd := True`, `frM := frH c0S.env`, both levels at `ls`
(`RootInv`'s `D` after the switch). -/
local notation "DU" => helloDR (asm := asm) hpw TI E (CtxRdU (asm := asm) hpw i0 E (fun _ => True) ls) ls (FR) W1'
  inv1 W2 inv2

/-- **`oPremH_R`'s `hW0` at `Ctx := CtxRdU`** (`LandRU.hW0_RdU` at `hlandRdU_root`; `rd := True`, both levels at
`ls`, as the root's): from level 1's statement at any fragment and `hhabctlRd`. -/
theorem hW0_RdU' (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    {I : InvS} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    (h1 : H1StmtHF W1 K (AR) (LB) ms1 (Ly) (RdLandH (asm := asm) hpw i0 E (fun _ => True) I ls
      (fun σC => mRdJ0 ((J') (TOP)) σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH
      (msBotH (asm := asm) hpw TI E (fun _ => True) ls inv1 inv2 [FR]) (Ly).lab helloSrc (Ly).Λ (LB) (MT) (AR)
      [FR] (mRdJ0 ((J') (TOP)) σC)) :
    ∀ s c fs, (DU).inv0 s c fs → (DU).W0 s c fs →
      SFactsACH (Ly).Λ ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ)
        helloSrc (DU).rd (DU).G (DU).own (DU).ar (Spike.Lib.X64HelloO.IH (DU)) (DU).L0 (DU).ls0 s c fs (DU).Dt
        (Spike.Lib.X64.WriteAb.Ab (Ly).lab) (DU).Cl
        (Spike.Lib.X64.Hello.ThreadsAb.AcH (Ly).lab Spike.Lib.X64.HelloPh.StartWf.pfxM) :=
  Spike.Lib.X64.HelloPh.LandRU.hW0_RdU hpw i0 E ls hpa hhp
    (hlandRdU_root hpw i0 E (fun _ => True) ls hpa hhp hlo0 hc hA13 hm h1 hhabctlRd)

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The start's level at `CtxRdH`. -/
local notation "WPRd" => Spike.Lib.X64.HelloPh.StartWcS.WS (Ly) NT (AR) helloSrc Spike.Lib.X64.WakeWf.DtW
  (Spike.Lib.X64.HelloPh.ClH (Ly)) (CtxRdH (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls) (FR)
  (Spike.Lib.X64.HelloPh.StartGlue.X0WH (Ly) (AX))

set_option hygiene false in
/-- `msUH` at `msBotH`'s fragment. -/
local notation "MSUB" => Spike.Lib.X64.HelloPh.StartH0U.msUH (asm := asm) hpw i0 E rd (IB) ls [FR]

/-- **The start segment at `CtxRdH`** (`StartH0U1.hst0_ofHU1_i0` at `msBotH`'s fragment,
`J1 := mRdJ0 (J' (topS Ly 0))`): its `hrd` is `HrdRoot.hrd_RdH`, `hloc` reflexivity, level 1's statement at any
fragment. Left: the loader's facts, the entry's admissibility, `wc_rodata`'s entry states inside the level
(`hWe`), its buffer call's site facts (`hq`) and the level-0 controls' facts (`hhabctlRd`). -/
theorem hst0_RdH (hE : E.Ok (Ly).Λ) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.X64HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hWe : ∀ v s c, Spike.Lib.X64.At (Ly).exe (Ly).endPc (RS helloLsw v)
      (Spike.Lib.X64.WakePh.MainGlue.FS (Ly) (RS0) helloLsw 0#64 v)
      (Spike.Lib.X64.Flow.Hello1.mNC (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)) s c → WPRd s c [])
    (hq : ∀ σC σ c, mRdJ0 ((J') (TOP)) σC σ c → ∃ q : Spike.Lib.X64.Alloc.Call, q.OK (MSUB) (Ly).lab ∧
      q.c0 = c ∧ q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (MSUB) = 3#64)
    {I : InvS} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    (h1 : H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandH (asm := asm) hpw i0 E rd I ls (fun σC => mRdJ0 ((J') (TOP)) σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSB) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (MT) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    Spike.Lib.SegWS (Spike.Lib.X64.HelloPh.StartH0B.W0H (asm := asm) hpw TI E Spike.Lib.X64.WakeWf.DtW
        (CtxRdH (asm := asm) hpw i0 E rd ls) (ls0T ls) (FR))
      (Spike.Lib.X64ConsumerA.TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB) (MSB)
      (Spike.Lib.X64.HelloPh.StartH0B.StartPH hpw TI E) (fun _ _ _ => False) :=
by
  have hrd := Spike.Lib.X64.HelloPh.HrdRoot.hrd_RdH hpw i0 E rd (IB) ls hpa hhp hlo0 hc hA13 hm (ls0 := ls)
  refine Spike.Lib.X64.HelloPh.StartH0U1.hst0_ofHU1_i0 (asm := asm) hpw i0 E hE (inv0 := fun _ _ _ => False)
    (J1 := fun σC => mRdJ0 ((J') (TOP)) σC) (W1 := W1) (K := K) (ms1 := ms1)
    hpa hhp hlo0 hstat hA13 hctr2 hc hWe ?_ (fun _ _ c h => ⟨c, .refl _, h⟩) hq (h1_rdLand_xa hpw i0 h1)
    hhabctlRd
  intro v m0 σC
  -- the frame condition pins `v` at the first stack's top
  by_cases hv : v = TOP
  case neg => exact Spike.Lib.X64.HelloPh.HrdRoot.rdPreW_vac fun m hm => hv hm.1.1.2.1.1
  subst hv
  exact hrd (TOP) m0 σC

/-- **The start segment at `CtxRdU`** (`RootUL.hst0_UH` at `hst0_RdH`): `RootInv`'s `hst0` at `CR := CtxRdU`. -/
theorem hst0_RdU (hE : E.Ok (Ly).Λ) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.X64HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hWe : ∀ v s c, Spike.Lib.X64.At (Ly).exe (Ly).endPc (RS helloLsw v)
      (Spike.Lib.X64.WakePh.MainGlue.FS (Ly) (RS0) helloLsw 0#64 v)
      (Spike.Lib.X64.Flow.Hello1.mNC (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)) s c → WPRd s c [])
    (hq : ∀ σC σ c, mRdJ0 ((J') (TOP)) σC σ c → ∃ q : Spike.Lib.X64.Alloc.Call, q.OK (MSUB) (Ly).lab ∧
      q.c0 = c ∧ q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (MSUB) = 3#64)
    {I : InvS} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    (h1 : H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandH (asm := asm) hpw i0 E rd I ls (fun σC => mRdJ0 ((J') (TOP)) σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSB) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (MT) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    Spike.Lib.SegWS (Spike.Lib.X64.HelloPh.StartH0B.W0H (asm := asm) hpw TI E Spike.Lib.X64.WakeWf.DtW
        (CtxRdU (asm := asm) hpw i0 E rd ls) (ls0T ls) (FR))
      (Spike.Lib.X64ConsumerA.TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB) (MSB)
      (Spike.Lib.X64.HelloPh.StartH0B.StartPH hpw TI E) (fun _ _ _ => False) :=
  Spike.Lib.X64.HelloPh.RootUL.hst0_UH hpw i0 E rd (CtxRdH (asm := asm) hpw i0 E rd ls) ls (FR) inv1 inv2 hE hA13
    (hst0_RdH hpw i0 E rd ls hE hpa hhp hlo0 hstat hA13 hctr2 hc hm hWe hq h1 hhabctlRd)

end Spike.Lib.X64.HelloPh.CtxRdU

/-- info: 'Spike.Lib.X64.HelloPh.CtxRdU.h1StmtHF_mono_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CtxRdU.h1StmtHF_mono_rd

/-- info: 'Spike.Lib.X64.HelloPh.CtxRdU.h1_rdLand_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CtxRdU.h1_rdLand_xa

/-- info: 'Spike.Lib.X64.HelloPh.CtxRdU.hlandRdU_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CtxRdU.hlandRdU_root

/-- info: 'Spike.Lib.X64.HelloPh.CtxRdU.hW0_RdU'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CtxRdU.hW0_RdU'

/-- info: 'Spike.Lib.X64.HelloPh.CtxRdU.hst0_RdH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CtxRdU.hst0_RdH

/-- info: 'Spike.Lib.X64.HelloPh.CtxRdU.hst0_RdU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CtxRdU.hst0_RdU
