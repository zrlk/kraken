/-
**hello's level-0 start segment with rodata's landing handed to `h1`** (x86-64; the twin of
`Spike/Lib/A64HelloStartH0U1.lean`; the accounting for level 0's `Q1 := ⊥`): `StartH0U0.hst0_ofHU0_i0` at the
root's fragment `I := I3 arW L0T (ls0T ls) inv0 inv1 inv2`, its `hRdU` discharged by `StartH0H1.hRdU_of_h1F` from
`h1 : H1StmtHF … RdLandH … inv1 [FR]`.

**Why `Q1 := ⊥` loses nothing.** Level 0's segment has no normal exit: `hello_start_rd_h0G0`'s only exit is
`wc_rodata`'s heap abort (closed by `hello_rd_hab_closed`), so its post is `fun _ _ _ => False`. The run continues
past rodata's allocator call not through an exit but through the allocation side condition `hxa`: every landing
`Ea` at `wc_rodata`'s call, with `r1Of` unmapped, is in `ms [FR]`'s allocation fragment, i.e. (by `hRdU`) in `I` at
the extended placement. Here `hRdU` is not a free premise: it is `hRdU_of_h1F h1`, so the landing is `RdLandH`,
which `h1` (the root's level-1 statement, through `land_I3aHF`) puts in `inv1 … [FR]`. The only remaining level-0
premise about the landing is `h1` itself (level 1's statement).

- `hst0_ofHU1_i0`: the statement, at `HelloImms.immsH Λ0 i0`.

## Differences from the AArch64 version

- As `StartH0U0`'s: `scc_rt_main`'s region `MainGlue.RS helloLsw v`, `J'` depending on `v` (`hloc` only at the
  first stack's top), main's thread pointer
  `tpOf (tcbS Ly)`, `hhabctlRd` at `wc_rodata`'s region at the first stack's top, the loader's facts the two parses
  `cellsOf asm`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hst0_ofHU1` (`hst0_ofHU1_i0`
  at `i0 := helloImms`).
-/
import Spike.Lib.X64HelloStartH0U0
import Spike.Lib.X64HelloStartH0H1

namespace Spike.Lib.X64.HelloPh.StartH0U1

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
open Spike.Lib.X64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.Flow.Hello1 (mR mF mRdJ0 mNC)
open Spike.Lib.X64.Flow.HelloRd (RdPreW)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.HelloPh.StartH0U (msUH)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.X64.HelloPh.StartH0H1 (RdLandH hRdU_of_h1F)
open Spike.Lib (FragS SegWS LocalRun PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The root's fragment. -/
local notation "I" => I3 (AR) (LB) (ls0T ls) inv0 inv1 inv2

set_option hygiene false in
/-- The root's memory sides at the frames `fs`, the entry's marks. -/
local notation "MSF" => fun fs : List TermRun.Frame => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s) (AR) (I) (LB) (ls0T ls) fs

set_option hygiene false in
local notation "MSU" => msUH (asm := asm) hpw i0 E rd (I) ls

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "WP" => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
local notation "JW" => JS (Ly) 0#64 c0S

set_option hygiene false in
local notation "RM" v => RS helloLsw v

set_option hygiene false in
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RM v) (JW)

set_option hygiene false in
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
local notation "TOP" => topS (Ly) 0#64

/-- **hello's level-0 start segment, rodata's landing handed to `h1`** (module doc): `hst0_ofHU0_i0` at
`I := I3 …`, `hRdU := hRdU_of_h1F h1`. -/
theorem hst0_ofHU1_i0 (E : Entry) (hE : E.Ok (Ly).Λ)
    {Ctx : FragS isa} {ls0 : Lsize} {rd : TermRun.Word → Prop} {ls : Lsize}
    {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
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
    {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) (mNC (Ly).lab (RM v) (JW)) s c →
      WP s c [])
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.X64.WakeTP.tpG (TV) fun s c => WP s c [FR]) KR
      (Ly).exe (Ly).endPc (mR (RM v)) (mF (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC)
      ((MSU) [FR]) (mRdJ0 ((J') v) σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 ((J') (TOP)) σC σ c → ∃ c', LocalRun helloSrc c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSU) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSU) [FR]) = 3#64)
    /- level 1's statement: rodata's landing is in `inv1 … [FR]` -/
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandH (asm := asm) hpw i0 E rd (I) ls J1) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSF) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (mR (RM (TOP))) (AR) [FR] (J1 σC)) :
    SegWS (W0H (asm := asm) hpw IH E DtW Ctx (ls0T ls0) (FR)) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly)))
      helloSrc (LB) (MSF) (StartPH hpw IH E) (fun _ _ _ => False) :=
  Spike.Lib.X64.HelloPh.StartH0U0.hst0_ofHU0_i0 (asm := asm) hpw i0 E hE hpa hhp hlo0 hstat hA13 hctr2 hc hWe hrd
    hloc hq (hRdU_of_h1F hpw i0 E h1) hhabctlRd

end Spike.Lib.X64.HelloPh.StartH0U1

/-- info: 'Spike.Lib.X64.HelloPh.StartH0U1.hst0_ofHU1_i0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0U1.hst0_ofHU1_i0
