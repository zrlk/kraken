/-
**hello's start segment at `ownGHXW`, level 0, and `RootH0.hstHg`'s `hst0` there** (x86-64; the counterpart of
AArch64's `A64HelloStartH0U0` and `A64HelloStartH0U1`, at `ownGHXW`): the start segment
`StartH0G0X.hello_start_rd_h0G0X` (the level `WSHFg (ownGHXW Ly ntA)`) at the root's memory sides with the child's
stack unmapped (`StartH0U.msUHg OX`, `OX := ownGHXW Ly ntA`), `KeepUnS.SegWS.mono_xa`/`keepUn` carrying it back to
the root's `ms`, its one exit (`wc_rodata`'s heap abort) closed by `RdHAbX.hello_rd_hab_closedX`, ending in
`StartH0B.W0Hg OX` (the entry's marks by `AbOffW.marks_target`); `hxa` from `HxaX.hxa_ofRdU` at `OX`.

Left as premises: the loader's facts (`hpa`, `hhp`, `hlo0`, `hstat`, `hA13`, `hctr2`, `hc`), the source and frame
premises `hWe`, `hrd`, `hloc`, `hq` at `msUHg OX`, `hhabctlRd`, and `hRdU` (in `hst0_X`: level 1's statement `h1`
at `RdLandHg OX`, through `StartH0H1.hRdU_of_h1Fg`).

- `hst0_ofHU0X_i0`: the start segment at `OX` (AArch64 `StartH0U0.hst0_ofHU0_i0`; `hRdU` may assume main's
  thread pointer at the landing), at `HelloImms.immsH Λ0 i0`.
- `hst0_X`: `RootH0.hstHg`'s `hst0` at `OX` (`I3 … ⊥ inv1 inv2`, the memory side `RootH0.msBotHg … OX`), from
  `h1`.

## Differences from the AArch64 version

AArch64's root owns `ownGH` (`A64HelloStartH0U0`, `A64HelloStartH0U1`); x86-64's main also holds its own and the
worker's TCB words, so the memory sides own `ownGHXW` and the level is `W0Hg (ownGHXW …)`. The start segment is
`hello_start_rd_h0G0X` (no thread-init premise, by `OwnSt.tiXPH`), the abort closure `hello_rd_hab_closedX` (the
abort path lifted by `HabLftX`), which asks `hA13`; `hst0_X` takes `I3`'s `inv0` disjunct `⊥` as `RootH0.hstHg`
asks.

- `scc_rt_main`'s region at the new stack's base `v` is `MainGlue.RS helloLsw v` (AArch64 `swR v (-helloLsw) 0`);
  `wc_rodata`'s caller's entry invariant `rdJH` takes it, so `J'` depends on `v` (`hrd`, `hRdU` at `J' v`; `hloc`
  only at the first stack's top `J' TOP`, the only base the start reaches), `rN` takes `wc_rodata`'s region and
  the kept cells reach `8` (AArch64 `0`).
- The thread pointer is `%fs`'s base `tpOf (tcbS Ly)` (AArch64 `TPIDR_EL0` at `pinA + 8`), and `hrd` is asked
  inside `WakeTP.tpG` (AArch64 `WakeWc.tpG`).
- `hhabctlRd` takes `wc_rodata`'s region at the first stack's top (`HabCtlRdH`'s).
- The stacks' bound is `X64WakeHClC.hbd_W`; the entry's `U r1Of` is `WakePh.StartH0X.entry_U` (AArch64
  `wideSt_threadAt` and `WakeOHinit.unowned_stack` inline, through `hsub1_W`); `SegWS`'s `mono_K`/`mono_W` are
  `WakePh.Land5.segWS_mono_K`/`segWS_mono_W`; `hxa`'s arena bounds are `HxaX.hxa_ofRdU`'s (AArch64 inline).
- The loader's facts are the two parses `cellsOf asm` (AArch64 `textProgram`).
- `StartH0G0X.hello_start_rd_h0G0X` also asks `me` in the immediate table; at `immsH Λ0 i0` that is
  `HelloImms.immsH_start`, so it is not a premise here.
-/
import Spike.Lib.X64HelloStartH0U
import Spike.Lib.X64HelloStartH0G0X
import Spike.Lib.X64HelloHxaX
import Spike.Lib.X64HelloStartH0B
import Spike.Lib.X64HelloRootH0
import Spike.Lib.X64HelloStartWcS
import Spike.Lib.X64HelloMainPreTF
import Spike.Lib.X64HelloStartWfP
import Spike.Lib.X64HelloMainWf
import Spike.Lib.X64WakeMainGlue
import Spike.Lib.X64WordsNone
import Spike.Lib.X64HelloFrameD
import Spike.Lib.X64HelloRdHAbCX
import Spike.Lib.X64HelloStartH0H1
import Spike.Lib.X64KeepUnS
import Spike.Lib.X64KeepUn
import Spike.Lib.X64WakeStartH0X
import Spike.Lib.X64WakeHClC
import Spike.Lib.X64WakeTP
import Spike.Lib.X64WakeLand5
import Spike.Lib.X64WakeAbOffW

namespace Spike.Lib.X64.HelloPh.StartH0X

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

set_option maxHeartbeats 1600000 in
/-- **hello's start segment at `immsH Λ0 i0` at `ownGHXW`, the child's stack unmapped, level 0** (module doc):
the start segment `StartH0G0X.hello_start_rd_h0G0X` at `msUHg OX` (its only exit `wc_rodata`'s heap abort),
`keepUn` carrying `r1Of` unmapped, the exit transported to `ms` and closed by `hello_rd_hab_closedX`; `hxa` at
`msUHg OX` from `hRdU` (`HxaX.hxa_ofRdU`). -/
theorem hst0_ofHU0X_i0 (E : Entry) (hE : E.Ok (Ly).Λ)
    {Ctx : FragS isa} {ls0 : Lsize}
    {rd : TermRun.Word → Prop} {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize}
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
    /- a landing the arena hands out, the child's stack unmapped, under main's thread pointer, is in `I` at the
    fresh label (`StartH0H1.hRdU_of_h1Fg`) -/
    (hRdU : ∀ v m0 σC, ∀ q : AG ((MSU) [FR]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR (RM v)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mR (RM v)) (mRdJ0 ((J') v) σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.X64.Alloc.N (Ly).lab ((MSU) [FR]) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR (RM v)) (-48) (-160) 8 mC m) →
      ∀ l b w s c, (LB) l = none →
        At (Ly).exe (Ly).endPc (aR (mR (RM v))) F' (Ea ((MSU) [FR]) q.1 l b w) s c →
        AllocLand (AR).heap (AR).cells b w → U (R1) s → TP (TV) s →
        I (fun l' => if l' = l then some b else (LB) l') (fun l' => if l' = l then w else ls0T ls l') s c [FR])
    /- the controls' facts at `rX .abort` -/
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSF) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (mR (RM (TOP))) (AR) [FR] (J1 σC)) :
    SegWS (W0Hg (asm := asm) hpw IH (OX) E DtW Ctx (ls0T ls0) (FR)) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly)))
      helloSrc (LB) (MSF) (StartPH hpw IH E) (fun _ _ _ => False) := by
  -- the ranges: `r1Of` disjoint from `rS0`, both in the address space
  have hbd' : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 :=
    Spike.Lib.X64WakeHClC.hbd_W hpw IH
  obtain ⟨h1l, h1s⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS0).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS0).size = 16384 := rfl
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS0).lo + (RS0).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS0) := by unfold Scc.Sem.Range.Disjoint; omega
  -- `hxa` at `msUH`: the landing is one the arena hands out (`HxaX.hxa_ofRdU`), the rest `hRdU` given `U r1Of`
  have hG0' := Spike.Lib.X64.HelloPh.StartH0G0X.hello_start_rd_h0G0X (Dt := DtW) (Ctx := Ctx) (lsize := ls0T ls0)
    (frM := FR) (lblS := LB) (rd := rd) (I := invUH hpw i0 I) (ls := ls) hpw IH hE hpa hhp hlo0 hstat hA13 hctr2 hc
    (Spike.Lib.X64.HelloImms.immsH_start Λ0 i0) hWe hrd hloc hq
    (Spike.Lib.X64.HelloPh.HxaX.hxa_ofRdU hpw i0 (OX) E (fs := [FR]) hRdU)
  -- the start segment at `unXa (ms fs) r1Of`, then `keepUn`
  have hG1 := Spike.Lib.X64.KeepUnS.SegWS.mono_xa (ms' := fun fs => unXa ((MSF) fs) (R1)) hG0' (fun _ => rfl)
    fun _ _ _ _ _ _ h hU => ⟨h.1, h.2 hU⟩
  have hG := Spike.Lib.X64.KeepUnS.SegWS.keepUn (fun _ => rfl) hG1 fun _ _ _ _ s' hk hs => by
    obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.X64.KeepUn.take_un pm hd hw1 hwS hs
  -- the exits at `ms`, closed; the take as `TakeCKS`; `WS` as `W0Hg`; the start pair as `hG`'s entry
  have hprog : (Ly).prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hpL : Scc.Sem.X64.cellsOf asm = some (Ly).prog := by rw [hprog]; exact hhp
  have hC := Spike.Lib.X64.HelloPh.RdHAbX.hello_rd_hab_closedX hpw IH (Ctx := Ctx) (ls0 := ls0) (J1 := J1) hpa hhp
    hlo0 hA13 hhabctlRd
  refine (Spike.Lib.X64.WakePh.Land5.segWS_mono_W (Spike.Lib.X64.WakePh.Land5.segWS_mono_K
      ((hG.mono_post fun s c fs hQ => ?_).seq hC)
      fun s c fs hW s' => Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1)
    (W' := W0Hg (asm := asm) hpw IH (OX) E DtW Ctx (ls0T ls0) (FR)) fun s c fs h => ?_).mono_pre
    fun s c fs ⟨hs, hc, hfs⟩ => ?_
  · obtain ⟨⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hsl, q, hq, hJ⟩, -⟩, hfs⟩, -⟩ := hQ
    exact ⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hsl, ⟨q.1, { q.2 with }⟩, hq, hJ⟩⟩, hfs⟩
  · show Spike.Lib.X64.WakeWf.W0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ s c fs
    rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]; exact h
  · subst hs hc hfs
    exact ⟨⟨Spike.Lib.X64.HelloPh.StartH0B.entry_atH hpw IH E hE, rfl⟩,
      Spike.Lib.X64.WakePh.StartH0X.entry_U (hpw := hpw) (i := IH) hE.1 hA13 _ _⟩


set_option hygiene false in
/-- The root's fragment with `I3`'s `inv0` disjunct `⊥` (`RootH0.msBotHg`'s). -/
local notation "IB" => I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2

set_option hygiene false in
/-- The root's memory sides at `invUH IB`, owning `OX`. -/
local notation "MSUB" => msUHg (asm := asm) hpw i0 (OX) E rd (IB) ls

set_option maxHeartbeats 1600000 in
/-- **`RootH0.hstHg`'s `hst0` at `OX`**: `hst0_ofHU0X_i0` at `I := I3 … ⊥ inv1 inv2` (the memory side
`RootH0.msBotHg … OX`), `hRdU := StartH0H1.hRdU_of_h1Fg h1` (rodata's landing handed to level 1's statement at
`OX`). -/
theorem hst0_X (E : Entry) (hE : E.Ok (Ly).Λ)
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
    {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) (mNC (Ly).lab (RM v) (JW)) s c →
      WP s c [])
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.X64.WakeTP.tpG (TV) fun s c => WP s c [FR]) KR
      (Ly).exe (Ly).endPc (mR (RM v)) (mF (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC)
      ((MSUB) [FR]) (mRdJ0 ((J') v) σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 ((J') (TOP)) σC σ c → ∃ c', LocalRun helloSrc c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSUB) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSUB) [FR]) = 3#64)
    /- level 1's statement: rodata's landing at `OX` is in `inv1 … [FR]` -/
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandHg (asm := asm) hpw i0 (OX) E rd (IB) ls J1) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH
      (msBotHg (asm := asm) hpw IH E rd ls inv1 inv2 (OX) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (mR (RM (TOP))) (AR) [FR] (J1 σC)) :
    SegWS (W0Hg (asm := asm) hpw IH (OX) E DtW Ctx (ls0T ls0) (FR))
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB)
      (msBotHg (asm := asm) hpw IH E rd ls inv1 inv2 (OX)) (StartPH hpw IH E) (fun _ _ _ => False) :=
  hst0_ofHU0X_i0 (asm := asm) (I := IB) hpw i0 E hE hpa hhp hlo0 hstat hA13 hctr2 hc hWe hrd hloc hq
    (hRdU_of_h1Fg hpw i0 E h1) hhabctlRd

end Spike.Lib.X64.HelloPh.StartH0X


/-- info: 'Spike.Lib.X64.HelloPh.StartH0X.hst0_ofHU0X_i0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0X.hst0_ofHU0X_i0

/-- info: 'Spike.Lib.X64.HelloPh.StartH0X.hst0_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0X.hst0_X
