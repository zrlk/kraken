/-
**wc_main's second `scc_rt_alloc_tcb` call at `ownGHXW`** (x86-64 only; the hello twin of
`Spike/Lib/X64WakeOwnTcb2X.lean`): `Tcb2CallW.tcb2Call_ownGH` (the call block at `.x23`) and
`Tcb2CallW.tcb2W_ownGKH` (the callee's nodes) moved from `SFactsSt2` at `ownGH` to `SFactsSt2` at `ownGHXW`
(`Lft2H`): every state is on a pool stack (main's frame `BandSp3H`, the callee's `BandAH`) at a pc from `.x1` on in
none of `InTH`, `InCH`, `InAbH` (`QPH`), so it holds `tcbM` only (`cls_poolH`); the call's two shared writes (the
counter `pnA`, the header `hdrA (tcb2QH g c0)`) miss `tcbM` (`PhRec.TcbSep`, `Tcb2W.tcb2H_hdrA_ne`).

- `bandOnP_sp3H`: main's `[-136, -128]` on the pool from `BandSp3H`.
- `tcb2LH`: the callee's nodes inside `Lft2H`.
- `tcb2CallLH`: the call block inside `Lft2H`.
- `tcb2W_ownGXH`, `tcb2Call_ownGXH`: the two producers at `ownGHXW`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there (its thread pointer is a register). Against x86-64 wake's
`OwnTcb2`: the code is helloCells (`hello_allocTcbIn`, `tcb_labsH`); the call block is at `.x23` (`4203726`, wake
`.x19`) in wc_main's frame addressed from `%rbp` (`oWH`, `%rsp` from `-128`; the callee's return pushed at `-136`,
wake `[-72, -64]`), its node `wcN3H` carrying the frame's words; the callee returns to `.x24` (`4203749`, wake
`.x20`); the header is `hdr2H` at `pinA + 80 + 24` (wake `+ 16`); the classes are `CstH`/`QPH`/`PPH` and `hW` is
about the worker's word `tcbWH L` (`pinA + 112`). The producers take the separation premises (`hsep`, `ha`, `hW`)
besides `Tcb2CallW`'s.
-/
import Spike.Lib.X64HelloOwnLft2X
import Spike.Lib.X64HelloOwnStartTi
import Spike.Lib.X64HelloTcb2CallW

namespace Spike.Lib.X64.HelloPh.OwnTcb2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (code_field)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout tcbNG)
open Spike.Lib.X64Consumer (Lbl CFacts)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW AS)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TN StackM hdrBlk_eq rmwBlk_eq)
open Spike.Lib.X64.Flow.Ret0.AllocTcb
open Spike.Lib.X64.WakePh (tcbM Keep keep_pc hw_fi hw_lea hw_rmwM BandOnP)
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_fi keep_lea keep_rmw keep_hdr)
open Spike.Lib.X64.HelloPh.Tcb2W (BandAH tcb_labsH)
open Spike.Lib.X64.Flow.HelloWc (hello_allocTcbIn tcb2QH tcb2CallH tcb2CallH_ok tcb2CallH_pc wcN3H x23L)
open Spike.Lib.X64.HelloPh.WcSp6 (oWH)
open Spike.Lib.X64.HelloPh.Tcb2CallW (BandSp3H lab_sp3H)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib (Region)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -184 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block of the call (`bb` its code check, `ok` its `okBlk`, `oo` its
entry offsets, `el` its label's value), `QP` at its end left. -/
local macro "tblkX " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soT $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [tcbNG]; rw [$el:term]; revert k; decide +kernel
    dsimp only [tcbNG] at hJ ⊢))

set_option hygiene false in
/-- A single-instruction node of the call (`z` bytes, `bb` its code check,
`el` its label's value, `hw` its write condition, `kp` its `Keep` from the
cell `hc` and the step `hs`). -/
local macro "tnodeX " z:term:max bb:term:max el:term:max hwx:term:max kp:term : tactic =>
  `(tactic| (
    refine nodeL2H hsep ha hW (sz := $z) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [tcbNG]; decide) ($hwx fun s c hAt => by
        obtain ⟨he, hn, -, hp', -⟩ := hAt
        exact (code_field L.lays rfl $bb (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp')
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl $bb (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := $kp
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tcbNG, rmwPc, hdrPc]; rw [$el:term]; decide +kernel
    · dsimp only [tcbNG, rmwPc, hdrPc]; rw [$el:term]; decide +kernel))

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop}

/-- **Main's frame at `.x23` on the pool**: its `[-136, -128]` from
`BandSp3`. -/
theorem bandOnP_sp3H {R : Region} (hb : BandSp3H L R) : BandOnP L R (-136) (-128) := fun k h1 h2 => by
  have := hb (k + 136) (by omega) (by omega)
  rwa [Region.callee_addr, show -136 + (k + 136) = k by omega] at this

section L

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

set_option maxHeartbeats 3200000 in
/-- **The second `scc_rt_alloc_tcb` call's nodes inside `Lft2`**: every
state on a pool stack (`hb`) at a `QP` pc holds `tcbM` only; the counter's
and the header's stores miss it. -/
theorem tcb2LH {R : Region} (hb : BandAH L R) (hR : R.OK) (hlo' : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (g : G) (c0 : Ctl) (hra : g.ra = (L.lab ".Lwc_main.x24").toBitVec) {F : MachineData → Prop}
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0)) 8 = none) :
    ∀ i, Spike.Lib.X64.Rt.TcbWG (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (tcb2QH g c0) i := by
  obtain ⟨eFn, eEn, eLen, eOk, eX20, -⟩ := tcb_labsH hlab (L := L)
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hPM : L.pnA ≠ tcbM L := fun h => hsep 1 (by decide)
    (by rw [show L.pinA + BitVec.ofNat 64 (8 * 1) = tcbM L from rfl, ← h]; simp)
  have hin := hp ▸ hello_allocTcbIn
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bL0⟩, fShr1⟩, bL1⟩, fAnd1⟩, bL2⟩,
    fShr2⟩, bL3⟩, fAnd2⟩, bL4⟩, fImul1⟩, bL5⟩, fShl1⟩, bL6⟩, sLea1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, sOk⟩, bO1⟩,
    fImul2⟩, bO2⟩, fShl2⟩, bO3⟩, fShl3⟩, bO4⟩, fOr1⟩, bO5⟩, bHdr⟩, bRet⟩ := hin
  have hin0 := hello_allocTcbIn
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin0
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, cE⟩, cEn⟩, cJ1⟩, cL0⟩, -⟩, cL1⟩, -⟩, cL2⟩,
    -⟩, cL3⟩, -⟩, cL4⟩, -⟩, cL5⟩, -⟩, cL6⟩, -⟩, cArg⟩, -⟩, cBnd⟩, cJ2⟩, -⟩, cO1⟩,
    -⟩, cO2⟩, -⟩, cO3⟩, -⟩, cO4⟩, -⟩, cO5⟩, -⟩, cRet⟩ := hin0
  intro i
  cases i <;> dsimp only [Spike.Lib.X64.Rt.TcbWG]
  case e =>
    tblkX cE atPro_ok atPro oE eFn
    rw [(atPro_walkG _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    tblkX cEn atChk_ok atChk oI eEn
    rw [(atChk_walkG _ _ hJ.2).1, eEn]; decide +kernel
  case j1 =>
    tblkX cJ1 atJ1_ok atJ1 oI eEn
    rw [(atJ1_walkG _ _ hJ.2).1]; show QPH ((_root_.Executable.labels L.exe |>.label lenL).toBitVec.toNat)
    rw [eLen]; decide +kernel
  case len =>
    tblkX cL0 atL0_ok atL0 oI eLen
    rw [(atL0_walkG _ _ hJ.2).1, eLen]; decide +kernel
  case l1 =>
    tblkX cL1 atL1_ok atL1 oI eLen
    rw [(atL1_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l2 =>
    tblkX cL2 atL2_ok atL2 oI eLen
    rw [(atL2_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l3 =>
    tblkX cL3 atL3_ok atL3 oI eLen
    rw [(atL3_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l4 =>
    tblkX cL4 atL4_ok atL4 oI eLen
    rw [(atL4_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l5 =>
    tblkX cL5 atL5_ok atL5 oI eLen
    rw [(atL5_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l6 =>
    tblkX cL6 atL6_ok atL6 oI eLen
    rw [(atL6_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case arg =>
    tblkX cArg atArg_ok atArg oI eLen
    rw [(atArg_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case bnd =>
    tblkX cBnd atBnd_ok atBnd oI eLen
    rw [(atBnd_walkG _ _ hJ.2.1 hJ.2.2
      (by show (80#64).toNat + (lenOf Spike.Lib.X64.HelloPh.hdr2H).toNat ≤ 131072; decide)).1, eLen]
    decide +kernel
  case j2 =>
    tblkX cJ2 atJ2_ok atJ2 oI eLen
    rw [(atJ2_walkG _ _ hJ.2).1]; show QPH ((_root_.Executable.labels L.exe |>.label okL).toBitVec.toNat)
    rw [eOk]; decide +kernel
  case o1 =>
    tblkX cO1 atO1_ok atO1 oI eOk
    rw [(atO1_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o2 =>
    tblkX cO2 atO2_ok atO2 oI eOk
    rw [(atO2_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o3 =>
    tblkX cO3 atO3_ok atO3 oI eOk
    rw [(atO3_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o4 =>
    tblkX cO4 atO4_ok atO4 oI eOk
    rw [(atO4_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o5 =>
    tblkX cO5 atO5_ok atO5 oI eOk
    rw [(atO5_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case ret =>
    tblkX cRet atRet_ok atRet oI eOk
    rw [(atRet_walkG _ _ hJ.2).1]
    show QPH (Int64.ofBitVec g.ra).toBitVec.toNat
    rw [hra, Int64.ofBitVec_toBitVec, show L.lab ".Lwc_main.x24" = Int64.ofNat 4203749 from eX20]
    decide +kernel
  case shr1 => tnodeX 3 fShr1 eLen hw_fi keep_fi hc rfl hs
  case and1 => tnodeX 3 fAnd1 eLen hw_fi keep_fi hc rfl hs
  case shr2 => tnodeX 3 fShr2 eLen hw_fi keep_fi hc rfl hs
  case and2 => tnodeX 3 fAnd2 eLen hw_fi keep_fi hc rfl hs
  case imul1 => tnodeX 4 fImul1 eLen hw_fi keep_fi hc rfl hs
  case shl1 => tnodeX 3 fShl1 eLen hw_fi keep_fi hc rfl hs
  case lea1 => tnodeX 7 sLea1 eLen hw_lea keep_lea hc hs
  case ok => tnodeX 7 sOk eOk hw_lea keep_lea hc hs
  case imul2 => tnodeX 4 fImul2 eOk hw_fi keep_fi hc rfl hs
  case shl2 => tnodeX 3 fShl2 eOk hw_fi keep_fi hc rfl hs
  case shl3 => tnodeX 3 fShl3 eOk hw_fi keep_fi hc rfl hs
  case or1 => tnodeX 3 fOr1 eOk hw_fi keep_fi hc rfl hs
  case rmw =>
    have hE : ∀ s c, Spike.Lib.X64.At L.exe L.endPc R F
        (tcbNG (_root_.Executable.labels L.exe).label (tcb2QH g c0) .rmw) s c →
        Kraken.Promising.Lower.X64.CellAt s (Spike.Lib.X64.xaddDir .rcx 0 .rax) 5 ∧
        Kraken.Promising.Lower.X64.eaddr s 5 (Spike.Lib.X64.mB .rcx 0) = L.pnA ∧
        Mem.loadInt s.st.1.dmem L.pnA 8 = none ∧ s.decls = {} := fun s c hAt => by
      obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      refine ⟨(code_field L.lays rfl bRmw (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp', ?_,
        hunP _ hF, hd⟩
      dsimp only [tcbNG] at hJ
      refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
      rw [hA.regs]
      simp [Reg64s.get64, hJ.2.2.2, hpn]
    refine nodeL2H hsep ha hW (sz := 5) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [tcbNG]; decide) (hw_rmwM hE hPM)
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_rmw hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [tcbNG, rmwPc]; rw [eLen]; decide +kernel
    · dsimp only [tcbNG, rmwPc]; rw [eLen]; decide +kernel
  case hdr =>
    have hE : ∀ s c, Spike.Lib.X64.At L.exe L.endPc R F
        (tcbNG (_root_.Executable.labels L.exe).label (tcb2QH g c0) .hdr) s c →
        Kraken.Promising.Lower.X64.CellAt s (Spike.Lib.X64.stDir .rcx 0 .rax) 3 ∧
        Kraken.Promising.Lower.X64.eaddr s 3 (Spike.Lib.X64.mB .rcx 0) =
          Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0) ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0)) 8 = none ∧ s.decls = {} :=
      fun s c hAt => by
        obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
        refine ⟨(code_field L.lays rfl bHdr (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp', ?_,
          hunH _ hF, hd⟩
        dsimp only [tcbNG] at hJ
        refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
        rw [hA.regs]
        simp [Reg64s.get64, hJ.2.2.2]
    refine nodeL2H hsep ha hW (sz := 3) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [tcbNG]; decide) (OwnSt.hw_stMH hE (Tcb2W.tcb2H_hdrA_ne g c0))
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_hdr hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [tcbNG, hdrPc]; rw [eOk]; decide +kernel
    · dsimp only [tcbNG, hdrPc]; rw [eOk]; decide +kernel

/-- **The call block at `.x23` inside `Lft2H`**: main's frame `[-136, -128]`
on the pool (`hb`), its pcs and the callee's entry `QP`. -/
theorem tcb2CallLH {R : Region} (hR : R.OK) (hlo3 : R.lo ≤ -136) (hhi : 16 ≤ R.hi) (hb : BandSp3H L R)
    {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {F : MachineData → Prop} :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (wcN3H L.lab c0 sl me cA fr) tcb2CallH := by
  obtain ⟨eFn, -, -, -, -, -⟩ := tcb_labsH hlab (L := L)
  have hin : Scc.Cert.Rt.X64.blockAtB helloCells x23L 0 tcb2CallH = true := by decide +kernel
  have hbp := bandOnP_sp3H hb
  refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) hin (ofNat_zero' _) tcb2CallH_ok hR hlo3 hhi
    (fun _ h => h.2) (fun s h => cls_poolH hlab hbp s h.1) (cls_poolH hlab hbp) ?_
    (fun k hk => (show ∀ k ≤ tcb2CallH.length, -136 ≤ (soRun (tcb2CallH.take k) oWH).sp ∧
      (soRun (tcb2CallH.take k) oWH).sp ≤ -128 by decide +kernel) k hk) (fun σ c hJ => ?_)
  · intro k hk
    show PPH ((_root_.Executable.labels L.exe).label ".Lwc_main.x23" + _).toBitVec.toNat
    rw [lab_sp3H hlab]; revert k; decide +kernel
  · rw [show (wcN3H L.lab c0 sl me cA fr).pc = (_root_.Executable.labels L.exe).label ".Lwc_main.x23" from rfl,
      show (wcN3H L.lab c0 sl me cA fr).o = oWH from rfl,
      (tcb2CallH_pc (_root_.Executable.labels L.exe).label _ σ).1]
    show QPH ((_root_.Executable.labels L.exe).label fnL).toBitVec.toNat
    rw [eFn]; decide +kernel

/-! ## The producers at `ownGXW` -/

/-- **`tcb2W_ownGK` at `ownGXW`.** -/
theorem tcb2W_ownGXH (hlo : L.Λ.code.lo = lo) {rS : Range} (rS' : Range)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hsepP : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo' : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hb : BandAH L R) (g : G) (hra : g.ra = (L.lab ".Lwc_main.x24").toBitVec)
    {F : MachineData → Prop}
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true
      ⟨Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0), 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0)) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    ∀ i, Spike.Lib.X64.Rt.TcbWG (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s)
      (Spike.Lib.X64.PhRec.K L rS') L.exe L.endPc R (fun m => F m ∧ StackM rS m) (tcb2QH g c0) i := by
  exact fun i => Spike.Lib.X64.WakePh.TcbWG.imp
    (Tcb2CallW.tcb2W_ownGKH hp hlo a rS' hsite hΛ hlab hsepP hhdr hC0 hR hlo' hhi hb g hra hmP hmH hunP hunH
      hsub hSM i)
    (tcb2LH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hlo' hhi g c0 hra
      (fun m hm => hunP m hm.1) (fun m hm => hunH m hm.1) i)
    fun _ _ h1 h2 => h2 h1

/-- **`tcb2Call_ownG` at `ownGXW`.** -/
theorem tcb2Call_ownGXH (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    {R : Region} (hR : R.OK) (hlo3 : R.lo ≤ -136) (hhi : 16 ≤ R.hi)
    (hb : BandSp3H L R) {F : MachineData → Prop} {rS : Range} (rS' : Range)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS')
      L.exe L.endPc R (fun m => F m ∧ StackM rS m) (wcN3H L.lab c0 sl me cA fr) tcb2CallH :=
  Spike.Lib.X64.AllocG.BlkW.imp (Tcb2CallW.tcb2Call_ownGH hp hlo a hsite hΛ hlab hC0 hR hlo3 hhi hb rS' hsub hSM)
    (tcb2CallLH (Dt := fun _ => False) hp hlab hsite hsep ha hW hR hlo3 hhi hb) fun _ _ h1 h2 => h2 h1

end L

end Spike.Lib.X64.HelloPh.OwnTcb2

/-- info: 'Spike.Lib.X64.HelloPh.OwnTcb2.bandOnP_sp3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTcb2.bandOnP_sp3H

/-- info: 'Spike.Lib.X64.HelloPh.OwnTcb2.tcb2LH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTcb2.tcb2LH

/-- info: 'Spike.Lib.X64.HelloPh.OwnTcb2.tcb2CallLH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTcb2.tcb2CallLH

/-- info: 'Spike.Lib.X64.HelloPh.OwnTcb2.tcb2W_ownGXH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTcb2.tcb2W_ownGXH

/-- info: 'Spike.Lib.X64.HelloPh.OwnTcb2.tcb2Call_ownGXH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTcb2.tcb2Call_ownGXH
