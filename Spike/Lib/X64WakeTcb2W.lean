/-
**wc_main's second `scc_rt_alloc_tcb` call inside the global owned-words
map** (x86-64; twin of `Spike/Lib/A64WakeTcb2W.lean`, its tools in
`Spike/Lib/X64WakeTcb2WLib.lean`): the node obligations `TcbWG` of
`scc_rt_alloc_tcb` at `tcb2Q g c0` for `SFactsSt2` at `ownG`
(`tcb2W_ownG`), from the instance's (`tcbW_postG` at `instOk2aP`,
`tcbPh2a`) moved along `ownG = own2a ∘ ph2a` where `ownG` picks `own2a`
(`Good2a`: the callee's pcs on a pool stack, its return to `.Lwc_main.x2`).

- `tcb_labs`, `wake_allocTcbIn`: the labels the pcs are decided from; the
  callee's code in `wakeCells`.
- `tcb2W_ownG`: the result.
- `tcb2_hdrA_ne`: the header's word is not `pinA + 8`.

**The call's writes** (for lifting `ownG` to `ownG ++ ownS`): the frame
slots of `R` at offsets `[-184, 8]` (the frame of 176 at `[-176, -24]`, the
saved `%rbp`, the return address), the counter's `lock xadd` at `L.pnA`
(node `rmw`), and the header's store at `hdrA L.lab (tcb2Q g c0) =
L.pinA + 128` (node `hdr`, `tcb2_hdrA_ne`).

**Unlike AArch64**: no `hal`; `hlo' : R.lo ≤ -184`, `hhi : 8 ≤ R.hi`
(A64's `-192`, `0`); the return is to `.Lwc_main.x2` (A64's
`.L21_wc_main.sp4`); 33 nodes (the length computation's flag-clobbering
instructions and the `leaq`s are nodes of their own, `keep_fi`,
`keep_lea`); the code's check has 35 conjuncts.
-/
import Spike.Lib.X64WakeTcb2WLib

namespace Spike.Lib.X64.WakePh.Tcb2W

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq code_field)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout tcbNG)
open Spike.Lib.X64 (ND BlkW NodeW At SO arun cellOff okBlk CodeAt)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TN StackM hdrBlk_eq rmwBlk_eq)
open Spike.Lib.X64.Flow.Ret0.AllocTcb
open Spike.Lib.X64.WakePh.Tcb2Call (tcb2Q)

variable {L : RuntimeLayout}

/-- The labels the call's pcs are decided from, at the canonical base. -/
theorem tcb_labs (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4198992 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4199011 ∧
    (_root_.Executable.labels L.exe).label lenL = Int64.ofNat 4199033 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4199247 ∧
    (_root_.Executable.labels L.exe).label ".Lwc_main.x2" = Int64.ofNat 4203410 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

theorem wake_allocTcbIn : allocTcbIn wakeCells = true := by decide +kernel

/-- `hso` of `blk2a` on a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -184 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block of the call at `l + off` (`ok` its `okBlk`, `bb` its code
check, `oo` its entry offsets), its end pc's `PcA` left. -/
local macro "tblk2 " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blk2a hlab hb hsite' h (code_field L.lays rfl $bb (by first | rfl | exact ofNat_zero' _))
      $ok hR (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT $blk $oo)
    · intro k hk; dsimp only [tcbNG]; rw [$el:term]; revert k; decide +kernel
    dsimp only [tcbNG] at hJ ⊢))

set_option hygiene false in
/-- `tblk2` for a block split by a return label (`m`, after its first `j`
rows; `blockAcrossB`). -/
local macro "tblk2A " bb:term:max j:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blk2a hlab hb hsite' h
      (Spike.Lib.X64.code_field_blockAcrossB L.lays rfl $bb (List.take_append_drop $j _) rfl)
      $ok hR (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT $blk $oo)
    · intro k hk; dsimp only [tcbNG]; rw [$el:term]; revert k; decide +kernel
    dsimp only [tcbNG] at hJ ⊢))

set_option hygiene false in
/-- A single-instruction node of the call (`z` bytes, `bb` its code check,
`kp` its `Keep` from the cell `hc` and the step `hs`). -/
local macro "tnode2 " z:term:max bb:term:max el:term:max kp:term : tactic =>
  `(tactic| (
    refine node2a (sz := $z) hlab hb h (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [tcbNG]; decide)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl $bb (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := $kp
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tcbNG, rmwPc, hdrPc]; rw [$el:term]; decide +kernel
    · dsimp only [tcbNG, rmwPc, hdrPc]; rw [$el:term]; decide +kernel))

/-- **`scc_rt_alloc_tcb`'s node obligations at `tcb2Q g c0` inside
`SFactsSt2` at `ownG`**: `tcbW_postG` at the second call's instance
(`instOk2aP`, `tcbPh2a`), each node moved to `ownG` where it picks `own2a`
(`blk2a`, `node2a`): the frame on a pool stack (`hb`), the return to
`.Lwc_main.x2` (`hra`), the counter's and the header's words mapped
(`hmP`, `hmH`) and off private memory (`hunP`, `hunH`). -/
theorem tcb2W_ownG (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    {rS : Range}
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 112#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    {Λ : Scc.Sem.Layout} {lbl : Spike.Lib.X64Consumer.Lbl} {c0 : Ctl}
    (hC0 : Spike.Lib.X64Consumer.CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo' : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hb : BandA L R) (g : G) (hra : g.ra = (L.lab ".Lwc_main.x2").toBitVec)
    {F : MachineData → Prop}
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true
      ⟨Spike.Lib.X64.Rt.hdrA L.lab (tcb2Q g c0), 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Rt.hdrA L.lab (tcb2Q g c0)) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    ∀ i, Spike.Lib.X64.Rt.TcbWG (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R (fun m => F m ∧ StackM rS m) (tcb2Q g c0) i := by
  obtain ⟨eFn, eEn, eLen, eOk, eX20, eSite⟩ := tcb_labs hlab (L := L)
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hT := Spike.Lib.X64.Rt.tcbW_postG (instOk2aP hp hlo a hsite (rS := rS)) (fun _ => rfl)
    (hp ▸ wake_allocTcbIn) hC0 hR hlo' hhi (tcb2Q g c0) rfl
    (ra := fun _ => L.lab ".Lwc_main.x2") hra (tcbPh2a hΛ hlab hsep hhdr)
    (hpn ▸ hmP) hmH (hpn ▸ hunP) hunH hsub hSM
  have hsite' : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → x = 4200277 := by
    intro x hx
    rw [hsite, show L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 from eSite] at hx
    cases hx; rfl
  have hin := hp ▸ wake_allocTcbIn
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bL0⟩, fShr1⟩, bL1⟩, fAnd1⟩, bL2⟩,
    fShr2⟩, bL3⟩, fAnd2⟩, bL4⟩, fImul1⟩, bL5⟩, fShl1⟩, bL6⟩, sLea1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, sOk⟩, bO1⟩,
    fImul2⟩, bO2⟩, fShl2⟩, bO3⟩, fShl3⟩, bO4⟩, fOr1⟩, bO5⟩, bHdr⟩, bRet⟩ := hin
  intro i
  have h := hT i
  cases i <;> dsimp only [Spike.Lib.X64.Rt.TcbWG] at h ⊢
  case e =>
    tblk2 bE atPro_ok atPro oE eFn
    rw [(atPro_walkG _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    tblk2 bEn atChk_ok atChk oI eEn
    rw [(atChk_walkG _ _ hJ.2).1, eEn]; decide +kernel
  case j1 =>
    tblk2 bJ1 atJ1_ok atJ1 oI eEn
    rw [(atJ1_walkG _ _ hJ.2).1]; show PcA (_root_.Executable.labels L.exe |>.label lenL); rw [eLen]; decide +kernel
  case len =>
    tblk2 bL0 atL0_ok atL0 oI eLen
    rw [(atL0_walkG _ _ hJ.2).1, eLen]; decide +kernel
  case l1 =>
    tblk2 bL1 atL1_ok atL1 oI eLen
    rw [(atL1_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l2 =>
    tblk2 bL2 atL2_ok atL2 oI eLen
    rw [(atL2_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l3 =>
    tblk2 bL3 atL3_ok atL3 oI eLen
    rw [(atL3_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l4 =>
    tblk2 bL4 atL4_ok atL4 oI eLen
    rw [(atL4_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l5 =>
    tblk2 bL5 atL5_ok atL5 oI eLen
    rw [(atL5_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l6 =>
    tblk2 bL6 atL6_ok atL6 oI eLen
    rw [(atL6_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case arg =>
    tblk2 bArg atArg_ok atArg oI eLen
    rw [(atArg_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case bnd =>
    tblk2 bBnd atBnd_ok atBnd oI eLen
    rw [(atBnd_walkG _ _ hJ.2.1 hJ.2.2
      (by show (112#64).toNat + (lenOf Spike.Lib.X64.WakePh.hdr2).toNat ≤ 131072; decide)).1, eLen]
    decide +kernel
  case j2 =>
    tblk2 bJ2 atJ2_ok atJ2 oI eLen
    rw [(atJ2_walkG _ _ hJ.2).1]; show PcA (_root_.Executable.labels L.exe |>.label okL); rw [eOk]; decide +kernel
  case o1 =>
    tblk2 bO1 atO1_ok atO1 oI eOk
    rw [(atO1_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o2 =>
    tblk2 bO2 atO2_ok atO2 oI eOk
    rw [(atO2_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o3 =>
    tblk2 bO3 atO3_ok atO3 oI eOk
    rw [(atO3_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o4 =>
    tblk2 bO4 atO4_ok atO4 oI eOk
    rw [(atO4_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o5 =>
    tblk2 bO5 atO5_ok atO5 oI eOk
    rw [(atO5_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case ret =>
    tblk2A bRet 11 atRet_ok atRet oI eOk
    rw [(atRet_walkG _ _ hJ.2).1]
    show PcA (Int64.ofBitVec g.ra)
    rw [hra, Int64.ofBitVec_toBitVec, show L.lab ".Lwc_main.x2" = Int64.ofNat 4203410 from eX20]
    decide +kernel
  case shr1 => tnode2 3 fShr1 eLen keep_fi hc rfl hs
  case and1 => tnode2 3 fAnd1 eLen keep_fi hc rfl hs
  case shr2 => tnode2 3 fShr2 eLen keep_fi hc rfl hs
  case and2 => tnode2 3 fAnd2 eLen keep_fi hc rfl hs
  case imul1 => tnode2 4 fImul1 eLen keep_fi hc rfl hs
  case shl1 => tnode2 3 fShl1 eLen keep_fi hc rfl hs
  case lea1 => tnode2 7 sLea1 eLen keep_lea hc hs
  case ok => tnode2 7 sOk eOk keep_lea hc hs
  case imul2 => tnode2 4 fImul2 eOk keep_fi hc rfl hs
  case shl2 => tnode2 3 fShl2 eOk keep_fi hc rfl hs
  case shl3 => tnode2 3 fShl3 eOk keep_fi hc rfl hs
  case or1 => tnode2 3 fOr1 eOk keep_fi hc rfl hs
  case rmw =>
    tnode2 5 bRmw eLen keep_rmw hc hd (a := L.pnA)
      (by
        dsimp only [tcbNG] at hJ
        refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
        rw [hA.regs]
        simp [Reg64s.get64, hJ.2.2.2, hpn])
      (hunP _ hF.1) hs
  case hdr =>
    tnode2 3 bHdr eOk keep_hdr hc hd (a := Spike.Lib.X64.Rt.hdrA L.lab (tcb2Q g c0))
      (by
        dsimp only [tcbNG] at hJ
        refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
        rw [hA.regs]
        simp [Reg64s.get64, hJ.2.2.2])
      (hunH _ hF.1) hs

/-- **The header's word is not `pinA + 8`** (the call's header store is
off `tcbM`). -/
theorem tcb2_hdrA_ne (g : G) (c0 : Ctl) :
    Spike.Lib.X64.Rt.hdrA L.lab (tcb2Q g c0) ≠ L.pinA + 8#64 := by
  rw [Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q_hdrA, L.lab_pin]
  intro h; bv_omega

end Spike.Lib.X64.WakePh.Tcb2W

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.tcb_labs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.tcb_labs

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.wake_allocTcbIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.wake_allocTcbIn

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.tcb2W_ownG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.tcb2W_ownG

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.tcb2_hdrA_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.tcb2_hdrA_ne
