/-
**The first `scc_rt_alloc_tcb` call lifted to `ownGXW`** (x86-64; X64-OwnW
lift layer): the call from `scc_rt_start` (returning to `.x0`,
its frame `[-184, 8]` off the pool, `StartTcb.BandT`). No state of the call
owns either TCB word (its pcs off every range, `NoH`; `Cst L [] []` by
`cls_off`), so `StartTcb.startTcb_WS`'s obligations inside `StartWf.WS` are
inside `WSX` (`ownGXW`). The nodes mirror `StartTcb.startTcb_WS`.

- `tcbL`: the call's nodes inside `Lft`.
- `tcbX`: `TcbW` inside `WS` is inside `WSX` (`TcbW.imp`); `startTcbX`:
  `startTcb_WS` inside `WSX`, the shape of `startEX`'s `htcbX`.

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnStartTk
import Spike.Lib.X64WakeStartTcbW

namespace Spike.Lib.X64.WakePh.OwnSt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (code_field)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64 (ND bAddr)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.WakePh.StartTcb (BandT)
open Spike.Lib.X64.WakePh.Tcb2W (soRun tcb_labs wake_allocTcbIn keep_fi keep_lea keep_rmw keep_hdr)
open Spike.Lib.X64.Flow.Ret0 (TN TcbG TcbW tcbN pinA pnA hdrBlk_eq rmwBlk_eq)
open Spike.Lib.X64.Flow.Ret0.AllocTcb
open Spike.Lib (Arena FragS)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -184 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block of the call inside `Lft` (`bb` its code check, `ok` its
`okBlk`, `blk` the block, `oo` its entry offsets, `el` its label's value),
its end pc's `NoH` left. -/
local macro "tblkL " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_
      (soT $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [tcbN]; rw [$el:term]; revert k; decide +kernel
    dsimp only [tcbN] at hJ ⊢))

set_option hygiene false in
/-- `tblkL` on a block split by a return label (`blkLA`). -/
local macro "tblkLA " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkLA hp hlab hsite hsep ha hW (P := PT) (Q := NoH) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_
      (soT $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [tcbN]; rw [$el:term]; revert k; decide +kernel
    dsimp only [tcbN] at hJ ⊢))

set_option hygiene false in
/-- A single-instruction node of the call inside `Lft` (`z` bytes, `bb` its
code check, `el` its label's value, `kp` its `Keep` from the cell `hc` and
the step `hs`). -/
local macro "tnodeL " z:term:max bb:term:max el:term:max kp:term : tactic =>
  `(tactic| (
    refine nodeL0 hlab hsep ha hW (sz := $z) (cls_off hlab hbd) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [tcbN]; decide)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $bb) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := $kp
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tcbN, rmwPc, hdrPc]; rw [$el:term]; decide +kernel
    · dsimp only [tcbN, rmwPc, hdrPc]; rw [$el:term]; decide +kernel))

variable {L : RuntimeLayout} {a : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

set_option maxHeartbeats 3200000 in
/-- **The first `scc_rt_alloc_tcb` call's nodes inside `Lft`**: every state
owns neither TCB word (its pcs off every range, its frame `[-184, 8]` off the
pool, `hbd`). -/
theorem tcbL (hp : L.prog = wakeCells)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hbd : BandT L R) (hR : R.OK) (hRlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TcbG) (hn0 : q.n0 = 0#64)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec) :
    ∀ i, TcbW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F q i := by
  have hpn : pnA L.lab = L.pnA := L.lab_pn
  have hpin : pinA L.lab = L.pinA := L.lab_pin
  have h0 : ∃ j < 7, L.pinA = L.pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hH : pinA L.lab + q.n0 = L.pinA := by rw [hn0, hpin, BitVec.add_zero]
  have eX0 : (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.x0L = Int64.ofNat 4198487 :=
    hlab _ _ (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)
  obtain ⟨eFn, eEn, eLen, eOk, -, -⟩ := tcb_labs hlab (L := L)
  have hin := wake_allocTcbIn
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bL0⟩, fShr1⟩, bL1⟩, fAnd1⟩, bL2⟩,
    fShr2⟩, bL3⟩, fAnd2⟩, bL4⟩, fImul1⟩, bL5⟩, fShl1⟩, bL6⟩, sLea1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, sOk⟩, bO1⟩,
    fImul2⟩, bO2⟩, fShl2⟩, bO3⟩, fShl3⟩, bO4⟩, fOr1⟩, bO5⟩, bHdr⟩, bRet⟩ := hin
  intro i
  cases i <;> dsimp only [TcbW]
  case e =>
    tblkL bE atPro_ok atPro oE eFn
    rw [(atPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    tblkL bEn atChk_ok atChk oI eEn
    rw [(atChk_walk _ _ hJ.2).1, eEn]; decide +kernel
  case j1 =>
    tblkL bJ1 atJ1_ok atJ1 oI eEn
    rw [(atJ1_walk _ _ hJ.2).1]; show NoH ((_root_.Executable.labels L.exe |>.label lenL).toBitVec.toNat)
    rw [eLen]; decide +kernel
  case len =>
    tblkL bL0 atL0_ok atL0 oI eLen
    rw [(atL0_walk _ _ hJ.2).1, eLen]; decide +kernel
  case l1 =>
    tblkL bL1 atL1_ok atL1 oI eLen
    rw [(atL1_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l2 =>
    tblkL bL2 atL2_ok atL2 oI eLen
    rw [(atL2_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l3 =>
    tblkL bL3 atL3_ok atL3 oI eLen
    rw [(atL3_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l4 =>
    tblkL bL4 atL4_ok atL4 oI eLen
    rw [(atL4_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l5 =>
    tblkL bL5 atL5_ok atL5 oI eLen
    rw [(atL5_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l6 =>
    tblkL bL6 atL6_ok atL6 oI eLen
    rw [(atL6_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case arg =>
    tblkL bArg atArg_ok atArg oI eLen
    rw [(atArg_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case bnd =>
    tblkL bBnd atBnd_ok atBnd oI eLen
    rw [(atBnd_walk _ _ hJ.2.1 hJ.2.2 (by rw [hn0]; decide)).1, eLen]; decide +kernel
  case j2 =>
    tblkL bJ2 atJ2_ok atJ2 oI eLen
    rw [(atJ2_walk _ _ hJ.2).1]; show NoH ((_root_.Executable.labels L.exe |>.label okL).toBitVec.toNat)
    rw [eOk]; decide +kernel
  case o1 =>
    tblkL bO1 atO1_ok atO1 oI eOk
    rw [(atO1_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o2 =>
    tblkL bO2 atO2_ok atO2 oI eOk
    rw [(atO2_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o3 =>
    tblkL bO3 atO3_ok atO3 oI eOk
    rw [(atO3_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o4 =>
    tblkL bO4 atO4_ok atO4 oI eOk
    rw [(atO4_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o5 =>
    tblkL bO5 atO5_ok atO5 oI eOk
    rw [(atO5_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case ret =>
    tblkLA bRet atRet_ok atRet oI eOk
    rw [(atRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec, show L.lab Spike.Lib.X64.Flow.Ret0.x0L =
      Int64.ofNat 4198487 from eX0]
    decide +kernel
  case shr1 => tnodeL 3 fShr1 eLen keep_fi hc rfl hs
  case and1 => tnodeL 3 fAnd1 eLen keep_fi hc rfl hs
  case shr2 => tnodeL 3 fShr2 eLen keep_fi hc rfl hs
  case and2 => tnodeL 3 fAnd2 eLen keep_fi hc rfl hs
  case imul1 => tnodeL 4 fImul1 eLen keep_fi hc rfl hs
  case shl1 => tnodeL 3 fShl1 eLen keep_fi hc rfl hs
  case lea1 => tnodeL 7 sLea1 eLen keep_lea hc hs
  case ok => tnodeL 7 sOk eOk keep_lea hc hs
  case imul2 => tnodeL 4 fImul2 eOk keep_fi hc rfl hs
  case shl2 => tnodeL 3 fShl2 eOk keep_fi hc rfl hs
  case shl3 => tnodeL 3 fShl3 eOk keep_fi hc rfl hs
  case or1 => tnodeL 3 fOr1 eOk keep_fi hc rfl hs
  case rmw =>
    tnodeL 5 bRmw eLen keep_rmw hc hd (a := L.pnA)
      (by
        dsimp only [tcbN] at hJ
        refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
        rw [hA.regs]; exact (Spike.Lib.X64.Flow.Ret0.bAddr_rcx hJ.2.2.2 0).trans (by rw [← hpn]; first | exact BitVec.add_zero _ | simp))
      (Spike.Lib.X64.PhRec.rtF_pn (hFr _ hF)) hs
  case hdr =>
    tnodeL 3 bHdr eOk keep_hdr hc hd (a := L.pinA)
      (by
        dsimp only [tcbN] at hJ
        refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
        rw [hA.regs]; exact (Spike.Lib.X64.Flow.Ret0.bAddr_rcx hJ.2.2.2 0).trans (by rw [← hH]; first | exact BitVec.add_zero _ | simp))
      (Spike.Lib.X64.PhRec.rtF_tcb (hFr _ hF) h0) hs

/-- **`TcbW` inside `WS` is inside `WSX`** for the first call (`tcbL`). -/
theorem tcbX (hp : L.prog = wakeCells)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hbd : BandT L R) (hR : R.OK) (hRlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {K : State → State → Prop} (q : TcbG) (hn0 : q.n0 = 0#64)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec)
    (h : ∀ i, TcbW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F q i) :
    ∀ i, TcbW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F q i := fun i =>
  TcbW.imp (h i) (tcbL hp hlab hsite hsep ha hW hbd hR hRlo hhi hFr q hn0 hra i) fun _ _ h1 h2 => h2 h1

end Spike.Lib.X64.WakePh.OwnSt

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.tcbL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.tcbL

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.tcbX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.tcbX
