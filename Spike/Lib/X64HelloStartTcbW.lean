/-
**hello.w's first `scc_rt_alloc_tcb` call inside `W0`** (x86-64; twin of
`Spike/Lib/A64HelloStartTcbW.lean`, wake's `X64WakeStartTcbW` at
`SccCode.helloCells`): every node of the call from `scc_rt_start`
(returning to `.x0`) inside the start's level `HelloPh.StartWf.WSH`, the
shape of `hello_start_wc_segWS`'s `htcbW`. Each node's `SFacts` at the first
instance are `Rt.tcbW_gen`'s at `phH` (`instOkHS`, `tcbPhH`), moved inside
`WSH` by `StartTcb.blkT_WSH` / `nodeT_WSH` (the `leaq`s) / `nodeT_WSfiH`
(the flag-clobbering instructions) / `nodeT_WSxaddH` (the counter's add) /
`nodeT_WSstH` (the header's store).

- `startTcb_WSH`: the call's node obligations inside `WSH`.

## Differences from the AArch64 version

As wake's x86-64 `StartTcbW`: no `hal`; the callee's region is given (`R`,
its frame `[-184, 8]` off the pool, `hbd`; `hRlo : R.lo ≤ -184`,
`hhi : 8 ≤ R.hi`) with the call's ghosts `q` (`hq`, `hn0`, `hra`), where
AArch64's `startTcb_WSH` builds the callee's region from the caller's
(`R.callee oI.sp (-192) 0`); 33 nodes (the length's and the header's
flag-clobbering instructions and the `leaq`s are nodes of their own,
`keep_fi`, `keep_lea`); the return is to `.Lscc_rt_start.x0` (AArch64's
`.sp2`). The callee's pcs are hello's (`PcTH`, `tcb_labsH`); the offsets
inside it are wake's.
-/
import Spike.Lib.X64HelloStartTcbL
import Spike.Lib.X64HelloStart
import Spike.Lib.X64HelloTcb2W
import Spike.Lib.X64HelloStartWf

namespace Spike.Lib.X64.HelloPh.StartTcb

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (code_field)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64 (ND bAddr)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.HelloPh.StartWf (WSH)
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_fi keep_lea keep_rmw keep_hdr)
open Spike.Lib.X64.HelloPh.Tcb2W (tcb_labsH)
open Spike.Lib.X64.Flow.HelloWc (hello_allocTcbIn)
open Spike.Lib.X64.WakePh (inPc Keep keep_pc WSep)
open Spike.Lib.X64.WakePh.StartTcb (BandT)
open Spike.Lib.X64.HelloPh.WcW (freeNH freeAtH cvH inCvH goodW_of_freeNH freeAt_labH)
open Spike.Lib.X64.Flow.Ret0 (TN TcbG TcbW tcbN pinA pnA hdrBlk_eq rmwBlk_eq)
open Spike.Lib.X64.Flow.Ret0.AllocTcb
open Spike.Lib (Arena FragS)

/-- A covered block's pcs are off the sites (`blkPh`'s first conjunct). -/
private theorem okB {okP : Nat → Bool} {phf : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {blk : List (Directive × Nat)} (h : Spike.Lib.X64Consumer.blkPh okP phf d lab pc ra blk = true) :
    ∀ j < blk.length, okP (pc + Int64.ofNat (Spike.Lib.X64.cellOff blk j)).toBitVec.toNat = true := fun j hj => by
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true] at this
  exact this.1.1

/-- A block without `ret` meets any `hret`. -/
private theorem nrB {blk : List (Directive × Nat)} (hb : Spike.Lib.X64Consumer.noRetBlk blk = true) {n : ND}
    {lb : Label → Int64} {ra' : Int64} : ∀ σ (c : Spike.Lib.Ctl), n.J σ c → ∀ j (hj : j < blk.length),
      Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((Spike.Lib.X64.arun lb (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot
        (Spike.Lib.X64.arun lb (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp) = ra' :=
  fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false hb j hj hr).elim

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -184 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block of the call at `l + off` (`bb` its code check, `ok` its
`okBlk`, `blk` the block, `oo` its entry offsets, `f` its phase field, `nr`
its no-`ret` lemma, `el` its label's value), `PcT` at its end left. -/
local macro "tblkW " rl:term:max bb:term:max ok:term:max blk:term:max oo:term:max f:term:max nr:term:max
    el:term:max : tactic =>
  `(tactic| (
    refine blkT_WSH (rl := $rl) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd $bb (by first | rfl | exact ofNat_zero' _)
      $ok hR (by omega) (by omega) h (okB $f) ?_ (soT $blk $oo) (finTH hlab hbd (fun σ c hJ => ?_) (soT $blk $oo))
      (by decide +kernel) (nrB $nr) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tcbN]; rw [$el:term]; revert k; decide +kernel
    dsimp only [tcbN] at hJ ⊢))

set_option hygiene false in
/-- A single-instruction node of the call (`lem` its `WSH` lemma, `z` bytes,
`bb` its code check, `pz` its `stepPcs` entry, `el` its label's value, `kp`
its `Keep` from the cell `hc` and the step `hs`). -/
local macro "tnodeW " lem:ident z:term:max bb:term:max pz:term:max el:term:max kp:term : tactic =>
  `(tactic| (
    refine $lem (z := $z) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd $bb (by first | rfl | exact ofNat_zero' _) h
      (hP.step $pz (by simp [Spike.Lib.X64.Rt.Tcb.stepPcs])).1
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [tcbN]; decide) (by decide +kernel)
      (fun σ c h => h.1.trans hq)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $bb) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := $kp
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tcbN]; rw [$el:term]; decide +kernel
    · dsimp only [tcbN]; rw [$el:term]; decide +kernel))

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {lbl' : Lbl}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s → X0 s)
  (hbd : BandT L R)

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd

set_option maxHeartbeats 3200000 in
/-- **`scc_rt_alloc_tcb`'s node obligations inside `WSH`**, called from
`scc_rt_start` returning to `.x0` (`hra`), on the first TCB (`hn0`): the
frame `[-184, 8]` of the callee's region off the pool (`hbd`), the counter's
and the header's words off the arena and not its counter word (`hoffP`,
`hoffH`). -/
theorem startTcb_WSH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hC0 : CFacts L.Λ lbl' c0) (hR : R.OK) (hRlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TcbG) (hq : q.c0 = c0) (hn0 : q.n0 = 0#64)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec)
    (hoffP : ¬ (ar.heap ≤ L.pnA.toNat ∧ L.pnA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pnA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffH : ¬ (ar.heap ≤ L.pinA.toNat ∧ L.pinA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pinA, 8⟩ : Loc) ≠ ar.ctrLoc) :
    ∀ i, TcbW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F q i := by
  have hpn : pnA L.lab = L.pnA := L.lab_pn
  have hpin : pinA L.lab = L.pinA := L.lab_pin
  have h0 : ∃ j < 7, L.pinA = L.pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hP := tcbPhH (Λ := L.Λ) (a := a) hΛ hlab hs
  have hH : pinA L.lab + q.n0 = L.pinA := by rw [hn0, hpin, BitVec.add_zero]
  have hT := Spike.Lib.X64.Rt.tcbW_gen (rS := rS) (lbl := lbl') (instOkHS (a := a) (rS := rS) hp hlo hlab)
    (fun _ => rfl) (hp ▸ hello_allocTcbIn) hC0 hR hRlo hhi q hq (ra := fun _ => L.lab Spike.Lib.X64.Flow.Ret0.x0L)
    hra (hn0 ▸ hP)
    (by rw [hpn]; exact (L.words_mapped _ L.pn_mem).1)
    (by rw [hH]; exact Spike.Lib.X64.PhRec.mapped_tcb h0)
    (fun m hm => by rw [hpn]; exact Spike.Lib.X64.PhRec.rtF_pn (hFr m hm))
    (fun m hm => by rw [hH]; exact Spike.Lib.X64.PhRec.rtF_tcb (hFr m hm) h0)
  obtain ⟨eFn, eEn, eLen, eOk, -, -⟩ := tcb_labsH hlab (L := L)
  have hin := hello_allocTcbIn
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bL0⟩, fShr1⟩, bL1⟩, fAnd1⟩, bL2⟩,
    fShr2⟩, bL3⟩, fAnd2⟩, bL4⟩, fImul1⟩, bL5⟩, fShl1⟩, bL6⟩, sLea1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, sOk⟩, bO1⟩,
    fImul2⟩, bO2⟩, fShl2⟩, bO3⟩, fShl3⟩, bO4⟩, fOr1⟩, bO5⟩, bHdr⟩, bRet⟩ := hin
  intro i
  have h := hT i
  cases i <;> dsimp only [TcbW] at h ⊢
  case e =>
    tblkW fnL bE atPro_ok atPro oE hP.e Spike.Lib.X64.Rt.Tcb.atPro_noRet eFn
    rw [(atPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    tblkW entryL bEn atChk_ok atChk oI hP.entry Spike.Lib.X64.Rt.Tcb.atChk_noRet eEn
    rw [(atChk_walk _ _ hJ.2).1, eEn]; decide +kernel
  case j1 =>
    tblkW entryL bJ1 atJ1_ok atJ1 oI hP.j1 Spike.Lib.X64.Rt.Tcb.atJ1_noRet eEn
    rw [(atJ1_walk _ _ hJ.2).1]; show PcTH (_root_.Executable.labels L.exe |>.label lenL); rw [eLen]
    decide +kernel
  case len =>
    tblkW lenL bL0 atL0_ok atL0 oI hP.len Spike.Lib.X64.Rt.Tcb.atL0_noRet eLen
    rw [(atL0_walk _ _ hJ.2).1, eLen]; decide +kernel
  case l1 =>
    tblkW lenL bL1 atL1_ok atL1 oI hP.l1 Spike.Lib.X64.Rt.Tcb.atL1_noRet eLen
    rw [(atL1_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l2 =>
    tblkW lenL bL2 atL2_ok atL2 oI hP.l2 Spike.Lib.X64.Rt.Tcb.atL2_noRet eLen
    rw [(atL2_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l3 =>
    tblkW lenL bL3 atL3_ok atL3 oI hP.l3 Spike.Lib.X64.Rt.Tcb.atL3_noRet eLen
    rw [(atL3_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l4 =>
    tblkW lenL bL4 atL4_ok atL4 oI hP.l4 Spike.Lib.X64.Rt.Tcb.atL4_noRet eLen
    rw [(atL4_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l5 =>
    tblkW lenL bL5 atL5_ok atL5 oI hP.l5 Spike.Lib.X64.Rt.Tcb.atL5_noRet eLen
    rw [(atL5_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l6 =>
    tblkW lenL bL6 atL6_ok atL6 oI hP.l6 Spike.Lib.X64.Rt.Tcb.atL6_noRet eLen
    rw [(atL6_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case arg =>
    tblkW lenL bArg atArg_ok atArg oI hP.arg Spike.Lib.X64.Rt.Tcb.atArg_noRet eLen
    rw [(atArg_walk _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case bnd =>
    tblkW lenL bBnd atBnd_ok atBnd oI hP.bnd Spike.Lib.X64.Rt.Tcb.atBnd_noRet eLen
    rw [(atBnd_walk _ _ hJ.2.1 hJ.2.2 (by rw [hn0]; decide)).1, eLen]; decide +kernel
  case j2 =>
    tblkW lenL bJ2 atJ2_ok atJ2 oI hP.j2 Spike.Lib.X64.Rt.Tcb.atJ2_noRet eLen
    rw [(atJ2_walk _ _ hJ.2).1]; show PcTH (_root_.Executable.labels L.exe |>.label okL); rw [eOk]
    decide +kernel
  case o1 =>
    tblkW okL bO1 atO1_ok atO1 oI hP.o1 Spike.Lib.X64.Rt.Tcb.atO1_noRet eOk
    rw [(atO1_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o2 =>
    tblkW okL bO2 atO2_ok atO2 oI hP.o2 Spike.Lib.X64.Rt.Tcb.atO2_noRet eOk
    rw [(atO2_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o3 =>
    tblkW okL bO3 atO3_ok atO3 oI hP.o3 Spike.Lib.X64.Rt.Tcb.atO3_noRet eOk
    rw [(atO3_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o4 =>
    tblkW okL bO4 atO4_ok atO4 oI hP.o4 Spike.Lib.X64.Rt.Tcb.atO4_noRet eOk
    rw [(atO4_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o5 =>
    tblkW okL bO5 atO5_ok atO5 oI hP.o5 Spike.Lib.X64.Rt.Tcb.atO5_noRet eOk
    rw [(atO5_walk _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case ret =>
    refine blkT_WSHA (rl := Spike.Lib.X64.Flow.Ret0.x0L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bRet rfl atRet_ok
      hR (by omega) (by omega) h (okB hP.ret) ?_ (soT atRet oI) (fun σ c hJ s m _ _ _ hs' => ?_)
      (by decide +kernel) (Spike.Lib.X64Consumer.hret_of_run atRet_ok fun σ c hJ => ?_) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tcbN]; rw [eOk]; revert k; decide +kernel
    · dsimp only [tcbN] at hJ hs'
      rw [(atRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec] at hs'
      exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact freeAt_labH hlab (by wsfreeH_dec))
    · dsimp only [tcbN] at hJ ⊢
      rw [(atRet_walk _ _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _
  case shr1 => tnodeW nodeT_WSfiH 3 fShr1 (L.lab lenL + Int64.ofNat 11, 3) eLen keep_fi hc rfl hs
  case and1 => tnodeW nodeT_WSfiH 3 fAnd1 (L.lab lenL + Int64.ofNat 29, 3) eLen keep_fi hc rfl hs
  case shr2 => tnodeW nodeT_WSfiH 3 fShr2 (L.lab lenL + Int64.ofNat 47, 3) eLen keep_fi hc rfl hs
  case and2 => tnodeW nodeT_WSfiH 3 fAnd2 (L.lab lenL + Int64.ofNat 65, 3) eLen keep_fi hc rfl hs
  case imul1 => tnodeW nodeT_WSfiH 4 fImul1 (L.lab lenL + Int64.ofNat 95, 4) eLen keep_fi hc rfl hs
  case shl1 => tnodeW nodeT_WSfiH 3 fShl1 (L.lab lenL + Int64.ofNat 132, 3) eLen keep_fi hc rfl hs
  case lea1 => tnodeW nodeT_WSH 7 sLea1 (L.lab lenL + Int64.ofNat 139, 7) eLen keep_lea hc hs
  case ok => tnodeW nodeT_WSH 7 sOk (L.lab okL + Int64.ofNat 0, 7) eOk keep_lea hc hs
  case imul2 => tnodeW nodeT_WSfiH 4 fImul2 (L.lab okL + Int64.ofNat 34, 4) eOk keep_fi hc rfl hs
  case shl2 => tnodeW nodeT_WSfiH 3 fShl2 (L.lab okL + Int64.ofNat 53, 3) eOk keep_fi hc rfl hs
  case shl3 => tnodeW nodeT_WSfiH 3 fShl3 (L.lab okL + Int64.ofNat 74, 3) eOk keep_fi hc rfl hs
  case or1 => tnodeW nodeT_WSfiH 3 fOr1 (L.lab okL + Int64.ofNat 95, 3) eOk keep_fi hc rfl hs
  case rmw =>
    have hA' : ∀ σ c, (tcbN (_root_.Executable.labels L.exe).label q .rmw).J σ c → bAddr σ.regs .rcx 0 = L.pnA :=
      fun σ c hJ => by
        dsimp only [tcbN] at hJ
        rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx hJ.2.2.2, ← hpn]; first | exact BitVec.add_zero _ | simp
    refine nodeT_WSxaddH (z := 5) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bRmw rfl h hP.rmwOk
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [tcbN]; decide) (by decide +kernel)
      (fun σ c h => h.1.trans hq)
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact Spike.Lib.X64.PhRec.rtF_pn (hFr _ hF))
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact hoffP)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bRmw) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_rmw hc hd (a := L.pnA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_pn (hFr _ hF)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tcbN, rmwPc]; rw [eLen]; decide +kernel
    · dsimp only [tcbN, rmwPc]; rw [eLen]; decide +kernel
  case hdr =>
    have hA' : ∀ σ c, (tcbN (_root_.Executable.labels L.exe).label q .hdr).J σ c → bAddr σ.regs .rcx 0 = L.pinA :=
      fun σ c hJ => by
        dsimp only [tcbN] at hJ
        rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx hJ.2.2.2, ← hH]; first | exact BitVec.add_zero _ | simp
    refine nodeT_WSstH (z := 3) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bHdr rfl h
      (hP.step (L.lab okL + Int64.ofNat 140, 3) (by simp [Spike.Lib.X64.Rt.Tcb.stepPcs])).1
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [tcbN]; decide) (by decide +kernel)
      (fun σ c h => h.1.trans hq)
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact Spike.Lib.X64.PhRec.rtF_tcb (hFr _ hF) h0)
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact hoffH)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bHdr) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_hdr hc hd (a := L.pinA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_tcb (hFr _ hF) h0) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tcbN, hdrPc]; rw [eOk]; decide +kernel
    · dsimp only [tcbN, hdrPc]; rw [eOk]; decide +kernel

end Gen

end Spike.Lib.X64.HelloPh.StartTcb

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.startTcb_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.startTcb_WSH
