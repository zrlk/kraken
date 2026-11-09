/-
**wake.w's `scc_rt_thread_init` call inside `W0`** (x86-64; twin of
`Spike/Lib/A64WakeStartTiW.lean`): every node of the call from
`scc_rt_start` (returning to `.x1`) inside the start's level `StartWf.WS`,
the shape of the start's `hti`. Each node's `SFacts` at the first instance
are `Rt.tiW_gen`'s at `phW` (`instOkWS`, `tiPhW`), moved inside `WS` by
`StartTi.blkI_WS` / `nodeI_WSst` (the TCB fields' stores), the nested
`scc_rt_stack_take` call by `takeW_WS`.

- `startTi_WS`: the call's node obligations inside `WS`.

**Unlike AArch64**: no `P`, no `hal`; the callee's frames are `[-248, 8]`
of `R` (`hbdI`; the take's `[-200, 8]` at `-48`; A64's `[-256, 0]`),
`hRlo : R.lo ≤ -248`, `hhi : 8 ≤ R.hi`; the return is to `.Lscc_rt_start.x1`
(A64's `.sp3`), the take's to `.x7` (A64's `.sp0`); `hSMt` is at
`R.callee (-48 - 0) (-200) 8`; x86-64's `scc_rt_thread_init` has the
call's own block node `.c7` (`tiCall`), its fields' values in blocks
`tiF1`/`tiZ`/`tiF4`/`tiF5` at `.x7 + 51/63/78/93/105` and its stores
`movq %rax, 8·j(%rcx)` (`stDir .rcx (8·j) .rax`, `keep_st`; A64's
`str x9, [x10, #8·j]`, `keep_str`) at `.x7 + storeOff`. The callee's
region is `Region.callee_ok`'s (A64's `StartU.callee_facts`); its
`TakeW` needs no frame-condition weakening (x86-64's `.call` is at `F`).
-/
import Spike.Lib.X64WakeStartTiT3

namespace Spike.Lib.X64.WakePh.StartTi

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
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib.X64.WakePh.WcW (freeN freeAt cv inCv goodW_of_freeN freeAt_lab)
open Spike.Lib.X64.Flow.Ret0 (TI TiG TiW tiN tiX7 tiTake tiCall tiCall_ok StackM stacksA pinA bAddr_rcx
  storeBlks_eq)
open Spike.Lib.X64.Flow.Ret0.ThreadInit
open Spike.Lib (Arena FragS)

/-- `hso` of a block of `scc_rt_thread_init` at offsets `o`, decided. -/
local macro "soI " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -48 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A store of TCB field `j` (`movq %rax, k(%rcx)`, `z` bytes at
`.x7 + off`, block `b`) inside `WS`. -/
local macro "tstW " b:term:max x:term:max j:term:max k:term:max z:term:max off:term:max : tactic =>
  `(tactic| focus
    have ha : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb := by
      simp [Spike.Lib.X64.Rt.Ti.tiAddrs]
    have hA' : ∀ σ c, (tiN (_root_.Executable.labels L.exe).label q $x).J σ c →
        bAddr σ.regs .rcx $k = q.tcb + BitVec.ofNat 64 (8 * $j) := fun σ c hJ => by
      dsimp only [tiN] at hJ
      rw [bAddr_rcx hJ.2.2.2]; exact congrArg (q.tcb + ·) (by decide)
    refine nodeI_WSst (z := $z) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 $b rfl h
      (hP.st (L.lab x7L + Int64.ofNat $off, $z) (by simp [Spike.Lib.X64.Rt.Ti.stPcs])).1
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [tiN]; decide) (by decide +kernel) (fun σ c h => h.1.trans hq)
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact Spike.Lib.X64.PhRec.rtF_tcb (hFr _ hF.1) (hfld _ ha))
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact hoffT _ ha)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $b) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_st hc hd (a := q.tcb + BitVec.ofNat 64 (8 * $j))
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_tcb (hFr _ hF.1) (hfld _ ha)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tiN]; rw [eX7]; decide +kernel)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {lbl' : Lbl}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbdI : BandI L R (-248))

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbdI

set_option maxHeartbeats 3200000 in
/-- **`scc_rt_thread_init`'s node obligations inside `WS`**, called from
`scc_rt_start` returning to `.x1` (`hra`), on the first TCB (`htcb`): the
frames `[-248, 8]` of the callee's region off the pool (`hbdI`), the TCB's
fields, the lock's and the next offset's words off the arena and not its
counter word (`hoffT`, `hoffL`, `hoffX`); `X0` off the take site by `hX0`,
at it from the site's range and frame (`hXs`).

VACUOUS at root (`hXs` unsatisfiable): superseded by `startTi_WSP`
(`Spike/Lib/X64WakeStartTiP.lean`). -/
theorem startTi_WS (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TiG) (hq : q.c0 = c0)
    (htcb : q.tcb = pinA L.lab + 0#64 + 8#64)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hSMt : Spike.Lib.X64.FStable (R.callee (-48 - 0) (-200) 8) (StackM rS))
    (hoffT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb,
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → X0 s) :
    ∀ i, TiW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      (StackM rS) q i := by
  have hfld : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∃ j < 7, b = L.pinA + BitVec.ofNat 64 (8 * j) :=
    fun _ hb => Spike.Lib.X64.Rt.StartU.tcb_fld (htcb ▸ hb)
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.X64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  have hT := Spike.Lib.X64.Rt.tiW_gen (rS := rS) (lbl := lbl') (instOkWS (a := a) (rS := rS) hp hlo hlab)
    (fun _ => rfl) (hp ▸ wake_tiIn) hC0 hR hRlo hhi q hq hra (tiPhW hΛ hlab)
    (fun _ hb => Spike.Lib.X64.PhRec.mapped_tcb (hfld _ hb))
    (fun _ hb m hm => Spike.Lib.X64.PhRec.rtF_tcb (hFr m hm) (hfld _ hb))
    (fun _ hb => tcb_not_ownW hs (hfld _ hb)) hsub hSM hSMt (hp ▸ wake_takeIn)
    (takePhW hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
      hs.lock_a hs.next_a)
    (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
    (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
    (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
    (fun m hm => by rw [hlk]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact Spike.Lib.X64.PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact Spike.Lib.X64.PhRec.rtF_next (hFr m hm)) hrS hro
  have hP := tiPhW (L := L) hΛ hlab
  have hbd48 : BandI L R (-48) := bandI_mono hbdI (by decide)
  obtain ⟨eFn, eEn⟩ := ti_labs hlab (L := L)
  obtain ⟨eT, -, -, -, -, -, -, -, -, -, -, eX7⟩ := take_labs hlab (L := L)
  have hin := wake_tiIn
  simp only [threadInitIn, storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bC⟩, -⟩, bSp⟩, bF1⟩, bF2⟩, bF3⟩, bF4⟩, bF5⟩, bRet⟩,
    bS0, bS1, bS2, bS3, bS4, bS5⟩ := hin
  rw [show callBlk = tiCall from rfl] at bC
  intro i
  have h := hT i
  cases i <;> dsimp only [TiW] at h ⊢
  case e =>
    refine blkI_WS (rl := fnL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bE (ofNat_zero' _)
      tiPro_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.e) ?_ (soI tiPro oE)
      (finI hlab hbd48 (fun σ c hJ => ?_) (soI tiPro oE)) (by decide +kernel)
      (nrB Spike.Lib.X64.Rt.Ti.tiPro_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eFn]; revert k; decide +kernel
    · dsimp only [tiN] at hJ ⊢; rw [(tiPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    refine blkI_WS (rl := entryL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bEn (ofNat_zero' _)
      tiArg_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.entry) ?_ (soI tiArg oI)
      (finI hlab hbd48 (fun σ c hJ => ?_) (soI tiArg oI)) (by decide +kernel)
      (nrB Spike.Lib.X64.Rt.Ti.tiArg_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eEn]; revert k; decide +kernel
    · dsimp only [tiN] at hJ ⊢; rw [(tiArg_walk _ _ hJ.2).1, eEn]; decide +kernel
  case c7 =>
    refine blkI_WS (rl := entryL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bC rfl
      tiCall_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.c7) ?_ (soI tiCall oI)
      (finI hlab hbd48 (fun σ c hJ => ?_) (soI tiCall oI)) (by decide +kernel)
      (nrB Spike.Lib.X64.Rt.Ti.tiCall_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eEn]; revert k; decide +kernel
    · dsimp only [tiN]; rw [Spike.Lib.X64.Flow.Ret0.tiCall_run]
      show PcI ((_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.StackTake.fnL); rw [eT]; decide +kernel
  case call =>
    intro g hg j
    have hR' := Spike.Lib.Region.callee_ok (kc := -48 - 0) (lo' := -200) (hi' := 8) hR (by omega) (by decide)
      (by omega) (by omega)
    exact takeW_WS hp hlo hlab hsite hcl hc0 hpl0 hX0
      (bandI_callee hbdI (by show (-248 : Int) ≤ -48 - 0 + -200; omega) (by decide)) hΛ hs hro hC0 hR'
      (by show (-200 : Int) ≤ -200; omega) (by show (8 : Int) ≤ 8; omega) hFr (tiTake q g) hq hg hrS hsub hSMt
      hoffL hoffX hXs j
  case x7 =>
    refine blkI_WS (rl := x7L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bSp (ofNat_zero' _)
      tiSp_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.x7) ?_ (soI tiSp oI)
      (finI hlab hbd48 (fun σ c hJ => ?_) (soI tiSp oI)) (by decide +kernel)
      (nrB Spike.Lib.X64.Rt.Ti.tiSp_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiX7]; rw [eX7]; revert k; decide +kernel
    · dsimp only [tiX7, tiN] at hJ ⊢; rw [(tiSp_walk _ _ hJ.2.1 hJ.2.2).1, eX7]; decide +kernel
  case st0 => tstW bS0 TI.st0 0 0 3 48
  case f1 =>
    refine blkI_WS (rl := x7L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF1 rfl tiF1_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f1) ?_ (soI tiF1 oI) (finI hlab hbd48 (fun σ c hJ => ?_) (soI tiF1 oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiF1_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eX7]; revert k; decide +kernel
    · dsimp only [tiN] at hJ ⊢; rw [(tiF1_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st1 => tstW bS1 TI.st1 1 8 4 59
  case f2 =>
    refine blkI_WS (rl := x7L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF2 rfl tiZ_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f2) ?_ (soI tiZ oI) (finI hlab hbd48 (fun σ c hJ => ?_) (soI tiZ oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiZ_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eX7]; revert k; decide +kernel
    · dsimp only [tiN] at hJ ⊢; rw [(tiZ_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st2 => tstW bS2 TI.st2 2 16 4 74
  case f3 =>
    refine blkI_WS (rl := x7L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF3 rfl tiZ_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f3) ?_ (soI tiZ oI) (finI hlab hbd48 (fun σ c hJ => ?_) (soI tiZ oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiZ_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eX7]; revert k; decide +kernel
    · dsimp only [tiN] at hJ ⊢; rw [(tiZ_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st3 => tstW bS3 TI.st3 3 24 4 89
  case f4 =>
    refine blkI_WS (rl := x7L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF4 rfl tiF4_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f4) ?_ (soI tiF4 oI) (finI hlab hbd48 (fun σ c hJ => ?_) (soI tiF4 oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiF4_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eX7]; revert k; decide +kernel
    · dsimp only [tiN] at hJ ⊢; rw [(tiF4_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st4 => tstW bS4 TI.st4 4 32 4 101
  case f5 =>
    refine blkI_WS (rl := x7L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF5 rfl tiF5_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f5) ?_ (soI tiF5 oI) (finI hlab hbd48 (fun σ c hJ => ?_) (soI tiF5 oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiF5_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eX7]; revert k; decide +kernel
    · dsimp only [tiN] at hJ ⊢; rw [(tiF5_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st5 => tstW bS5 TI.st5 5 40 4 113
  case ret =>
    refine blkI_WSA (rl := Spike.Lib.X64.Flow.Ret0.x1L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bRet rfl tiRet_ok
      hR (by omega) (by omega) h (okPc_of_blkPh hP.ret) ?_ (soI tiRet oI) (fun σ c hJ s m _ _ _ hs' => ?_)
      (by decide +kernel) (Spike.Lib.X64Consumer.hret_of_run tiRet_ok fun σ c hJ => ?_) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiN]; rw [eX7]; revert k; decide +kernel
    · dsimp only [tiN] at hJ hs'
      rw [(tiRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec] at hs'
      exact goodW_of_freeN hlab (by unfold pcOf; rw [hs']; exact freeAt_lab hlab (by wsfree_dec))
    · dsimp only [tiN] at hJ ⊢
      rw [(tiRet_walk _ _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _

end Gen

end Spike.Lib.X64.WakePh.StartTi

/-- info: 'Spike.Lib.X64.WakePh.StartTi.startTi_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.startTi_WS
