/-
**wake.w's second `scc_rt_stack_take` call inside `W0`, up to the free count's
load** (AArch64): the nodes `takeA` of the call from the second `scc_rt_thread_init`
(returning to its `.sp0`) inside the start's level `StartWf.WS`, from
their `SFactsSt` at the second instance (`take2T`) by `StartTi.blk2_WS` /
`node2_WS` / `node2_WSswp` / `node2_WSldr`, the take's frame `[-208, 0]`
on the pool (`hbd`).

- `take2A_WS`: the nodes up to the free count's load inside `WS`.
-/
import Spike.Lib.A64WakeTi2T0

namespace Spike.Lib.A64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (ND)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.Tcb2W (soRun)
open Spike.Lib.A64.Flow.Ret0 (TK TakeG TakeW StackM stacksA takeNG labMid)
open Spike.Lib.A64.Flow.Ret0.StackTake
open Spike.Lib (Arena FragS)
open Spike.Lib.A64.WakePh.Ti2 (BandP fin2)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -208 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 0
    by decide) k hk)

set_option hygiene false in
/-- `hk` of a label pair's instruction (`adrp`/`add`, `kp`), block `b` at `e`. -/
local macro "khk " b:term:max e:term:max kp:term:max : term =>
  `(fun s c hAt s' hs => by
      obtain ⟨he', hn, -, hp', -⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ $b) $e s he' hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; simp [takeNG, labMid])
      exact ⟨$kp hc hs, by rw [keep_pc hc ($kp hc hs), hp']; rfl⟩)

section Gen

variable {P : MachineData → Prop}
variable {L : RuntimeLayout} {Pl : MachineData → Prop} {a : BitVec 64} {rS : Range}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s : State, Pl s.st.1 → Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hPl : ∀ m m', F m → Spike.Lib.A64.Flow.DFrame R m m' → Pl m')
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbd : BandP L R (-208))

include hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd

set_option maxHeartbeats 3200000 in
/-- **`scc_rt_stack_take`'s nodes up to the free count's load inside
`WS`** (`takeA`), called from `scc_rt_thread_init` returning to its `.sp0`
(`hra`), the lock's word off the arena and not its counter word (`hoffL`). -/
theorem take2A_WS (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS))
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc) :
    ∀ i, takeA i = true → TakeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q i P := by
  have hT := take2T (P := P) (a := a) hp hlo hΛ hlab hsite hs hro hR hal hRlo hhi hFr q hra hrS hsub hSM
  have hP := takePh2b hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN
    hs.lock_freeN hs.lock_a hs.next_a
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.A64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  obtain ⟨eFn, eEn, eCls, eDone, eSpin, eLk, -, -, -, -, -, -⟩ := take_labs hlab (L := L)
  have hin := wake_takeIn
  simp only [stackTakeIn, labIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bCls⟩, bJ1⟩, ⟨bD0, bD1⟩⟩, bD2⟩, ⟨bD7, bD8⟩⟩, bD9⟩,
    ⟨bD14, bD15⟩⟩, bD16⟩, bSp0⟩, bSwp⟩, bSp3⟩, bLk0⟩, bLdn⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hin
  rw [swp_eq] at bSwp; rw [ldr_eq] at bLdn
  have hJ0 : ∀ i, ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true i).J σ c → i ≠ .ret → c = c0 := by
    intro i σ c h hi; cases i <;> first | exact h.1.trans hq | exact absurd rfl hi
  intro i hi
  have h := hT i
  cases i <;> (try (exfalso; revert hi; decide)) <;> dsimp only [TakeW] at h ⊢
  case e =>
    refine blk2_WS (rl := fnL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bE (Spike.Lib.A64.Flow.ofNat4_zero _) stPro_ok
      hR hal (by omega) (by omega) h (okPc_of_blkPh hP.e) ?_ (soT stPro oE) (fin2 hlab hbd (fun σ c hJ => ?_)
      (soT stPro oE)) (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stPro_noRet) (fun σ c h => hJ0 .e σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eFn]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stPro_walk _ _ hJ.2).1, eFn]; decide
  case entry =>
    refine blk2_WS (rl := entryL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bEn (Spike.Lib.A64.Flow.ofNat4_zero _)
      stInit_ok hR hal (by omega) (by omega) h (okPc_of_blkPh hP.entry) ?_ (soT stInit oI)
      (fin2 hlab hbd (fun σ c hJ => ?_) (soT stInit oI)) (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stInit_noRet)
      (fun σ c h => hJ0 .entry σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eEn]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stInit_walk _ _ hJ.2).1, eCls]; decide
  case cls =>
    refine blk2_WS (rl := clsL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bCls (Spike.Lib.A64.Flow.ofNat4_zero _)
      stCls_ok hR hal (by omega) (by omega) h (okPc_of_blkPh hP.cls) ?_ (soT stCls oI)
      (fin2 hlab hbd (fun σ c hJ => ?_) (soT stCls oI)) (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stCls_noRet)
      (fun σ c h => hJ0 .cls σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stCls_walk _ _ hJ.2).1, eCls]; decide
  case j1 =>
    refine blk2_WS (rl := clsL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bJ1 rfl stJ1_ok hR hal (by omega) (by omega)
      h (okPc_of_blkPh hP.j1) ?_ (soT stJ1 oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stJ1 oI)) (by decide +kernel)
      (nrB Spike.Lib.A64.Rt.Take.stJ1_noRet) (fun σ c h => hJ0 .j1 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [stJ1_run]; dsimp only; rw [eDone]; decide
  case d0 =>
    refine ⟨node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bD0 rfl h.1
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1 (khk bD0 rfl keep_adrp) ?_ (by dsimp only [takeNG]; decide)
      (by decide +kernel) (fun σ c h => hJ0 .d0 σ c h nofun),
      node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bD1 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 0).symm h.2
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1
      (khk bD1 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 0).symm keep_add) ?_ (by dsimp only [labMid]; decide) (by decide +kernel)
      (fun σ c ⟨σ0, h, _⟩ => hJ0 .d0 σ0 c h nofun)⟩
    · dsimp only [takeNG]; rw [eDone]; decide
    · dsimp only [labMid]; rw [eDone]; decide
  case d2 =>
    refine blk2_WS (rl := doneL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bD2 rfl stFreeN_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.d2) ?_ (soT stFreeN oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stFreeN oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stFreeN_noRet) (fun σ c h => hJ0 .d2 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stFreeN_walk _ _ hJ.2.1 hJ.2.2).1, eDone]; decide
  case d7 =>
    refine ⟨node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bD7 rfl h.1
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1 (khk bD7 rfl keep_adrp) ?_ (by dsimp only [takeNG]; decide)
      (by decide +kernel) (fun σ c h => hJ0 .d7 σ c h nofun),
      node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bD8 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 7).symm h.2
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1
      (khk bD8 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 7).symm keep_add) ?_ (by dsimp only [labMid]; decide) (by decide +kernel)
      (fun σ c ⟨σ0, h, _⟩ => hJ0 .d7 σ0 c h nofun)⟩
    · dsimp only [takeNG]; rw [eDone]; decide
    · dsimp only [labMid]; rw [eDone]; decide
  case d9 =>
    refine blk2_WS (rl := doneL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bD9 rfl stFree_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.d9) ?_ (soT stFree oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stFree oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stFree_noRet) (fun σ c h => hJ0 .d9 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stFree_walk _ _ hJ.2).1, eDone]; decide
  case d14 =>
    refine ⟨node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bD14 rfl h.1
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1 (khk bD14 rfl keep_adrp) ?_ (by dsimp only [takeNG]; decide)
      (by decide +kernel) (fun σ c h => hJ0 .d14 σ c h nofun),
      node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bD15 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 14).symm h.2
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1
      (khk bD15 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 14).symm keep_add) ?_ (by dsimp only [labMid]; decide) (by decide +kernel)
      (fun σ c ⟨σ0, h, _⟩ => hJ0 .d14 σ0 c h nofun)⟩
    · dsimp only [takeNG]; rw [eDone]; decide
    · dsimp only [labMid]; rw [eDone]; decide
  case d16 =>
    refine blk2_WS (rl := doneL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bD16 rfl stLock_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.d16) ?_ (soT stLock oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stLock oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stLock_noRet) (fun σ c h => hJ0 .d16 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stLock_walk _ _ hJ.2.1 hJ.2.2).1, eSpin]; decide
  case sp0 =>
    refine blk2_WS (rl := spinL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bSp0 (Spike.Lib.A64.Flow.ofNat4_zero _)
      stSwp_ok hR hal (by omega) (by omega) h (okPc_of_blkPh hP.sp0) ?_ (soT stSwp oI)
      (fin2 hlab hbd (fun σ c hJ => ?_) (soT stSwp oI)) (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stSwp_noRet)
      (fun σ c h => hJ0 .sp0 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eSpin]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stSwp_walk _ _ hJ.2).1, eSpin]; decide
  case swp =>
    refine node2_WSswp hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bSwp rfl h hP.swpOk
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [takeNG]; decide) (by decide +kernel) (fun σ c h => hJ0 .swp σ c h nofun)
      (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bSwp) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; simp [takeNG])
      have hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg .X10).toBitVec 8 = none := by
        dsimp only [takeNG] at hJ
        rw [hA.regs]; simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hlk]
        exact Spike.Lib.A64.PhRec.rtF_lock (hFr _ hF)
      exact ⟨keep_swp hc hd hdm hs, by rw [keep_pc hc (keep_swp hc hd hdm hs), hp']; rfl⟩
    · dsimp only [takeNG, swpPc]; rw [eSpin]; decide
    · dsimp only [takeNG] at hJ
      simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hlk]; exact Spike.Lib.A64.PhRec.rtF_lock (hFr _ hF)
    · dsimp only [takeNG] at hJ
      simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hlk]; exact hoffL
  case sp3 =>
    refine blk2_WS (rl := spinL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bSp3 rfl stSpin_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.sp3) ?_ (soT stSpin oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stSpin oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stSpin_noRet) (fun σ c h => hJ0 .sp3 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eSpin]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stSpin_walk _ _ hJ.2.1 hJ.2.2).1, eLk]; decide
  case lk0 =>
    refine blk2_WS (rl := lockedL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bLk0 (Spike.Lib.A64.Flow.ofNat4_zero _)
      stLdN_ok hR hal (by omega) (by omega) h (okPc_of_blkPh hP.lk0) ?_ (soT stLdN oI)
      (fin2 hlab hbd (fun σ c hJ => ?_) (soT stLdN oI)) (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stLdN_noRet)
      (fun σ c h => hJ0 .lk0 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stLdN_walk _ _ hJ.2).1, eLk]; decide
  case ldn =>
    refine node2_WSldr hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bLdn rfl h hP.ldnOk
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [takeNG]; decide) (by decide +kernel) (fun σ c h => hJ0 .ldn σ c h nofun)
      (fun σ c m hJ hF => ?_)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bLdn) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; simp [takeNG])
      have hdm : Mem.loadInt s.st.1.dmem (Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 0) 8 = none := by
        dsimp only [takeNG] at hJ
        rw [Spike.Lib.A64.Rt.Tcb.rAddr_zero, hA.regs]; simp only [Reg64s.getXReg]; rw [hJ.2.2, hfr]
        exact Spike.Lib.A64.PhRec.rtF_freeN (hFr _ hF)
      exact ⟨keep_ldr hc hd hdm hs, by rw [keep_pc hc (keep_ldr hc hd hdm hs), hp']; rfl⟩
    · dsimp only [takeNG, freeNPc]; rw [eLk]; decide
    · dsimp only [takeNG] at hJ
      rw [Spike.Lib.A64.Rt.Tcb.rAddr_zero]; simp only [Reg64s.getXReg]; rw [hJ.2.2, hfr]
      exact Spike.Lib.A64.PhRec.rtF_freeN (hFr _ hF)

end Gen

/-- info: 'Spike.Lib.A64.WakePh.StartTi.take2A_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms take2A_WS

end Spike.Lib.A64.WakePh.StartTi
