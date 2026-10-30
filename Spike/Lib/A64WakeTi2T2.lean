/-
**wake.w's second `scc_rt_stack_take` call inside `W0`, past the free count's
load** (AArch64): the nodes of the call from the second `scc_rt_thread_init`
(returning to its `.sp0`) off `takeA` inside the start's level
`StartWf.WS`, from their `SFactsSt` at the second instance (`take2T`) by
`StartTi.blk2_WS` / `node2_WS` / `node2_WSstlr` / `node2_WSldop` /
`site2_WS`, the take's frame `[-208, 0]` on the pool (`hbd`).

- `take2B_WS`: the nodes past the free count's load inside `WS`.
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
/-- `hk` of a single instruction (`kp`), block `b` at `e`. -/
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
/-- **`scc_rt_stack_take`'s nodes past the free count's load inside `WS`**
(off `takeA`), called from `scc_rt_thread_init` returning to its `.sp0`
(`hra`), the lock's and the next offset's words off the arena and not its
counter word (`hoffL`, `hoffX`); `X0` at the take site from its range and
frame, the site frame `P` and region cells (`hXs`). -/
theorem take2B_WS (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS))
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 →
      (∀ k, R.Off k → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome) → X0 s) :
    ∀ i, takeA i = false → TakeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q i P := by
  have hT := take2T (P := P) (a := a) hp hlo hΛ hlab hsite hs hro hR hal hRlo hhi hFr q hra hrS hsub hSM
  have hP := takePh2b hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN
    hs.lock_freeN hs.lock_a hs.next_a
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hnx : Spike.Lib.A64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  obtain ⟨-, -, -, -, -, eLk, eBump, eOk, eTk, eSite, e8, eSp⟩ := take_labs hlab (L := L)
  have hin := wake_takeIn
  simp only [stackTakeIn, labIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    bLk2⟩, ⟨bB0, bB1⟩⟩, bB2⟩, bUnl⟩, ⟨bB6, bB7⟩⟩, bB8⟩, bNxt⟩, bB12⟩, bB21⟩, ⟨bOk0, bOk1⟩⟩, bOk2⟩, bTk⟩, -⟩,
    bSite⟩, bRet⟩ := hin
  rw [stlr_eq] at bUnl; rw [ldadd_eq] at bNxt; rw [nop_eq] at bSite
  have hJ0 : ∀ i, ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true i).J σ c → i ≠ .ret → c = c0 := by
    intro i σ c h hi; cases i <;> first | exact h.1.trans hq | exact absurd rfl hi
  intro i hi
  have h := hT i
  cases i <;> (try (exfalso; revert hi; decide)) <;> dsimp only [TakeW] at h ⊢
  case lk2 =>
    refine blk2_WS (rl := lockedL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bLk2 rfl stEmpty_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.lk2) ?_ (soT stEmpty oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stEmpty oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stEmpty_noRet) (fun σ c h => hJ0 .lk2 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stEmpty_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide
  case b0 =>
    refine ⟨node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bB0 rfl h.1
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1 (khk bB0 rfl keep_adrp) ?_ (by dsimp only [takeNG]; decide)
      (by decide +kernel) (fun σ c h => hJ0 .b0 σ c h nofun),
      node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bB1 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 0).symm h.2
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1
      (khk bB1 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 0).symm keep_add) ?_ (by dsimp only [labMid]; decide)
      (by decide +kernel) (fun σ c ⟨σ0, h, _⟩ => hJ0 .b0 σ0 c h nofun)⟩
    · dsimp only [takeNG]; rw [eBump]; decide
    · dsimp only [labMid]; rw [eBump]; decide
  case b2 =>
    refine blk2_WS (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bB2 rfl stUnl_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.b2) ?_ (soT stUnl oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stUnl oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stUnl_noRet) (fun σ c h => hJ0 .b2 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stUnl_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide
  case unl =>
    refine node2_WSstlr hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bUnl rfl h hP.unlOk
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [takeNG]; decide) (by decide +kernel) (fun σ c h => hJ0 .unl σ c h nofun)
      (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bUnl) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; simp [takeNG])
      have hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg .X10).toBitVec 8 = none := by
        dsimp only [takeNG] at hJ
        rw [hA.regs]; simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hlk]
        exact Spike.Lib.A64.PhRec.rtF_lock (hFr _ hF)
      exact ⟨keep_stlr hc hd hdm hs, by rw [keep_pc hc (keep_stlr hc hd hdm hs), hp']; rfl⟩
    · dsimp only [takeNG, unlPc]; rw [eBump]; decide
    · dsimp only [takeNG] at hJ
      simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hlk]; exact Spike.Lib.A64.PhRec.rtF_lock (hFr _ hF)
    · dsimp only [takeNG] at hJ
      simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hlk]; exact hoffL
  case b6 =>
    refine ⟨node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bB6 rfl h.1
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1 (khk bB6 rfl keep_adrp) ?_ (by dsimp only [takeNG]; decide)
      (by decide +kernel) (fun σ c h => hJ0 .b6 σ c h nofun),
      node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bB7 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 6).symm h.2
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1
      (khk bB7 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 6).symm keep_add) ?_ (by dsimp only [labMid]; decide)
      (by decide +kernel) (fun σ c ⟨σ0, h, _⟩ => hJ0 .b6 σ0 c h nofun)⟩
    · dsimp only [takeNG]; rw [eBump]; decide
    · dsimp only [labMid]; rw [eBump]; decide
  case b8 =>
    refine blk2_WS (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bB8 rfl stAdd_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.b8) ?_ (soT stAdd oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stAdd oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stAdd_noRet) (fun σ c h => hJ0 .b8 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stAdd_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide
  case nxt =>
    refine node2_WSldop hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bNxt rfl h hP.nxtOk
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [takeNG]; decide) (by decide +kernel) (fun σ c h => hJ0 .nxt σ c h nofun)
      (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bNxt) rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; simp [takeNG])
      have hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg .X10).toBitVec 8 = none := by
        dsimp only [takeNG] at hJ
        rw [hA.regs]; simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hnx]
        exact Spike.Lib.A64.PhRec.rtF_next (hFr _ hF)
      exact ⟨Tcb2W.keep_rmw hc hd hdm hs, by rw [keep_pc hc (Tcb2W.keep_rmw hc hd hdm hs), hp']; rfl⟩
    · dsimp only [takeNG, nextPc]; rw [eBump]; decide
    · dsimp only [takeNG] at hJ
      simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hnx]; exact Spike.Lib.A64.PhRec.rtF_next (hFr _ hF)
    · dsimp only [takeNG] at hJ
      simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hnx]; exact hoffX
  case b12 =>
    refine blk2_WS (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bB12 rfl stBnd_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.b12) ?_ (soT stBnd oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stBnd oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stBnd_noRet) (fun σ c h => hJ0 .b12 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide
    · dsimp only [takeNG]; rw [stBnd_run]; dsimp only
      split
      · rw [e8]; decide
      · rw [eBump]; decide
  case b21 =>
    refine blk2_WS (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bB21 rfl stJ2_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.b21) ?_ (soT stJ2 oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stJ2 oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stJ2_noRet) (fun σ c h => hJ0 .b21 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide
    · dsimp only [takeNG]; rw [stJ2_run]; dsimp only; rw [eOk]; decide
  case ok0 =>
    refine ⟨node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bOk0 rfl h.1
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1 (khk bOk0 rfl keep_adrp) ?_ (by dsimp only [takeNG]; decide)
      (by decide +kernel) (fun σ c h => hJ0 .ok0 σ c h nofun),
      node2_WS hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bOk1 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 0).symm h.2
      (hP.si _ (by simp [Spike.Lib.A64.Rt.Take.siPcs])).1
      (khk bOk1 (Spike.Lib.A64.Flow.Ret0.ofNat4_succ' _ 0).symm keep_add) ?_ (by dsimp only [labMid]; decide)
      (by decide +kernel) (fun σ c ⟨σ0, h, _⟩ => hJ0 .ok0 σ0 c h nofun)⟩
    · dsimp only [takeNG]; rw [eOk]; decide
    · dsimp only [labMid]; rw [eOk]; decide
  case ok2 =>
    refine blk2_WS (rl := okL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bOk2 rfl stOk_ok hR hal (by omega)
      (by omega) h (okPc_of_blkPh hP.ok2) ?_ (soT stOk oI) (fin2 hlab hbd (fun σ c hJ => ?_) (soT stOk oI))
      (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stOk_noRet) (fun σ c h => hJ0 .ok2 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eOk]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stOk_walk _ _ hJ.2.1 hJ.2.2).1, eTk]; decide
  case tk =>
    refine blk2_WS (rl := takenL) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd bTk (Spike.Lib.A64.Flow.ofNat4_zero _)
      stSite_ok hR hal (by omega) (by omega) h (okPc_of_blkPh hP.tk) ?_ (soT stSite oI)
      (fin2 hlab hbd (fun σ c hJ => ?_) (soT stSite oI)) (by decide +kernel) (nrB Spike.Lib.A64.Rt.Take.stSite_noRet)
      (fun σ c h => hJ0 .tk σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eTk]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢; rw [(stSite_walk _ _ hJ.2).1, eTk]; decide
  case site =>
    exact site2_WS hp hlo hlab hsite hcl hc0 hpl0 (fun m m' h hd => hPl m m' h.1 hd) hX0 hbd bSite (Spike.Lib.A64.Flow.ofNat4_zero _) h
      (fun k x hx => hP.siteAb k x hx) (khk bSite (Spike.Lib.A64.Flow.ofNat4_zero _) keep_nop)
      (by dsimp only [takeNG]; rw [eSite]; decide) (by dsimp only [takeNG]; decide) (by decide +kernel)
      (fun σ c h => hJ0 .site σ c h nofun) fun s hpc hr hm => hXs s hpc hr hm.1 hm.2
  case ret =>
    have eSp' : L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL = Int64.ofNat 2165272 := eSp
    refine blk2_WS (rl := Spike.Lib.A64.Flow.Ret0.ThreadInit.spL) hp hlo hlab hsite hcl hc0 hpl0
      (fun m m' h hd => hPl m m' h.1 hd) hX0 hbd bRet rfl
      stRet_ok hR hal (by omega) (by omega) h (okPc_of_blkPh hP.ret) ?_ (soT stRet oI)
      (fin2 hlab hbd (fun σ c hJ => ?_) (soT stRet oI)) (by decide +kernel)
      (Spike.Lib.A64Consumer.hret_of_run stRet_ok fun σ c hJ => ?_) (fun _ _ h => h.2.1.trans hq)
    · intro k hk; dsimp only [takeNG]; rw [eSite]; revert k; decide
    · dsimp only [takeNG] at hJ ⊢
      rw [(stRet_walk _ _ hJ.2.2).1, hra, Int64.ofBitVec_toBitVec, eSp']; decide
    · dsimp only [takeNG] at hJ ⊢
      rw [(stRet_walk _ _ hJ.2.2).1, hra]; exact Int64.ofBitVec_toBitVec _

end Gen

/-- info: 'Spike.Lib.A64.WakePh.StartTi.take2B_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms take2B_WS

end Spike.Lib.A64.WakePh.StartTi
