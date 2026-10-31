/-
**wake.w's `scc_rt_stack_take` call inside `W0`, past the free count's
load** (x86-64; twin of `Spike/Lib/A64WakeStartTiT2.lean`): the nodes of
the call from `scc_rt_thread_init` (returning to its `.x7`) off `takeA`
inside the start's level `StartWf.WS`, from their `SFacts` at the first
instance (`takeT`) by `StartTi.blkI_WS` / `nodeI_WS` / `nodeI_WSst` /
`nodeI_WSxadd` / `siteI_WS`, the take's frame `[-200, 8]` off the pool
(`hbd`).

- `takeB_WS`: the nodes past the free count's load inside `WS`.

**Unlike AArch64**: no `P` (`hXs` takes the frame condition alone), no
`hal`; `hRlo : R.lo ≤ -200`, `hhi : 8 ≤ R.hi`, `hbd : BandI L R (-200)`
(A64's `-208`, `0`); the return is to `Code.Ti.x7L` (A64's `.sp0`).
AArch64's `adrp`/`add` label pairs (`.b0`/`.b6`/`.ok0`) are x86-64's single
`leaq L(%rip), %rax` nodes `.b0`/`.b31`/`.ok0` (`keep_lea`); the lock's
release `stlr` (`nodeI_WSstlr`, `keep_stlr`) is a plain `movq %rax,
(%rcx)` (`nodeI_WSst`, `keep_st`), the next offset's `ldaddal`
(`nodeI_WSldop`) is `lock xaddq %rax, (%rcx)` (`nodeI_WSxadd`,
`Tcb2W.keep_rmw`). x86-64's nodes are `.lk7`, `.b7`, `.b38`, `.b61`,
`.b108`, `.ok7` (A64's `.lk2`, `.b2`, `.b8`, `.b12`, `.b21`, `.ok2`).
-/
import Spike.Lib.X64WakeStartTiT1

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
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_lea keep_rmw)
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW StackM stacksA takeNG unlBlk_eq nxtBlk_eq)
open Spike.Lib.X64.Flow.Ret0.StackTake
open Spike.Lib.X64.Flow.Ret0.AllocTcb (siAt)
open Spike.Lib (Arena FragS)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -200 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A `leaq L(%rip), %rax` node of the take (`bb` its code check, `i` its
node, `el` its label's value). -/
local macro "tsi " bb:term:max i:term:max el:term:max : tactic =>
  `(tactic| (
    refine nodeI_WS hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd $bb (by first | rfl | exact ofNat_zero' _) h
      (hP.si _ (by simp [Spike.Lib.X64.Rt.Take.siPcs])).1 (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (by decide +kernel) (fun σ c h => hJ0 $i σ c h nofun)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $bb) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_lea hc hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG]; rw [$el:term]; decide +kernel))

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
  (hbd : BandI L R (-200))

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd

set_option maxHeartbeats 3200000 in
/-- **`scc_rt_stack_take`'s nodes past the free count's load inside `WS`**
(off `takeA`), called from `scc_rt_thread_init` returning to its `.x7`
(`hra`), the lock's and the next offset's words off the arena and not its
counter word (`hoffL`, `hoffX`); `X0` at the take site from its range and
frame (`hXs`).

VACUOUS at root (`hXs` unsatisfiable): superseded by `takeB_WSP`
(`Spike/Lib/X64WakeStartTiP.lean`). -/
theorem takeB_WS (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.Code.Ti.x7L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → X0 s) :
    ∀ i, takeA i = false → TakeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q i := by
  have hT := takeT (a := a) (lbl' := lbl') hp hlo hΛ hlab hs hro hC0 hR hRlo hhi hFr q hq hra hrS hsub hSM
  have hP := takePhW hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
    hs.lock_a hs.next_a
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  obtain ⟨-, -, -, -, -, eLk, eBump, eOk, eTk, eSite, eFull, eX7⟩ := take_labs hlab (L := L)
  have hin := wake_takeIn
  simp only [stackTakeIn, siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, bLk7⟩,
    sB0⟩, bB7⟩, bUnl⟩, sB31⟩, bB38⟩, bNxt⟩, bB61⟩, bB108⟩, sOk0⟩, bOk7⟩, bTk⟩, -⟩, bSite⟩, bRet⟩ := hin
  rw [unlBlk_eq] at bUnl; rw [nxtBlk_eq] at bNxt; rw [Spike.Lib.X64.Rt.Take.nopBlk_eq] at bSite
  have hJ0 : ∀ i, ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true i).J σ c → i ≠ .ret → c = c0 := by
    intro i σ c h hi; cases i <;> first | exact h.1.trans hq | exact (hi rfl).elim
  intro i hi
  have h := hT i
  cases i <;> (try (exfalso; revert hi; decide)) <;> dsimp only [TakeW] at h ⊢
  case lk7 =>
    refine blkI_WS (rl := lockedL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bLk7 rfl stEmpty_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.lk7) ?_ (soT stEmpty oI) (finI hlab hbd (fun σ c hJ => ?_) (soT stEmpty oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stEmpty_noRet) (fun σ c h => hJ0 .lk7 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stEmpty_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case b0 => tsi sB0 .b0 eBump
  case b7 =>
    refine blkI_WS (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bB7 rfl stUnl_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.b7) ?_ (soT stUnl oI) (finI hlab hbd (fun σ c hJ => ?_) (soT stUnl oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stUnl_noRet) (fun σ c h => hJ0 .b7 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stUnl_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case unl =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .unl).J σ c →
        bAddr σ.regs .rcx 0 = L.lockA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2.1, hlk]
    refine nodeI_WSst hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bUnl rfl h hP.unlOk
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [takeNG]; decide) (by decide +kernel)
      (fun σ c h => hJ0 .unl σ c h nofun)
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr _ hF))
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact hoffL)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bUnl) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_st hc hd (a := L.lockA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_lock (hFr _ hF)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG, unlPc]; rw [eBump]; decide +kernel
  case b31 => tsi sB31 .b31 eBump
  case b38 =>
    refine blkI_WS (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bB38 rfl stAdd_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.b38) ?_ (soT stAdd oI) (finI hlab hbd (fun σ c hJ => ?_) (soT stAdd oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stAdd_noRet) (fun σ c h => hJ0 .b38 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stAdd_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case nxt =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .nxt).J σ c →
        bAddr σ.regs .rcx 0 = L.nextA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2.1, hnx]
    refine nodeI_WSxadd hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bNxt rfl h hP.nxtOk
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [takeNG]; decide) (by decide +kernel)
      (fun σ c h => hJ0 .nxt σ c h nofun)
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact Spike.Lib.X64.PhRec.rtF_next (hFr _ hF))
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact hoffX)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bNxt) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_rmw hc hd (a := L.nextA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_next (hFr _ hF)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG, nextPc]; rw [eBump]; decide +kernel
  case b61 =>
    refine blkI_WS (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bB61 rfl stBnd_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.b61) ?_ (soT stBnd oI) (finI hlab hbd (fun σ c hJ => ?_) (soT stBnd oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stBnd_noRet) (fun σ c h => hJ0 .b61 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG]; rw [stBnd_run]; dsimp only
      split
      · rw [eFull]; decide +kernel
      · rw [eBump]; decide +kernel
  case b108 =>
    refine blkI_WS (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bB108 rfl stJ2_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.b108) ?_ (soT stJ2 oI) (finI hlab hbd (fun σ c hJ => ?_) (soT stJ2 oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stJ2_noRet) (fun σ c h => hJ0 .b108 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stJ2_walk _ _ hJ.2).1, eOk]; decide +kernel
  case ok0 => tsi sOk0 .ok0 eOk
  case ok7 =>
    refine blkI_WS (rl := okL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bOk7 rfl stOk_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.ok7) ?_ (soT stOk oI) (finI hlab hbd (fun σ c hJ => ?_) (soT stOk oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stOk_noRet) (fun σ c h => hJ0 .ok7 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eOk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stOk_walk _ _ hJ.2.1 hJ.2.2).1, eTk]; decide +kernel
  case tk =>
    refine blkI_WS (rl := takenL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bTk (ofNat_zero' _) stSite_ok
      hR (by omega) (by omega) h (okPc_of_blkPh hP.tk) ?_ (soT stSite oI) (finI hlab hbd (fun σ c hJ => ?_)
      (soT stSite oI)) (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stSite_noRet)
      (fun σ c h => hJ0 .tk σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eTk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSite_walk _ _ hJ.2).1, eTk]; decide +kernel
  case site =>
    refine siteI_WS hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bSite (ofNat_zero' _) h
      (fun k x hx => hP.siteAb k x hx) (fun s c hAt s' hs => ?_)
      (by dsimp only [takeNG]; rw [eSite]; decide +kernel) (by dsimp only [takeNG]; decide) (by decide +kernel)
      (fun σ c h => hJ0 .site σ c h nofun) hXs
    obtain ⟨he, hn, -, hp', -⟩ := hAt
    have hc := (code_field L.lays rfl (hp ▸ bSite) (ofNat_zero' _) s he hn).cell0 rfl rfl hp'
    have hK : Keep s s' := keep_nop hc hs
    exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
  case ret =>
    have eX7' : L.lab Spike.Lib.X64.Rt.Code.Ti.x7L = Int64.ofNat 4199569 := eX7
    refine blkI_WS (rl := Spike.Lib.X64.Rt.Code.Ti.x7L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bRet rfl
      stRet_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.ret) ?_ (soT stRet oI)
      (finI hlab hbd (fun σ c hJ => ?_) (soT stRet oI)) (by decide +kernel)
      (Spike.Lib.X64Consumer.hret_of_run stRet_ok fun σ c hJ => ?_) (fun _ _ h => h.2.1.trans hq)
    · intro k hk; dsimp only [takeNG]; rw [eSite]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢
      rw [(stRet_walk _ _ hJ.2.2).1, hra, Int64.ofBitVec_toBitVec, eX7']; decide +kernel
    · dsimp only [takeNG] at hJ ⊢
      rw [(stRet_walk _ _ hJ.2.2).1, hra]; exact Int64.ofBitVec_toBitVec _

end Gen

end Spike.Lib.X64.WakePh.StartTi

/-- info: 'Spike.Lib.X64.WakePh.StartTi.takeB_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.takeB_WS
