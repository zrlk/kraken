/-
**hello.w's `scc_rt_stack_take` call inside `W0`, up to the free count's
load** (x86-64; twin of `Spike/Lib/A64HelloStartTiT1.lean`, wake's
`X64WakeStartTiT1` at `SccCode.helloCells`): the nodes `takeA` of the call
from `scc_rt_thread_init` (returning to its `.x8`) inside the start's level
`HelloPh.StartWf.WSH`, from their `SFacts` at the first instance (`takeTH`)
by `StartTi.blkI_WSH` / `nodeI_WSH` / `nodeI_WSxchgH` / `nodeI_WSldH`, the
take's frame `[-200, 8]` off the pool (`hbd`).

- `takeA_WSH`: the nodes up to the free count's load inside `WSH`; a
  stepping stone of the `P` route (`StartTi.takeW_WSPH`,
  `Spike/Lib/X64HelloStartTiP.lean`; wake's `X64WakeStartTiP`). Its nodes
  are off the take site, so it carries no site premise and is not vacuous.

## Differences from the AArch64 version

As wake's x86-64 `StartTiT1`: no `P`, no `hal`; `hRlo : R.lo ≤ -200`,
`hhi : 8 ≤ R.hi`, `hbd : BandI L R (-200)` (A64's `-208`, `0`). AArch64's
`adrp`/`add` label pairs are x86-64's single `leaq L(%rip), %rax` nodes
`.d0`/`.d26`/`.d52` (`keep_lea`); the lock's `swpal` is
`xchgq %rax, (%rcx)` (`nodeI_WSxchgH`, `keep_xchg`), the free count's `ldr`
is `movq (%rcx), %rax` (`nodeI_WSldH`, `keep_ld`). The blocks' pcs are
`cellOff` bytes on and their returns the slot at `%rsp` (`nrB`). The return
is to `Rt.x8L` (A64's `.sp0`; wake's x86-64 `.x7`).
-/
import Spike.Lib.X64HelloStartTiT0

namespace Spike.Lib.X64.HelloPh.StartTi

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
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_lea)
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW StackM stacksA takeNG swpBlk_eq ldnBlk_eq)
open Spike.Lib.X64.Flow.Ret0.StackTake
open Spike.Lib.X64.Flow.Ret0.AllocTcb (siAt)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64.WakePh (inPc Keep keep_pc WSep)
open Spike.Lib.X64.WakePh.StartTi (BandI takeA okPc_of_blkPh nrB keep_xchg keep_ld)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -200 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A `leaq L(%rip), %rax` node of the take at `doneL` (`bb` its code
check, `i` its node). -/
local macro "tsi " bb:term:max i:term:max : tactic =>
  `(tactic| (
    refine nodeI_WSH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd $bb (by first | rfl | exact ofNat_zero' _) h
      (hP.si _ (by simp [Spike.Lib.X64.Rt.Take.siPcs])).1 (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (by decide +kernel) (fun σ c h => hJ0 $i σ c h nofun)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $bb) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_lea hc hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG]; rw [eDone]; decide +kernel))

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
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbd : BandI L R (-200))

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd

set_option maxHeartbeats 3200000 in
/-- **`scc_rt_stack_take`'s nodes up to the free count's load inside
`WSH`** (`takeA`), called from `scc_rt_thread_init` returning to its `.x8`
(`hra`), the lock's word off the arena and not its counter word (`hoffL`). -/
theorem takeA_WSH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.x8L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc) :
    ∀ i, takeA i = true → TakeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q i := by
  have hT := takeTH (a := a) (lbl' := lbl') hp hlo hΛ hlab hs hro hC0 hR hRlo hhi hFr q hq hra hrS hsub hSM
  have hP := takePhH hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
    hs.lock_a hs.next_a
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.X64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  obtain ⟨eFn, eEn, eCls, eDone, eSpin, eLk, -, -, -, -, -, -⟩ := take_labsH hlab (L := L)
  have hin := hello_takeIn
  simp only [stackTakeIn, siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bCls⟩, bJ1⟩, sD0⟩, bD7⟩, sD26⟩, bD33⟩, sD52⟩, bD59⟩,
    bSp0⟩, bSwp⟩, bSp14⟩, bLk0⟩, bLdn⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hin
  rw [swpBlk_eq] at bSwp; rw [ldnBlk_eq] at bLdn
  have hJ0 : ∀ i, ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true i).J σ c → i ≠ .ret → c = c0 := by
    intro i σ c h hi; cases i <;> first | exact h.1.trans hq | exact (hi rfl).elim
  intro i hi
  have h := hT i
  cases i <;> (try (exfalso; revert hi; decide)) <;> dsimp only [TakeW] at h ⊢
  case e =>
    refine blkI_WSH (rl := fnL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bE (ofNat_zero' _) stPro_ok
      hR (by omega) (by omega) h (okPc_of_blkPh hP.e) ?_ (soT stPro oE) (finIH hlab hbd (fun σ c hJ => ?_)
      (soT stPro oE)) (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stPro_noRet) (fun σ c h => hJ0 .e σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eFn]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    refine blkI_WSH (rl := entryL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bEn (ofNat_zero' _) stInit_ok
      hR (by omega) (by omega) h (okPc_of_blkPh hP.entry) ?_ (soT stInit oI) (finIH hlab hbd (fun σ c hJ => ?_)
      (soT stInit oI)) (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stInit_noRet)
      (fun σ c h => hJ0 .entry σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eEn]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stInit_walk _ _ hJ.2).1, eCls]; decide +kernel
  case cls =>
    refine blkI_WSH (rl := clsL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bCls (ofNat_zero' _) stCls_ok
      hR (by omega) (by omega) h (okPc_of_blkPh hP.cls) ?_ (soT stCls oI) (finIH hlab hbd (fun σ c hJ => ?_)
      (soT stCls oI)) (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stCls_noRet)
      (fun σ c h => hJ0 .cls σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stCls_walk _ _ hJ.2).1, eCls]; decide +kernel
  case j1 =>
    refine blkI_WSH (rl := clsL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bJ1 rfl stJ1_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.j1) ?_ (soT stJ1 oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stJ1 oI)) (by decide +kernel)
      (nrB Spike.Lib.X64.Rt.Take.stJ1_noRet) (fun σ c h => hJ0 .j1 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stJ1_walk _ _ hJ.2).1, eDone]; decide +kernel
  case d0 => tsi sD0 .d0
  case d7 =>
    refine blkI_WSH (rl := doneL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bD7 rfl stFreeN_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.d7) ?_ (soT stFreeN oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stFreeN oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stFreeN_noRet) (fun σ c h => hJ0 .d7 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stFreeN_walk _ _ hJ.2.1 hJ.2.2).1, eDone]; decide +kernel
  case d26 => tsi sD26 .d26
  case d33 =>
    refine blkI_WSH (rl := doneL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bD33 rfl stFree_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.d33) ?_ (soT stFree oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stFree oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stFree_noRet) (fun σ c h => hJ0 .d33 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stFree_walk _ _ hJ.2).1, eDone]; decide +kernel
  case d52 => tsi sD52 .d52
  case d59 =>
    refine blkI_WSH (rl := doneL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bD59 rfl stLock_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.d59) ?_ (soT stLock oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stLock oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stLock_noRet) (fun σ c h => hJ0 .d59 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stLock_walk _ _ hJ.2.1 hJ.2.2).1, eSpin]; decide +kernel
  case sp0 =>
    refine blkI_WSH (rl := spinL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bSp0 (ofNat_zero' _) stSwp_ok
      hR (by omega) (by omega) h (okPc_of_blkPh hP.sp0) ?_ (soT stSwp oI) (finIH hlab hbd (fun σ c hJ => ?_)
      (soT stSwp oI)) (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stSwp_noRet)
      (fun σ c h => hJ0 .sp0 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eSpin]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSwp_walk _ _ hJ.2).1, eSpin]; decide +kernel
  case swp =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .swp).J σ c →
        bAddr σ.regs .rcx 0 = L.lockA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2.1, hlk]
    refine nodeI_WSxchgH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bSwp rfl h hP.swpOk
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [takeNG]; decide) (by decide +kernel)
      (fun σ c h => hJ0 .swp σ c h nofun)
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr _ hF))
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact hoffL)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bSwp) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_xchg hc hd (a := L.lockA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_lock (hFr _ hF)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG, swpPc]; rw [eSpin]; decide +kernel
  case sp14 =>
    refine blkI_WSH (rl := spinL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bSp14 rfl stSpin_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.sp14) ?_ (soT stSpin oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stSpin oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stSpin_noRet) (fun σ c h => hJ0 .sp14 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eSpin]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSpin_walk _ _ hJ.2.1 hJ.2.2).1, eLk]; decide +kernel
  case lk0 =>
    refine blkI_WSH (rl := lockedL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bLk0 (ofNat_zero' _) stLdN_ok
      hR (by omega) (by omega) h (okPc_of_blkPh hP.lk0) ?_ (soT stLdN oI) (finIH hlab hbd (fun σ c hJ => ?_)
      (soT stLdN oI)) (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stLdN_noRet)
      (fun σ c h => hJ0 .lk0 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stLdN_walk _ _ hJ.2).1, eLk]; decide +kernel
  case ldn =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .ldn).J σ c →
        bAddr σ.regs .rcx 0 = L.freeNA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2, hfr]
    refine nodeI_WSldH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bLdn rfl h hP.ldnOk
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [takeNG]; decide) (by decide +kernel)
      (fun σ c h => hJ0 .ldn σ c h nofun)
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact Spike.Lib.X64.PhRec.rtF_freeN (hFr _ hF))
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bLdn) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_ld ⟨by decide, by decide⟩ hc hd (a := L.freeNA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_freeN (hFr _ hF)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG, freeNPc]; rw [eLk]; decide +kernel

end Gen

end Spike.Lib.X64.HelloPh.StartTi

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.takeA_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.takeA_WSH
