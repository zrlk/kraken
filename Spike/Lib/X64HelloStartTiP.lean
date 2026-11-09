/-
**hello.w's first `scc_rt_thread_init` call inside `W0`, with the take
site's frame condition also `P`** (x86-64; twin of `X64WakeStartTiP` at
`SccCode.helloCells`, the return point `.x8`; the `P` of
`Spike/Lib/A64HelloStartTiT2.lean`, `…T3.lean`, `…W.lean`): the hello
start's `scc_rt_stack_take` and `scc_rt_thread_init` nodes inside
`StartWf.WSH` with `X0` at the take site from its range, frame condition
**and `P`** (`hXs`), concluding `Rt.TakeWP … P` / `Rt.TiWAtP … x8L P`
(`Spike/Lib/Rt/X64SegsA.lean`).

As on wake.w, a `P`-free producer's `hXs` (`F s.st.1 → X0 s` at the site) is
not satisfiable at the root: there `X0` asks `¬ StackM rS` at the site, and
the take keeps `F` (`takeMem` makes `StackM rS` true). So the `P`-free
twins of AArch64's `takeB_WSH`, `takeW_WSH`, `startTi_WSH` are not stated;
only these carry the root's `P := ¬ StackM rS0` to the site.

- `ti_labsH`: `scc_rt_thread_init`'s labels at hello's canonical base.
- `takeB_WSnsH`, `startTi_WSncH`: the nodes off the site / off the call,
  with no site premise (stepping stones of the `P` twins, not vacuous).
- `takeB_WSPH`, `takeW_WSPH`, `startTi_WSPH`: the `P` twins.

## Differences from the AArch64 version

AArch64's `TakeW … P` and `TiW … P` carry `P` in place; on x86-64 `P` sits
in `Rt.TakeWP` / `Rt.TiWAtP`, the x86-64 `TakeW` / `TiW` having none (as
`X64WakeStartTiP`). The rest as wake's x86-64 `StartTiP` / `StartTiW`: no
`hal`; frames' high end `8`; `hRlo : R.lo ≤ -248` for the call, `-200` for
the take; `cellOff` / `z`-byte offsets, `Keep` on `%rsp`/`%rbp`. Specific
to hello: `scc_rt_thread_init` returns to `.x8` (`Rt.x8L`; wake's `.x7`,
A64's `.sp0`), so its obligations are `Rt.TiWAt … x8L` from `Rt.tiWAt_gen`
at `x8L` (wake: `Ret0.TiW` from `Rt.tiW_gen` and `tiWAt_x7`), its nodes
`Rt.tiNAt … x8L` / `tiX7At`, its code check `threadInitInAt … x8L`
(`HelloPh.hello_tiIn`); hello's addresses are wake's `+ 37`
(`scc_rt_thread_init` at `4199582`, `.x8` at `4199606`).
-/
import Spike.Lib.X64HelloStartTiT1
import Spike.Lib.X64WakeStartTiP

namespace Spike.Lib.X64.HelloPh.StartTi

section Labs

open Scc.Sem.X64 (codeLabel)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (helloCells)

variable {L : Spike.Lib.X64.Rt.RuntimeLayout}

/-- `scc_rt_thread_init`'s labels at hello's canonical base. -/
theorem ti_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.ThreadInit.fnL = Int64.ofNat 4199582 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.ThreadInit.entryL = Int64.ofNat 4199594 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

end Labs

section TakeBP

open Spike.Lib.X64.WakePh (inPc Keep keep_pc WSep keep_nop)
open Spike.Lib.X64.WakePh.StartTi (BandI takeA okPc_of_blkPh nrB keep_xchg keep_ld keep_st bandI_mono bandI_callee)
open Spike.Lib.X64.HelloPh.Ti2 (PcIH)

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
    refine nodeI_WSH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd $bb (by first | rfl | exact ofNat_zero' _) h
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
/-- **`takeB_WS` off the take site, with no site premise**: the nodes
past the free count's load (off `takeA`) other than `.site`, inside `WSH`. -/
theorem takeB_WSnsH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.x8L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc) :
    ∀ i, takeA i = false → i ≠ .site → TakeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q i := by
  have hT := takeTH (a := a) (lbl' := lbl') hp hlo hΛ hlab hs hro hC0 hR hRlo hhi hFr q hq hra hrS hsub hSM
  have hP := takePhH hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
    hs.lock_a hs.next_a
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  obtain ⟨-, -, -, -, -, eLk, eBump, eOk, eTk, eSite, eFull, eX8⟩ := take_labsH hlab (L := L)
  have hin := hello_takeIn
  simp only [stackTakeIn, siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, bLk7⟩,
    sB0⟩, bB7⟩, bUnl⟩, sB31⟩, bB38⟩, bNxt⟩, bB61⟩, bB108⟩, sOk0⟩, bOk7⟩, bTk⟩, -⟩, bSite⟩, bRet⟩ := hin
  rw [unlBlk_eq] at bUnl; rw [nxtBlk_eq] at bNxt; rw [Spike.Lib.X64.Rt.Take.nopBlk_eq] at bSite
  have hJ0 : ∀ i, ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true i).J σ c → i ≠ .ret → c = c0 := by
    intro i σ c h hi; cases i <;> first | exact h.1.trans hq | exact (hi rfl).elim
  intro i hi hsi
  have h := hT i
  cases i <;> (try (exfalso; revert hi; decide)) <;> dsimp only [TakeW] at h ⊢
  case lk7 =>
    refine blkI_WSH (rl := lockedL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bLk7 rfl stEmpty_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.lk7) ?_ (soT stEmpty oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stEmpty oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stEmpty_noRet) (fun σ c h => hJ0 .lk7 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stEmpty_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case b0 => tsi sB0 .b0 eBump
  case b7 =>
    refine blkI_WSH (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bB7 rfl stUnl_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.b7) ?_ (soT stUnl oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stUnl oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stUnl_noRet) (fun σ c h => hJ0 .b7 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stUnl_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case unl =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .unl).J σ c →
        bAddr σ.regs .rcx 0 = L.lockA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2.1, hlk]
    refine nodeI_WSstH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bUnl rfl h hP.unlOk
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
    refine blkI_WSH (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bB38 rfl stAdd_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.b38) ?_ (soT stAdd oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stAdd oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stAdd_noRet) (fun σ c h => hJ0 .b38 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stAdd_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case nxt =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .nxt).J σ c →
        bAddr σ.regs .rcx 0 = L.nextA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2.1, hnx]
    refine nodeI_WSxaddH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bNxt rfl h hP.nxtOk
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
    refine blkI_WSH (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bB61 rfl stBnd_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.b61) ?_ (soT stBnd oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stBnd oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stBnd_noRet) (fun σ c h => hJ0 .b61 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG]; rw [stBnd_run]; dsimp only
      split
      · rw [eFull]; decide +kernel
      · rw [eBump]; decide +kernel
  case b108 =>
    refine blkI_WSH (rl := bumpL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bB108 rfl stJ2_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.b108) ?_ (soT stJ2 oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stJ2 oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stJ2_noRet) (fun σ c h => hJ0 .b108 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stJ2_walk _ _ hJ.2).1, eOk]; decide +kernel
  case ok0 => tsi sOk0 .ok0 eOk
  case ok7 =>
    refine blkI_WSH (rl := okL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bOk7 rfl stOk_ok hR (by omega)
      (by omega) h (okPc_of_blkPh hP.ok7) ?_ (soT stOk oI) (finIH hlab hbd (fun σ c hJ => ?_) (soT stOk oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stOk_noRet) (fun σ c h => hJ0 .ok7 σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eOk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stOk_walk _ _ hJ.2.1 hJ.2.2).1, eTk]; decide +kernel
  case tk =>
    refine blkI_WSH (rl := takenL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bTk (ofNat_zero' _) stSite_ok
      hR (by omega) (by omega) h (okPc_of_blkPh hP.tk) ?_ (soT stSite oI) (finIH hlab hbd (fun σ c hJ => ?_)
      (soT stSite oI)) (by decide +kernel) (nrB Spike.Lib.X64.Rt.Take.stSite_noRet)
      (fun σ c h => hJ0 .tk σ c h nofun)
    · intro k hk; dsimp only [takeNG]; rw [eTk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSite_walk _ _ hJ.2).1, eTk]; decide +kernel
  case site => exact absurd rfl hsi
  case ret =>
    have eX8' : L.lab Spike.Lib.X64.Rt.x8L = Int64.ofNat 4199606 := eX8
    refine blkI_WSHA (rl := Spike.Lib.X64.Rt.x8L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bRet rfl
      stRet_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.ret) ?_ (soT stRet oI)
      (finIH hlab hbd (fun σ c hJ => ?_) (soT stRet oI)) (by decide +kernel)
      (Spike.Lib.X64Consumer.hret_of_run stRet_ok fun σ c hJ => ?_) (fun _ _ h => h.2.1.trans hq)
    · intro k hk; dsimp only [takeNG]; rw [eSite]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢
      rw [(stRet_walk _ _ hJ.2.2).1, hra, Int64.ofBitVec_toBitVec, eX8']; decide +kernel
    · dsimp only [takeNG] at hJ ⊢
      rw [(stRet_walk _ _ hJ.2.2).1, hra]; exact Int64.ofBitVec_toBitVec _

set_option maxHeartbeats 3200000 in
/-- **`takeB_WS` with the take site's frame condition also `P`**
(`Rt.TakeWP`; AArch64's `takeB_WS`): `X0` at the site from its range, frame
condition and `P` (`hXs`); off the site, `takeB_WSnsH`. -/
theorem takeB_WSPH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.x8L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    {P : MachineData → Prop}
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 → X0 s) :
    ∀ i, takeA i = false → Spike.Lib.X64.Rt.TakeWP (WSH L a ar p Dt Cl Ctx lbl lsize frM X0)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F (StackM rS) q P i := by
  intro i hi
  by_cases hsi : i = .site
  case neg =>
    rw [Spike.Lib.X64.Rt.takeWP_eq hsi]
    exact takeB_WSnsH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd hΛ hs hro hC0 hR hRlo hhi hFr q hq hra hrS hsub hSM
      hoffL hoffX i hi hsi
  subst hsi
  have hT := takeTH (a := a) (lbl' := lbl') hp hlo hΛ hlab hs hro hC0 hR hRlo hhi hFr q hq hra hrS hsub hSM
  have hP := takePhH hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
    hs.lock_a hs.next_a
  obtain ⟨-, -, -, -, -, -, -, -, -, eSite, -, -⟩ := take_labsH hlab (L := L)
  have hin := hello_takeIn
  simp only [stackTakeIn, siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, bLk7⟩,
    sB0⟩, bB7⟩, bUnl⟩, sB31⟩, bB38⟩, bNxt⟩, bB61⟩, bB108⟩, sOk0⟩, bOk7⟩, bTk⟩, -⟩, bSite⟩, bRet⟩ := hin
  rw [Spike.Lib.X64.Rt.Take.nopBlk_eq] at bSite
  have hJ0 : ∀ i, ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true i).J σ c → i ≠ .ret → c = c0 := by
    intro i σ c h hi; cases i <;> first | exact h.1.trans hq | exact (hi rfl).elim
  have h := hT .site
  dsimp only [TakeW] at h
  show ∀ s c, _ → _
  refine siteI_WSH (F := fun m => F m ∧ P m) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd bSite (ofNat_zero' _)
    (fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, hD.1, hJ⟩)
    (fun k x hx => hP.siteAb k x hx) (fun s c hAt s' hs => ?_)
    (by dsimp only [takeNG]; rw [eSite]; decide +kernel) (by dsimp only [takeNG]; decide) (by decide +kernel)
    (fun σ c h => hJ0 .site σ c h nofun) (fun s hs hr hFP => hXs s hs hr hFP.1 hFP.2)
  obtain ⟨he, hn, -, hp', -⟩ := hAt
  have hc := (code_field L.lays rfl (hp ▸ bSite) (ofNat_zero' _) s he hn).cell0 rfl rfl hp'
  have hK : Keep s s' := keep_nop hc hs
  exact ⟨hK, by rw [keep_pc hc hK, hp']⟩

end Gen

end TakeBP

section TakeWP

open Spike.Lib.X64.WakePh (inPc Keep keep_pc WSep keep_nop)
open Spike.Lib.X64.WakePh.StartTi (BandI takeA okPc_of_blkPh nrB keep_xchg keep_ld keep_st bandI_mono bandI_callee)
open Spike.Lib.X64.HelloPh.Ti2 (PcIH)

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.HelloPh.StartWf (WSH)
open Spike.Lib.X64.Flow.Ret0 (TakeG TakeW StackM stacksA)
open Spike.Lib (Arena FragS)

variable {L : RuntimeLayout}

set_option maxHeartbeats 400000 in
/-- **`takeW_WS` with the take site's frame condition also `P`**
(`Rt.TakeWP`; AArch64's `takeW_WS`): `takeA_WSH` (`TakeWP.of_takeW`) and
`takeB_WSPH`. -/
theorem takeW_WSPH {a : BitVec 64} {rS : Range} {lbl' : Lbl} {R : Spike.Lib.Region} {F : MachineData → Prop}
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
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.x8L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    {P : MachineData → Prop}
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 → X0 s) :
    ∀ i, Spike.Lib.X64.Rt.TakeWP (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q P i := by
  intro i
  cases h : takeA i
  · exact takeB_WSPH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd hΛ hs hro hC0 hR hRlo hhi hFr q hq hra hrS hsub hSM
      hoffL hoffX hXs i h
  · exact .of_takeW <| takeA_WSH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd hΛ hs hro hC0 hR hRlo hhi hFr q hq hra hrS hsub
      hSM hoffL i h

end TakeWP

section StartTiP

open Spike.Lib.X64.WakePh (inPc Keep keep_pc WSep keep_nop)
open Spike.Lib.X64.WakePh.StartTi (BandI takeA okPc_of_blkPh nrB keep_xchg keep_ld keep_st bandI_mono bandI_callee)
open Spike.Lib.X64.HelloPh.Ti2 (PcIH)


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
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib.X64.HelloPh.WcW (freeNH freeAtH cvH inCvH goodW_of_freeNH freeAt_labH)
open Spike.Lib.X64.Flow.Ret0 (TI TiG tiTake tiCall tiCall_ok StackM stacksA pinA bAddr_rcx
  storeBlks_eq)
open Spike.Lib.X64.Rt (TiWAt tiNAt tiX7At x8L)
open Spike.Lib.X64.Flow.Ret0.ThreadInit
open Spike.Lib (Arena FragS)


/-- `hso` of a block of `scc_rt_thread_init` at offsets `o`, decided. -/
local macro "soI " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -48 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A store of TCB field `j` (`movq %rax, k(%rcx)`, `z` bytes at
`.x7 + off`, block `b`) inside `WSH`. -/
local macro "tstW " b:term:max x:term:max j:term:max k:term:max z:term:max off:term:max : tactic =>
  `(tactic| focus
    have ha : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb := by
      simp [Spike.Lib.X64.Rt.Ti.tiAddrs]
    have hA' : ∀ σ c, (tiNAt (_root_.Executable.labels L.exe).label q x8L $x).J σ c →
        bAddr σ.regs .rcx $k = q.tcb + BitVec.ofNat 64 (8 * $j) := fun σ c hJ => by
      dsimp only [tiNAt] at hJ
      rw [bAddr_rcx hJ.2.2.2]; exact congrArg (q.tcb + ·) (by decide)
    refine nodeI_WSstH (z := $z) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 $b rfl h
      (hP.st (L.lab x8L + Int64.ofNat $off, $z) (by simp [Spike.Lib.X64.Rt.Ti.stPcsAt])).1
      (fun s c hAt s' hs => ?_) ?_ (by dsimp only [tiNAt]; decide) (by decide +kernel) (fun σ c h => h.1.trans hq)
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact Spike.Lib.X64.PhRec.rtF_tcb (hFr _ hF.1) (hfld _ ha))
      (fun σ c m hJ hF => by rw [hA' σ c hJ]; exact hoffT _ ha)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $b) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_st hc hd (a := q.tcb + BitVec.ofNat 64 (8 * $j))
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_tcb (hFr _ hF.1) (hfld _ ha)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tiNAt]; rw [eX8]; decide +kernel)

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
  (hbdI : BandI L R (-248))

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbdI

set_option maxHeartbeats 3200000 in
set_option maxHeartbeats 3200000 in
/-- **`startTi_WS` off the take's call, with no site premise**: the
nodes of `scc_rt_thread_init` other than `.call`, inside `WSH`. -/
theorem startTi_WSncH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TiG) (hq : q.c0 = c0)
    (htcb : q.tcb = pinA L.lab + 0#64 + 8#64)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hSMt : Spike.Lib.X64.FStable (R.callee (-48 - 0) (-200) 8) (StackM rS))
    (hoffT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb,
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc) :
    ∀ i, i ≠ .call → TiWAt (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      (StackM rS) q x8L i := by
  have hfld : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∃ j < 7, b = L.pinA + BitVec.ofNat 64 (8 * j) :=
    fun _ hb => Spike.Lib.X64.Rt.StartU.tcb_fld (htcb ▸ hb)
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.X64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  have hT := Spike.Lib.X64.Rt.tiWAt_gen (x := x8L) (rS := rS) (lbl := lbl') (instOkHS (a := a) (rS := rS) hp hlo hlab)
    (fun _ => rfl) (hp ▸ hello_tiIn) hC0 hR hRlo hhi q hq hra (tiPhH hΛ hlab)
    (fun _ hb => Spike.Lib.X64.PhRec.mapped_tcb (hfld _ hb))
    (fun _ hb m hm => Spike.Lib.X64.PhRec.rtF_tcb (hFr m hm) (hfld _ hb))
    (fun _ hb => Spike.Lib.X64.WakePh.tcb_not_ownW hs (hfld _ hb)) hsub hSM hSMt (hp ▸ hello_takeIn)
    (takePhH hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
      hs.lock_a hs.next_a)
    (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
    (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
    (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
    (fun m hm => by rw [hlk]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact Spike.Lib.X64.PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact Spike.Lib.X64.PhRec.rtF_next (hFr m hm)) hrS hro
  have hP := tiPhH (L := L) hΛ hlab
  have hbd48 : BandI L R (-48) := bandI_mono hbdI (by decide)
  obtain ⟨eFn, eEn⟩ := ti_labsH hlab (L := L)
  obtain ⟨eT, -, -, -, -, -, -, -, -, -, -, eX8⟩ := take_labsH hlab (L := L)
  have hin := hello_tiIn
  simp only [threadInitInAt, storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bC⟩, -⟩, bSp⟩, bF1⟩, bF2⟩, bF3⟩, bF4⟩, bF5⟩, bRet⟩,
    bS0, bS1, bS2, bS3, bS4, bS5⟩ := hin
  rw [show callBlk = tiCall from rfl] at bC
  intro i hic
  have h := hT i
  cases i <;> dsimp only [TiWAt] at h ⊢
  case e =>
    refine blkI_WSH (rl := fnL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bE (ofNat_zero' _)
      tiPro_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.e) ?_ (soI tiPro oE)
      (finIH hlab hbd48 (fun σ c hJ => ?_) (soI tiPro oE)) (by decide +kernel)
      (nrB Spike.Lib.X64.Rt.Ti.tiPro_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiNAt]; rw [eFn]; revert k; decide +kernel
    · dsimp only [tiNAt] at hJ ⊢; rw [(tiPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    refine blkI_WSH (rl := entryL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bEn (ofNat_zero' _)
      tiArg_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.entry) ?_ (soI tiArg oI)
      (finIH hlab hbd48 (fun σ c hJ => ?_) (soI tiArg oI)) (by decide +kernel)
      (nrB Spike.Lib.X64.Rt.Ti.tiArg_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiNAt]; rw [eEn]; revert k; decide +kernel
    · dsimp only [tiNAt] at hJ ⊢; rw [(tiArg_walk _ _ hJ.2).1, eEn]; decide +kernel
  case c7 =>
    refine blkI_WSH (rl := entryL) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bC rfl
      tiCall_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.c7) ?_ (soI tiCall oI)
      (finIH hlab hbd48 (fun σ c hJ => ?_) (soI tiCall oI)) (by decide +kernel)
      (nrB Spike.Lib.X64.Rt.Ti.tiCall_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiNAt]; rw [eEn]; revert k; decide +kernel
    · dsimp only [tiNAt]; rw [Spike.Lib.X64.Flow.Ret0.tiCall_run]
      show PcIH ((_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.StackTake.fnL); rw [eT]; decide +kernel
  case call => exact absurd rfl hic
  case x7 =>
    refine blkI_WSH (rl := x8L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bSp (ofNat_zero' _)
      tiSp_ok hR (by omega) (by omega) h (okPc_of_blkPh hP.x7) ?_ (soI tiSp oI)
      (finIH hlab hbd48 (fun σ c hJ => ?_) (soI tiSp oI)) (by decide +kernel)
      (nrB Spike.Lib.X64.Rt.Ti.tiSp_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiX7At]; rw [eX8]; revert k; decide +kernel
    · dsimp only [tiX7At, tiNAt] at hJ ⊢; rw [(tiSp_walk _ _ hJ.2.1 hJ.2.2).1, eX8]; decide +kernel
  case st0 => tstW bS0 TI.st0 0 0 3 48
  case f1 =>
    refine blkI_WSH (rl := x8L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF1 rfl tiF1_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f1) ?_ (soI tiF1 oI) (finIH hlab hbd48 (fun σ c hJ => ?_) (soI tiF1 oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiF1_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiNAt]; rw [eX8]; revert k; decide +kernel
    · dsimp only [tiNAt] at hJ ⊢; rw [(tiF1_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st1 => tstW bS1 TI.st1 1 8 4 59
  case f2 =>
    refine blkI_WSH (rl := x8L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF2 rfl tiZ_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f2) ?_ (soI tiZ oI) (finIH hlab hbd48 (fun σ c hJ => ?_) (soI tiZ oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiZ_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiNAt]; rw [eX8]; revert k; decide +kernel
    · dsimp only [tiNAt] at hJ ⊢; rw [(tiZ_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st2 => tstW bS2 TI.st2 2 16 4 74
  case f3 =>
    refine blkI_WSH (rl := x8L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF3 rfl tiZ_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f3) ?_ (soI tiZ oI) (finIH hlab hbd48 (fun σ c hJ => ?_) (soI tiZ oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiZ_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiNAt]; rw [eX8]; revert k; decide +kernel
    · dsimp only [tiNAt] at hJ ⊢; rw [(tiZ_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st3 => tstW bS3 TI.st3 3 24 4 89
  case f4 =>
    refine blkI_WSH (rl := x8L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF4 rfl tiF4_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f4) ?_ (soI tiF4 oI) (finIH hlab hbd48 (fun σ c hJ => ?_) (soI tiF4 oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiF4_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiNAt]; rw [eX8]; revert k; decide +kernel
    · dsimp only [tiNAt] at hJ ⊢; rw [(tiF4_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st4 => tstW bS4 TI.st4 4 32 4 101
  case f5 =>
    refine blkI_WSH (rl := x8L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bF5 rfl tiF5_ok hR (by omega) (by omega)
      h (okPc_of_blkPh hP.f5) ?_ (soI tiF5 oI) (finIH hlab hbd48 (fun σ c hJ => ?_) (soI tiF5 oI))
      (by decide +kernel) (nrB Spike.Lib.X64.Rt.Ti.tiF5_noRet) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiNAt]; rw [eX8]; revert k; decide +kernel
    · dsimp only [tiNAt] at hJ ⊢; rw [(tiF5_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st5 => tstW bS5 TI.st5 5 40 4 113
  case ret =>
    refine blkI_WSHA (rl := Spike.Lib.X64.Flow.Ret0.x1L) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd48 bRet rfl tiRet_ok
      hR (by omega) (by omega) h (okPc_of_blkPh hP.ret) ?_ (soI tiRet oI) (fun σ c hJ s m _ _ _ hs' => ?_)
      (by decide +kernel) (Spike.Lib.X64Consumer.hret_of_run tiRet_ok fun σ c hJ => ?_) (fun σ c h => h.1.trans hq)
    · intro k hk; dsimp only [tiNAt]; rw [eX8]; revert k; decide +kernel
    · dsimp only [tiNAt] at hJ hs'
      rw [(tiRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec] at hs'
      exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact freeAt_labH hlab (by wsfreeH_dec))
    · dsimp only [tiNAt] at hJ ⊢
      rw [(tiRet_walk _ _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _

set_option maxHeartbeats 3200000 in
/-- **`startTi_WS` with the take site's frame condition also `P`**
(`Rt.TiWAtP` at `.x7`; AArch64's `startTi_WS`): at the call `takeW_WSPH`,
off it `startTi_WSncH` (`tiWAt_x7`). -/
theorem startTi_WSPH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
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
    {P : MachineData → Prop}
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 → X0 s) :
    ∀ i, Spike.Lib.X64.Rt.TiWAtP (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
      L.endPc R F (StackM rS) q x8L P i := by
  intro i
  by_cases hic : i = .call
  case neg =>
    rw [Spike.Lib.X64.Rt.tiWAtP_eq hic]
    exact startTi_WSncH hp hlo hlab hsite hcl hc0 hpl0 hX0 hbdI hΛ hs hro hC0 hR hRlo hhi hFr q hq htcb hra hrS hsub
      hSM hSMt hoffT i hic
  subst hic
  intro g hg j
  have hR' := Spike.Lib.Region.callee_ok (kc := -48 - 0) (lo' := -200) (hi' := 8) hR (by omega) (by decide)
    (by omega) (by omega)
  exact takeW_WSPH hp hlo hlab hsite hcl hc0 hpl0 hX0
    (bandI_callee hbdI (by show (-248 : Int) ≤ -48 - 0 + -200; omega) (by decide)) hΛ hs hro hC0 hR'
    (by show (-200 : Int) ≤ -200; omega) (by show (8 : Int) ≤ 8; omega) hFr (tiTake q g) hq hg hrS hsub hSMt
    hoffL hoffX hXs j

end Gen

end StartTiP

end Spike.Lib.X64.HelloPh.StartTi

-- No axioms beyond Lean's.
/-- info: 'Spike.Lib.X64.HelloPh.StartTi.takeB_WSnsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.takeB_WSnsH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.takeB_WSPH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.takeB_WSPH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.takeW_WSPH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.takeW_WSPH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.startTi_WSncH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.startTi_WSncH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.startTi_WSPH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.startTi_WSPH
