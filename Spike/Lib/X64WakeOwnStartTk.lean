/-
**The first `scc_rt_stack_take` call lifted to `ownGXW`** (x86-64; X64-OwnW
lift layer): the call from the first `scc_rt_thread_init`
(returning to its `.x7`, the take's frame `[-200, 8]` off the pool) owns
neither TCB word at any of its states (`Cst L [] []`: no pc of `InA`,
`InT`, `InC`, `InAb`, `%rsp` off the pool), so its node obligations
inside the start's level `StartWf.WS` (`StartTi.takeW_WS`) are inside
`WSX` (`ownGXW`). The nodes mirror `StartTi.takeA_WS` / `takeB_WS`.

- `PT`: a pc of no range, off the take site.
- `takeL`: the take's nodes inside `Lft` (`blkL` / `nodeL0`).
- `takeX`: `TakeW` inside `WS` is inside `WSX` (`TakeW.imp`).

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnLftC
import Spike.Lib.X64WakeStartTiT3

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
open Spike.Lib.X64.WakePh.StartTi
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_lea keep_rmw)
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW StackM stacksA takeNG swpBlk_eq ldnBlk_eq unlBlk_eq nxtBlk_eq)
open Spike.Lib.X64.Flow.Ret0.StackTake
open Spike.Lib.X64.Flow.Ret0.AllocTcb (siAt)
open Spike.Lib (Arena FragS)

/-- **A pc of no range, off the take site.** -/
def PT (q : Nat) : Prop := NoH q ∧ q ≠ 4200277

instance (q : Nat) : Decidable (PT q) := by unfold PT; infer_instance

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -200 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A `leaq L(%rip), %rax` node of the take inside `Lft` (`bb` its code
check, `el` its label's value). -/
local macro "tsiL " bb:term:max el:term:max : tactic =>
  `(tactic| (
    refine nodeL0 hlab hsep ha hW (sz := 7) (cls_off hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $bb) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_lea hc hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG]; rw [$el:term]; decide +kernel))

variable {L : RuntimeLayout} {a : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

set_option maxHeartbeats 3200000 in
/-- **The first take's nodes inside `Lft`**: every state owns neither TCB
word (its pcs off every range, its frame `[-200, 8]` off the pool, `hbd`). -/
theorem takeL (hp : L.prog = wakeCells)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hbd : BandI L R (-200)) (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {M : MachineData → Prop} (q : TakeG)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.Code.Ti.x7L).toBitVec) :
    ∀ i, TakeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F M q i := by
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.X64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  obtain ⟨eFn, eEn, eCls, eDone, eSpin, eLk, eBump, eOk, eTk, eSite, eFull, eX7⟩ := take_labs hlab (L := L)
  have hin := wake_takeIn
  simp only [stackTakeIn, siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bCls⟩, bJ1⟩, sD0⟩, bD7⟩, sD26⟩, bD33⟩, sD52⟩, bD59⟩,
    bSp0⟩, bSwp⟩, bSp14⟩, bLk0⟩, bLdn⟩, bLk7⟩,
    sB0⟩, bB7⟩, bUnl⟩, sB31⟩, bB38⟩, bNxt⟩, bB61⟩, bB108⟩, sOk0⟩, bOk7⟩, bTk⟩, -⟩, bSite⟩, bRet⟩ := hin
  rw [swpBlk_eq] at bSwp; rw [ldnBlk_eq] at bLdn
  rw [unlBlk_eq] at bUnl; rw [nxtBlk_eq] at bNxt; rw [Spike.Lib.X64.Rt.Take.nopBlk_eq] at bSite
  intro i
  cases i <;> dsimp only [TakeW]
  case e =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bE (ofNat_zero' _) stPro_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stPro oE) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eFn]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bEn (ofNat_zero' _) stInit_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stInit oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eEn]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stInit_walk _ _ hJ.2).1, eCls]; decide +kernel
  case cls =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bCls (ofNat_zero' _) stCls_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stCls oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stCls_walk _ _ hJ.2).1, eCls]; decide +kernel
  case j1 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bJ1 rfl stJ1_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stJ1 oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stJ1_walk _ _ hJ.2).1, eDone]; decide +kernel
  case d0 => tsiL sD0 eDone
  case d7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bD7 rfl stFreeN_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stFreeN oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stFreeN_walk _ _ hJ.2.1 hJ.2.2).1, eDone]; decide +kernel
  case d26 => tsiL sD26 eDone
  case d33 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bD33 rfl stFree_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stFree oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stFree_walk _ _ hJ.2).1, eDone]; decide +kernel
  case d52 => tsiL sD52 eDone
  case d59 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bD59 rfl stLock_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stLock oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stLock_walk _ _ hJ.2.1 hJ.2.2).1, eSpin]; decide +kernel
  case sp0 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bSp0 (ofNat_zero' _) stSwp_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stSwp oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eSpin]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSwp_walk _ _ hJ.2).1, eSpin]; decide +kernel
  case swp =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .swp).J σ c →
        bAddr σ.regs .rcx 0 = L.lockA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2.1, hlk]
    refine nodeL0 hlab hsep ha hW (sz := 3) (cls_off hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bSwp) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_xchg hc hd (a := L.lockA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_lock (hFr _ hF)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG, swpPc]; rw [eSpin]; decide +kernel
  case sp14 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bSp14 rfl stSpin_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stSpin oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eSpin]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSpin_walk _ _ hJ.2.1 hJ.2.2).1, eLk]; decide +kernel
  case lk0 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bLk0 (ofNat_zero' _) stLdN_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stLdN oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stLdN_walk _ _ hJ.2).1, eLk]; decide +kernel
  case ldn =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .ldn).J σ c →
        bAddr σ.regs .rcx 0 = L.freeNA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2, hfr]
    refine nodeL0 hlab hsep ha hW (sz := 3) (cls_off hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bLdn) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_ld ⟨by decide, by decide⟩ hc hd (a := L.freeNA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_freeN (hFr _ hF)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG, freeNPc]; rw [eLk]; decide +kernel
  case lk7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bLk7 rfl stEmpty_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stEmpty oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stEmpty_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case b0 => tsiL sB0 eBump
  case b7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bB7 rfl stUnl_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stUnl oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stUnl_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case unl =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .unl).J σ c →
        bAddr σ.regs .rcx 0 = L.lockA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2.1, hlk]
    refine nodeL0 hlab hsep ha hW (sz := 3) (cls_off hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bUnl) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_st hc hd (a := L.lockA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_lock (hFr _ hF)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG, unlPc]; rw [eBump]; decide +kernel
  case b31 => tsiL sB31 eBump
  case b38 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bB38 rfl stAdd_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stAdd oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stAdd_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case nxt =>
    have hA' : ∀ σ c, (takeNG (_root_.Executable.labels L.exe).label q true .nxt).J σ c →
        bAddr σ.regs .rcx 0 = L.nextA := fun σ c hJ => by
      dsimp only [takeNG] at hJ
      simp [bAddr, Reg64s.get64, hJ.2.2.1, hnx]
    refine nodeL0 hlab hsep ha hW (sz := 5) (cls_off hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bNxt) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_rmw hc hd (a := L.nextA)
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ))
        (Spike.Lib.X64.PhRec.rtF_next (hFr _ hF)) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG, nextPc]; rw [eBump]; decide +kernel
  case b61 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bB61 rfl stBnd_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stBnd oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG]; rw [stBnd_run]; dsimp only
      split
      · rw [eFull]; decide +kernel
      · rw [eBump]; decide +kernel
  case b108 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bB108 rfl stJ2_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stJ2 oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stJ2_walk _ _ hJ.2).1, eOk]; decide +kernel
  case ok0 => tsiL sOk0 eOk
  case ok7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bOk7 rfl stOk_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stOk oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eOk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stOk_walk _ _ hJ.2.1 hJ.2.2).1, eTk]; decide +kernel
  case tk =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bTk (ofNat_zero' _) stSite_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stSite oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eTk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSite_walk _ _ hJ.2).1, eTk]; decide +kernel
  case site =>
    refine fun s c hAt => (nodeL0 hlab hsep ha hW (P := NoH) (sz := 1) (cls_off hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) s c hAt).1
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bSite) (ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_nop hc hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG]; rw [eSite]; decide +kernel
  case ret =>
    have eX7' : L.lab Spike.Lib.X64.Rt.Code.Ti.x7L = Int64.ofNat 4199569 := eX7
    refine blkLA hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bRet rfl stRet_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd s h.1) (cls_off hlab hbd) ?_ (soT stRet oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eSite]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢
      rw [(stRet_walk _ _ hJ.2.2).1, hra, Int64.ofBitVec_toBitVec, eX7']; decide +kernel

/-- **`TakeW` inside `WS` is inside `WSX`** at the first take (`takeL`). -/
theorem takeX (hp : L.prog = wakeCells)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hbd : BandI L R (-200)) (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {K : State → State → Prop} {M : MachineData → Prop} (q : TakeG)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.Code.Ti.x7L).toBitVec)
    (h : ∀ i, TakeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M q i) :
    ∀ i, TakeW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M q i := fun i =>
  TakeW.imp (h i) (takeL hp hlab hsite hsep ha hW hbd hR hRlo hhi hFr q hra i) fun _ _ h1 h2 => h2 h1

end Spike.Lib.X64.WakePh.OwnSt

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.takeX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.takeX
