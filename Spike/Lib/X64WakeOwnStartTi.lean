/-
**The first `scc_rt_thread_init` call lifted to `ownGXW`** (x86-64; X64-OwnW
lift layer): the call from `scc_rt_start` (returning to `.x1`,
its frames `[-248, 8]` off the pool) on main's TCB (`q.tcb = tcbM`). Before
the take store (`.st0`, `.x7 + 48`) no state owns either TCB word
(`Cst L [] []`); `.st0` takes main's word (`W0.takeS`, as
`nodeW_st0X`); from `.x7 + 51` on (`InT`) and at the return to `.x1`
(`InA`) states own main's word only (`Cst L (tM L) []`), the field stores
`st1`–`st5` writing the TCB's other words (`hw_stM`). So `StartTi.startTi_WS`'s
obligations inside `StartWf.WS` are inside `WSX` (`ownGXW`). The nodes
mirror `StartTi.startTi_WS`.

- `QM`, `PM`: main's word's classes (`InA`/`InT`, off `InC`/`InAb`; and
  off the take site).
- `hw_stM`: a plain store off `tcbM` writes no word of `tM`.
- `st0L`: `.st0` inside `Lft` (main takes its word).
- `tiL`: the call's nodes inside `Lft`; `tiX`: `TiWAt` inside `WS` is inside
  `WSX` (`TiWAt.imp`).

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnStartTk
import Spike.Lib.X64WakeStartTiT3

namespace Spike.Lib.X64.WakePh.OwnSt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 (writeTree_mono)
open Scc.Cert.Rt.X64 (code_field codeT_eq)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64 (ND bAddr NodeW At stDir mB)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.WakePh.StartTi
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib.X64ConsumerA (rsp_of_abs)
open Spike.Lib.X64.Flow.Ret0 (TI TiG tiTake tiCall tiCall_ok StackM stacksA pinA bAddr_rcx storeBlks_eq)
open Spike.Lib.X64.Flow.Ret0.ThreadInit
open Spike.Lib (Arena FragS)

/-- **Main's word's class**: `InA` or `InT`, off `InC` and `InAb`. -/
def QM (q : Nat) : Prop := (InA q ∨ InT q) ∧ ¬ InC q ∧ ¬ InAb q

instance (q : Nat) : Decidable (QM q) := by unfold QM; infer_instance

/-- `QM` off the take site. -/
def PM (q : Nat) : Prop := QM q ∧ q ≠ 4200277

instance (q : Nat) : Decidable (PM q) := by unfold PM; infer_instance

/-- `hso` of a block of `scc_rt_thread_init` at offsets `o`, decided. -/
local macro "soI " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -48 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

variable {L : RuntimeLayout} {a : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

/-- **A plain store off `tcbM` writes no word of `tM`.** -/
theorem hw_stM {n : ND} {b r : Reg64} {i : Int64} {z : Nat} {A : BitVec 64}
    (h : ∀ s c, At L.exe L.endPc R F n s c → Kraken.Promising.Lower.X64.CellAt s (stDir b i r) z ∧
      Kraken.Promising.Lower.X64.eaddr s z (mB b i) = A ∧ Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {})
    (hA : A ≠ tcbM L) :
    ∀ s c, At L.exe L.endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ tM L) ∧ ∀ w, (l, w) ∉ ([] : List (Loc × Val))) tree := by
  intro s c hAt _ tree he
  obtain ⟨hc, ha, hd, hdc⟩ := h s c hAt
  rw [Kraken.Promising.Lower.X64.exec_store_agrees hc ha hd (Spike.Lib.X64.agrees_of_decls hdc _ _)] at he
  cases he
  refine ⟨⟨fun w hw => ?_, fun w hw => by simp at hw⟩, fun _ => trivial⟩
  simp only [tM, List.mem_singleton, Prod.mk.injEq] at hw
  obtain ⟨hl, -⟩ := hw
  injection hl with h1
  exact hA h1

section L

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

/-- **`.st0` inside `Lft`**: main takes its TCB word (`W0.takeS`, as
`nodeW_st0X`); the worker's word is owned at neither the store's state nor
its successor (both off the pool). -/
theorem st0L {q : TiG} (htcb : q.tcb = tcbM L) (hun : ∀ m, F m → Mem.loadInt m.dmem (tcbM L) 8 = none)
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-40)).toNat ∧
      (R.addr (-40)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    NodeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F
      (Spike.Lib.X64.Rt.tiNAt L.lab q Spike.Lib.X64.Flow.Ret0.ThreadInit.x7L .st0) := by
  intro s c hAt
  refine ⟨fun hws => ?_, fun _ h => h⟩
  obtain ⟨hpc', hc, ha'⟩ := st0_at hp hlab hAt
  rw [htcb] at ha'
  obtain ⟨-, -, hdc, -, σ, hA, hD, hJ⟩ := hAt
  have hex := Kraken.Promising.Lower.X64.exec_store_agrees hc ha' (hun _ hD)
    (Spike.Lib.X64.agrees_of_decls hdc _ _)
  have hV : (s.st.1.regs.get (.low .rax .W64)).setWidth 128 = (tcbM L).setWidth 128 := by
    rw [Spike.Lib.X64.Reg64s.get_low64, hA.regs, Reg64s.get64_rax, hJ.2.2.1, htcb]
  rw [hV] at hex
  have hsp := rsp_of_abs hA
  dsimp only [Spike.Lib.X64.Rt.tiNAt] at hsp
  have hnp : ¬ spPool L s := by unfold spPool; rw [hsp]; exact hoff
  have hc0 : Cst L [] [] s := cst_off hlab hnp (by unfold pcOf; rw [hpc']; decide)
  have hpc1 : pcOf (Kraken.Promising.Lower.X64.after s 3 s.st.1) = 4199620 := by
    show (s.st.2 + Int64.ofNat 3).toBitVec.toNat = _; rw [hpc']; decide
  have hc1 : Cst L (tM L) [] (Kraken.Promising.Lower.X64.after s 3 s.st.1) :=
    cst_offM hlab hnp (by rw [hpc1]; decide)
  have hsys : abi.atSys s = false := atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  have htk : ∀ a', (Spike.Lib.X64.PhRec.μ L).site .take = some a' → pcOf s ≠ a' := by
    intro a' ha2 hpcs
    rw [hsite] at ha2
    cases ha2
    unfold pcOf at hpcs
    rw [hpc', siteV hlab] at hpcs
    exact absurd hpcs (by decide)
  have h1 := Spike.Lib.X64.WakeWf.W0.takeS (ownS := ownS L) hws hex rfl hc0.1 hc1.1 (tcbM_notG hsep ha s) hsys htk
  refine Spike.Lib.X64.WakeWf.W0.appendS (ownS := ownSW L) (own := ownGX L a) h1 ⟨?_, ?_, ownSW_disj hW⟩
  · intro s' hs'
    rcases hs' with ⟨-, tree, htr, hl⟩ | ⟨hs2, -⟩ | ⟨a', ha2, hpcs, -⟩
    · rw [hex] at htr
      cases htr
      obtain ⟨b, rfl⟩ := hl
      rw [hc1.2, hc0.2]
    · rw [hsys] at hs2; cases hs2
    · exact absurd hpcs (htk a' ha2)
  · intro _ tree _
    rw [hc0.2]
    exact writeTree_mono (fun _ _ _ w h => by simp at h) (Spike.Lib.Consumer1.writeTree_true tree)

set_option hygiene false in
/-- A store of TCB field `j` (`movq %rax, k(%rcx)`, `z` bytes, block `b`)
inside `Lft`. -/
local macro "tstL " b:term:max x:term:max j:term:max k:term:max z:term:max _off:term:max : tactic =>
  `(tactic| focus
    have ha' : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb := by
      simp [Spike.Lib.X64.Rt.Ti.tiAddrs]
    have hA' : ∀ σ c, (Spike.Lib.X64.Rt.tiNAt (_root_.Executable.labels L.exe).label q
        Spike.Lib.X64.Flow.Ret0.ThreadInit.x7L $x).J σ c →
        bAddr σ.regs .rcx $k = q.tcb + BitVec.ofNat 64 (8 * $j) := fun σ c hJ => by
      dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ
      rw [bAddr_rcx hJ.2.2.2]; exact congrArg (q.tcb + ·) (by decide)
    refine nodeL hlab hsep ha hW (sz := $z) (P := QM) (cls_offM hlab hbd48) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [Spike.Lib.X64.Rt.tiNAt]; decide) (hw_stM (b := .rcx) (r := .rax) (i := $k) (z := $z)
        (A := q.tcb + BitVec.ofNat 64 (8 * $j)) (fun s c hAt => ?_) ?_)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $b) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_st hc hd (a := q.tcb + BitVec.ofNat 64 (8 * $j))
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ)) (hunT _ ha' _ hF.1) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eX7]; decide +kernel
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      exact ⟨(code_field L.lays rfl (hp ▸ $b) rfl s he hn).cell0 rfl rfl hp',
        (Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ), hunT _ ha' _ hF.1, hd⟩
    · rw [htcb]; intro h
      simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] at h
      bv_omega)

set_option maxHeartbeats 3200000 in
/-- **The first `scc_rt_thread_init` call's nodes inside `Lft`**, called
from `scc_rt_start` returning to `.x1` (`hra`) on main's TCB (`htcb`), its
frames `[-248, 8]` off the pool (`hbdI`), the TCB's words unmapped in
private memory under `F` (`hunT`). -/
theorem tiL (hbdI : BandI L R (-248)) (hR : R.OK) (hRlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {M : MachineData → Prop} (q : TiG) (htcb : q.tcb = tcbM L)
    (hunT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec) :
    ∀ i, Spike.Lib.X64.Rt.TiWAt (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F M
      q Spike.Lib.X64.Flow.Ret0.ThreadInit.x7L i := by
  have hbd48 : BandI L R (-48) := bandI_mono hbdI (by decide)
  obtain ⟨eFn, eEn⟩ := ti_labs hlab (L := L)
  obtain ⟨eT, -, -, -, -, -, -, -, -, -, -, eX7⟩ := take_labs hlab (L := L)
  have e1 : L.lab Spike.Lib.X64.Flow.Ret0.x1L = Int64.ofNat 4198500 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hin := wake_tiIn
  simp only [threadInitIn, storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bC⟩, -⟩, bSp⟩, bF1⟩, bF2⟩, bF3⟩, bF4⟩, bF5⟩, bRet⟩,
    bS0, bS1, bS2, bS3, bS4, bS5⟩ := hin
  rw [show callBlk = tiCall from rfl] at bC
  intro i
  cases i <;> dsimp only [Spike.Lib.X64.Rt.TiWAt]
  case e =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bE (ofNat_zero' _) tiPro_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd48 s h.1) (cls_off hlab hbd48) ?_ (soI tiPro oE) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eFn]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢; rw [(tiPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bEn (ofNat_zero' _) tiArg_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd48 s h.1) (cls_off hlab hbd48) ?_ (soI tiArg oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eEn]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢; rw [(tiArg_walk _ _ hJ.2).1, eEn]; decide +kernel
  case c7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bC rfl tiCall_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd48 s h.1) (cls_off hlab hbd48) ?_ (soI tiCall oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eEn]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [Spike.Lib.X64.Flow.Ret0.tiCall_run]
      show NoH ((_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.StackTake.fnL).toBitVec.toNat; rw [eT]; decide +kernel
  case call =>
    intro g hg j
    have hR' := Spike.Lib.Region.callee_ok (kc := -48 - 0) (lo' := -200) (hi' := 8) hR (by omega) (by decide)
      (by omega) (by omega)
    exact takeL hp hlab hsite hsep ha hW
      (bandI_callee hbdI (by show (-248 : Int) ≤ -48 - 0 + -200; omega) (by decide)) hR'
      (by show (-200 : Int) ≤ -200; omega) (by show (8 : Int) ≤ 8; omega) hFr (tiTake q g) hg j
  case x7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PT) (Q := NoH) bSp (ofNat_zero' _) tiSp_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_off hlab hbd48 s h.1) (cls_off hlab hbd48) ?_ (soI tiSp oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiX7At]; rw [eX7]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiX7At, Spike.Lib.X64.Rt.tiNAt] at hJ ⊢; rw [(tiSp_walk _ _ hJ.2.1 hJ.2.2).1, eX7]; decide +kernel
  case st0 =>
    exact st0L hp hlab hsite hsep ha hW (htcb.trans rfl) (fun m hm => hunT _ (by rw [← htcb]; simp [Spike.Lib.X64.Rt.Ti.tiAddrs]) m hm.1)
      (hbdI (-40) (by decide) (by decide))
  case f1 =>
    refine blkL hp hlab hsite hsep ha hW (P := PM) (Q := QM) bF1 rfl tiF1_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_offM hlab hbd48 s h.1) (cls_offM hlab hbd48) ?_ (soI tiF1 oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eX7]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢; rw [(tiF1_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st1 => tstL bS1 TI.st1 1 8 4 59
  case f2 =>
    refine blkL hp hlab hsite hsep ha hW (P := PM) (Q := QM) bF2 rfl tiZ_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_offM hlab hbd48 s h.1) (cls_offM hlab hbd48) ?_ (soI tiZ oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eX7]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢; rw [(tiZ_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st2 => tstL bS2 TI.st2 2 16 4 74
  case f3 =>
    refine blkL hp hlab hsite hsep ha hW (P := PM) (Q := QM) bF3 rfl tiZ_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_offM hlab hbd48 s h.1) (cls_offM hlab hbd48) ?_ (soI tiZ oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eX7]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢; rw [(tiZ_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st3 => tstL bS3 TI.st3 3 24 4 89
  case f4 =>
    refine blkL hp hlab hsite hsep ha hW (P := PM) (Q := QM) bF4 rfl tiF4_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_offM hlab hbd48 s h.1) (cls_offM hlab hbd48) ?_ (soI tiF4 oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eX7]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢; rw [(tiF4_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st4 => tstL bS4 TI.st4 4 32 4 101
  case f5 =>
    refine blkL hp hlab hsite hsep ha hW (P := PM) (Q := QM) bF5 rfl tiF5_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_offM hlab hbd48 s h.1) (cls_offM hlab hbd48) ?_ (soI tiF5 oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eX7]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢; rw [(tiF5_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st5 => tstL bS5 TI.st5 5 40 4 113
  case ret =>
    refine blkL hp hlab hsite hsep ha hW (P := PM) (Q := QM) bRet rfl tiRet_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_offM hlab hbd48 s h.1) (cls_offM hlab hbd48) ?_ (soI tiRet oI)
      (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eX7]; revert k; decide +kernel
    · dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢
      rw [(tiRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec, e1]; decide +kernel

/-- **`TiWAt` inside `WS` is inside `WSX`** at the first `scc_rt_thread_init`
call (`tiL`). -/
theorem tiX (hbdI : BandI L R (-248)) (hR : R.OK) (hRlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {K : State → State → Prop} {M : MachineData → Prop} (q : TiG)
    (htcb : q.tcb = tcbM L)
    (hunT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec)
    (h : ∀ i, Spike.Lib.X64.Rt.TiWAt (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M
      q Spike.Lib.X64.Flow.Ret0.ThreadInit.x7L i) :
    ∀ i, Spike.Lib.X64.Rt.TiWAt (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M
      q Spike.Lib.X64.Flow.Ret0.ThreadInit.x7L i := fun i =>
  TiWAt.imp (h i) (tiL hp hlab hsite hsep ha hW hbdI hR hRlo hhi hFr q htcb hunT hra i) fun _ _ h1 h2 => h2 h1

end L

end Spike.Lib.X64.WakePh.OwnSt

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.st0L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.st0L

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.tiX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.tiX
