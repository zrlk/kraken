/-
**wc_main's reserve at `ownGXW`** (x86-64; X64-res-ownGX):
`WcW.reserveW_wcG` (the reserve's nodes inside `SFactsSt2` at `ownG`) moved
to `SFactsSt2` at `ownGXW` (`Lft2`): every state of `scc_rt_thread_reserve`
called from `.x19` is on a pool stack (its frame `[-40, 8]`, `hb`) at a pc
from `.x1` on in none of `InT`, `InC`, `InAb` (`QP`; the reserve is at
`[4199447, 4199555)`, its return `.x19 = 4203387`), so it holds `tcbM` only
(`cls_pool`); its one shared write (the `lock xaddq` on the counter
`ntA`) misses `tcbM` (`ha`).

- `res_labs`: the labels the reserve's pcs are decided from.
- `ReserveW.imp`: the reserve's node obligations from two.
- `resL`: the reserve's nodes inside `Lft2`.
- `reserveW_wcGX`: `reserveW_wcG` at `ownGXW`.

**Deviations.** None: new lemmas. `reserveW_wcGX` takes `ownGXW`'s
separation premises (`hsep : PhRec.TcbSep L`, `ha : tcbM L ≠ ntA L.lab`,
`hW`) and the frame's band on the pool (`hb : BandOnP L R (-40) 8`) besides
`reserveW_wcG`'s (whose counter separation is renamed `hsepN`).
-/
import Spike.Lib.X64WakeOwnLft2
import Spike.Lib.X64WakeWcResWI

namespace Spike.Lib.X64.WakePh.OwnRes

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open Scc.Cert.Rt.X64 (codeT_eq code_field)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Reserve (rPro rArg rBnd rJ rRet rmwBlk fnL entryL okL rmwPc oE oI)
open Spike.Lib.X64.Rt.Reserve (ResG RN rvN ReserveW ntA)
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_lea keep_rmw)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {Dt : State → Prop}

/-- The labels the reserve's pcs are decided from, at the canonical base. -/
theorem res_labs (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4199447 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4199455 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4199536 ∧
    (_root_.Executable.labels L.exe).label ".Lwc_main.x1" = Int64.ofNat 4203387 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

/-- **The reserve's node obligations from two.** -/
theorem ReserveW.imp {W W1 W2 : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {q : ResG} {i : RN}
    (h1 : ReserveW W1 K exe endPc R F q i) (h2 : ReserveW W2 (fun _ _ => False) exe endPc R F q i)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : ReserveW W K exe endPc R F q i := by
  cases i <;> dsimp only [ReserveW] at h1 h2 ⊢
  all_goals first
    | exact Spike.Lib.X64.AllocG.BlkW.imp h1 h2 hw
    | exact Spike.Lib.X64.AllocG.NodeW.imp h1 h2 hw

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -40 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block of the reserve (`bb` its code check, `ok` its `okBlk`, `oo` its
entry offsets, `el` its label's value), `QP` at its end left. -/
local macro "rblkX " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      hlo' hhi (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
      (soT $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [rvN]; rw [$el:term]; revert k; decide +kernel
    dsimp only [rvN] at hJ ⊢))

set_option hygiene false in
/-- `rblkX` for a block split by its return label (`blkL2A`, `blockAcrossB`). -/
local macro "rblkXA " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL2A hp hlab hsite hsep ha hW (P := PP) (Q := QP) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      hlo' hhi (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
      (soT $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [rvN]; rw [$el:term]; revert k; decide +kernel
    dsimp only [rvN] at hJ ⊢))

section L

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ ntA L.lab)
  (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
include hp hlab hsite hsep ha hW

set_option maxHeartbeats 1600000 in
/-- **The reserve's nodes inside `Lft2`** for `q` at old counter `0`
returning to `.x19`: every state on a pool stack (`hb`) at a `QP` pc holds
`tcbM` only; the counter's add misses it. -/
theorem resL {R : Region} (hb : BandOnP L R (-40) 8) (hR : R.OK) (hlo' : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (q : ResG) (hn : q.n = 0#64) (hra : q.g.ra = (L.lab ".Lwc_main.x1").toBitVec) {F : MachineData → Prop}
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    ∀ i, ReserveW (Lft2 Λ L (ntA L.lab) Dt) (fun _ _ => False) L.exe L.endPc R F q i := by
  obtain ⟨eFn, eEn, eOk, eX19⟩ := res_labs hlab (L := L)
  have hin0 := Spike.Lib.X64.Flow.WakeWc.wake_reserveIn
  simp only [Spike.Lib.X64.Flow.Reserve.reserveIn, Spike.Lib.X64.Flow.Ret0.AllocTcb.siAt,
    Bool.and_eq_true] at hin0
  obtain ⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := hin0
  have hbA : Scc.Cert.Rt.X64.blockAtB L.prog entryL 0
      [((Spike.Lib.X64.SI.leaRip .rax "scc_rt_nthreads").toDir, 7)] = true := by rw [hp]; exact bA
  have hbR : Scc.Cert.Rt.X64.blockAtB L.prog entryL 22 [(Spike.Lib.X64.xaddDir .rcx 0 .rax, 5)] = true := by
    rw [hp, ← show rmwBlk = [(Spike.Lib.X64.xaddDir .rcx 0 .rax, 5)] by decide]; exact bRmw
  intro i
  cases i <;> dsimp only [ReserveW]
  case e =>
    rblkX bE Spike.Lib.X64.Flow.Reserve.rPro_ok rPro oE eFn
    rw [(Spike.Lib.X64.Flow.Reserve.rPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case arg =>
    rblkX bArg Spike.Lib.X64.Flow.Reserve.rArg_ok rArg oI eEn
    rw [(Spike.Lib.X64.Flow.Reserve.rArg_walk _ _ hJ.2.1 hJ.2.2).1, eEn]; decide +kernel
  case bnd =>
    rblkX bBnd Spike.Lib.X64.Flow.Reserve.rBnd_ok rBnd oI eEn
    rw [(Spike.Lib.X64.Flow.Reserve.rBnd_walk _ _ hJ.2.1 hJ.2.2 (by rw [hn]; decide)).1, eEn]; decide +kernel
  case j =>
    rblkX bJ Spike.Lib.X64.Flow.Reserve.rJ_ok rJ oI eEn
    rw [(Spike.Lib.X64.Flow.Reserve.rJ_walk _ _ hJ.2).1]
    show QP ((_root_.Executable.labels L.exe).label okL).toBitVec.toNat
    rw [eOk]; decide +kernel
  case ok =>
    rblkXA bOk Spike.Lib.X64.Flow.Reserve.rRet_ok rRet oI eOk
    rw [(Spike.Lib.X64.Flow.Reserve.rRet_walk _ _ hJ.2).1]
    show QP (Int64.ofBitVec q.g.ra).toBitVec.toNat
    rw [hra, Int64.ofBitVec_toBitVec, show L.lab ".Lwc_main.x1" = Int64.ofNat 4203387 from eX19]
    decide +kernel
  case entry =>
    refine nodeL2 hlab hsep ha hW (sz := 7) (P := QP) (cls_pool hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [rvN]; decide) (hw_lea fun s c hAt => by
        obtain ⟨he, hn, -, hp', -⟩ := hAt
        exact (code_field L.lays rfl hbA (ofNat_zero' _) s he hn).cell0 rfl rfl hp')
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl hbA (ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_lea hc hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [rvN]; rw [eEn]; decide +kernel
    · dsimp only [rvN]; rw [eEn]; decide +kernel
  case rmw =>
    have hE : ∀ s c, Spike.Lib.X64.At L.exe L.endPc R F
        (rvN (_root_.Executable.labels L.exe).label q .rmw) s c →
        Kraken.Promising.Lower.X64.CellAt s (Spike.Lib.X64.xaddDir .rcx 0 .rax) 5 ∧
        Kraken.Promising.Lower.X64.eaddr s 5 (Spike.Lib.X64.mB .rcx 0) = ntA L.lab ∧
        Mem.loadInt s.st.1.dmem (ntA L.lab) 8 = none ∧ s.decls = {} := fun s c hAt => by
      obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      refine ⟨(code_field L.lays rfl hbR rfl s he hn).cell0 rfl rfl hp', ?_, hunN _ hF, hd⟩
      refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
      rw [hA.regs, ← hJ.2.2.2]; simp [Reg64s.get64]
    refine nodeL2 hlab hsep ha hW (sz := 5) (P := QP) (cls_pool hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [rvN]; decide) (hw_rmwM hE (Ne.symm ha))
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_rmw hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [rvN, rmwPc]; rw [eEn]; decide +kernel
    · dsimp only [rvN, rmwPc]; rw [eEn]; decide +kernel

end L

section Inst

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ ntA L.lab)
  (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
include hp hlo hΛ hlab hsite hsep ha hW

/-- **`WcW.reserveW_wcG` at `ownGXW`**: the reserve inside `SFactsSt2` at
`ownGXW L (ntA L.lab)`, at old counter `0` returning to `.x19`, for any
frame ghost and control `g`, its frame `[-40, 8]` on the pool (`hb`). -/
theorem reserveW_wcGX {rS : Range} {R : Region} {F : MachineData → Prop}
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hb : BandOnP L R (-40) 8) (hR : R.OK) (hlo' : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Spike.Lib.Ctl) (hra : g.1.ra = (L.lab ".Lwc_main.x1").toBitVec)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    ∀ i, ReserveW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ⟨g.1, 0#64, g.2⟩ i := fun i =>
  ReserveW.imp (WcW.reserveW_wcG hp hlo hΛ hlab hsite hsepN hR hlo' hhi g hra hmN hunN i)
    (resL (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hlo' hhi ⟨g.1, 0#64, g.2⟩ rfl hra
      hunN i)
    fun _ _ h1 h2 => h2 h1

end Inst

end Spike.Lib.X64.WakePh.OwnRes

/-- info: 'Spike.Lib.X64.WakePh.OwnRes.resL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnRes.resL

/-- info: 'Spike.Lib.X64.WakePh.OwnRes.reserveW_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnRes.reserveW_wcGX
