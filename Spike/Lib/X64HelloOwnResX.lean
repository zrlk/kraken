/-
**hello.w's `wc_main` reserve at `ownGHXW`** (x86-64 only; the hello counterpart of `X64WakeOwnResX`):
`WcW.reserveW_wcGH` (the reserve's nodes inside `SFactsSt2` at `ownGH`, `X64HelloWcResWI`) moved to
`SFactsSt2` at `ownGHXW` (`Lft2H`). Every state of `scc_rt_thread_reserve` called from `wc_main` is on a pool
stack (its frame `[-40, 8]`, `hb`) at a pc from `.x1` on in none of `InTH`, `InCH`, `InAbH` (`QPH`; the reserve
is at `[4199484, 4199582)`, its return `.x23 = 4203764`), so it holds `tcbM` only (`cls_poolH`); its one
shared write (the `lock xaddq` on the counter `ntA`) misses `tcbM` (`ha`).

- `res_labsH`: the labels the reserve's pcs are decided from.
- `resLH`: the reserve's nodes inside `Lft2H`.
- `reserveW_wcGHX`: `reserveW_wcGH` at `ownGHXW`.

The reserve's `ReserveW.imp` is x86-64 wake's (`X64WakeOwnResX`), generic in the fragments.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against x86-64 wake's `OwnRes`: the reserve returns to
`.Lwc_main.x1` (wake `.x19`), its labels are hello's, and `hW` is about the worker's word `tcbWH L`
(`pinA + 144`; wake's `tcb2 L`).
-/
import Spike.Lib.X64HelloOwnLft2X
import Spike.Lib.X64HelloWcResWI
import Spike.Lib.X64WakeOwnResX

namespace Spike.Lib.X64.HelloPh.OwnRes

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open Scc.Cert.Rt.X64 (codeT_eq code_field)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Reserve (rPro rArg rBnd rJ rRet rmwBlk fnL entryL okL rmwPc oE oI)
open Spike.Lib.X64.Rt.Reserve (ResG RN rvN ReserveW ntA)
open Spike.Lib.X64.WakePh (tcbM Keep BandOnP keep_pc hw_lea hw_rmwM)
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_lea keep_rmw)
open Spike.Lib.X64.WakePh.OwnRes (ReserveW.imp)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {Dt : State → Prop}

/-- The labels the reserve's pcs are decided from, at the canonical base. -/
theorem res_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4199484 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4199492 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4199573 ∧
    (_root_.Executable.labels L.exe).label ".Lwc_main.x1" = Int64.ofNat 4203764 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -40 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block of the reserve (`bb` its code check, `ok` its `okBlk`, `oo` its entry offsets, `el` its label's
value), `QPH` at its end left. -/
local macro "rblkXH " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      hlo' hhi (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soT $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [rvN]; rw [$el:term]; revert k; decide +kernel
    dsimp only [rvN] at hJ ⊢))

set_option hygiene false in
/-- `rblkXH` for a block split by its return label (`blkL2HA`, `blockAcrossB`). -/
local macro "rblkXHA " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL2HA hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      hlo' hhi (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soT $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [rvN]; rw [$el:term]; revert k; decide +kernel
    dsimp only [rvN] at hJ ⊢))

section L

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ ntA L.lab)
  (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
include hp hlab hsite hsep ha hW

set_option maxHeartbeats 1600000 in
/-- **The reserve's nodes inside `Lft2H`** for `q` at old counter `0` returning to `.x23`: every state on a pool
stack (`hb`) at a `QPH` pc holds `tcbM` only; the counter's add misses it. -/
theorem resLH {R : Region} (hb : BandOnP L R (-40) 8) (hR : R.OK) (hlo' : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (q : ResG) (hn : q.n = 0#64) (hra : q.g.ra = (L.lab ".Lwc_main.x1").toBitVec) {F : MachineData → Prop}
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    ∀ i, ReserveW (Lft2H Λ L (ntA L.lab) Dt) (fun _ _ => False) L.exe L.endPc R F q i := by
  obtain ⟨eFn, eEn, eOk, eX23⟩ := res_labsH hlab (L := L)
  have hin0 := Spike.Lib.X64.Flow.HelloWc.hello_reserveIn
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
    rblkXH bE Spike.Lib.X64.Flow.Reserve.rPro_ok rPro oE eFn
    rw [(Spike.Lib.X64.Flow.Reserve.rPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case arg =>
    rblkXH bArg Spike.Lib.X64.Flow.Reserve.rArg_ok rArg oI eEn
    rw [(Spike.Lib.X64.Flow.Reserve.rArg_walk _ _ hJ.2.1 hJ.2.2).1, eEn]; decide +kernel
  case bnd =>
    rblkXH bBnd Spike.Lib.X64.Flow.Reserve.rBnd_ok rBnd oI eEn
    rw [(Spike.Lib.X64.Flow.Reserve.rBnd_walk _ _ hJ.2.1 hJ.2.2 (by rw [hn]; decide)).1, eEn]; decide +kernel
  case j =>
    rblkXH bJ Spike.Lib.X64.Flow.Reserve.rJ_ok rJ oI eEn
    rw [(Spike.Lib.X64.Flow.Reserve.rJ_walk _ _ hJ.2).1]
    show QPH ((_root_.Executable.labels L.exe).label okL).toBitVec.toNat
    rw [eOk]; decide +kernel
  case ok =>
    rblkXHA bOk Spike.Lib.X64.Flow.Reserve.rRet_ok rRet oI eOk
    rw [(Spike.Lib.X64.Flow.Reserve.rRet_walk _ _ hJ.2).1]
    show QPH (Int64.ofBitVec q.g.ra).toBitVec.toNat
    rw [hra, Int64.ofBitVec_toBitVec, show L.lab ".Lwc_main.x1" = Int64.ofNat 4203764 from eX23]
    decide +kernel
  case entry =>
    refine nodeL2H hsep ha hW (sz := 7) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
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
    refine nodeL2H hsep ha hW (sz := 5) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [rvN]; decide) (hw_rmwM hE (Ne.symm ha))
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_rmw hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [rvN, rmwPc]; rw [eEn]; decide +kernel
    · dsimp only [rvN, rmwPc]; rw [eEn]; decide +kernel

end L

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ ntA L.lab)
  (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
include hp hlo hΛ hlab hsite hsep ha hW

/-- **`WcW.reserveW_wcGH` at `ownGHXW`**: the reserve inside `SFactsSt2` at `ownGHXW L (ntA L.lab)`, at old
counter `0` returning to `.x23`, for any frame ghost and control `g`, its frame `[-40, 8]` on the pool (`hb`). -/
theorem reserveW_wcGHX {rS : Range} {R : Region} {F : MachineData → Prop}
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hb : BandOnP L R (-40) 8) (hR : R.OK) (hlo' : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Spike.Lib.Ctl) (hra : g.1.ra = (L.lab ".Lwc_main.x1").toBitVec)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    ∀ i, ReserveW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ⟨g.1, 0#64, g.2⟩ i := fun i =>
  ReserveW.imp (WcW.reserveW_wcGH hp hlo hΛ hlab hsite hsepN hR hlo' hhi g hra hmN hunN i)
    (resLH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hlo' hhi ⟨g.1, 0#64, g.2⟩ rfl hra
      hunN i)
    fun _ _ h1 h2 => h2 h1

end Inst

end Spike.Lib.X64.HelloPh.OwnRes

/-- info: 'Spike.Lib.X64.HelloPh.OwnRes.resLH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnRes.resLH

/-- info: 'Spike.Lib.X64.HelloPh.OwnRes.reserveW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnRes.reserveW_wcGHX
