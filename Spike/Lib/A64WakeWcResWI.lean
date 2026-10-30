/-
**`wc_main`'s reserve inside `SFactsSt2` at `ownG`** (AArch64):
`WcResW.res` at the pre-spawn chain's `W`. `Rt.Reserve.reserveW_gen` at the
first instance (`instOkW`, owned words `ownW L (ntA L.lab)`, no take phase,
the source control replaced by `A64Consumer.c0`), each node moved to
`ownG`, which picks `ownW` at the reserve's pcs (all free: off `ownG`'s
four ranges and the take site, checked by the kernel against the
certificate's labels).

- `resAgree`: at each reserve node of `q` (old counter `0`, returning to
  `.sp3`), `ownG` is `ownW` at its states and their successors.
- `reserveW_wcG`: `∀ i, ReserveW … i` at `SFactsSt2`/`ownG` for every frame
  ghost and control.
-/
import Spike.Lib.A64WakeWcPreWI

namespace Spike.Lib.A64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ofNat4_zero ofNat4_succ)
open Spike.Lib.A64.Flow.Reserve (rPro rArg rBnd rJ rRet fnL entryL okL rmwPc rmwDir oE oI)
open Spike.Lib.A64.Rt.Reserve (ResG RN rvN ReserveW ntA)
open Kraken.Promising.Lower.A64 (CellAt after)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}

/-- The reserve's code in `wakeProg`. -/
theorem wake_reserveIn' : Spike.Lib.A64.Flow.Reserve.reserveIn wakeProg = true :=
  Spike.Lib.A64.Flow.WakeWc.wake_reserveIn

/-- The agreement a node's obligation is moved to `ownG` with. -/
abbrev AgW (L : RuntimeLayout) (a : BitVec 64) : Spike.Lib.Frag isaLSE2 := fun s _ =>
  ownG L a s = ownW L a (phW (pcOf s)) ∧
    ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownG L a s' = ownW L a (phW (pcOf s'))

section Agree

variable (hp : L.prog = wakeProg) (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlab hsite

/-- **`ownG` is `ownW` at the reserve's nodes** for `q` at old counter `0`
returning to `.sp3` (`hra`), with the counter unmapped under `F` (`hunN`, for
the `ldadd`'s step). -/
theorem resAgree (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (q : ResG) (hn : q.n = 0#64) (hra : q.g.ra = (L.lab ".L21_wc_main.sp3").toBitVec)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    ∀ i, ReserveW (AgW L a) (fun _ _ => False) L.exe L.endPc R F q i := by
  have hin := wake_reserveIn'
  simp only [Spike.Lib.A64.Flow.Reserve.reserveIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := hin
  intro i
  cases i <;> dsimp only [ReserveW]
  case e =>
    refine blkAgreeW hlab (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bE) (ofNat4_zero _))
      Spike.Lib.A64.Flow.Reserve.rPro_ok hR hal (by omega) (by omega) hsite
      (fun j hj => by
        have := freeAt_pc hlab (l := fnL) (k := 0) (n := 5) (by free_dec) (j := j) (by simp [rPro] at hj ⊢; omega)
        rwa [ofNat4_zero] at this) (fun σ c hJ => ?_)
    show freeN (Spike.Lib.A64.Flow.arun L.lab rPro
      ⟨L.lab fnL, oE, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.A64.Flow.Reserve.rPro_walk _ _ hJ.2).1]
    have := freeAt_pc hlab (l := fnL) (k := 0) (n := 5) (by free_dec) (j := 4) (by omega)
    rwa [ofNat4_zero] at this
  case entry =>
    refine nodeAgreeW hlab hsite (freeAt_lab hlab (l := entryL) (by free_dec))
      (freeK hlab (l := entryL) (k := 1) (by free_dec)) ?_
    rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := cell1 hp bA h1 h2 (by rw [h4', ofNat4_zero]; rfl)
    refine ⟨_, _, hc, fun imm h => ?_, Spike.Lib.A64.Flow.exec_si hc, fun s' hu => ?_⟩
    · cases h
    · simp only [TreeLeaf] at hu
      subst hu; rfl
  case add =>
    refine nodeAgreeW hlab hsite (freeK hlab (l := entryL) (k := 1) (by free_dec))
      (by have := freeK hlab (l := entryL) (k := 2) (by free_dec); rwa [ofNat4_succ] at this) ?_
    rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := cell1 hp bA1 h1 h2 h4'
    refine ⟨_, _, hc, fun imm h => ?_, Spike.Lib.A64.Flow.exec_si hc, fun s' hu => ?_⟩
    · cases h
    · simp only [TreeLeaf] at hu
      subst hu; rfl
  case arg =>
    refine blkAgreeW hlab (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bArg) rfl)
      Spike.Lib.A64.Flow.Reserve.rArg_ok hR hal (by omega) (by omega) hsite
      (fun j hj => freeAt_pc hlab (l := entryL) (k := 2) (n := 4) (by free_dec) (j := j)
        (by simp [rArg] at hj ⊢; omega)) (fun σ c hJ => ?_)
    show freeN (Spike.Lib.A64.Flow.arun L.lab rArg
      ⟨L.lab entryL + Int64.ofNat (4 * 2), oI, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.A64.Flow.Reserve.rArg_walk _ _ hJ.2.1 hJ.2.2).1]
    exact freeAt_pc hlab (l := entryL) (k := 2) (n := 4) (by free_dec) (j := 3) (by omega)
  case rmw =>
    refine nodeAgreeW hlab hsite (freeK hlab (l := entryL) (k := 5) (by free_dec))
      (by have := freeK hlab (l := entryL) (k := 6) (by free_dec); rwa [ofNat4_succ] at this) ?_
    rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, hJ⟩
    have hc := cell1 hp bRmw h1 h2 h4'
    have hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg .X10).toBitVec 8 = none := by
      rw [hA.regs]; simp only [Reg64s.getXReg]; rw [hJ.2.2.2]; exact hunN _ hF
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_ldop hc hdm, fun s' hu => ?_⟩
    · cases h
    · rw [h3', EvTree.access_empty] at hu
      simp only [TreeLeaf] at hu
      obtain ⟨_, rfl⟩ := hu
      rfl
  case bnd =>
    refine blkAgreeW hlab (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bBnd) rfl)
      Spike.Lib.A64.Flow.Reserve.rBnd_ok hR hal (by omega) (by omega) hsite
      (fun j hj => freeAt_pc hlab (l := entryL) (k := 6) (n := 10) (by free_dec) (j := j)
        (by simp [rBnd] at hj ⊢; omega)) (fun σ c hJ => ?_)
    show freeN (Spike.Lib.A64.Flow.arun L.lab rBnd
      ⟨L.lab entryL + Int64.ofNat (4 * 6), oI, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.A64.Flow.Reserve.rBnd_walk _ _ hJ.2.1 hJ.2.2 (by rw [hn]; decide)).1]
    exact freeAt_pc hlab (l := entryL) (k := 6) (n := 10) (by free_dec) (j := 9) (by omega)
  case j =>
    refine blkAgreeW hlab (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bJ) rfl)
      Spike.Lib.A64.Flow.Reserve.rJ_ok hR hal (by omega) (by omega) hsite
      (fun j hj => freeAt_pc hlab (l := entryL) (k := 15) (n := 1) (by free_dec) (j := j)
        (by simp [rJ] at hj ⊢; omega)) (fun σ c hJ => ?_)
    show freeN (Spike.Lib.A64.Flow.arun L.lab rJ
      ⟨L.lab entryL + Int64.ofNat (4 * 15), oI, σ⟩).pc.toBitVec.toNat = true
    rw [Spike.Lib.A64.Flow.Reserve.rJ_run]
    exact freeAt_lab hlab (l := okL) (by free_dec)
  case ok =>
    refine blkAgreeW hlab (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ bOk) (ofNat4_zero _))
      Spike.Lib.A64.Flow.Reserve.rRet_ok hR hal (by omega) (by omega) hsite
      (fun j hj => by
        have := freeAt_pc hlab (l := okL) (k := 0) (n := 5) (by free_dec) (j := j) (by simp [rRet] at hj ⊢; omega)
        rwa [ofNat4_zero] at this) (fun σ c hJ => ?_)
    show freeN (Spike.Lib.A64.Flow.arun L.lab rRet
      ⟨L.lab okL, oI, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.A64.Flow.Reserve.rRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec]
    exact freeAt_lab hlab (l := ".L21_wc_main.sp3") (by free_dec)

end Agree

section Inst

variable (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **The reserve inside `SFactsSt2` at `ownG`** (the owned word the counter
`scc_rt_nthreads`), at old counter `0` returning to `.sp3`, for any frame
ghost and control `g`: `reserveW_gen` at `instOkW` and the control `c0`,
moved to `ownG` (`resAgree`) and to `g.2`. The counter is apart from the
runtime's words (`hsep`), mapped (`hmN`) and unmapped under `F` (`hunN`). -/
theorem reserveW_wcG
    (hsep : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (g : Spike.Lib.A64.Flow.Reserve.G × Ctl) (hra : g.1.ra = (L.lab ".L21_wc_main.sp3").toBitVec)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    ∀ i, ReserveW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L (ntA L.lab)) s)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ⟨g.1, 0#64, g.2⟩ i := by
  let q0 : ResG := ⟨g.1, 0#64, Spike.Lib.A64Consumer.c0⟩
  have hW := Spike.Lib.A64.Rt.Reserve.reserveW_gen (instOkW hp hlo (ntA L.lab) (fun _ => False) hsite (rS := rS))
    (Λ := Λ) (lbl := fun _ => none) (rS := rS) (F := F) (fun _ => rfl) (by rw [hp]; exact wake_reserveIn')
    Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hR hal hlo' hhi q0 rfl (ra := L.lab ".L21_wc_main.sp3") hra
    (resPhW hΛ (Tk := fun s => (fun _ : Nat => False) (phW (pcOf s))) hlab hsep (fun _ _ _ _ h => h)) hmN hunN
  have hag := resAgree hp hlab hsite (ntA L.lab) hR hal hlo' hhi q0 rfl hra hunN
  intro i
  have h1 := hW i
  have h2 := hag i
  cases i <;> dsimp only [ReserveW] at h1 h2 ⊢
  case e =>
    exact blkW_mapC (n' := rvN L.lab q0 .e) rfl rfl
      (Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case entry =>
    exact nodeW_mapC (n' := rvN L.lab q0 .entry) rfl rfl
      (Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case add =>
    exact nodeW_mapC (n' := rvN L.lab q0 .add) rfl rfl
      (Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case arg =>
    exact blkW_mapC (n' := rvN L.lab q0 .arg) rfl rfl
      (Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case rmw =>
    exact nodeW_mapC (n' := rvN L.lab q0 .rmw) rfl rfl
      (Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case bnd =>
    exact blkW_mapC (n' := rvN L.lab q0 .bnd) rfl rfl
      (Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case j =>
    exact blkW_mapC (n' := rvN L.lab q0 .j) rfl rfl
      (Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case ok =>
    exact blkW_mapC (n' := rvN L.lab q0 .ok) rfl rfl
      (Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩

end Inst

end Spike.Lib.A64.WakePh.WcW

/-- info: 'Spike.Lib.A64.WakePh.WcW.resAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.resAgree

/-- info: 'Spike.Lib.A64.WakePh.WcW.reserveW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.reserveW_wcG
