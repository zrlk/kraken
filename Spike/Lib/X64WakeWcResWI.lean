/-
**`wc_main`'s reserve inside `SFactsSt2` at `ownG`** (x86-64; twin of
`Spike/Lib/A64WakeWcResWI.lean`): `WcResW.res` at the pre-spawn chain's
`W`. `Rt.Reserve.reserveW_gen` at the first instance (`instOkW`, owned
words `ownW L (ntA L.lab)`, no take phase, the source control replaced by
`X64Consumer.c0`), each node moved to `ownG`, which picks `ownW` at the
reserve's pcs (all free: off `ownG`'s four ranges and the take site,
checked by the kernel against the certificate's labels).

- `ResAgW`: the agreement a node's obligation is moved to `ownG` with.
- `resAgree`: at each reserve node of `q` (old counter `0`, returning to
  `.x19`), `ownG` is `ownW` at its states and their successors.
- `reserveW_wcG`: `∀ i, ReserveW … i` at `SFactsSt2`/`ownG` for every frame
  ghost and control.

**Where this differs from AArch64**: the reserve is x86-64's
(`X64Reserve`: `rPro` at `scc_rt_thread_reserve`, the `leaq` at `.entry`,
`rArg` at `.entry + 7`, the `lock xaddq` at `.entry + 22`, `rBnd` at
`.entry + 27`, `rJ` at `.entry + 65`, `rRet` at `.ok`; A64's has a second
single instruction, `add`, and an `ldadd`); it returns to `.Lwc_main.x1`
(A64's `.sp3`); its frame is `[-40, 8)` (`R.lo ≤ -40`, `8 ≤ R.hi`; A64's
`[-48, 0)`, 16-aligned, `hal`); the agreement is named `ResAgW` (A64's
`AgW`, a name `X64WakeOwnGAbT` already uses); the free pcs are byte offsets
(`freeAt l os`, `freeBlk`).
-/
import Spike.Lib.X64WakeWcPreWI

namespace Spike.Lib.X64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (blockAtB code_field)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At arun mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add')
open Spike.Lib.X64.Flow.Reserve (rPro rArg rBnd rJ rRet rmwBlk fnL entryL okL rmwPc oE oI)
open Spike.Lib.X64.Rt.Reserve (ResG RN rvN ReserveW ntA)
open Kraken.Promising.Lower.X64 (CellAt exec_xaddG_agrees)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}

/-- The agreement a node's obligation is moved to `ownG` with. -/
abbrev ResAgW (L : RuntimeLayout) (a : BitVec 64) : Spike.Lib.Frag isa := fun s _ =>
  ownG L a s = ownW L a (phW (pcOf s)) ∧
    ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownG L a s' = ownW L a (phW (pcOf s'))

section Agree

variable (hp : L.prog = wakeCells) (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlab hsite

/-- A block's agreement from its code at `lab l + k`, its free pcs
(`freeBlk`) and its free end. -/
private theorem blkAg {a : BitVec 64} {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat}
    {blo bhi : Int} (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : Spike.Lib.X64.okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hfree : freeBlk l k blk = true)
    (hlast : ∀ σ c, n.J σ c → freeN (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (ResAgW L a) (fun _ _ => False) L.exe L.endPc R F n blk :=
  blkAgreeW hlab (code_field L.lays rfl (hp ▸ hb) he) hok hR hlo' hhi hsite
    (fun j hj => by rw [← he]; exact freeBlk_pc hlab hfree hj) hlast

/-- **`ownG` is `ownW` at the reserve's nodes** for `q` at old counter `0`
returning to `.x19` (`hra`), with the counter unmapped under `F` (`hunN`,
for the `lock xaddq`'s step). -/
theorem resAgree (hlo : L.Λ.code.lo = lo) (rS : Range) (a : BitVec 64) (hR : R.OK) (hlo' : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (q : ResG) (hn : q.n = 0#64) (hra : q.g.ra = (L.lab ".Lwc_main.x1").toBitVec)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    ∀ i, ReserveW (ResAgW L a) (fun _ _ => False) L.exe L.endPc R F q i := by
  have hin := Spike.Lib.X64.Flow.WakeWc.wake_reserveIn
  simp only [Spike.Lib.X64.Flow.Reserve.reserveIn, Spike.Lib.X64.Flow.Ret0.AllocTcb.siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := hin
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  intro i
  cases i <;> dsimp only [ReserveW]
  case e =>
    refine blkAg hp hlab hsite (l := fnL) (k := 0) bE (ofNat_zero' _) Spike.Lib.X64.Flow.Reserve.rPro_ok hR hlo'
      hhi (by wcfreeB_dec) fun σ c hJ => ?_
    show freeN (arun L.lab rPro ⟨L.lab fnL, oE, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.X64.Flow.Reserve.rPro_walk _ _ hJ.2).1]
    exact freeAt_pc hlab (l := fnL) (os := [8]) (by wcfree_dec) (List.mem_singleton.mpr rfl)
  case entry =>
    have hb : blockAtB L.prog entryL 0 [((Spike.Lib.X64.SI.leaRip .rax "scc_rt_nthreads").toDir, 7)] = true := by
      rw [hp]; exact bA
    refine nodeAgreeW hlab hsite (z := 7) (freeAt_lab hlab (l := entryL) (by wcfree_dec)) ?_ ?_
    · show freeN (L.lab entryL + Int64.ofNat 7).toBitVec.toNat = true
      exact freeAt_pc hlab (l := entryL) (os := [7]) (by wcfree_dec) (List.mem_singleton.mpr rfl)
    rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb (ofNat_zero' _) h1 h2 h4'
    refine ⟨_, _, hc, fun w w' h => (by cases h), Spike.Lib.X64.exec_si hc, fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    subst hu; rfl
  case arg =>
    refine blkAg hp hlab hsite (l := entryL) (k := 7) bArg rfl Spike.Lib.X64.Flow.Reserve.rArg_ok hR hlo' hhi
      (by wcfreeB_dec) fun σ c hJ => ?_
    show freeN (arun L.lab rArg ⟨L.lab entryL + Int64.ofNat 7, oI, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.X64.Flow.Reserve.rArg_walk _ _ hJ.2.1 hJ.2.2).1, ← ofNat_add']
    exact freeAt_pc hlab (l := entryL) (os := [7 + 15]) (by wcfree_dec) (List.mem_singleton.mpr rfl)
  case rmw =>
    have hb : blockAtB L.prog entryL 22 rmwBlk = true := by rw [hp]; exact bRmw
    have hfr : freeAt entryL [22, 22 + 5] = true := by wcfree_dec
    refine nodeAgreeW hlab hsite (z := 5) (freeAt_pc hlab hfr (o := 22) (by simp))
      (by have := freeAt_pc hlab hfr (o := 22 + 5) (by simp); rwa [ofNat_add'] at this) ?_
    rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, hJ⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb rfl h1 h2 h4'
    have ha' : Kraken.Promising.Lower.X64.eaddr s 5 (mB .rcx 0) = ntA L.lab :=
      (eaddr_mB s 5 .rcx 0).trans (by rw [hA.regs, ← hJ.2.2.2]; simp [Reg64s.get64])
    refine ⟨_, _, hc, fun w w' h => (by cases h),
      exec_xaddG_agrees (w := .W64) hc ha' (hunN _ hF) (agrees_of_decls h3' _ _), fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl
  case bnd =>
    refine blkAg hp hlab hsite (l := entryL) (k := 27) bBnd rfl Spike.Lib.X64.Flow.Reserve.rBnd_ok hR hlo' hhi
      (by wcfreeB_dec) fun σ c hJ => ?_
    show freeN (arun L.lab rBnd ⟨L.lab entryL + Int64.ofNat 27, oI, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.X64.Flow.Reserve.rBnd_walk _ _ hJ.2.1 hJ.2.2 (by rw [hn]; decide)).1, ← ofNat_add']
    exact freeAt_pc hlab (l := entryL) (os := [27 + 38]) (by wcfree_dec) (List.mem_singleton.mpr rfl)
  case j =>
    refine blkAg hp hlab hsite (l := entryL) (k := 65) bJ rfl Spike.Lib.X64.Flow.Reserve.rJ_ok hR hlo' hhi
      (by wcfreeB_dec) fun σ c hJ => ?_
    show freeN (arun L.lab rJ ⟨L.lab entryL + Int64.ofNat 65, oI, σ⟩).pc.toBitVec.toNat = true
    rw [Spike.Lib.X64.Flow.Reserve.rJ_run]
    exact freeAt_lab hlab (l := okL) (by wcfree_dec)
  case ok =>
    have he : L.lab okL + Int64.ofNat 0 = L.lab okL := ofNat_zero' _
    refine blkAgreeW hlab (Spike.Lib.X64.code_field_blockAcrossB L.lays rfl (hp ▸ bOk) (List.take_append_drop 3 _) he)
      Spike.Lib.X64.Flow.Reserve.rRet_ok hR hlo' hhi hsite
      (fun j hj => by
        have h := freeBlk_pc hlab (l := okL) (k := 0) (by wcfreeB_dec) hj
        rw [he] at h; exact h) fun σ c hJ => ?_
    show freeN (arun L.lab rRet ⟨L.lab okL, oI, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.X64.Flow.Reserve.rRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec]
    exact freeAt_lab hlab (l := ".Lwc_main.x1") (by wcfree_dec)

end Agree

section Inst

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **The reserve inside `SFactsSt2` at `ownG`** (the owned word the counter
`scc_rt_nthreads`), at old counter `0` returning to `.x19`, for any frame
ghost and control `g`: `reserveW_gen` at `instOkW` and the control `c0`,
moved to `ownG` (`resAgree`) and to `g.2`. The counter is apart from the
runtime's words (`hsep`), mapped (`hmN`) and unmapped under `F` (`hunN`). -/
theorem reserveW_wcG
    (hsep : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hR : R.OK) (hlo' : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Spike.Lib.Ctl) (hra : g.1.ra = (L.lab ".Lwc_main.x1").toBitVec)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none) :
    ∀ i, ReserveW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L (ntA L.lab)) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ⟨g.1, 0#64, g.2⟩ i := by
  let q0 : ResG := ⟨g.1, 0#64, Spike.Lib.X64Consumer.c0⟩
  have hW := Spike.Lib.X64.Rt.Reserve.reserveW_gen (instOkW hp hlo (ntA L.lab) (fun _ => False) hsite (rS := rS))
    (Λ := Λ) (lbl := fun _ => none) (rS := rS) (F := F) (fun _ => rfl)
    (by rw [hp]; exact Spike.Lib.X64.Flow.WakeWc.wake_reserveIn)
    Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hR hlo' hhi q0 rfl (ra := L.lab ".Lwc_main.x1") hra
    (Spike.Lib.X64.WakePh.resPhW hΛ (Tk := fun s => (fun _ : Nat => False) (phW (pcOf s))) hlab hsep
      (fun _ _ _ _ h => h)) hmN hunN
  have hag := resAgree hp hlab hsite hlo rS (ntA L.lab) hR hlo' hhi q0 rfl hra hunN
  intro i
  have h1 := hW i
  have h2 := hag i
  cases i <;> dsimp only [ReserveW] at h1 h2 ⊢
  case e =>
    exact blkW_mapC (n' := rvN L.lab q0 .e) rfl rfl
      (Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case entry =>
    exact nodeW_mapC (n' := rvN L.lab q0 .entry) rfl rfl
      (Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.nodeW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case arg =>
    exact blkW_mapC (n' := rvN L.lab q0 .arg) rfl rfl
      (Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case rmw =>
    exact nodeW_mapC (n' := rvN L.lab q0 .rmw) rfl rfl
      (Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.nodeW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case bnd =>
    exact blkW_mapC (n' := rvN L.lab q0 .bnd) rfl rfl
      (Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case j =>
    exact blkW_mapC (n' := rvN L.lab q0 .j) rfl rfl
      (Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩
  case ok =>
    exact blkW_mapC (n' := rvN L.lab q0 .ok) rfl rfl
      (Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 h1) h2)
      fun σ c hJ => ⟨_, ⟨rfl, hJ.2⟩, fun _ h => h⟩

end Inst

end Spike.Lib.X64.WakePh.WcW

/-- info: 'Spike.Lib.X64.WakePh.WcW.resAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.resAgree

/-- info: 'Spike.Lib.X64.WakePh.WcW.reserveW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.reserveW_wcG
