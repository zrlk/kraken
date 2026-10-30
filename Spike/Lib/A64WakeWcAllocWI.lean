/-
**`scc_rt_alloc` inside `SFactsSt2` at `ownG`** (AArch64): the box's
allocation in `WcPreW.alloc` at the pre-spawn chain's `W`. `AllocG.allocStS`
at the first instance (`instOkW`, owned words `ownW L a`, no take phase)
combined (`AllocW.imp`) with the agreement of `ownG` and `ownW` at the
allocator's nodes: every allocator pc is free (off `ownG`'s four ranges and
the take site), and so is every successor except the heap abort's `bl`,
whose target `scc_rt_abort` is in `ownG`'s abort range with `x30` neither
of the two return points `ownG` reads there.

The pcs and phase facts are checked by the kernel against the certificate's
labels, with no absolute address in this file.

- `arun_pc_last`, `freeAt_succ`: a block's last pc, and the free pc after a
  checked one.
- `blkAgreeL`, `nodeSiL`: a block's and a single instruction's agreement from
  their label-relative pcs.
- `allocTabW`, `allocPhW`: the allocator's phase check at `phW`.
- `allocAgree`: the agreement at every node of `AllocW`.
- `allocW_wcG`: `AllocW` at `SFactsSt2`/`ownG`.
-/
import Spike.Lib.A64WakeWcResWI
import Spike.Lib.A64AllocGSt
import Spike.Lib.LowerA64.NodeTp

namespace Spike.Lib.A64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact codeT codeT_eq factOk blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ofNat4_zero ofNat4_succ)
open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRet iRmw iHdr b0 b1 b2 b3 b4 b5 b6 b7 b9 b11
  b12 b13 b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)
open Kraken.Promising.Lower.A64 (CellAt after)
open Spike.Lib.A64.Rt.PhOfTab (blkPh_of_factOk step_of_factOk ok_of_factOk ph_of_factOk)

/-! ## A block's last pc -/

/-- **The pc a covered block ends at**: its last directive's target from the
pc before it. -/
theorem arun_pc_last (lab : Label → Int64) {blo bhi : Int} {blk : List Directive} {pc : Int64}
    {o : Spike.Lib.A64.Flow.SO} {σ : Spike.Lib.A64.Flow.AS} (h : Spike.Lib.A64.Flow.okBlk blo bhi o blk = true)
    {n : Nat} (hn : n + 1 = blk.length) {a : Spike.Lib.A64.Flow.AI}
    (ha : Spike.Lib.A64.Flow.classify (blk[n]'(by omega)) = some a) :
    (Spike.Lib.A64.Flow.arun lab blk ⟨pc, o, σ⟩).pc =
      a.tgt lab (pc + Int64.ofNat (4 * n) + Int64.ofNat 4) (Spike.Lib.A64.Flow.arun lab (blk.take n) ⟨pc, o, σ⟩).σ := by
  have e : Spike.Lib.A64.Flow.arun lab blk ⟨pc, o, σ⟩ = Spike.Lib.A64.Flow.arun lab (blk.take (n + 1)) ⟨pc, o, σ⟩ := by
    rw [List.take_of_length_le (by omega)]
  rw [e, Spike.Lib.A64.Flow.arun_take_succ lab (by omega)]
  simp only [Spike.Lib.A64.Flow.dstep, ha]
  rw [Spike.Lib.A64.Flow.arun_pc lab (am := ⟨pc, o, σ⟩) h (by omega)]

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}

/-- **The pc after a checked one is free.** -/
theorem freeAt_succ (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {k m : Nat} (h : freeAt l k m = true) {j : Nat} (hj : j + 1 < m) :
    freeN (L.lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j) + Int64.ofNat 4).toBitVec.toNat = true := by
  have := freeAt_pc hlab h (j := j + 1) hj
  rwa [show Int64.ofNat (4 * (j + 1)) = Int64.ofNat (4 * j) + Int64.ofNat 4 by
    rw [Nat.mul_succ, Int64.ofNat_add], ← Int64.add_assoc] at this

/-- The labels the heap abort's entry reads, below `2 ^ 64` (with room for `+ 8`). -/
theorem abortLab (l : Label) (h : l ∈ [("scc_rt_abort" : Label), "scc_rt_thr_worker", ".L2_scc_rt_alloc.4_full",
    ".L3_scc_rt_alloc_tcb.sp13", ".L21_wc_main.sp11"]) :
    (codeOf lo wakeProg l).isSome = true ∧ cv l + 8 < 2 ^ 64 := by
  have : [("scc_rt_abort" : Label), "scc_rt_thr_worker", ".L2_scc_rt_alloc.4_full", ".L3_scc_rt_alloc_tcb.sp13",
      ".L21_wc_main.sp11"].all (fun l => (codeOf lo wakeProg l).isSome && decide (cv l + 8 < 2 ^ 64)) = true := by
    unfold cv; rw [← codeT_eq]; decide +kernel
  have := List.all_eq_true.mp this l h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

/-- The abort range is nonempty and `x30` past the abort's `bl` is neither return
point `ownG` reads. -/
theorem abortCv : cv "scc_rt_abort" < cv "scc_rt_thr_worker" ∧
    cv ".L2_scc_rt_alloc.4_full" + 8 ≠ cv ".L3_scc_rt_alloc_tcb.sp13" ∧
    cv ".L2_scc_rt_alloc.4_full" + 8 ≠ cv ".L21_wc_main.sp11" := by
  have : (decide (cv "scc_rt_abort" < cv "scc_rt_thr_worker") &&
    decide (cv ".L2_scc_rt_alloc.4_full" + 8 ≠ cv ".L3_scc_rt_alloc_tcb.sp13") &&
    decide (cv ".L2_scc_rt_alloc.4_full" + 8 ≠ cv ".L21_wc_main.sp11")) = true := by
    unfold cv; rw [← codeT_eq]; decide +kernel
  simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using this

/-- **The heap abort's entry from `scc_rt_alloc`** is where `ownG` picks
`ownW`: in the abort range, `x30` past the `bl` (neither return point
`ownG` reads there). -/
theorem goodW_abort (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hpc : pcOf s = (L.lab "scc_rt_abort").toBitVec.toNat)
    (hx : s.st.1.regs.X30.toBitVec =
      BitVec.ofInt 64 (((L.lab ".L2_scc_rt_alloc.4_full").toInt + 4 + 4).bmod 18446744073709551616)) :
    GoodW L s := by
  obtain ⟨sA, bA⟩ := abortLab "scc_rt_abort" (by simp)
  obtain ⟨sT, bT⟩ := abortLab "scc_rt_thr_worker" (by simp)
  obtain ⟨sF, bF⟩ := abortLab ".L2_scc_rt_alloc.4_full" (by simp)
  obtain ⟨s13, b13⟩ := abortLab ".L3_scc_rt_alloc_tcb.sp13" (by simp)
  obtain ⟨s11, b11⟩ := abortLab ".L21_wc_main.sp11" (by simp)
  obtain ⟨hAT, h13, h11⟩ := abortCv
  have eA := lab_cv hlab sA (by omega)
  have eT := lab_cv hlab sT (by omega)
  have e13 := lab_cv hlab s13 (by omega)
  have e11 := lab_cv hlab s11 (by omega)
  have eF := lab_cv hlab sF (by omega)
  have ex : s.st.1.regs.X30.toBitVec.toNat = cv ".L2_scc_rt_alloc.4_full" + 8 := by
    rw [hx, Spike.Lib.A64.Flow.Ret0.ofInt_bmod, Int.add_assoc, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt,
      BitVec.toNat_add, eF]
    simp only [BitVec.toNat_ofInt]; omega
  unfold GoodW
  refine .inr (.inl ⟨⟨by rw [hpc]; exact Nat.le_refl _, by rw [hpc, eA, eT]; exact hAT⟩, fun ⟨h, _⟩ => ?_, fun h => ?_⟩)
  · have := congrArg BitVec.toNat h; rw [ex, e13] at this; exact h13 this
  · have := congrArg BitVec.toNat h; rw [ex, e11] at this; exact h11 this

section Agree

variable (hp : L.prog = wakeProg) (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlab hsite

/-- **A block's agreement** from its pcs `l + 4 k + 4 j` (free, `hfree`) and
its end (free, `hlast`). -/
theorem blkAgreeL (a : BitVec 64) {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt wakeProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi) (hfree : freeAt l k blk.length = true)
    (hlast : ∀ σ c, n.J σ c →
      freeN (Spike.Lib.A64.Flow.arun L.lab blk ⟨L.lab l + Int64.ofNat (4 * k), n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (AgW L a) (fun _ _ => False) L.exe L.endPc R F n blk :=
  blkAgreeW hlab (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) he) hok hR hal hlo' hhi hsite
    (fun j hj => by rw [← he]; exact freeAt_pc hlab hfree hj) (fun σ c hJ => by rw [← he]; exact hlast σ c hJ)

/-- **A single instruction's agreement** at `l + 4 k`, it and the next pc
free (`hfree`). -/
theorem nodeSiL (a : BitVec 64) {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [si.toDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hfree : freeAt l k 2 = true) :
    NodeW (AgW L a) (fun _ _ => False) L.exe L.endPc R F n := by
  have h0 := freeAt_pc hlab hfree (j := 0) (by omega)
  rw [ofNat4_zero] at h0
  have h1 := freeAt_succ hlab hfree (j := 0) (by omega)
  rw [ofNat4_zero] at h1
  refine nodeAgreeW hlab hsite (he ▸ h0) (he ▸ h1) ?_
  rintro s c ⟨h1', h2', -, h4', -⟩
  have hc := cell1 hp hb h1' h2' (h4'.trans he.symm)
  refine ⟨_, _, hc, fun imm h => ?_, Spike.Lib.A64.Flow.exec_si hc, fun s' hu => ?_⟩
  · cases si <;> cases h
  · simp only [TreeLeaf] at hu
    subst hu; rfl

set_option maxHeartbeats 1600000 in
/-- **`ownG` is `ownW` at `scc_rt_alloc`'s nodes** for a call `q` returning to
`wc_main`'s `.sp0` (`hra`), the counter and the headers unmapped under `F`
(`hq`, `hmem`, for the add's and the header store's steps). -/
theorem allocAgree (a : BitVec 64) {ms : Spike.Lib.MemSide isaLSE2} {q : Call}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hra : q.ra = (L.lab ".L21_wc_main.sp0").toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (AgW L a) (fun _ _ => False) L.exe L.endPc R F := by
  have hA := Spike.Lib.A64.AllocG.allocIn_spec (prog := wakeProg) (by decide +kernel)
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ := hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkAgreeL hp hlab hsite a h0 (by pc_tac) b0_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b0_ok (n := 6) rfl rfl]
    exact freeAt_succ hlab (l := "scc_rt_alloc") (k := 0) (m := 8) (by free_dec) (j := 6) (by omega)
  · refine blkAgreeL hp hlab hsite a h1 (by pc_tac) b1_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b1_ok (n := 3) rfl rfl]
    simp only [Spike.Lib.A64.Flow.AI.tgt]
    split
    · exact freeAt_lab hlab (l := ".L2_scc_rt_alloc.4_full") (by free_dec)
    · exact freeAt_succ hlab (l := ".L2_scc_rt_alloc.0_entry") (k := 0) (m := 5) (by free_dec) (j := 3) (by omega)
  · refine blkAgreeL hp hlab hsite a h2 (by pc_tac) b2_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b2_ok (n := 0) rfl rfl]
    exact freeAt_lab hlab (l := ".L2_scc_rt_alloc.1_cnt") (by free_dec)
  · exact nodeSiL hp hlab hsite a h3 (l := ".L2_scc_rt_alloc.1_cnt") (k := 0) (by pc_tac) (by free_dec)
  · exact nodeSiL hp hlab hsite a h4 (l := ".L2_scc_rt_alloc.1_cnt") (k := 1) (by pc_tac) (by free_dec)
  · refine blkAgreeL hp hlab hsite a h5 (by pc_tac) b3_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b3_ok (n := 2) rfl rfl]
    exact freeAt_succ hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 2) (m := 4) (by free_dec) (j := 2) (by omega)
  · have he : L.lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5) = (N L.lab ms q .rmw).pc := by pc_tac
    have f0 := freeAt_pc hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 5) (n := 2) (by free_dec) (j := 0) (by omega)
    have f1 := freeAt_succ hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 5) (m := 2) (by free_dec) (j := 0) (by omega)
    rw [ofNat4_zero] at f0 f1
    refine nodeAgreeW hlab hsite (he ▸ f0) (he ▸ f1) ?_
    rintro s c ⟨h1', h2', h3', h4', σ, hAb, hF, hJ⟩
    have hc := cell1 hp h6 h1' h2' (h4'.trans he.symm)
    have hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg .X10).toBitVec 8 = none := by
      rw [hAb.regs]; simp only [Reg64s.getXReg]; rw [hJ.2.1]; exact hmem _ (.inl rfl) _ hF
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_ldop hc hdm, fun s' hu => ?_⟩
    · cases h
    · rw [h3', EvTree.access_empty] at hu
      simp only [TreeLeaf] at hu
      obtain ⟨_, rfl⟩ := hu
      rfl
  · refine blkAgreeL hp hlab hsite a h7 (by pc_tac) b4_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b4_ok (n := 8) rfl rfl]
    simp only [Spike.Lib.A64.Flow.AI.tgt]
    split
    · exact freeAt_lab hlab (l := ".L2_scc_rt_alloc.2_slow") (by free_dec)
    · exact freeAt_succ hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 6) (m := 10) (by free_dec) (j := 8) (by omega)
  · refine blkAgreeL hp hlab hsite a h8 (by pc_tac) b5_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b5_ok (n := 0) rfl rfl]
    exact freeAt_lab hlab (l := ".L2_scc_rt_alloc.5_ok") (by free_dec)
  · refine blkAgreeL hp hlab hsite a h9 (by pc_tac) b6_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b6_ok (n := 3) rfl rfl]
    simp only [Spike.Lib.A64.Flow.AI.tgt]
    split
    · exact freeAt_lab hlab (l := ".L2_scc_rt_alloc.3_spin") (by free_dec)
    · exact freeAt_succ hlab (l := ".L2_scc_rt_alloc.2_slow") (k := 0) (m := 5) (by free_dec) (j := 3) (by omega)
  · refine blkAgreeL hp hlab hsite a h10 (by pc_tac) b7_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b7_ok (n := 0) rfl rfl]
    exact freeAt_lab hlab (l := ".L2_scc_rt_alloc.4_full") (by free_dec)
  · have he : L.lab ".L2_scc_rt_alloc.4_full" + Int64.ofNat (4 * 0) = (N L.lab ms q .full).pc := by pc_tac
    have hf : freeAt ".L2_scc_rt_alloc.4_full" 0 2 = true := by free_dec
    have hl : b9.length = 2 := rfl
    refine hagW hlab (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ h11) he) b9_ok hR hal (by omega) (by omega)
      (fun x hx k hk => ?_) (fun σ c _ k hk s m _ _ _ hs => ?_) (fun σ c _ k hk s m hAb _ _ hs => ?_)
    · rw [hsite] at hx; cases hx
      rw [← he]; exact site_ne_of_freeN hlab (freeAt_pc hlab hf (by omega))
    · exact goodW_of_freeN hlab (by unfold pcOf; rw [hs, ← he]; exact freeAt_pc hlab hf (by omega))
    · rcases Nat.lt_or_ge (k + 1) 2 with hk1 | hk1
      · refine goodW_of_freeN hlab ?_
        unfold pcOf; rw [hs, Spike.Lib.A64.Flow.arun_pc _ b9_ok (by omega), ← he]
        exact freeAt_pc hlab hf hk1
      · rw [List.take_of_length_le (by omega)] at hAb hs
        dsimp only [N] at hAb hs
        rw [Spike.Lib.A64.Alloc.b9_run] at hAb hs
        have hm : s.st.1 = m := by rw [hs]
        refine goodW_abort hlab (by unfold pcOf; rw [hs]) ?_
        rw [hm, hAb.regs]
  · refine blkAgreeL hp hlab hsite a h12 (by pc_tac) b11_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b11_ok (n := 7) rfl rfl]
    exact freeAt_succ hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 0) (m := 9) (by free_dec) (j := 7) (by omega)
  · exact nodeSiL hp hlab hsite a h13 (l := ".L2_scc_rt_alloc.5_ok") (k := 8) (by pc_tac) (by free_dec)
  · exact nodeSiL hp hlab hsite a h14 (l := ".L2_scc_rt_alloc.5_ok") (k := 9) (by pc_tac) (by free_dec)
  · refine blkAgreeL hp hlab hsite a h15 (by pc_tac) b12_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b12_ok (n := 30) rfl rfl]
    exact freeAt_succ hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 10) (m := 32) (by free_dec) (j := 30) (by omega)
  · have he : L.lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41) = (N L.lab ms q .hdr).pc := by pc_tac
    have f0 := freeAt_pc hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 41) (n := 2) (by free_dec) (j := 0) (by omega)
    have f1 := freeAt_succ hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 41) (m := 2) (by free_dec) (j := 0) (by omega)
    rw [ofNat4_zero] at f0 f1
    refine nodeAgreeW hlab hsite (he ▸ f0) (he ▸ f1) ?_
    rintro s c ⟨h1', h2', h3', h4', σ, hAb, hF, hJ⟩
    obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, h10⟩ := hJ
    have hc := cell1 hp h16 h1' h2' (h4'.trans he.symm)
    have hAeq := Spike.Lib.A64.AllocG.hdr_addrS (hq _ hF) hle hn28 h10
    have ha : BitVec.ofInt 64 ((s.st.1.regs.getXReg .X10).toBitVec.toInt + (0 : Int64).toInt) =
        Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 := by rw [hAb.regs]; rfl
    refine ⟨_, _, hc, fun imm h => ?_,
      Kraken.Promising.Lower.A64.exec_str hc ha (hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) _ hF), fun s' hu => ?_⟩
    · cases h
    · rw [h3', EvTree.access_empty] at hu
      simp only [TreeLeaf] at hu
      obtain ⟨_, rfl⟩ := hu
      rfl
  · refine blkAgreeL hp hlab hsite a h17 (by pc_tac) b13_ok hR hal (by omega) (by omega) (by free_dec)
      fun σ c _ => ?_
    dsimp only [N]
    rw [arun_pc_last _ b13_ok (n := 11) rfl rfl]
    exact freeAt_succ hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 42) (m := 13) (by free_dec) (j := 11) (by omega)
  · have he : L.lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 54) = (N L.lab ms q .ret).pc := by pc_tac
    refine Spike.Lib.LowerA64.BlkW.nodeW (blkAgreeL hp hlab hsite a (blk := [iRet.toDir]) h18 he
      (blo := -160) (bhi := 0) (by dsimp only [N]; decide) hR hal (by omega) (by omega) (by free_dec)
      fun σ c hJ => ?_) (List.cons_ne_nil _ _)
    obtain ⟨o, -, -, -, -, -, h30, -⟩ := hJ
    have hc : Spike.Lib.A64.Flow.classify iRet.toDir = some iRet := rfl
    simp only [Spike.Lib.A64.Flow.arun, List.foldl, Spike.Lib.A64.Flow.dstep, hc]
    simp [iRet, Spike.Lib.A64.Flow.AI.tgt, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, Reg64s.getXReg,
      h30, hra]
    exact freeAt_lab hlab (l := ".L21_wc_main.sp0") (by free_dec)

end Agree

/-! ## The allocator's phase check at `phW` -/

/-- **`scc_rt_alloc`'s facts** (`allocPhOk`'s, and the phases of the entry
and of `wc_main`'s return point `.sp0`), as the certificate's table. -/
def allocTabW : List PhFact :=
  [.blk "scc_rt_alloc" 0 b0 none none, .blk ".L2_scc_rt_alloc.0_entry" 0 b1 none none,
   .blk ".L2_scc_rt_alloc.0_entry" 4 b2 none none, .step ".L2_scc_rt_alloc.1_cnt" 0, .step ".L2_scc_rt_alloc.1_cnt" 1,
   .blk ".L2_scc_rt_alloc.1_cnt" 2 b3 none none, .step ".L2_scc_rt_alloc.1_cnt" 5,
   .blk ".L2_scc_rt_alloc.1_cnt" 6 b4 none none, .blk ".L2_scc_rt_alloc.1_cnt" 15 b5 none none,
   .blk ".L2_scc_rt_alloc.2_slow" 0 b6 none none, .blk ".L2_scc_rt_alloc.2_slow" 4 b7 none none,
   .blk ".L2_scc_rt_alloc.4_full" 0 b9 none none, .blk ".L2_scc_rt_alloc.5_ok" 0 b11 none none,
   .step ".L2_scc_rt_alloc.5_ok" 8, .step ".L2_scc_rt_alloc.5_ok" 9, .blk ".L2_scc_rt_alloc.5_ok" 10 b12 none none,
   .step ".L2_scc_rt_alloc.5_ok" 41, .blk ".L2_scc_rt_alloc.5_ok" 42 b13 none none,
   .ok ".L2_scc_rt_alloc.5_ok" 54, .ph ".L2_scc_rt_alloc.5_ok" 54 0, .ph "scc_rt_alloc" 0 0,
   .ph ".L21_wc_main.sp0" 0 0]

/-- The table's facts hold at the resolved phases. -/
theorem allocFactsW : allocTabW.all (factOk (codeT lo wakeProg) okC phC) = true := by decide +kernel

section Ph

variable {lab : Label → Int64} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x)
include hΛ hlab

/-- **`allocPhOk` at `phW`** with the certificate's labels. -/
theorem allocPhW : Spike.Lib.A64.AllocG.allocPhOk (okPcOf lo wakeProg Λ) phW lab = true := by
  have h := allocFactsW
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at h
  simp only [allocTabW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, -⟩ := h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = lab r := fun _ h => by cases h
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo wakeProg) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have so : ∀ {l : String} {k : Nat}, factOk (codeOf lo wakeProg) (okPcOf lo wakeProg Λ) phW (.step l k) = true →
      Spike.Lib.A64.StubW.phOne (okPcOf lo wakeProg Λ) phW (lab l + Int64.ofNat (4 * k)) = true := fun h => by
    obtain ⟨h1, h2⟩ := step_of_factOk hlab h
    simp only [Spike.Lib.A64.StubW.phOne, h1, h2, beq_self_eq_true, Bool.and_self]
  have e20 := ph_of_factOk hlab f20
  rw [ofNat4_zero] at e20
  unfold Spike.Lib.A64.AllocG.allocPhOk
  rw [blkPh_of_factOk hlab hr hn f0, blkPh_of_factOk hlab hr hn f1, blkPh_of_factOk hlab hr hn f2, so f3, so f4,
    blkPh_of_factOk hlab hr hn f5, so f6, blkPh_of_factOk hlab hr hn f7, blkPh_of_factOk hlab hr hn f8,
    blkPh_of_factOk hlab hr hn f9, blkPh_of_factOk hlab hr hn f10, blkPh_of_factOk hlab hr hn f11,
    blkPh_of_factOk hlab hr hn f12, so f13, so f14, blkPh_of_factOk hlab hr hn f15, so f16,
    blkPh_of_factOk hlab hr hn f17, ok_of_factOk hlab f18,
    ph_of_factOk hlab f19, e20]
  rfl

/-- **`wc_main`'s return point is in the phase of the allocator's entry.** -/
theorem allocRaW : phW (lab ".L21_wc_main.sp0").toBitVec.toNat = phW (lab "scc_rt_alloc").toBitVec.toNat := by
  have h := allocFactsW
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at h
  simp only [allocTabW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f20, f21⟩ := h
  have e20 := ph_of_factOk hlab f20
  have e21 := ph_of_factOk hlab f21
  rw [ofNat4_zero] at e20 e21
  rw [e20, e21]

end Ph

/-! ## `scc_rt_alloc` at `SFactsSt2`/`ownG` -/

section Inst

variable (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`scc_rt_alloc` inside `SFactsSt2` at `ownG`** (owned word `a`), none
moved by the take, for a call `q` returning to `wc_main`'s `.sp0` (`hra`):
`allocStS` at `instOkW` (no take phase, an empty stack range at the pool's
start, `hpool`) combined with `allocAgree`. The call's premises at any site (`hq`, `Call.OKS`), the
memory side's writable words mapped (`hmp`), the counter and the headers
unmapped under `F` (`hmem`) and off the owned words (`hno`). -/
theorem allocW_wcG (a : BitVec 64) {ms : Spike.Lib.MemSide isaLSE2} {q : Call}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hpool : Λ.stackPool.lo ≤ 2 ^ 64)
    (hra : q.ra = (L.lab ".L21_wc_main.sp0").toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true l = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownW L a j) :
    AllocW ms q (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F := by
  have hS := Spike.Lib.A64.AllocG.allocStS (instOkW hp hlo a (fun _ => False) hsite (rS := rS))
    (by rw [hp]; exact Spike.Lib.A64.Flow.WakeWc.wake_alloc) (allocPhW hΛ hlab) (Λ := Λ)
    (rS := ⟨Λ.stackPool.lo, 0⟩) (ownOf := ownW L a) (fun _ => rfl) hR hal hlo' hhi hl hh
    ⟨Nat.le_refl _, Nat.add_le_add_left (Nat.zero_le _) _⟩ (by simpa using hpool)
    (fun _ _ _ _ hc _ _ => absurd hc (by simp only [Scc.Sem.Range.contains]; omega)) hq
    (by rw [hra, Int64.ofBitVec_toBitVec]; exact allocRaW hΛ hlab) hmp hmem hno
  exact Spike.Lib.A64.AllocG.AllocW.imp hS (allocAgree hp hlab hsite a hR hal hlo' hhi hra hq hmem)
    fun s _ h1 h2 => h1.toSt2.congr h2.1 h2.2

end Inst

end Spike.Lib.A64.WakePh.WcW

/-- info: 'Spike.Lib.A64.WakePh.WcW.allocAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.allocAgree

/-- info: 'Spike.Lib.A64.WakePh.WcW.allocPhW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.allocPhW

/-- info: 'Spike.Lib.A64.WakePh.WcW.allocW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.allocW_wcG
