/-
**`scc_rt_alloc` inside `SFactsSt2` at `ownGH`** (x86-64; hello twin of
`Spike/Lib/A64HelloAllocWI.lean`): the allocator in `HelloRd.RdPreW.alloc`
(rodata's buffer, returning to `.Lwc_rodata.x15`) and `wc_main`'s box
(returning to `.Lwc_main.x22`) at the pre-spawn chain's `W`.
`AllocG.allocStS` at the first instance (`instOkH`, owned words `ownH L a`,
no take phase) combined (`AllocW.imp`) with the agreement of `ownGH` and
`ownH` at the allocator's nodes: every allocator pc is free (`freeNH`), and
so is every successor except the heap abort's `call`, whose target
`scc_rt_abort` is in `ownGH`'s abort range with the return address it pushes
neither of the two return points `ownGH` reads there
(`.Lscc_rt_alloc_tcb.x6`, `.Lwc_main.x27`). Unlike wake's, the return point
is a parameter `rl` (`AllocRetH`: one of the two calls' return points).

The pcs and phase facts are checked by the kernel against the certificate's
labels, with no absolute address in this file.

- `freeAt_addH`: a free pc `k + z` bytes after a label.
- `abortLabsH`, `abortCvH`, `goodW_abortH`: at the heap abort's entry from
  `scc_rt_alloc`, `ownGH` picks `ownH`.
- `AllocRetH`, `AllocRetH.free`: the two return points, both free.
- `blkAgreeLH`, `nodeSiLH`, `nodeFiLH`: a block's, a single instruction's
  and an instruction with undefined flags' agreement.
- `allocAgreeH`: the agreement at every node of `AllocW`.
- `allocTabH`, `allocFactsH`, `allocPhH`, `allocRaH`: the allocator's phase
  check at `phH`.
- `allocW_wcGH`: `AllocW` at `SFactsSt2`/`ownGH`.

**Where this differs from AArch64**: the allocator's blocks are byte-sized
`(Directive × Nat)` lists at byte offsets, so the free pcs are lists of byte
offsets (`freeAtH l os`) and the counter's add (`lock xaddq`) and the header's
store are single nodes proved by `exec_xaddG_agrees`/`exec_store_agrees`
rather than steps at 4-byte word indices; instructions with undefined flags get their own
lemma (`nodeFiLH`). The heap abort is a `call`, so `goodW_abortH` reads the
pushed return address `.full + 12` at `%rsp` rather than `x30`.
-/
import Spike.Lib.X64HelloWcResWI
import Spike.Lib.X64WakeWcAllocWI

namespace Spike.Lib.X64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhFact codeT codeT_eq factOk blockAtB okPcOf code_field)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf privLoad)
open SccCode (helloCells)
open Spike.Lib.X64.HelloPh
open Spike.Lib.X64.WakePh (raAt raAddr raSp abFns)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At arun mB eaddr_mB agrees_of_decls SI FI)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add')
open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet fnL entryL cntL slowL fullL okL oE bPro bChk
  bJ1 bC1 bC2 bJ2 bSlow bJ3 bFull bO0 bO1 bO2 bO3 bO4 bO5 bO6 bO7 bO8 bO9 bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok
  bJ2_ok bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)
open Kraken.Promising.Lower.X64 (CellAt exec_xaddG_agrees exec_store_agrees)
open Spike.Lib.X64.Rt.PhOfTab (blkPh_of_factOk step_of_factOk ok_of_factOk ph_of_factOk)

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}

/-- **A free pc `k + z` bytes after a label**, as `lab l + ofNat k + ofNat z`. -/
theorem freeAt_addH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {k z : Nat} (h : freeAtH l [k + z] = true) :
    freeNH (L.lab l + Int64.ofNat k + Int64.ofNat z).toBitVec.toNat = true := by
  have := freeAt_pcH hlab h (List.mem_singleton.mpr rfl)
  rwa [ofNat_add'] at this

/-! ## The heap abort's entry -/

/-- The labels the heap abort's entry reads, below `2 ^ 64` (with room for `+ 12`). -/
theorem abortLabsH (l : Label) (h : l ∈ [("scc_rt_abort" : Label), "scc_rt_thr_worker", ".Lscc_rt_alloc.full",
    ".Lscc_rt_alloc_tcb.x6", ".Lwc_main.x27"]) :
    (codeLabel lo helloCells l).isSome = true ∧ cvH l + 12 < 2 ^ 64 := by
  have : [("scc_rt_abort" : Label), "scc_rt_thr_worker", ".Lscc_rt_alloc.full", ".Lscc_rt_alloc_tcb.x6",
      ".Lwc_main.x27"].all (fun l => (codeLabel lo helloCells l).isSome && decide (cvH l + 12 < 2 ^ 64)) = true := by
    unfold cvH; rw [← codeT_eq]; decide +kernel
  have := List.all_eq_true.mp this l h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

/-- The abort range is nonempty and the return address past the abort's
`call` is neither return point `ownGH` reads. -/
theorem abortCvH : cvH "scc_rt_abort" < cvH "scc_rt_thr_worker" ∧
    cvH ".Lscc_rt_alloc.full" + 12 ≠ cvH ".Lscc_rt_alloc_tcb.x6" ∧
    cvH ".Lscc_rt_alloc.full" + 12 ≠ cvH ".Lwc_main.x27" := by
  have : (decide (cvH "scc_rt_abort" < cvH "scc_rt_thr_worker") &&
    decide (cvH ".Lscc_rt_alloc.full" + 12 ≠ cvH ".Lscc_rt_alloc_tcb.x6") &&
    decide (cvH ".Lscc_rt_alloc.full" + 12 ≠ cvH ".Lwc_main.x27")) = true := by
    unfold cvH; rw [← codeT_eq]; decide +kernel
  simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using this

/-- **The heap abort's entry from `scc_rt_alloc`** is where `ownGH` picks
`ownH`: in the abort range, the word at `%rsp` (the return address word
`raAddr` reads at the dispatcher's entry) the `call`'s return address
`.full + 12` (neither return point `ownGH` reads there). -/
theorem goodW_abortH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hpc : pcOf s = (L.lab "scc_rt_abort").toBitVec.toNat)
    (hra : privLoad s s.st.1.regs.rsp.toBitVec = some ((L.lab ".Lscc_rt_alloc.full").toBitVec + 12#64)) :
    GoodWH L s := by
  obtain ⟨sA, bA⟩ := abortLabsH "scc_rt_abort" (by simp)
  obtain ⟨sT, bT⟩ := abortLabsH "scc_rt_thr_worker" (by simp)
  obtain ⟨sF, bF⟩ := abortLabsH ".Lscc_rt_alloc.full" (by simp)
  obtain ⟨s6, b6⟩ := abortLabsH ".Lscc_rt_alloc_tcb.x6" (by simp)
  obtain ⟨s27, b27⟩ := abortLabsH ".Lwc_main.x27" (by simp)
  obtain ⟨hAT, h6, h27⟩ := abortCvH
  have eA := lab_cvH hlab sA (by omega)
  have eT := lab_cvH hlab sT (by omega)
  have eF := lab_cvH hlab sF (by omega)
  have e6 := lab_cvH hlab s6 (by omega)
  have e27 := lab_cvH hlab s27 (by omega)
  have hin : pcOf s ∈ raSp L := by
    rw [hpc]; simp [raSp, abFns]
  have hA : raAddr L s = s.st.1.regs.rsp.toBitVec := by simp only [raAddr, hin, ↓reduceIte]
  have hv : ∀ l, raAt L l s → ((L.lab ".Lscc_rt_alloc.full").toBitVec + 12#64).toNat = (L.lab l).toBitVec.toNat :=
    fun l h => by
      unfold raAt at h; rw [hA, hra, Option.some.injEq] at h; rw [h]
  have ex : ((L.lab ".Lscc_rt_alloc.full").toBitVec + 12#64).toNat = cvH ".Lscc_rt_alloc.full" + 12 := by
    rw [BitVec.toNat_add, eF]; simp only [BitVec.toNat_ofNat]; omega
  unfold GoodWH
  refine .inr (.inl ⟨⟨by rw [hpc]; exact Nat.le_refl _, by rw [hpc, eA, eT]; exact hAT⟩, fun ⟨h, _⟩ => ?_,
    fun h => ?_⟩)
  · have := hv _ h; rw [ex, e6] at this; exact h6 this
  · have := hv _ h; rw [ex, e27] at this; exact h27 this

/-- **The allocator's return points at hello**: rodata's buffer call's
`.Lwc_rodata.x15` and `wc_main`'s box call's `.Lwc_main.x22`. -/
def AllocRetH (rl : Label) : Prop := rl = ".Lwc_rodata.x15" ∨ rl = ".Lwc_main.x22"

/-- Both return points are free. -/
theorem AllocRetH.free {rl : Label} (h : AllocRetH rl) : freeAtH rl [0] = true := by
  rcases h with rfl | rfl <;> wcfreeH_dec

/-! ## The agreement at the allocator's nodes -/

section Agree

variable (hp : L.prog = helloCells) (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlab hsite

/-- **A block's agreement** from its code at `lab l + k`, its free pcs
(`freeBlkH`) and its free end (`hlast`). -/
theorem blkAgreeLH (a : BitVec 64) {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat}
    {blo bhi : Int} (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : Spike.Lib.X64.okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hfree : freeBlkH l k blk = true)
    (hlast : ∀ σ c, n.J σ c → freeNH (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (ResAgWH L a) (fun _ _ => False) L.exe L.endPc R F n blk :=
  blkAgreeWH hlab (code_field L.lays rfl (hp ▸ hb) he) hok hR hlo' hhi hsite
    (fun j hj => by rw [← he]; exact freeBlk_pcH hlab hfree hj) hlast

/-- **A single instruction's agreement** at `lab l + k` (`z` bytes), it and
the next pc free (`hfree`). -/
theorem nodeSiLH (a : BitVec 64) {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hfree : freeAtH l [k, k + z] = true) :
    NodeW (ResAgWH L a) (fun _ _ => False) L.exe L.endPc R F n := by
  have f0 := freeAt_pcH hlab hfree (o := k) (by simp)
  have f1 := freeAt_pcH hlab hfree (o := k + z) (by simp)
  rw [ofNat_add', he] at f1
  rw [he] at f0
  refine nodeAgreeWH hlab hsite f0 f1 ?_
  rintro s c ⟨h1, h2, -, h4, -⟩
  have hc : CellAt s si.toDir z := (code_field L.lays rfl (hp ▸ hb) he s h1 h2).cell0 rfl rfl h4
  refine ⟨_, _, hc, fun w w' h => ?_, Spike.Lib.X64.exec_si hc, fun s' hu => ?_⟩
  · cases si; cases h
  · simp only [TreeLeaf] at hu
    subst hu; rfl

/-- **An instruction with undefined flags' agreement** at `lab l + k` (`z`
bytes), it and the next pc free (`hfree`). -/
theorem nodeFiLH (a : BitVec 64) {n : ND} {fi : FI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(fi.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hfree : freeAtH l [k, k + z] = true) :
    NodeW (ResAgWH L a) (fun _ _ => False) L.exe L.endPc R F n := by
  have f0 := freeAt_pcH hlab hfree (o := k) (by simp)
  have f1 := freeAt_pcH hlab hfree (o := k + z) (by simp)
  rw [ofNat_add', he] at f1
  rw [he] at f0
  refine nodeAgreeWH hlab hsite f0 f1 ?_
  rintro s c ⟨h1, h2, -, h4, -⟩
  have hc : CellAt s fi.toDir z := (code_field L.lays rfl (hp ▸ hb) he s h1 h2).cell0 rfl rfl h4
  obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
  refine ⟨_, t, hc, fun w w' h => ?_, hex, fun s' hu => ?_⟩
  · cases fi <;> cases h
  · obtain ⟨_, rfl⟩ := Spike.Lib.X64.WakeWf.silentLeaf hst hu; rfl

/-- The free end of a block of `scc_rt_alloc`, `o` bytes after a label. -/
local macro "fend " l:term:max o:term:max : tactic =>
  `(tactic| exact freeAt_pcH hlab (l := $l) (os := [$o]) (o := $o) (by wcfreeH_dec) (List.mem_singleton.mpr rfl))

/-- The free end of a block of `scc_rt_alloc` at `lab l + k`, `z` bytes on. -/
local macro "fadd " l:term:max k:term:max z:term:max : tactic =>
  `(tactic| exact freeAt_addH hlab (l := $l) (k := $k) (z := $z) (by wcfreeH_dec))

/-- The free end of a block of `scc_rt_alloc` at a label. -/
local macro "flab " l:term:max : tactic =>
  `(tactic| exact freeAt_labH hlab (l := $l) (by wcfreeH_dec))

set_option maxHeartbeats 1600000 in
/-- **`ownGH` is `ownH` at `scc_rt_alloc`'s nodes** for a call `q`
returning to a free label `rl` (`hrl`, `hra`), the counter and the headers
unmapped under `F` (`hq`, `hmem`, for the add's and the header store's
steps), in a region of the allocator's frame. -/
theorem allocAgreeH (a : BitVec 64) {ms : Spike.Lib.MemSide isa} {q : Call}
    (hR : R.OK) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi) {rl : Label} (hrl : freeAtH rl [0] = true)
    (hra : q.ra = (L.lab rl).toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (ResAgWH L a) (fun _ _ => False) L.exe L.endPc R F := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := Spike.Lib.X64.AllocG.allocIn_spec
      Spike.Lib.X64.Flow.HelloRd.hello_alloc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine blkAgreeLH hp hlab hsite a h0 (by pc_tac) bPro_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bPro_run]; fend fnL 23
  · refine blkAgreeLH hp hlab hsite a h1 (by pc_tac) bChk_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bChk_run]
    split
    · flab fullL
    · fend entryL 16
  · refine blkAgreeLH hp hlab hsite a h2 (by pc_tac) bJ1_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bJ1_run]; flab cntL
  · exact nodeSiLH hp hlab hsite a h3 (by pc_tac) (by wcfreeH_dec)
  · refine blkAgreeLH hp hlab hsite a h4 (by pc_tac) bC1_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bC1_run]; fadd cntL 7 12
  · -- The counter's add, `lock xaddq %rax, (%rcx)`.
    have he : L.lab cntL + Int64.ofNat 19 = (N L.lab ms q .rmw).pc := rfl
    have hfr : freeAtH cntL [19, 19 + 5] = true := by wcfreeH_dec
    have f0 := freeAt_pcH hlab hfr (o := 19) (by simp)
    have f1 := freeAt_pcH hlab hfr (o := 19 + 5) (by simp)
    rw [ofNat_add'] at f1
    refine nodeAgreeWH hlab hsite (z := 5) f0 f1 ?_
    rintro s c ⟨h1', h2', h3', h4', σ, hA, hF, hJ⟩
    have hc : CellAt s iRmw 5 := (code_field L.lays rfl (hp ▸ h5) he s h1' h2').cell0 rfl rfl h4'
    have ha' : Kraken.Promising.Lower.X64.eaddr s 5 (mB .rcx 0) = BitVec.ofNat 64 ms.ctr :=
      (eaddr_mB s 5 .rcx 0).trans (by
        rw [hA.regs, ← Spike.Lib.X64.AllocG.ctr_addrS (hq _ hF) hJ.2.1]; rfl)
    refine ⟨_, _, hc, fun w w' h => (by cases h),
      exec_xaddG_agrees (w := .W64) hc ha' (hmem _ (.inl rfl) _ hF) (agrees_of_decls h3' _ _), fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl
  · refine blkAgreeLH hp hlab hsite a h6 (by pc_tac) bC2_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bC2_run]
    split
    · flab slowL
    · fadd cntL 24 35
  · refine blkAgreeLH hp hlab hsite a h7 (by pc_tac) bJ2_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bJ2_run]; flab okL
  · refine blkAgreeLH hp hlab hsite a h8 (by pc_tac) bSlow_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bSlow_run]
    split
    · flab ".Lscc_rt_alloc.spin"
    · fend slowL 16
  · refine blkAgreeLH hp hlab hsite a h9 (by pc_tac) bJ3_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bJ3_run]; flab fullL
  · -- The heap abort's block: its last step enters `scc_rt_abort`.
    have he : L.lab fullL + Int64.ofNat 0 = (N L.lab ms q .full).pc := by pc_tac
    have hf : freeBlkH fullL 0 bFull = true := by wcfreeBH_dec
    refine hagWH hlab (code_field L.lays rfl (hp ▸ h10) he) bFull_ok hR (by omega) (by omega)
      (fun x hx k hk => ?_) (fun σ c _ k hk s m _ _ _ hs => ?_) (fun σ c _ k hk s m hAb _ _ hs => ?_)
    · rw [hsite] at hx; cases hx
      rw [← he]; exact site_ne_of_freeNH hlab (freeBlk_pcH hlab hf hk)
    · exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs, ← he]; exact freeBlk_pcH hlab hf hk)
    · rcases Nat.lt_or_ge (k + 1) bFull.length with hk1 | hk1
      · refine goodW_of_freeNH hlab ?_
        unfold pcOf; rw [hs, Spike.Lib.X64.arun_pc _ bFull_ok hk1, ← he]
        exact freeBlk_pcH hlab hf hk1
      · rw [List.take_of_length_le (by omega)] at hAb hs
        dsimp only [N] at hAb hs
        rw [Spike.Lib.X64.Alloc.bFull_run] at hAb hs
        have hm : s.st.1 = m := by rw [hs]
        refine goodW_abortH hlab (by unfold pcOf; rw [hs]) ?_
        obtain ⟨j, hj1, hj2⟩ := hAb.slot (-160) ⟨by decide, hlo', by omega⟩
        rw [hm, Spike.Lib.X64ConsumerA.rsp_of_abs hAb]
        unfold privLoad
        rw [hm, hj1, Option.map_some, hj2]
        simp [Spike.Lib.upd]
  · refine blkAgreeLH hp hlab hsite a h11 (by pc_tac) bO0_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO0_run]; fend okL 11
  · exact nodeFiLH hp hlab hsite a h12 (by pc_tac) (by wcfreeH_dec)
  · refine blkAgreeLH hp hlab hsite a h13 (by pc_tac) bO1_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO1_run]; fadd okL 14 15
  · exact nodeFiLH hp hlab hsite a h14 (by pc_tac) (by wcfreeH_dec)
  · refine blkAgreeLH hp hlab hsite a h15 (by pc_tac) bO2_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO2_run]; fadd okL 32 4
  · exact nodeSiLH hp hlab hsite a h16 (by pc_tac) (by wcfreeH_dec)
  · refine blkAgreeLH hp hlab hsite a h17 (by pc_tac) bO3_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO3_run]; fadd okL 43 15
  · exact nodeFiLH hp hlab hsite a h18 (by pc_tac) (by wcfreeH_dec)
  · refine blkAgreeLH hp hlab hsite a h19 (by pc_tac) bO4_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO4_run]; fadd okL 61 27
  · exact nodeFiLH hp hlab hsite a h20 (by pc_tac) (by wcfreeH_dec)
  · refine blkAgreeLH hp hlab hsite a h21 (by pc_tac) bO5_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO5_run]; fadd okL 92 15
  · exact nodeFiLH hp hlab hsite a h22 (by pc_tac) (by wcfreeH_dec)
  · refine blkAgreeLH hp hlab hsite a h23 (by pc_tac) bO6_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO6_run]; fadd okL 110 15
  · exact nodeFiLH hp hlab hsite a h24 (by pc_tac) (by wcfreeH_dec)
  · refine blkAgreeLH hp hlab hsite a h25 (by pc_tac) bO7_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO7_run]; fadd okL 128 12
  · exact nodeFiLH hp hlab hsite a h26 (by pc_tac) (by wcfreeH_dec)
  · refine blkAgreeLH hp hlab hsite a h27 (by pc_tac) bO8_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO8_run]; fadd okL 143 27
  · -- The header's store, `movq %rax, (%rcx)`.
    have he : L.lab okL + Int64.ofNat 170 = (N L.lab ms q .hdr).pc := rfl
    have hfr : freeAtH okL [170, 170 + 3] = true := by wcfreeH_dec
    have f0 := freeAt_pcH hlab hfr (o := 170) (by simp)
    have f1 := freeAt_pcH hlab hfr (o := 170 + 3) (by simp)
    rw [ofNat_add'] at f1
    refine nodeAgreeWH hlab hsite (z := 3) f0 f1 ?_
    rintro s c ⟨h1', h2', h3', h4', σ, hA, hF, hJ⟩
    obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, hcx⟩ := hJ
    have hc : CellAt s iHdr 3 := (code_field L.lays rfl (hp ▸ h28) he s h1' h2').cell0 rfl rfl h4'
    have ha' : Kraken.Promising.Lower.X64.eaddr s 3 (mB .rcx 0) = Spike.Lib.X64.bAddr σ.regs .rcx 0 :=
      (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs]; rfl)
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_store_agrees hc ha'
      (hmem _ (.inr ⟨o.toNat, hle, Spike.Lib.X64.AllocG.hdr_addrS (hq _ hF) hle hn28 hcx⟩) _ hF)
      (agrees_of_decls h3' _ _), fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl
  · refine blkAgreeLH hp hlab hsite a h29 (by pc_tac) bO9_ok hR hlo' hhi (by wcfreeBH_dec) fun σ c _ => ?_
    dsimp only [N]; rw [Spike.Lib.X64.Alloc.bO9_run]; fadd okL 173 53
  · -- The `ret`, to `rl`.
    refine Spike.Lib.LowerX64.BlkW.nodeW (blkAgreeLH hp hlab hsite a (blk := [(iRet.toDir, 1)]) h30 rfl
      (blo := -160) (bhi := 8) (by dsimp only [N]; decide) hR hlo' hhi (by wcfreeBH_dec)
      fun σ c hJ => ?_) (List.cons_ne_nil _ _)
    obtain ⟨o, -, -, -, -, -, h30', -⟩ := hJ
    have hc : Spike.Lib.X64.classify iRet.toDir = some iRet := rfl
    simp only [Spike.Lib.X64.arun, List.foldl, Spike.Lib.X64.dstep, hc]
    simp only [N, iRet, Spike.Lib.X64.AI.tgt, h30', hra, Int64.ofBitVec_toBitVec]
    exact freeAt_labH hlab hrl

end Agree

/-! ## The allocator's phase check at `phH` -/

/-- **`scc_rt_alloc`'s facts** (`allocPhOk`'s, and the phases of the entry
and of the two return points), as the certificate's table. -/
def allocTabH : List PhFact :=
  [.blk fnL 0 bPro none none, .blk entryL 0 bChk none none, .blk entryL 16 bJ1 none none, .step cntL 0 7,
   .blk cntL 7 bC1 none none, .step cntL 19 5, .blk cntL 24 bC2 none none, .blk cntL 59 bJ2 none none,
   .blk slowL 0 bSlow none none, .blk slowL 16 bJ3 none none, .blk fullL 0 bFull none none,
   .blk okL 0 bO0 none none, .step okL 11 3, .blk okL 14 bO1 none none, .step okL 29 3, .blk okL 32 bO2 none none,
   .step okL 36 7, .blk okL 43 bO3 none none, .step okL 58 3, .blk okL 61 bO4 none none, .step okL 88 4,
   .blk okL 92 bO5 none none, .step okL 107 3, .blk okL 110 bO6 none none, .step okL 125 3,
   .blk okL 128 bO7 none none, .step okL 140 3, .blk okL 143 bO8 none none, .step okL 170 3,
   .blk okL 173 bO9 none none, .ok okL 226, .ph okL 226 0, .ph fnL 0 0, .ph ".Lwc_rodata.x15" 0 0,
   .ph ".Lwc_main.x22" 0 0]

/-- The table's facts hold at the resolved phases. -/
theorem allocFactsH : allocTabH.all (factOk (codeT lo helloCells) okC phC) = true := by decide +kernel

section Ph

variable {lab : Label → Int64} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x)
include hΛ hlab

/-- **`allocPhOk` at `phH`** with the certificate's labels. -/
theorem allocPhH : Spike.Lib.X64.AllocG.allocPhOk (okPcOf lo helloCells Λ) phH lab = true := by
  have h := allocFactsH
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at h
  simp only [allocTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22,
    f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, -, -⟩ := h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (codeLabel lo helloCells) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have so : ∀ {l : String} {k z : Nat},
      factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH (.step l k z) = true →
      Spike.Lib.X64.StubW.phOne (okPcOf lo helloCells Λ) phH (lab l + Int64.ofNat k) z = true := fun h => by
    obtain ⟨h1, h2⟩ := step_of_factOk hlab h
    simp only [Spike.Lib.X64.StubW.phOne, h1, h2, beq_self_eq_true, Bool.and_self]
  have e32 := ph_of_factOk hlab f32
  rw [ofNat_zero'] at e32
  unfold Spike.Lib.X64.AllocG.allocPhOk Spike.Lib.X64.AllocG.aBlk
  rw [blkPh_of_factOk hlab hr hn f0, blkPh_of_factOk hlab hr hn f1, blkPh_of_factOk hlab hr hn f2, so f3,
    blkPh_of_factOk hlab hr hn f4, so f5, blkPh_of_factOk hlab hr hn f6, blkPh_of_factOk hlab hr hn f7,
    blkPh_of_factOk hlab hr hn f8, blkPh_of_factOk hlab hr hn f9, blkPh_of_factOk hlab hr hn f10,
    blkPh_of_factOk hlab hr hn f11, so f12, blkPh_of_factOk hlab hr hn f13, so f14, blkPh_of_factOk hlab hr hn f15,
    so f16, blkPh_of_factOk hlab hr hn f17, so f18, blkPh_of_factOk hlab hr hn f19, so f20,
    blkPh_of_factOk hlab hr hn f21, so f22, blkPh_of_factOk hlab hr hn f23, so f24, blkPh_of_factOk hlab hr hn f25,
    so f26, blkPh_of_factOk hlab hr hn f27, so f28, blkPh_of_factOk hlab hr hn f29, ok_of_factOk hlab f30,
    ph_of_factOk hlab f31, e32]
  rfl

/-- **Both return points are in the phase of the allocator's entry.** -/
theorem allocRaH {rl : Label} (hrl : AllocRetH rl) :
    phH (lab rl).toBitVec.toNat = phH (lab fnL).toBitVec.toNat := by
  have h := allocFactsH
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at h
  simp only [allocTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f32,
    f33, f34⟩ := h
  have e32 := ph_of_factOk hlab f32
  have e33 := ph_of_factOk hlab f33
  have e34 := ph_of_factOk hlab f34
  rw [ofNat_zero'] at e32 e33 e34
  rcases hrl with rfl | rfl
  · rw [e32, e33]
  · rw [e32, e34]

end Ph

/-! ## `scc_rt_alloc` at `SFactsSt2`/`ownGH` -/

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`scc_rt_alloc` inside `SFactsSt2` at `ownGH`** (owned word `a`), none
moved by the take, for a call `q` returning to one of the two return points (`hrl`, `hra`):
`allocStS` at `instOkH` (no take phase, an empty stack range at the pool's
start, `hpool`) combined with `allocAgreeH`. The call's premises at any site
(`hq`, `Call.OKS`), the memory side's writable words mapped (`hmp`), the
counter and the headers unmapped under `F` (`hmem`) and off the owned words
(`hno`). -/
theorem allocW_wcGH (a : BitVec 64) {ms : Spike.Lib.MemSide isa} {q : Call}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hpool : Λ.stackPool.lo ≤ 2 ^ 64)
    {rl : Label} (hrl : AllocRetH rl) (hra : q.ra = (L.lab rl).toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true l = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j) :
    AllocW ms q (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F := by
  have hS := Spike.Lib.X64.AllocG.allocStS (instOkH hp hlo a (fun _ => False) hsite (rS := rS))
    (by rw [hp]; exact Spike.Lib.X64.Flow.HelloRd.hello_alloc) (allocPhH hΛ hlab) (Λ := Λ)
    (rS := ⟨Λ.stackPool.lo, 0⟩) (ownOf := ownH L a) (fun _ => rfl) hR hR8 hlo' hhi hl hh
    ⟨Nat.le_refl _, Nat.add_le_add_left (Nat.zero_le _) _⟩ (by simpa using hpool)
    (fun _ _ _ _ hc _ _ => absurd hc (by simp only [Scc.Sem.Range.contains]; omega)) hq
    (by rw [hra, Int64.ofBitVec_toBitVec]; exact allocRaH hΛ hlab hrl) hmp hmem hno
  exact Spike.Lib.X64.AllocG.AllocW.imp hS
    (allocAgreeH hp hlab hsite a hR hlo' hhi (AllocRetH.free hrl) hra hq hmem)
    fun s _ h1 h2 => h1.toSt2.congr h2.1 h2.2

end Inst

end Spike.Lib.X64.HelloPh.WcW

/-- info: 'Spike.Lib.X64.HelloPh.WcW.goodW_abortH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.goodW_abortH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.allocAgreeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.allocAgreeH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.allocPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.allocPhH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.allocW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.allocW_wcGH
