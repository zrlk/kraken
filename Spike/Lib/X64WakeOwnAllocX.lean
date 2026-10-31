/-
**`wc_main`'s allocator at `ownGXW`** (x86-64; X64-OwnW Wc group): `WcW.allocW_wcG` (`scc_rt_alloc`
called from `wc_main`, returning to
`.x18`, inside `SFactsSt2` at `ownG`) moved to `SFactsSt2` at `ownGXW`
(`Lft2`), from outside (`AllocG.AllocW.imp`). The allocator's frame
`[-160, 8]` is on the pool (`hb : BandOnP L R (-160) 8`):
- its pcs, the slow path's `.spin` and the return point `.x18` are from
  `.x1` on in none of `InT`, `InC`, `InAb` (`QP`, off the take site:
  `PP`), so they hold `tcbM` only (`cls_pool`);
- the heap abort's entry `scc_rt_abort` (in `InAb`) holds `tcbM` only too:
  on the pool from `.x1` on (`selfOwn`), and the return address the `call`
  pushes is `.full + 12`, not `.x23` (not `selfOwnW`; `cst_abortA`);
- its two shared writes (the counter's `lock xaddq`, the header's store)
  miss `tcbM` (`hnoM`).

- `labN`: a label's value from the certificate.
- `cst_abortA`: `Cst L (tM L) []` at the heap abort's entry from the
  allocator.
- `allocL`: the allocator's nodes inside `Lft2`.
- `allocW_wcGX`: `allocW_wcG` at `ownGXW`.

**Deviations.** None: new lemmas. `allocW_wcGX` takes `ownGXW`'s
separation premises (`hsep`, `ha`, `hW`), the frame's band on the pool
(`hb`) and `hnoM` (the counter and the headers are not `tcbM`, in
`hmem`'s/`hno`'s form) besides `allocW_wcG`'s.
-/
import Spike.Lib.X64WakeOwnLft2
import Spike.Lib.X64WakeOwnLftC
import Spike.Lib.X64WakeWcAllocWI

namespace Spike.Lib.X64.WakePh.OwnAlloc

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf privLoad abi)
open Scc.Cert.Rt.X64 (code_field codeT codeT_eq)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At mB eaddr_mB)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet fnL entryL cntL slowL fullL okL oE oI
  bPro bChk bJ1 bC1 bC2 bJ2 bSlow bJ3 bFull bO0 bO1 bO2 bO3 bO4 bO5 bO6 bO7 bO8 bO9 bPro_ok bChk_ok bJ1_ok
  bC1_ok bC2_ok bJ2_ok bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok
  bO9_ok)
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_fi keep_lea keep_rmw keep_hdr)
open Kraken.Promising.Lower.X64 (CellAt eaddr)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop} {R : Region}
  {F : MachineData → Prop}

/-- **A label's value** from the certificate's table. -/
theorem labN (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {y : Nat} (h : codeT lo wakeCells l = some y) (hy : y < 2 ^ 64) : (L.lab l).toBitVec.toNat = y := by
  rw [hlab _ _ (by rw [← codeT_eq]; exact h)]
  simp [Nat.mod_eq_of_lt hy]

/-- **Main's word only at the heap abort's entry from `scc_rt_alloc`**: on
the pool (`hsp`) at `scc_rt_abort` (`hpc`), the return address at `%rsp`
`.full + 12` (`hra`, not `.x23`). -/
theorem cst_abortA (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hsp : spPool L s) (hpc : pcOf s = (L.lab "scc_rt_abort").toBitVec.toNat)
    (hra : privLoad s s.st.1.regs.rsp.toBitVec = some ((L.lab ".Lscc_rt_alloc.full").toBitVec + 12#64)) :
    Cst L (tM L) [] s := by
  have eA := labN hlab (l := "scc_rt_abort") (y := 4202449) (by decide +kernel) (by decide)
  have e1 := labN hlab (l := ".Lscc_rt_start.x1") (y := 4198500) (by decide +kernel) (by decide)
  have e7 := labN hlab (l := ".Lscc_rt_thread_init.x7") (y := 4199569) (by decide +kernel) (by decide)
  have eT := labN hlab (l := "scc_rt_stack_take") (y := 4199695) (by decide +kernel) (by decide)
  have e21 := labN hlab (l := ".Lwc_main.x21") (y := 4203397) (by decide +kernel) (by decide)
  have eK := labN hlab (l := ".Lwc_main.stk") (y := 4203514) (by decide +kernel) (by decide)
  have eF := labN hlab (l := ".Lscc_rt_alloc.full") (y := 4198751) (by decide +kernel) (by decide)
  have e23 := labN hlab (l := ".Lwc_main.x23") (y := 4203484) (by decide +kernel) (by decide)
  refine ⟨ownS_of_self (.inl ⟨hsp, by rw [hpc, eA, e1]; decide⟩), ownSW_of_not ?_⟩
  rintro (⟨-, h1, h2⟩ | ⟨h1, h2⟩ | ⟨-, h3⟩)
  · rw [hpc, eA, e7] at h1; rw [hpc, eA, eT] at h2; omega
  · rw [hpc, eA, e21] at h1; rw [hpc, eA, eK] at h2; omega
  · have hin : pcOf s ∈ raSp L := by rw [hpc]; simp [raSp, abFns]
    have hA : raAddr L s = s.st.1.regs.rsp.toBitVec := by simp only [raAddr, hin, ↓reduceIte]
    unfold raAt at h3
    rw [hA, hra, Option.some.injEq] at h3
    have := congrArg BitVec.toNat h3
    rw [BitVec.toNat_add, eF, e23] at this
    simp only [BitVec.toNat_ofNat] at this
    omega

/-- The allocator's labels and its return point, at the canonical base. -/
theorem alloc_labs (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4198629 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4198652 ∧
    (_root_.Executable.labels L.exe).label cntL = Int64.ofNat 4198670 ∧
    (_root_.Executable.labels L.exe).label slowL = Int64.ofNat 4198731 ∧
    (_root_.Executable.labels L.exe).label fullL = Int64.ofNat 4198751 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4198765 ∧
    (_root_.Executable.labels L.exe).label ".Lscc_rt_alloc.spin" = Int64.ofNat 4198749 ∧
    (_root_.Executable.labels L.exe).label ".Lwc_main.x18" = Int64.ofNat 4203326 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soA " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -160 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block of the allocator (`bb` its code check, `ok` its `okBlk`, `oo`
its entry offsets, `el` its label's value), `QP` at its end left. -/
local macro "ablk " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) $bb (by pc_tac) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
      (soA $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [N]; simp only [$el:term]; revert k; decide +kernel
    dsimp only [N]))

set_option hygiene false in
/-- A single-instruction node of the allocator (`z` bytes, `bb` its code
check, `el` its label's value, `hw` its write condition, `kp` its `Keep`
from the cell `hc` and the step `hs`). -/
local macro "anodeX " z:term:max bb:term:max el:term:max hwx:term:max kp:term : tactic =>
  `(tactic| (
    refine nodeL2 hlab hsep ha hW (sz := $z) (P := QP) (cls_pool hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [N]; decide) ($hwx fun s c hAt => by
        obtain ⟨he, hn, -, hp', -⟩ := hAt
        exact (code_field L.lays rfl (hp ▸ $bb) (by pc_tac) s he hn).cell0 rfl rfl hp')
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $bb) (by pc_tac) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := $kp
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [N]; simp only [$el:term]; decide +kernel
    · dsimp only [N]; simp only [$el:term]; decide +kernel))

section L

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
  (hb : BandOnP L R (-160) 8)
include hp hlab hsite hsep ha hW hb

set_option maxHeartbeats 3200000 in
/-- **`scc_rt_alloc`'s nodes inside `Lft2`** for a call `q` returning to
`.x18` (`hra`): every state on the pool (`hb`) at a `QP` pc, or at the heap
abort's entry (`cst_abortA`), holds `tcbM` only; the counter's add and the
header's store miss it (`hnoM`). -/
theorem allocL (hR : R.OK) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi) {ms : Spike.Lib.MemSide isa} {q : Call}
    (hra : q.ra = (L.lab ".Lwc_main.x18").toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoM : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      w ≠ tcbM L) :
    AllocW ms q (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F := by
  obtain ⟨eFn, eEn, eCnt, eSlow, eFull, eOk, eSpin, eX18⟩ := alloc_labs hlab (L := L)
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := Spike.Lib.X64.AllocG.allocIn_spec
      Spike.Lib.X64.Flow.WakeWc.wake_alloc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · ablk h0 bPro_ok bPro oE eFn
    rw [Spike.Lib.X64.Alloc.bPro_run]; simp only [eFn]; decide +kernel
  · ablk h1 bChk_ok bChk oI eEn
    rw [Spike.Lib.X64.Alloc.bChk_run]
    split
    · simp only [eFull]; decide +kernel
    · simp only [eEn]; decide +kernel
  · ablk h2 bJ1_ok bJ1 oI eEn
    rw [Spike.Lib.X64.Alloc.bJ1_run]; simp only [eCnt]; decide +kernel
  · anodeX 7 h3 eCnt hw_lea (keep_lea hc hs)
  · ablk h4 bC1_ok bC1 oI eCnt
    rw [Spike.Lib.X64.Alloc.bC1_run]; simp only [eCnt]; decide +kernel
  · -- The counter's add, `lock xaddq %rax, (%rcx)`.
    have hE : ∀ s c, At L.exe L.endPc R F (N L.lab ms q .rmw) s c →
        CellAt s (Spike.Lib.X64.xaddDir .rcx 0 .rax) 5 ∧ eaddr s 5 (mB .rcx 0) = BitVec.ofNat 64 ms.ctr ∧
        Mem.loadInt s.st.1.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧ s.decls = {} := fun s c hAt => by
      obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      refine ⟨(code_field L.lays rfl (hp ▸ h5) rfl s he hn).cell0 rfl rfl hp', ?_, hmem _ (.inl rfl) _ hF, hd⟩
      exact (eaddr_mB s 5 .rcx 0).trans (by
        rw [hA.regs, ← Spike.Lib.X64.AllocG.ctr_addrS (hq _ hF) hJ.2.1]; rfl)
    refine nodeL2 hlab hsep ha hW (sz := 5) (P := QP) (cls_pool hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [N]; decide) (hw_rmwM hE (hnoM _ (.inl rfl)))
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_rmw hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [N]; simp only [eCnt]; decide +kernel
    · dsimp only [N]; simp only [eCnt]; decide +kernel
  · ablk h6 bC2_ok bC2 oI eCnt
    rw [Spike.Lib.X64.Alloc.bC2_run]
    split
    · simp only [eSlow]; decide +kernel
    · simp only [eCnt]; decide +kernel
  · ablk h7 bJ2_ok bJ2 oI eCnt
    rw [Spike.Lib.X64.Alloc.bJ2_run]; simp only [eOk]; decide +kernel
  · ablk h8 bSlow_ok bSlow oI eSlow
    rw [Spike.Lib.X64.Alloc.bSlow_run]
    split
    · simp only [eSpin]; decide +kernel
    · simp only [eSlow]; decide +kernel
  · ablk h9 bJ3_ok bJ3 oI eSlow
    rw [Spike.Lib.X64.Alloc.bJ3_run]; simp only [eFull]; decide +kernel
  · -- The heap abort's block: its last step enters `scc_rt_abort` (`cst_abortA`).
    have he : L.lab fullL + Int64.ofNat 0 = (N L.lab ms q .full).pc := by pc_tac
    refine BlkW.lft2 (blkW_cstOkB hsep ha hW
      (fun s hs' hn => code_field L.lays rfl (hp ▸ h10) he s hs' hn) bFull_ok hR (by omega) (by omega)
      ?_ (P := PP) (fun s h => cls_pool hlab hb s h.1) ?_ (soA bFull oI) ?_)
    · intro a' ha' j hj
      rw [hsite] at ha'; cases ha'
      rw [siteV hlab]
      have h := (show ∀ j < bFull.length, PP ((_root_.Executable.labels L.exe).label fullL +
        Int64.ofNat (Spike.Lib.X64.cellOff bFull j)).toBitVec.toNat by simp only [eFull]; decide +kernel) j hj
      exact h.2
    · intro j hj; dsimp only [N]; simp only [eFull]; revert j; decide +kernel
    · intro σ c _ s m hAb _ _ hs
      dsimp only [N] at hAb hs
      rw [Spike.Lib.X64.Alloc.bFull_run] at hAb hs
      have hm : s.st.1 = m := by rw [hs]
      have hsp : s.st.1.regs.rsp.toBitVec = R.addr (-160) := by
        rw [hm, Spike.Lib.X64ConsumerA.rsp_of_abs hAb]
      refine cst_abortA hlab ?_ (by unfold pcOf; rw [hs]) ?_
      · unfold spPool; rw [hsp]; exact hb (-160) (Int.le_refl _) (by omega)
      · obtain ⟨j, hj1, hj2⟩ := hAb.slot (-160) ⟨by decide, hlo', by omega⟩
        rw [hsp]
        unfold privLoad
        rw [hm, hj1, Option.map_some, hj2]
        simp [Spike.Lib.upd]
  · ablk h11 bO0_ok bO0 oI eOk
    rw [Spike.Lib.X64.Alloc.bO0_run]; simp only [eOk]; decide +kernel
  · anodeX 3 h12 eOk hw_fi (keep_fi hc rfl hs)
  · ablk h13 bO1_ok bO1 oI eOk
    rw [Spike.Lib.X64.Alloc.bO1_run]; simp only [eOk]; decide +kernel
  · anodeX 3 h14 eOk hw_fi (keep_fi hc rfl hs)
  · ablk h15 bO2_ok bO2 oI eOk
    rw [Spike.Lib.X64.Alloc.bO2_run]; simp only [eOk]; decide +kernel
  · anodeX 7 h16 eOk hw_lea (keep_lea hc hs)
  · ablk h17 bO3_ok bO3 oI eOk
    rw [Spike.Lib.X64.Alloc.bO3_run]; simp only [eOk]; decide +kernel
  · anodeX 3 h18 eOk hw_fi (keep_fi hc rfl hs)
  · ablk h19 bO4_ok bO4 oI eOk
    rw [Spike.Lib.X64.Alloc.bO4_run]; simp only [eOk]; decide +kernel
  · anodeX 4 h20 eOk hw_fi (keep_fi hc rfl hs)
  · ablk h21 bO5_ok bO5 oI eOk
    rw [Spike.Lib.X64.Alloc.bO5_run]; simp only [eOk]; decide +kernel
  · anodeX 3 h22 eOk hw_fi (keep_fi hc rfl hs)
  · ablk h23 bO6_ok bO6 oI eOk
    rw [Spike.Lib.X64.Alloc.bO6_run]; simp only [eOk]; decide +kernel
  · anodeX 3 h24 eOk hw_fi (keep_fi hc rfl hs)
  · ablk h25 bO7_ok bO7 oI eOk
    rw [Spike.Lib.X64.Alloc.bO7_run]; simp only [eOk]; decide +kernel
  · anodeX 3 h26 eOk hw_fi (keep_fi hc rfl hs)
  · ablk h27 bO8_ok bO8 oI eOk
    rw [Spike.Lib.X64.Alloc.bO8_run]; simp only [eOk]; decide +kernel
  · -- The header's store, `movq %rax, (%rcx)`.
    have hE : ∀ s c, At L.exe L.endPc R F (N L.lab ms q .hdr) s c →
        ∃ A : BitVec 64, A ≠ tcbM L ∧ CellAt s (Spike.Lib.X64.stDir .rcx 0 .rax) 3 ∧ eaddr s 3 (mB .rcx 0) = A ∧
          Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {} := fun s c hAt => by
      obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, hcx⟩ := hJ
      have hm : ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧
          (Spike.Lib.X64.bAddr σ.regs .rcx 0).toNat = q.hdrAt ms o :=
        ⟨o.toNat, hle, Spike.Lib.X64.AllocG.hdr_addrS (hq _ hF) hle hn28 hcx⟩
      exact ⟨_, hnoM _ (.inr hm), (code_field L.lays rfl (hp ▸ h28) rfl s he hn).cell0 rfl rfl hp',
        (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs]; rfl), hmem _ (.inr hm) _ hF, hd⟩
    refine nodeL2 hlab hsep ha hW (sz := 3) (P := QP) (cls_pool hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [N]; decide) (fun s c hAt => ?_)
    · obtain ⟨A, -, hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_hdr hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [N]; simp only [eOk]; decide +kernel
    · dsimp only [N]; simp only [eOk]; decide +kernel
    · intro _ tree hex
      obtain ⟨A, hAM, hc, hea, hun, hd⟩ := hE s c hAt
      rw [Kraken.Promising.Lower.X64.exec_store_agrees hc hea hun (Spike.Lib.X64.agrees_of_decls hd _ _)] at hex
      cases hex
      refine ⟨⟨fun w hw => ?_, fun w hw => by simp at hw⟩, fun _ => trivial⟩
      simp only [tM, List.mem_singleton, Prod.mk.injEq] at hw
      obtain ⟨hl, -⟩ := hw
      injection hl with h1
      exact hAM h1
  · ablk h29 bO9_ok bO9 oI eOk
    rw [Spike.Lib.X64.Alloc.bO9_run]; simp only [eOk]; decide +kernel
  · -- The `ret`, to `.x18`.
    refine Spike.Lib.LowerX64.BlkW.nodeW (blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP)
      (blk := [(iRet.toDir, 1)]) h30 rfl (blo := -160) (bhi := 8) (by dsimp only [N]; decide) hR hlo' hhi
      (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_ (soA [(iRet.toDir, 1)] oE)
      fun σ c hJ => ?_) (List.cons_ne_nil _ _)
    · intro k hk; dsimp only [N]; simp only [eOk]; revert k; decide +kernel
    obtain ⟨o, -, -, -, -, -, h30', -⟩ := hJ
    have hc : Spike.Lib.X64.classify iRet.toDir = some iRet := rfl
    simp only [Spike.Lib.X64.arun, List.foldl, Spike.Lib.X64.dstep, hc]
    simp only [N, iRet, Spike.Lib.X64.AI.tgt, h30', hra, Int64.ofBitVec_toBitVec]
    simp only [eX18]; decide +kernel

/-- **`allocW_wcG` at `ownGXW`**: `allocW_wcG`'s premises, `ownGXW`'s
separation (`hsep`, `ha`, `hW`), the frame's band on the pool (`hb`), and
the counter and the headers off `tcbM` (`hnoM`). -/
theorem allocW_wcGX (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {rS : Range}
    {ms : Spike.Lib.MemSide isa} {q : Call}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hpool : Λ.stackPool.lo ≤ 2 ^ 64)
    (hra : q.ra = (L.lab ".Lwc_main.x18").toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true l = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownW L a j)
    (hnoM : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      w ≠ tcbM L) :
    AllocW ms q (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F :=
  Spike.Lib.X64.AllocG.AllocW.imp
    (WcW.allocW_wcG hp hlo hΛ hlab hsite a hR hR8 hlo' hhi hl hh hpool hra hq hmp hmem hno)
    (allocL (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hlo' hhi hra hq hmem hnoM)
    fun _ _ h1 h2 => h2 h1

end L

end Spike.Lib.X64.WakePh.OwnAlloc

/-- info: 'Spike.Lib.X64.WakePh.OwnAlloc.cst_abortA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnAlloc.cst_abortA

/-- info: 'Spike.Lib.X64.WakePh.OwnAlloc.allocL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnAlloc.allocL

/-- info: 'Spike.Lib.X64.WakePh.OwnAlloc.allocW_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnAlloc.allocW_wcGX
