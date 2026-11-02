/-
**hello.w's allocator at `ownGHXW`** (x86-64 only; the hello counterpart of `X64WakeOwnAllocX`):
`WcW.allocW_wcGH` (`scc_rt_alloc` returning to `.Lwc_main.x22` or `.Lwc_rodata.x15`, inside `SFactsSt2` at
`ownGH`, `X64HelloAllocWI`) moved to `SFactsSt2` at `ownGHXW` (`Lft2H`), from outside (`AllocG.AllocW.imp`).
The allocator's frame `[-160, 8]` is on the pool (`hb : BandOnP L R (-160) 8`):
- its pcs, the slow path's `.spin` and both return points are from `.x1` on in none of `InTH`, `InCH`, `InAbH`
  (`QPH`, off the take site: `PPH`), so they hold `tcbM` only (`cls_poolH`);
- the heap abort's entry `scc_rt_abort` (in `InAbH`) holds `tcbM` only too: on the pool from `.x1` on
  (`selfOwnH`), and the return address the `call` pushes is `.full + 12`, not `.x27` (not `selfOwnWH`;
  `cst_abortAH`);
- its two shared writes (the counter's `lock xaddq`, the header's store) miss `tcbM` (`hnoM`).

- `labNH`: a label's value from the certificate.
- `cst_abortAH`: `CstH L (tM L) []` at the heap abort's entry from the allocator.
- `alloc_labsH`: the allocator's labels.
- `allocLH`: the allocator's nodes inside `Lft2H`.
- `allocW_wcGHX`: `allocW_wcGH` at `ownGHXW`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against x86-64 wake's `OwnAlloc`: hello's allocator has
two callers (`AllocRetH`: `.Lwc_main.x22` and `.Lwc_rodata.x15`; wake's one, `.x18`), the worker's word is held
from the second `scc_rt_thread_init`'s self store at `.x8 + 51` and on the abort path from `.x27` (wake `.x7`,
`.x23`), and `hW` is about `tcbWH L` (`pinA + 112`; wake's `tcb2 L`).
-/
import Spike.Lib.X64HelloOwnLft2X
import Spike.Lib.X64HelloAllocWI
import Spike.Lib.X64WakeOwnAllocX

namespace Spike.Lib.X64.HelloPh.OwnAlloc

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf privLoad abi)
open Scc.Cert.Rt.X64 (code_field codeT codeT_eq)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At mB eaddr_mB)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet fnL entryL cntL slowL fullL okL oE oI
  bPro bChk bJ1 bC1 bC2 bJ2 bSlow bJ3 bFull bO0 bO1 bO2 bO3 bO4 bO5 bO6 bO7 bO8 bO9 bPro_ok bChk_ok bJ1_ok
  bC1_ok bC2_ok bJ2_ok bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok
  bO9_ok)
open Spike.Lib.X64.WakePh (tcbM tM Keep BandOnP keep_pc spPool raAt raAddr raSp abFns hw_fi hw_lea hw_rmwM)
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_fi keep_lea keep_rmw keep_hdr)
open Spike.Lib.X64.HelloPh.WcW (AllocRetH)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Kraken.Promising.Lower.X64 (CellAt eaddr)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop} {R : Region}
  {F : MachineData → Prop}

/-- **A label's value** from the certificate's table. -/
theorem labNH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {y : Nat} (h : codeT lo helloCells l = some y) (hy : y < 2 ^ 64) : (L.lab l).toBitVec.toNat = y := by
  rw [hlab _ _ (by rw [← codeT_eq]; exact h)]
  simp [Nat.mod_eq_of_lt hy]

/-- **Main's word only at the heap abort's entry from `scc_rt_alloc`**: on the pool (`hsp`) at `scc_rt_abort`
(`hpc`), the return address at `%rsp` `.full + 12` (`hra`, not `.x27`). -/
theorem cst_abortAH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hsp : spPool L s) (hpc : pcOf s = (L.lab "scc_rt_abort").toBitVec.toNat)
    (hra : privLoad s s.st.1.regs.rsp.toBitVec = some ((L.lab ".Lscc_rt_alloc.full").toBitVec + 12#64)) :
    CstH L (tM L) [] s := by
  have eA := labNH hlab (l := "scc_rt_abort") (y := 4202486) (by decide +kernel) (by decide)
  have e1 := labNH hlab (l := ".Lscc_rt_start.x1") (y := 4198500) (by decide +kernel) (by decide)
  have e8 := labNH hlab (l := ".Lscc_rt_thread_init.x8") (y := 4199606) (by decide +kernel) (by decide)
  have eT := labNH hlab (l := "scc_rt_stack_take") (y := 4199732) (by decide +kernel) (by decide)
  have e25 := labNH hlab (l := ".Lwc_main.x25") (y := 4203774) (by decide +kernel) (by decide)
  have eK := labNH hlab (l := ".Lwc_main.stk") (y := 4203948) (by decide +kernel) (by decide)
  have eF := labNH hlab (l := ".Lscc_rt_alloc.full") (y := 4198788) (by decide +kernel) (by decide)
  have e27 := labNH hlab (l := ".Lwc_main.x27") (y := 4203909) (by decide +kernel) (by decide)
  refine ⟨ownSH_of_self (.inl ⟨hsp, by rw [hpc, eA, e1]; decide⟩), ownSWH_of_not ?_⟩
  rintro (⟨-, h1, h2⟩ | ⟨h1, h2⟩ | ⟨-, h3⟩)
  · rw [hpc, eA, e8] at h1; rw [hpc, eA, eT] at h2; omega
  · rw [hpc, eA, e25] at h1; rw [hpc, eA, eK] at h2; omega
  · have hin : pcOf s ∈ raSp L := by rw [hpc]; simp [raSp, abFns]
    have hA : raAddr L s = s.st.1.regs.rsp.toBitVec := by simp only [raAddr, hin, ↓reduceIte]
    unfold raAt at h3
    rw [hA, hra, Option.some.injEq] at h3
    have := congrArg BitVec.toNat h3
    rw [BitVec.toNat_add, eF, e27] at this
    simp only [BitVec.toNat_ofNat] at this
    omega

/-- The allocator's labels and its return points, at the canonical base. -/
theorem alloc_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4198666 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4198689 ∧
    (_root_.Executable.labels L.exe).label cntL = Int64.ofNat 4198707 ∧
    (_root_.Executable.labels L.exe).label slowL = Int64.ofNat 4198768 ∧
    (_root_.Executable.labels L.exe).label fullL = Int64.ofNat 4198788 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4198802 ∧
    (_root_.Executable.labels L.exe).label ".Lscc_rt_alloc.spin" = Int64.ofNat 4198786 ∧
    (_root_.Executable.labels L.exe).label ".Lwc_main.x22" = Int64.ofNat 4203703 ∧
    (_root_.Executable.labels L.exe).label ".Lwc_rodata.x15" = Int64.ofNat 4203184 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soA " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -160 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block of the allocator (`bb` its code check, `ok` its `okBlk`, `oo` its entry offsets, `el` its label's
value), `QPH` at its end left. -/
local macro "ablkH " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) $bb (by pc_tac) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soA $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [N]; simp only [$el:term]; revert k; decide +kernel
    dsimp only [N]))

set_option hygiene false in
/-- A single-instruction node of the allocator (`z` bytes, `bb` its code check, `el` its label's value, `hw` its
write condition, `kp` its `Keep` from the cell `hc` and the step `hs`). -/
local macro "anodeXH " z:term:max bb:term:max el:term:max hwx:term:max kp:term : tactic =>
  `(tactic| (
    refine nodeL2H hsep ha hW (sz := $z) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
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

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
  (hb : BandOnP L R (-160) 8)
include hp hlab hsite hsep ha hW hb

set_option maxHeartbeats 3200000 in
/-- **`scc_rt_alloc`'s nodes inside `Lft2H`** for a call `q` returning to `rl` (`hrl`, `hra`): every state on
the pool (`hb`) at a `QPH` pc, or at the heap abort's entry (`cst_abortAH`), holds `tcbM` only; the counter's add
and the header's store miss it (`hnoM`). -/
theorem allocLH (hR : R.OK) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi) {ms : Spike.Lib.MemSide isa} {q : Call}
    {rl : Label} (hrl : AllocRetH rl) (hra : q.ra = (L.lab rl).toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoM : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      w ≠ tcbM L) :
    AllocW ms q (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F := by
  obtain ⟨eFn, eEn, eCnt, eSlow, eFull, eOk, eSpin, eX22, eX15⟩ := alloc_labsH hlab (L := L)
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := Spike.Lib.X64.AllocG.allocIn_spec
      Spike.Lib.X64.Flow.HelloRd.hello_alloc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · ablkH h0 bPro_ok bPro oE eFn
    rw [Spike.Lib.X64.Alloc.bPro_run]; simp only [eFn]; decide +kernel
  · ablkH h1 bChk_ok bChk oI eEn
    rw [Spike.Lib.X64.Alloc.bChk_run]
    split
    · simp only [eFull]; decide +kernel
    · simp only [eEn]; decide +kernel
  · ablkH h2 bJ1_ok bJ1 oI eEn
    rw [Spike.Lib.X64.Alloc.bJ1_run]; simp only [eCnt]; decide +kernel
  · anodeXH 7 h3 eCnt hw_lea (keep_lea hc hs)
  · ablkH h4 bC1_ok bC1 oI eCnt
    rw [Spike.Lib.X64.Alloc.bC1_run]; simp only [eCnt]; decide +kernel
  · -- The counter's add, `lock xaddq %rax, (%rcx)`.
    have hE : ∀ s c, At L.exe L.endPc R F (N L.lab ms q .rmw) s c →
        CellAt s (Spike.Lib.X64.xaddDir .rcx 0 .rax) 5 ∧ eaddr s 5 (mB .rcx 0) = BitVec.ofNat 64 ms.ctr ∧
        Mem.loadInt s.st.1.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧ s.decls = {} := fun s c hAt => by
      obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      refine ⟨(code_field L.lays rfl (hp ▸ h5) rfl s he hn).cell0 rfl rfl hp', ?_, hmem _ (.inl rfl) _ hF, hd⟩
      exact (eaddr_mB s 5 .rcx 0).trans (by
        rw [hA.regs, ← Spike.Lib.X64.AllocG.ctr_addrS (hq _ hF) hJ.2.1]; rfl)
    refine nodeL2H hsep ha hW (sz := 5) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [N]; decide) (hw_rmwM hE (hnoM _ (.inl rfl)))
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_rmw hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [N]; simp only [eCnt]; decide +kernel
    · dsimp only [N]; simp only [eCnt]; decide +kernel
  · ablkH h6 bC2_ok bC2 oI eCnt
    rw [Spike.Lib.X64.Alloc.bC2_run]
    split
    · simp only [eSlow]; decide +kernel
    · simp only [eCnt]; decide +kernel
  · ablkH h7 bJ2_ok bJ2 oI eCnt
    rw [Spike.Lib.X64.Alloc.bJ2_run]; simp only [eOk]; decide +kernel
  · ablkH h8 bSlow_ok bSlow oI eSlow
    rw [Spike.Lib.X64.Alloc.bSlow_run]
    split
    · simp only [eSpin]; decide +kernel
    · simp only [eSlow]; decide +kernel
  · ablkH h9 bJ3_ok bJ3 oI eSlow
    rw [Spike.Lib.X64.Alloc.bJ3_run]; simp only [eFull]; decide +kernel
  · -- The heap abort's block: its last step enters `scc_rt_abort` (`cst_abortAH`).
    have he : L.lab fullL + Int64.ofNat 0 = (N L.lab ms q .full).pc := by pc_tac
    refine BlkW.lft2H (blkW_cstOkHB hsep ha hW
      (fun s hs' hn => code_field L.lays rfl (hp ▸ h10) he s hs' hn) bFull_ok hR (by omega) (by omega)
      ?_ (P := PPH) (fun s h => cls_poolH hlab hb s h.1) ?_ (soA bFull oI) ?_)
    · intro a' ha' j hj
      rw [hsite] at ha'; cases ha'
      rw [siteVH hlab]
      have h := (show ∀ j < bFull.length, PPH ((_root_.Executable.labels L.exe).label fullL +
        Int64.ofNat (Spike.Lib.X64.cellOff bFull j)).toBitVec.toNat by simp only [eFull]; decide +kernel) j hj
      exact h.2
    · intro j hj; dsimp only [N]; simp only [eFull]; revert j; decide +kernel
    · intro σ c _ s m hAb _ _ hs
      dsimp only [N] at hAb hs
      rw [Spike.Lib.X64.Alloc.bFull_run] at hAb hs
      have hm : s.st.1 = m := by rw [hs]
      have hsp : s.st.1.regs.rsp.toBitVec = R.addr (-160) := by
        rw [hm, Spike.Lib.X64ConsumerA.rsp_of_abs hAb]
      refine cst_abortAH hlab ?_ (by unfold pcOf; rw [hs]) ?_
      · unfold spPool; rw [hsp]; exact hb (-160) (Int.le_refl _) (by omega)
      · obtain ⟨j, hj1, hj2⟩ := hAb.slot (-160) ⟨by decide, hlo', by omega⟩
        rw [hsp]
        unfold privLoad
        rw [hm, hj1, Option.map_some, hj2]
        simp [Spike.Lib.upd]
  · ablkH h11 bO0_ok bO0 oI eOk
    rw [Spike.Lib.X64.Alloc.bO0_run]; simp only [eOk]; decide +kernel
  · anodeXH 3 h12 eOk hw_fi (keep_fi hc rfl hs)
  · ablkH h13 bO1_ok bO1 oI eOk
    rw [Spike.Lib.X64.Alloc.bO1_run]; simp only [eOk]; decide +kernel
  · anodeXH 3 h14 eOk hw_fi (keep_fi hc rfl hs)
  · ablkH h15 bO2_ok bO2 oI eOk
    rw [Spike.Lib.X64.Alloc.bO2_run]; simp only [eOk]; decide +kernel
  · anodeXH 7 h16 eOk hw_lea (keep_lea hc hs)
  · ablkH h17 bO3_ok bO3 oI eOk
    rw [Spike.Lib.X64.Alloc.bO3_run]; simp only [eOk]; decide +kernel
  · anodeXH 3 h18 eOk hw_fi (keep_fi hc rfl hs)
  · ablkH h19 bO4_ok bO4 oI eOk
    rw [Spike.Lib.X64.Alloc.bO4_run]; simp only [eOk]; decide +kernel
  · anodeXH 4 h20 eOk hw_fi (keep_fi hc rfl hs)
  · ablkH h21 bO5_ok bO5 oI eOk
    rw [Spike.Lib.X64.Alloc.bO5_run]; simp only [eOk]; decide +kernel
  · anodeXH 3 h22 eOk hw_fi (keep_fi hc rfl hs)
  · ablkH h23 bO6_ok bO6 oI eOk
    rw [Spike.Lib.X64.Alloc.bO6_run]; simp only [eOk]; decide +kernel
  · anodeXH 3 h24 eOk hw_fi (keep_fi hc rfl hs)
  · ablkH h25 bO7_ok bO7 oI eOk
    rw [Spike.Lib.X64.Alloc.bO7_run]; simp only [eOk]; decide +kernel
  · anodeXH 3 h26 eOk hw_fi (keep_fi hc rfl hs)
  · ablkH h27 bO8_ok bO8 oI eOk
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
    refine nodeL2H hsep ha hW (sz := 3) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
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
  · ablkH h29 bO9_ok bO9 oI eOk
    rw [Spike.Lib.X64.Alloc.bO9_run]; simp only [eOk]; decide +kernel
  · -- The `ret`, to `rl`.
    refine Spike.Lib.LowerX64.BlkW.nodeW (blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH)
      (blk := [(iRet.toDir, 1)]) h30 rfl (blo := -160) (bhi := 8) (by dsimp only [N]; decide) hR hlo' hhi
      (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soA [(iRet.toDir, 1)] oE)
      fun σ c hJ => ?_) (List.cons_ne_nil _ _)
    · intro k hk; dsimp only [N]; simp only [eOk]; revert k; decide +kernel
    obtain ⟨o, -, -, -, -, -, h30', -⟩ := hJ
    have hc : Spike.Lib.X64.classify iRet.toDir = some iRet := rfl
    simp only [Spike.Lib.X64.arun, List.foldl, Spike.Lib.X64.dstep, hc]
    simp only [N, iRet, Spike.Lib.X64.AI.tgt, h30', hra, Int64.ofBitVec_toBitVec]
    rcases hrl with rfl | rfl
    · simp only [eX15]; decide +kernel
    · simp only [eX22]; decide +kernel

/-- **`allocW_wcGH` at `ownGHXW`**: `allocW_wcGH`'s premises, `ownGHXW`'s separation (`hsep`, `ha`, `hW`), the
frame's band on the pool (`hb`), and the counter and the headers off `tcbM` (`hnoM`). -/
theorem allocW_wcGHX (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {rS : Range}
    {ms : Spike.Lib.MemSide isa} {q : Call}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hpool : Λ.stackPool.lo ≤ 2 ^ 64)
    {rl : Label} (hrl : AllocRetH rl) (hra : q.ra = (L.lab rl).toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true l = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hnoM : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      w ≠ tcbM L) :
    AllocW ms q (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F :=
  Spike.Lib.X64.AllocG.AllocW.imp
    (WcW.allocW_wcGH hp hlo hΛ hlab hsite a hR hR8 hlo' hhi hl hh hpool hrl hra hq hmp hmem hno)
    (allocLH (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hlo' hhi hrl hra hq hmem hnoM)
    fun _ _ h1 h2 => h2 h1

end L

end Spike.Lib.X64.HelloPh.OwnAlloc

/-- info: 'Spike.Lib.X64.HelloPh.OwnAlloc.cst_abortAH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnAlloc.cst_abortAH

/-- info: 'Spike.Lib.X64.HelloPh.OwnAlloc.allocLH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnAlloc.allocLH

/-- info: 'Spike.Lib.X64.HelloPh.OwnAlloc.allocW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnAlloc.allocW_wcGHX
