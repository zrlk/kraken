/-
**hello.w's `wc_main` obligations before the reserve at `ownGHXW`** (x86-64 only; the hello counterpart of
`X64WakeOwnWcPreX`): `X64HelloWcPreWI`'s producers at `SFactsSt2`/`ownGH` (`proW_wcGH`, `eW_wcGH`,
`wcSp0W_wcGH`, `resBlW_wcGH`) moved to `SFactsSt2` at `ownGHXW` (`Lft2H`), from outside (`XProW.imp`,
`BlkW.imp`, `NodeW.imp` with a second obligation inside `Lft2H`). `wc_main` from its entry to the reserve's call
and the blocks' ends (`.Lwc_main.stk`, `scc_rt_alloc`, `scc_rt_thread_reserve`) are `QPH` pcs, and its frame's
band `[-144, 8]` is on the pool (`hb`), so every state holds `tcbM` only (`cls_poolH`). The limit's `%fs` load
writes nothing, and the box store misses `tcbM` (`hboxM`).

- `wc_labsH`: the labels the pcs are decided from.
- `proLH`, `eLH`, `sp0bLH`, `sp0stLH`, `resBlLH`: the nodes inside `Lft2H`.
- `proW_wcGHX`, `eW_wcGHX`, `wcSp0W_wcGHX`, `resBlW_wcGHX`: the producers at `ownGHXW`.

The limit load's `keep_fsld`/`hw_fsld` are x86-64 wake's (`X64WakeOwnWcPreX`), generic in the code.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against x86-64 wake's `OwnWc`: hello's frame is 128
bytes (wake 64), so the band is `[-144, 8]` (wake `[-80, 8]`: the body at `-136`, the calls' return addresses at
`-144`); the prologue spills five arguments; `.x22` follows the allocator's call (wake `.x18`); the box cell is
at slot `-56` (wake `-24`, `BoxOkH`); the producers take `hW` about the worker's word `tcbWH L` (`pinA + 144`).
-/
import Spike.Lib.X64HelloOwnLft2X
import Spike.Lib.X64HelloWcPreWI
import Spike.Lib.X64WakeOwnWcPreX

namespace Spike.Lib.X64.HelloPh.OwnWc

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range WriteTree)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (codeT_eq code_field label_labelGapB)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At fsDir stDir mB bAddr)
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok
  xHead_run xLea_run xCmp_run xFr_run xS1 xS2 hdRegs prologueIn ofNat_add' ofNat_zero')
open Spike.Lib.X64.Flow.HelloWc
open Spike.Lib.X64.Flow.WakeWc (AGB)
open Spike.Lib.X64.WakePh (tcbM Keep BandOnP keep_pc)
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib.X64.WakePh.OwnWc (keep_fsld hw_fsld)
open Spike.Lib.X64.HelloPh.WcW (BoxOkH bAddr_boxH slot_boxH)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop} {rS : Range}
  {R : Region} {F : MachineData → Prop}

/-- The labels `wc_main`'s pcs are decided from, at the canonical base. -/
theorem wc_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab "wc_main" = Int64.ofNat 4203661 ∧ L.lab ".Lwc_main.chk" = Int64.ofNat 4203665 ∧
    L.lab ".Lwc_main.entry" = Int64.ofNat 4203715 ∧ L.lab ".Lwc_main.x0" = Int64.ofNat 4203741 ∧
    L.lab ".Lwc_main.stk" = Int64.ofNat 4203986 ∧ L.lab "scc_rt_alloc" = Int64.ofNat 4198666 ∧
    L.lab "scc_rt_thread_reserve" = Int64.ofNat 4199484 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soWH " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -144 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

section L

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

set_option maxHeartbeats 1600000 in
/-- **`wc_main`'s prologue inside `Lft2H`**: the limit's load at the thread pointer `tp` (`htp`), its word
unmapped under `F` (`hun`). -/
theorem proLH (hb : BandOnP L R (-144) 8) (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F ms (L.lab "wc_main") 128 8 ".Lwc_main.stk" 5 9 3 6
      7 [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)] J0 := by
  obtain ⟨eW, eC, eE, -, eK, -, -⟩ := wc_labsH hlab (L := L)
  have h := hello_wcPro
  simp only [hWcPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".Lwc_main.chk" = L.lab "wc_main" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "wc_main" + 1 + 3 = L.lab ".Lwc_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 = L.lab ".Lwc_main.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e23 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6 =
      L.lab ".Lwc_main.chk" + Int64.ofNat 23 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hxs : (xS2 128 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bHd (ofNat_zero' _)
      (xHead_ok (lo := -136) (hi := 0) (by decide) (Int.le_refl _)) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soWH xHead (⟨0, []⟩ : Spike.Lib.X64.SO))
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab "wc_main" + Int64.ofNat (Spike.Lib.X64.cellOff xHead k)).toBitVec.toNat
      rw [eW]; revert k; decide +kernel
    · rw [xHead_run]; show QPH (L.lab "wc_main" + 1 + 3).toBitVec.toNat; rw [eW]; decide +kernel
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bLea
      (by show _ = L.lab "wc_main" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -136) (hi := 0) _ _) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soWH (xLea 128 5) Spike.Lib.X64.Flow.oH)
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab "wc_main" + 1 + 3 + _).toBitVec.toNat; rw [eW]; revert k; decide +kernel
    · show QPH (Spike.Lib.X64.arun _ (xLea 128 5) ⟨L.lab "wc_main" + 1 + 3, Spike.Lib.X64.Flow.oH, σ⟩).pc.toBitVec.toNat
      rw [xLea_run (Z := 128) _ _ _ (by decide)]
      show QPH (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eW]; decide +kernel
  · have hE : ∀ s c, At L.exe L.endPc R F (xProN2 (L.lab "wc_main") 5 128 J0) s c →
        CellAt s (fsDir .r11 8) 9 ∧
        fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨he, hn, hd, hp', σ2, hA, hF, σ0, hJ0, rfl⟩
      refine ⟨(code_field L.lays rfl (hp ▸ bLd) (by show _ = L.lab "wc_main" + 1 + 3 + _; rw [h4]) s he hn).cell0
        rfl rfl hp', ?_, hun _ hF, hd⟩
      rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 128 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
        rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    refine nodeL2H hsep ha hW (sz := 9) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [xProN2]; decide) (hw_fsld hE)
    · obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_fsld hc hd hea hun' hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show QPH (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eW]; decide +kernel
    · show QPH (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat; rw [eW]; decide +kernel
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bCmp
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -136) (hi := 0) _ _ _ _) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soWH (xCmp ".Lwc_main.stk" 3 6) (Spike.Lib.X64.Flow.oL 128)) (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + _).toBitVec.toNat
      rw [eW]; revert k; decide +kernel
    · show QPH (Spike.Lib.X64.arun _ (xCmp ".Lwc_main.stk" 3 6)
        ⟨L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9, Spike.Lib.X64.Flow.oL 128, σ⟩).pc.toBitVec.toNat
      rw [(xCmp_run _ _ _ _ _ _ _).1]
      split
      · rw [eW]; decide +kernel
      · show QPH (L.lab ".Lwc_main.stk").toBitVec.toNat; rw [eK]; decide +kernel
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bFr
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _ + _ + _; rw [e23])
      (xFr_ok (lo := -136) (hi := 0) _ _ _ (by decide)) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soWH (xFr 128 7 [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)])
        (Spike.Lib.X64.Flow.oL 128)) (fun σ c _ => ?_)
    · intro k hk
      show PPH (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6 +
        _).toBitVec.toNat
      rw [eW]; revert k; decide +kernel
    · show QPH (Spike.Lib.X64.arun _ (xFr 128 7 [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4),
          (.r8, -40, 4)])
        ⟨L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6,
          Spike.Lib.X64.Flow.oL 128, σ⟩).pc.toBitVec.toNat
      rw [(xFr_run _ _ _ _ _ _).1, eW]; decide +kernel

/-- **`wc_main`'s entry block inside `Lft2H`** (its call to `scc_rt_alloc`). -/
theorem eLH (hb : BandOnP L R (-144) 8) (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (wNH L.lab R J0 J1 .e) wcEH := by
  obtain ⟨-, -, eE, -, -, eA, -⟩ := wc_labsH hlab (L := L)
  refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) (l := ".Lwc_main.entry") (k := 0)
    (by have := hello_wcEInH; simp only [wcEInH, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) wcEH_ok hR hRlo hhi (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
    (soWH wcEH oWRH) (fun σ c _ => ?_)
  · intro k hk; show PPH (L.lab ".Lwc_main.entry" + _).toBitVec.toNat; rw [eE]; revert k; decide +kernel
  · show QPH (Spike.Lib.X64.arun _ wcEH ⟨_, oWRH, σ⟩).pc.toBitVec.toNat
    rw [wcEH_run]; show QPH (L.lab "scc_rt_alloc").toBitVec.toNat; rw [eA]; decide +kernel

/-- **`.x22`'s block inside `Lft2H`.** -/
theorem sp0bLH (hb : BandOnP L R (-144) 8) (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (sNH ms L.lab R J0 .b) wcS0H := by
  obtain ⟨-, -, -, e22, -, -, -⟩ := wc_labsH hlab (L := L)
  refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) (l := ".Lwc_main.x0") (k := 0)
    (by have := hello_wcS0InH; simp only [wcS0InH, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) wcS0H_ok hR hRlo hhi (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
    (soWH wcS0H oWRH) (fun σ c _ => ?_)
  · intro k hk; show PPH (L.lab ".Lwc_main.x0" + _).toBitVec.toNat; rw [e22]; revert k; decide +kernel
  · show QPH (Spike.Lib.X64.arun _ wcS0H ⟨_, oWRH, σ⟩).pc.toBitVec.toNat
    rw [wcS0H_run]; show QPH (L.lab ".Lwc_main.x0" + Int64.ofNat 15).toBitVec.toNat; rw [e22]; decide +kernel

omit hsite in
/-- **The box store inside `Lft2H`**: every cell the allocator may return has `BoxOkH` (`hbox`) and is off
`tcbM` (`hboxM`). -/
theorem sp0stLH (hb : BandOnP L R (-144) 8) {ms : Spike.Lib.MemSide isa}
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hboxM : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) ≠ tcbM L) :
    NodeW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (sNH ms L.lab R J0 .st) := by
  obtain ⟨-, -, -, e22, -, -, -⟩ := wc_labsH hlab (L := L)
  have hin := hello_wcS0InH
  simp only [wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨-, h3⟩ := hin
  refine Spike.Lib.X64.WakePh.WcW.NodeW.ofAll (fun σ => σ.slot (-56)) fun A => ?_
  by_cases hA : BoxOkH Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    obtain ⟨q, o, hj, hlo', hle, e⟩ := slot_boxH hJ
    exact absurd (e ▸ hbox q o hj hlo' hle) hA
  by_cases hM : A = tcbM L
  case pos =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, hsA⟩
    obtain ⟨q, o, hj, hlo', hle, e⟩ := slot_boxH hJ
    exact absurd (e.symm.trans (hsA.trans hM)) (hboxM q o hj hlo' hle)
  have hAM : A ≠ tcbM L := hM
  obtain ⟨-, hunA, -⟩ := hA
  have hE : ∀ s c, At L.exe L.endPc R F
      ⟨(sNH ms L.lab R J0 .st).pc, (sNH ms L.lab R J0 .st).o,
        fun σ c => (sNH ms L.lab R J0 .st).J σ c ∧ σ.slot (-56) = A⟩ s c →
      CellAt s (stDir .rcx 0 .rax) 3 ∧ eaddr s 3 (mB .rcx 0) = A ∧
      Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {} := by
    rintro s c ⟨he, hn, hd, hp', σ, hA', hF, hJ, hsA⟩
    exact ⟨(code_field L.lays rfl (hp ▸ h3) rfl s he hn).cell0 rfl rfl hp',
      (Spike.Lib.X64.eaddr_mB s 3 .rcx 0).trans (by rw [hA'.regs, ← hsA]; exact bAddr_boxH hJ), hunA _ hF, hd⟩
  refine nodeL2H hsep ha hW (sz := 3) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
    (by dsimp only [sNH]; decide) (Spike.Lib.X64.WakePh.OwnSt.hw_stM hE hAM)
  · obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
    have hK : Keep s s' := Spike.Lib.X64.WakePh.StartTi.keep_st hc hd hea hun' hs
    exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
  · show QPH (L.lab ".Lwc_main.x0" + Int64.ofNat 15).toBitVec.toNat; rw [e22]; decide +kernel
  · show QPH (L.lab ".Lwc_main.x0" + Int64.ofNat 15 + Int64.ofNat 3).toBitVec.toNat; rw [e22]; decide +kernel

/-- **The reserve's call block inside `Lft2H`.** -/
theorem resBlLH (hb : BandOnP L R (-144) 8) (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (rNH ms L.lab R J0 Q .bl) resBH := by
  obtain ⟨-, -, -, e22, -, -, eR⟩ := wc_labsH hlab (L := L)
  refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) (l := ".Lwc_main.x0") (k := 18)
    (by have := hello_wcResInH; simp only [wcResInH, Bool.and_eq_true] at this; exact this.1)
    rfl resBH_ok hR hRlo hhi (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
    (soWH resBH (⟨-128, [(.rbp, 0)]⟩ : Spike.Lib.X64.SO)) (fun σ c _ => ?_)
  · intro k hk; show PPH (L.lab ".Lwc_main.x0" + Int64.ofNat 18 + _).toBitVec.toNat; rw [e22]; revert k
    decide +kernel
  · show QPH (Spike.Lib.X64.arun _ resBH ⟨_, ⟨-128, [(.rbp, 0)]⟩, σ⟩).pc.toBitVec.toNat
    rw [resBH_run]; show QPH (L.lab "scc_rt_thread_reserve").toBitVec.toNat; rw [eR]; decide +kernel

end L

/-! ## The producers at `ownGHXW` -/

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
  (hb : BandOnP L R (-144) 8)
include hp hlo hΛ hlab hsite hsep ha hW hb

/-- **`WcW.proW_wcGH` at `ownGHXW`.** -/
theorem proW_wcGHX (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms (L.lab "wc_main") 128 8 ".Lwc_main.stk" 5 9 3 6 7
      [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)] J0 :=
  Spike.Lib.X64.Flow.XProW.imp (WcW.proW_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi htp hmr hun)
    (proLH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi htp hun)
    fun _ _ h1 h2 => h2 h1

/-- **`WcW.eW_wcGH` at `ownGHXW`.** -/
theorem eW_wcGHX (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wNH L.lab R J0 J1 .e) wcEH :=
  Spike.Lib.X64.AllocG.BlkW.imp (WcW.eW_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi)
    (eLH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1

/-- **`WcW.wcSp0W_wcGH` at `ownGHXW`**: the box cells also off `tcbM` (`hboxM`). -/
theorem wcSp0W_wcGHX (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hboxM : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) ≠ tcbM L) :
    WcSp0WH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 :=
  have h := WcW.wcSp0W_wcGH hp hlo hΛ hlab hsite a (rS := rS) hR hRlo hhi hbox
  ⟨Spike.Lib.X64.AllocG.BlkW.imp h.1
      (sp0bLH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.2
      (sp0stLH (Λ := Λ) (Dt := fun _ => False) hp hlab hsep ha hW hb hbox hboxM) fun _ _ h1 h2 => h2 h1⟩

/-- **`WcW.resBlW_wcGH` at `ownGHXW`.** -/
theorem resBlW_wcGHX (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (rNH ms L.lab R J0 Q .bl) resBH :=
  Spike.Lib.X64.AllocG.BlkW.imp (WcW.resBlW_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi)
    (resBlLH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1

end Inst

end Spike.Lib.X64.HelloPh.OwnWc

/-- info: 'Spike.Lib.X64.HelloPh.OwnWc.proW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnWc.proW_wcGHX

/-- info: 'Spike.Lib.X64.HelloPh.OwnWc.eW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnWc.eW_wcGHX

/-- info: 'Spike.Lib.X64.HelloPh.OwnWc.wcSp0W_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnWc.wcSp0W_wcGHX

/-- info: 'Spike.Lib.X64.HelloPh.OwnWc.resBlW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnWc.resBlW_wcGHX
