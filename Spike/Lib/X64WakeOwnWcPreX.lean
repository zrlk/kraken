/-
**`wc_main`'s obligations before the reserve at `ownGXW`** (x86-64;
X64-OwnW Wc group): `WcW`'s producers at `SFactsSt2`/`ownG`
(`proW_wcG`, `eW_wcG`, `wcSp0W_wcG`, `resBlW_wcG`) moved to `SFactsSt2` at
`ownGXW` (`Lft2`), from outside (`XProW.imp`, `BlkW.imp`, `NodeW.imp` with
a second obligation inside `Lft2`): `wc_main` from its entry to the
reserve's call (`[4203303, 4203387]`) and the blocks' ends (`.Lwc_main.stk`,
`scc_rt_alloc`, `scc_rt_thread_reserve`) are `QP` pcs, its frame's band
`[-80, 8]` on the pool (`hb`), so every state holds `tcbM` only
(`cls_pool`); the limit's `%fs` load writes nothing, and the box store
misses `tcbM` (`hboxM`).

- `wc_labs`: the labels the pcs are decided from.
- `keep_fsld`, `hw_fsld`: the limit's load `movq %fs:8, %r11` keeps `%rsp`
  and `%rbp` and writes nothing.
- `proL`, `eL`, `sp0bL`, `sp0stL`, `resBlL`: the nodes inside `Lft2`.
- `proW_wcGX`, `eW_wcGX`, `wcSp0W_wcGX`, `resBlW_wcGX`: the producers at
  `ownGXW`.

**Deviations.** None: new lemmas. The producers take `ownGXW`'s separation
premises (`hsep`, `ha`, `hW`) and the frame's band (`hb : BandOnP L R (-80)
8`) besides the `ownG` producers'; the box store also takes `hboxM` (every
cell the allocator may return is off `tcbM`), carried.
-/
import Spike.Lib.X64WakeOwnLft2
import Spike.Lib.X64WakeWcPreWI
import Spike.Lib.X64Hello1WImp

namespace Spike.Lib.X64.WakePh.OwnWc

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range WriteTree)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (codeT_eq code_field label_labelGapB)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At fsDir stDir mB bAddr)
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok
  xHead_run xLea_run xCmp_run xFr_run xS1 xS2 hdRegs prologueIn ofNat_add' ofNat_zero')
open Spike.Lib.X64.Flow.WakeWc
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib.X64.WakePh.WcW (BoxOk bAddr_box slot_box)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop} {rS : Range}
  {R : Region} {F : MachineData → Prop}

/-- The labels `wc_main`'s pcs are decided from, at the canonical base. -/
theorem wc_labs (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab "wc_main" = Int64.ofNat 4203303 ∧ L.lab ".Lwc_main.chk" = Int64.ofNat 4203307 ∧
    L.lab ".Lwc_main.entry" = Int64.ofNat 4203338 ∧ L.lab ".Lwc_main.x0" = Int64.ofNat 4203364 ∧
    L.lab ".Lwc_main.stk" = Int64.ofNat 4203552 ∧ L.lab "scc_rt_alloc" = Int64.ofNat 4198629 ∧
    L.lab "scc_rt_thread_reserve" = Int64.ofNat 4199447 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

section Fs

variable {μ : Marks} {s s' : State} {z : Nat}

/-- **The limit's load `movq %fs:k, %r11`** of an unmapped word keeps
`%rsp` and `%rbp`. -/
theorem keep_fsld {k : Int64} (hc : CellAt s (fsDir .r11 k) z) (hdc : s.decls = {}) {A : BitVec 64}
    (ha : fsAddr s z { base := none, idx := none, disp := .int64 k } = A)
    (hdm : Mem.loadInt s.st.1.dmem A 8 = none) (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.X64.exec_movfs_load_agrees hc ha hdm (Spike.Lib.X64.agrees_of_decls hdc _ _)]
      at htr
    cases htr
    obtain ⟨v, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **The limit's load writes nothing.** -/
theorem hw_fsld {exe : _root_.Executable} {endPc : Int64} {n : ND} {c1 c2 : List (Loc × Val)} {k : Int64}
    {A : BitVec 64}
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (fsDir .r11 k) z ∧
      fsAddr s z { base := none, idx := none, disp := .int64 k } = A ∧
      Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {}) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  obtain ⟨hc, ha, hd, hdc⟩ := h s c hAt
  rw [Kraken.Promising.Lower.X64.exec_movfs_load_agrees hc ha hd (Spike.Lib.X64.agrees_of_decls hdc _ _)] at he
  cases he
  exact fun _ => trivial

end Fs

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soW " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -80 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

section L

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

set_option maxHeartbeats 1600000 in
/-- **`wc_main`'s prologue inside `Lft2`**: the limit's load at the thread
pointer `tp` (`htp`), its word unmapped under `F` (`hun`). -/
theorem proL (hb : BandOnP L R (-80) 8) (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F ms (L.lab "wc_main") 64 8 ".Lwc_main.stk" 5 9 3 6
      4 [(.rdi, -8, 4)] J0 := by
  obtain ⟨eW, eC, eE, -, eK, -, -⟩ := wc_labs hlab (L := L)
  have h := wake_wcPro
  simp only [wcPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".Lwc_main.chk" = L.lab "wc_main" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "wc_main" + 1 + 3 = L.lab ".Lwc_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 = L.lab ".Lwc_main.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e23 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6 =
      L.lab ".Lwc_main.chk" + Int64.ofNat 23 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hxs : (xS2 64 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) bHd (ofNat_zero' _)
      (xHead_ok (lo := -72) (hi := 0) (by decide) (Int.le_refl _)) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_ (soW xHead (⟨0, []⟩ : Spike.Lib.X64.SO))
      (fun σ c _ => ?_)
    · intro k hk; show PP (L.lab "wc_main" + Int64.ofNat (cellOff xHead k)).toBitVec.toNat
      rw [eW]; revert k; decide +kernel
    · rw [xHead_run]; show QP (L.lab "wc_main" + 1 + 3).toBitVec.toNat; rw [eW]; decide +kernel
  · refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) bLea
      (by show _ = L.lab "wc_main" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -72) (hi := 0) _ _) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_ (soW (xLea 64 5) Spike.Lib.X64.Flow.oH)
      (fun σ c _ => ?_)
    · intro k hk; show PP (L.lab "wc_main" + 1 + 3 + _).toBitVec.toNat; rw [eW]; revert k; decide +kernel
    · show QP (arun _ (xLea 64 5) ⟨L.lab "wc_main" + 1 + 3, Spike.Lib.X64.Flow.oH, σ⟩).pc.toBitVec.toNat
      rw [xLea_run (Z := 64) _ _ _ (by decide)]
      show QP (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eW]; decide +kernel
  · have hE : ∀ s c, At L.exe L.endPc R F (xProN2 (L.lab "wc_main") 5 64 J0) s c →
        CellAt s (fsDir .r11 8) 9 ∧
        fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨he, hn, hd, hp', σ2, hA, hF, σ0, hJ0, rfl⟩
      refine ⟨(code_field L.lays rfl (hp ▸ bLd) (by show _ = L.lab "wc_main" + 1 + 3 + _; rw [h4]) s he hn).cell0
        rfl rfl hp', ?_, hun _ hF, hd⟩
      rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 64 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
        rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    refine nodeL2 hlab hsep ha hW (sz := 9) (P := QP) (cls_pool hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [xProN2]; decide) (hw_fsld hE)
    · obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_fsld hc hd hea hun' hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show QP (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eW]; decide +kernel
    · show QP (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat; rw [eW]; decide +kernel
  · refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) bCmp
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -72) (hi := 0) _ _ _ _) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_ (soW (xCmp ".Lwc_main.stk" 3 6) (Spike.Lib.X64.Flow.oL 64))
      (fun σ c _ => ?_)
    · intro k hk; show PP (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + _).toBitVec.toNat
      rw [eW]; revert k; decide +kernel
    · show QP (arun _ (xCmp ".Lwc_main.stk" 3 6)
        ⟨L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9, Spike.Lib.X64.Flow.oL 64, σ⟩).pc.toBitVec.toNat
      rw [(xCmp_run _ _ _ _ _ _ _).1]
      split
      · rw [eW]; decide +kernel
      · show QP (L.lab ".Lwc_main.stk").toBitVec.toNat; rw [eK]; decide +kernel
  · refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) bFr
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _ + _ + _; rw [e23])
      (xFr_ok (lo := -72) (hi := 0) _ _ _ (by decide)) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
      (soW (xFr 64 4 [(.rdi, -8, 4)]) (Spike.Lib.X64.Flow.oL 64)) (fun σ c _ => ?_)
    · intro k hk
      show PP (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6 +
        _).toBitVec.toNat
      rw [eW]; revert k; decide +kernel
    · show QP (arun _ (xFr 64 4 [(.rdi, -8, 4)])
        ⟨L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6,
          Spike.Lib.X64.Flow.oL 64, σ⟩).pc.toBitVec.toNat
      rw [(xFr_run _ _ _ _ _ _).1, eW]; decide +kernel

/-- **`wc_main`'s entry block inside `Lft2`** (its call to `scc_rt_alloc`). -/
theorem eL (hb : BandOnP L R (-80) 8) (hR : R.OK) (hRlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi)
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (wN L.lab R J0 .e) wcE := by
  obtain ⟨-, -, eE, -, -, eA, -⟩ := wc_labs hlab (L := L)
  refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) (l := ".Lwc_main.entry") (k := 0)
    (by have := wake_wcEIn; simp only [wcEIn, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) wcE_ok hR hRlo hhi (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
    (soW wcE oWR) (fun σ c _ => ?_)
  · intro k hk; show PP (L.lab ".Lwc_main.entry" + _).toBitVec.toNat; rw [eE]; revert k; decide +kernel
  · show QP (arun _ wcE ⟨_, oWR, σ⟩).pc.toBitVec.toNat
    rw [wcE_run]; show QP (L.lab "scc_rt_alloc").toBitVec.toNat; rw [eA]; decide +kernel

/-- **`.x18`'s block inside `Lft2`.** -/
theorem sp0bL (hb : BandOnP L R (-80) 8) (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (sN ms L.lab R J0 .b) wcS0 := by
  obtain ⟨-, -, -, e18, -, -, -⟩ := wc_labs hlab (L := L)
  refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) (l := ".Lwc_main.x0") (k := 0)
    (by have := wake_wcS0In; simp only [wcS0In, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) wcS0_ok hR hRlo hhi (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
    (soW wcS0 oWR) (fun σ c _ => ?_)
  · intro k hk; show PP (L.lab ".Lwc_main.x0" + _).toBitVec.toNat; rw [e18]; revert k; decide +kernel
  · show QP (arun _ wcS0 ⟨_, oWR, σ⟩).pc.toBitVec.toNat
    rw [wcS0_run]; show QP (L.lab ".Lwc_main.x0" + Int64.ofNat 15).toBitVec.toNat; rw [e18]; decide +kernel

omit hsite in
/-- **The box store inside `Lft2`**: every cell the allocator may return
has `BoxOk` (`hbox`) and is off `tcbM` (`hboxM`). -/
theorem sp0stL (hb : BandOnP L R (-80) 8) {ms : Spike.Lib.MemSide isa}
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOk Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hboxM : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) ≠ tcbM L) :
    NodeW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (sN ms L.lab R J0 .st) := by
  obtain ⟨-, -, -, e18, -, -, -⟩ := wc_labs hlab (L := L)
  have hin := wake_wcS0In
  simp only [wcS0In, Bool.and_eq_true] at hin
  obtain ⟨-, h3⟩ := hin
  refine WcW.NodeW.ofAll (fun σ => σ.slot (-24)) fun A => ?_
  by_cases hA : BoxOk Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    obtain ⟨q, o, hj, hlo', hle, e⟩ := slot_box hJ
    exact absurd (e ▸ hbox q o hj hlo' hle) hA
  by_cases hM : A = tcbM L
  case pos =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, hsA⟩
    obtain ⟨q, o, hj, hlo', hle, e⟩ := slot_box hJ
    exact absurd (e.symm.trans (hsA.trans hM)) (hboxM q o hj hlo' hle)
  have hAM : A ≠ tcbM L := hM
  obtain ⟨-, hunA, -⟩ := hA
  have hE : ∀ s c, At L.exe L.endPc R F
      ⟨(sN ms L.lab R J0 .st).pc, (sN ms L.lab R J0 .st).o,
        fun σ c => (sN ms L.lab R J0 .st).J σ c ∧ σ.slot (-24) = A⟩ s c →
      CellAt s (stDir .rcx 0 .rax) 3 ∧ eaddr s 3 (mB .rcx 0) = A ∧
      Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {} := by
    rintro s c ⟨he, hn, hd, hp', σ, hA', hF, hJ, hsA⟩
    exact ⟨(code_field L.lays rfl (hp ▸ h3) rfl s he hn).cell0 rfl rfl hp',
      (Spike.Lib.X64.eaddr_mB s 3 .rcx 0).trans (by rw [hA'.regs, ← hsA]; exact bAddr_box hJ), hunA _ hF, hd⟩
  refine nodeL2 hlab hsep ha hW (sz := 3) (P := QP) (cls_pool hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
    (by dsimp only [sN]; decide) (OwnSt.hw_stM hE hAM)
  · obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
    have hK : Keep s s' := StartTi.keep_st hc hd hea hun' hs
    exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
  · show QP (L.lab ".Lwc_main.x0" + Int64.ofNat 15).toBitVec.toNat; rw [e18]; decide +kernel
  · show QP (L.lab ".Lwc_main.x0" + Int64.ofNat 15 + Int64.ofNat 3).toBitVec.toNat; rw [e18]; decide +kernel

/-- **The reserve's call block inside `Lft2`.** -/
theorem resBlL (hb : BandOnP L R (-80) 8) (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    BlkW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (rN ms L.lab R J0 Q .bl) resB := by
  obtain ⟨-, -, -, e18, -, -, eR⟩ := wc_labs hlab (L := L)
  refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) (l := ".Lwc_main.x0") (k := 18)
    (by have := wake_wcResIn; simp only [wcResIn, Bool.and_eq_true] at this; exact this.1)
    rfl resB_ok hR hRlo hhi (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
    (soW resB (⟨-64, [(.rbp, 0)]⟩ : Spike.Lib.X64.SO)) (fun σ c _ => ?_)
  · intro k hk; show PP (L.lab ".Lwc_main.x0" + Int64.ofNat 18 + _).toBitVec.toNat; rw [e18]; revert k
    decide +kernel
  · show QP (arun _ resB ⟨_, ⟨-64, [(.rbp, 0)]⟩, σ⟩).pc.toBitVec.toNat
    rw [resB_run]; show QP (L.lab "scc_rt_thread_reserve").toBitVec.toNat; rw [eR]; decide +kernel

end L

/-! ## The producers at `ownGXW` -/

section Inst

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
  (hb : BandOnP L R (-80) 8)
include hp hlo hΛ hlab hsite hsep ha hW hb

/-- **`WcW.proW_wcG` at `ownGXW`.** -/
theorem proW_wcGX (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms (L.lab "wc_main") 64 8 ".Lwc_main.stk" 5 9 3 6 4 [(.rdi, -8, 4)] J0 :=
  Spike.Lib.X64.Flow.XProW.imp (WcW.proW_wcG hp hlo hΛ hlab hsite a hR hRlo hhi htp hmr hun)
    (proL (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi htp hun)
    fun _ _ h1 h2 => h2 h1

/-- **`WcW.eW_wcG` at `ownGXW`.** -/
theorem eW_wcGX (hR : R.OK) (hRlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi)
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wN L.lab R J0 .e) wcE :=
  Spike.Lib.X64.AllocG.BlkW.imp (WcW.eW_wcG hp hlo hΛ hlab hsite a hR hRlo hhi)
    (eL (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1

/-- **`WcW.wcSp0W_wcG` at `ownGXW`**: the box cells also off `tcbM`
(`hboxM`). -/
theorem wcSp0W_wcGX (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOk Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hboxM : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) ≠ tcbM L) :
    WcSp0W (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 :=
  have h := WcW.wcSp0W_wcG hp hlo hΛ hlab hsite a (rS := rS) hR hRlo hhi hbox
  ⟨Spike.Lib.X64.AllocG.BlkW.imp h.b
      (sp0bL (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.st
      (sp0stL (Λ := Λ) (Dt := fun _ => False) hp hlab hsep ha hW hb hbox hboxM) fun _ _ h1 h2 => h2 h1⟩

/-- **`WcW.resBlW_wcG` at `ownGXW`.** -/
theorem resBlW_wcGX (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (rN ms L.lab R J0 Q .bl) resB :=
  Spike.Lib.X64.AllocG.BlkW.imp (WcW.resBlW_wcG hp hlo hΛ hlab hsite a hR hRlo hhi)
    (resBlL (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1

end Inst

end Spike.Lib.X64.WakePh.OwnWc

/-- info: 'Spike.Lib.X64.WakePh.OwnWc.proW_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnWc.proW_wcGX

/-- info: 'Spike.Lib.X64.WakePh.OwnWc.eW_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnWc.eW_wcGX

/-- info: 'Spike.Lib.X64.WakePh.OwnWc.wcSp0W_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnWc.wcSp0W_wcGX

/-- info: 'Spike.Lib.X64.WakePh.OwnWc.resBlW_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnWc.resBlW_wcGX
