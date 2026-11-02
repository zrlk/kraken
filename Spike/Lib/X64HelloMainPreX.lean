/-
**hello.w's `scc_rt_main` up to `call wc_rodata` inside the start's level at `ownGHXW`** (x86-64; the hello twin of
`Spike/Lib/X64WakeMainPreX.lean`): `MainWf.mainPreWH_W0SH`'s prologue and `.entry`'s call block inside
`StartWf.WSH` (at `ownGH`) are inside `WSHX` (at `ownGHXW`). They run on the new stack, from `scc_rt_main` (past
`.x1`) to `wc_rodata`'s entry, in none of `InTH`, `InCH`, `InAbH` (`QPH`), the frame's band `[-80, 8]` on the pool
(`hb`): every state holds main's TCB word only (`cls_poolH`), and the limit's `%fs` load writes nothing (`hw_fsld`).

- `main_labsH`: the labels the pcs are decided from.
- `proLMH`, `callLMH`: the prologue's and the call block's nodes inside `LftH` (by `blkLH`, `nodeLH`).
- `mainPreWHX`: `mainPreWH_W0SH`'s pair inside `WSHX`.

## Differences from the AArch64 version

AArch64's start level owns `ownGH` throughout, so its `scc_rt_main` prefix is used as is; x86-64's main also holds
its own TCB word from `.x1` on (`ownSH`), so the prefix is lifted to `WSHX`. Against x86-64 wake's `MainPreX`: hello's
`scc_rt_main` calls `wc_rodata` first (`Hello1.mN0`, `mB0`; wake `WakeM.wN0`, `wB0` into `wc_main`), its frame is
`64` bytes (band `[-80, 8]`, `xLea 64`, `xFr 64`; wake `32`, `[-48, 8]`), and the pair is
`mainPreWH_W0SH`'s (`XProW ∧ BlkW`; wake `MainPreWW`), with `mB0_ok`'s region bounds (`R.lo ≤ -288`, `8 ≤ R.hi`).
Wake's `blkLB`/`nodeLB` are hello's `blkLH`/`nodeLH`; `keep_fsld`, `hw_fsld`, `soRun` read no program and are
used as they are.
-/
import Spike.Lib.X64HelloOwnLftCX
import Spike.Lib.X64HelloOwnLft2X
import Spike.Lib.X64HelloMainWf
import Spike.Lib.X64WakeMainPreX

namespace Spike.Lib.X64.HelloPh.MainPreX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range WriteTree)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (codeT_eq code_field label_labelGapB blockAtB)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SpAt rsp_of_abs)
open Spike.Lib.X64 (ND BlkW NodeW At fsDir okBlk arun cellOff)
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok
  xHead_run xLea_run xCmp_run xFr_run xS1 xS2 hdRegs prologueIn ofNat_add' ofNat_zero')
open Spike.Lib.X64.Flow.Hello1 (mN0 mB0 mB0_ok mB0_run mO)
open Spike.Lib.X64.WakePh (tcbM Keep keep_pc BandOnP)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib.X64.WakePh.OwnWc (keep_fsld hw_fsld)
open Spike.Lib.X64.HelloPh.StartWf (WSH)
open Spike.Lib.X64.HelloPh (lo LftH WSHX QPH PPH cls_poolH blkLH nodeLH)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr)
open Spike.Lib (Region Arena FragS)
open Spike.Lib.X64Consumer (Lbl Lsize)

variable {L : RuntimeLayout} {a : BitVec 64} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

/-- The labels hello's `scc_rt_main`'s pcs are decided from, at the canonical base. -/
theorem main_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab "scc_rt_main" = Int64.ofNat 4198540 ∧ L.lab ".Lscc_rt_main.stk" = Int64.ofNat 4198638 ∧
    L.lab ".Lscc_rt_main.entry" = Int64.ofNat 4198571 ∧ L.lab "wc_rodata" = Int64.ofNat 4203131 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soM " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -80 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

section L

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

variable (hb : BandOnP L R (-80) 8)
include hb

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_main`'s prologue inside `LftH`**: the limit's load at the thread pointer `tp` (`htp`), its word
unmapped under `F` (`hun`). -/
theorem proLMH (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F ms
      (L.lab "scc_rt_main") 64 8 ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J := by
  obtain ⟨eM, eK, -, -⟩ := main_labsH hlab (L := L)
  have h := Spike.Lib.X64.Flow.HelloM.hello_mainPro
  simp only [Spike.Lib.X64.Flow.HelloM.hMainPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".Lscc_rt_main.chk" = L.lab "scc_rt_main" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "scc_rt_main" + 1 + 3 = L.lab ".Lscc_rt_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 =
      L.lab ".Lscc_rt_main.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e19 : L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 =
      L.lab ".Lscc_rt_main.chk" + Int64.ofNat 19 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hxs : (xS2 64 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bHd (ofNat_zero' _)
      (xHead_ok (lo := -72) (hi := 0) (by decide) (Int.le_refl _)) hR (by omega) hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soM xHead (⟨0, []⟩ : Spike.Lib.X64.SO))
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab "scc_rt_main" + Int64.ofNat (cellOff xHead k)).toBitVec.toNat
      rw [eM]; revert k; decide +kernel
    · rw [xHead_run]; show QPH (L.lab "scc_rt_main" + 1 + 3).toBitVec.toNat; rw [eM]; decide +kernel
  · refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bLea
      (by show _ = L.lab "scc_rt_main" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -72) (hi := 0) _ _) hR (by omega) hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soM (xLea 64 5) Spike.Lib.X64.Flow.oH)
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab "scc_rt_main" + 1 + 3 + _).toBitVec.toNat; rw [eM]; revert k; decide +kernel
    · show QPH (arun _ (xLea 64 5) ⟨L.lab "scc_rt_main" + 1 + 3, Spike.Lib.X64.Flow.oH, σ⟩).pc.toBitVec.toNat
      rw [xLea_run (Z := 64) _ _ _ (by decide)]
      show QPH (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eM]; decide +kernel
  · have hE : ∀ s c, At L.exe L.endPc R F (xProN2 (L.lab "scc_rt_main") 5 64 J) s c →
        CellAt s (fsDir .r11 8) 9 ∧
        fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨he, hn, hd, hp', σ2, hA, hF, σ0, hJ0, rfl⟩
      refine ⟨(code_field L.lays rfl (hp ▸ bLd) (by show _ = L.lab "scc_rt_main" + 1 + 3 + _; rw [h4]) s he hn).cell0
        rfl rfl hp', ?_, hun _ hF, hd⟩
      rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 64 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
        rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    refine nodeLH hsep ha hW (sz := 9) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [xProN2]; decide) (hw_fsld hE)
    · obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_fsld hc hd hea hun' hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show QPH (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eM]; decide +kernel
    · show QPH (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat; rw [eM]; decide +kernel
  · refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bCmp
      (by show _ = L.lab "scc_rt_main" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -72) (hi := 0) _ _ _ _) hR (by omega) hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soM (xCmp ".Lscc_rt_main.stk" 3 2) (Spike.Lib.X64.Flow.oL 64)) (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + _).toBitVec.toNat
      rw [eM]; revert k; decide +kernel
    · show QPH (arun _ (xCmp ".Lscc_rt_main.stk" 3 2)
        ⟨L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9, Spike.Lib.X64.Flow.oL 64, σ⟩).pc.toBitVec.toNat
      rw [(xCmp_run _ _ _ _ _ _ _).1]
      split
      · rw [eM]; decide +kernel
      · show QPH (L.lab ".Lscc_rt_main.stk").toBitVec.toNat; rw [eK]; decide +kernel
  · refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bFr
      (by show _ = L.lab "scc_rt_main" + 1 + 3 + _ + _ + _ + _; rw [e19])
      (xFr_ok (lo := -72) (hi := 0) _ _ _ (by decide)) hR (by omega) hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soM (xFr 64 4 [(.rdi, -8, 4)]) (Spike.Lib.X64.Flow.oL 64)) (fun σ c _ => ?_)
    · intro k hk
      show PPH (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 +
        _).toBitVec.toNat
      rw [eM]; revert k; decide +kernel
    · show QPH (arun _ (xFr 64 4 [(.rdi, -8, 4)])
        ⟨L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2,
          Spike.Lib.X64.Flow.oL 64, σ⟩).pc.toBitVec.toNat
      rw [(xFr_run _ _ _ _ _ _).1, eM]; decide +kernel

/-- **`.entry`'s call block inside `LftH`**: it ends at `wc_rodata`'s entry. -/
theorem callLMH (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi) {J : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F
      (mN0 (_root_.Executable.labels L.exe).label R J) mB0 := by
  obtain ⟨-, -, eE, eR⟩ := main_labsH hlab (L := L)
  have h := Spike.Lib.X64.Flow.HelloM.hello_mainIn
  simp only [Spike.Lib.X64.Flow.Hello1.mainIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨b0, -⟩, -⟩, -⟩ := h
  refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) (l := ".Lscc_rt_main.entry") (k := 0) b0
    (ofNat_zero' _) mB0_ok hR hRlo hhi (fun _ h => h.2)
    (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
    (soM mB0 mO) (fun σ c _ => ?_)
  · intro k hk
    show PPH (L.lab ".Lscc_rt_main.entry" + Int64.ofNat (cellOff mB0 k)).toBitVec.toNat
    rw [eE]; revert k; decide +kernel
  · dsimp only [mN0]
    rw [mB0_run]
    show QPH (L.lab "wc_rodata").toBitVec.toNat
    rw [eR]; decide +kernel

end L

/-- **hello's `scc_rt_main` up to `call wc_rodata` inside `WSHX`**: `h` (inside `WSH`, `MainWf.mainPreWH_W0SH`) and
every node inside `LftH` (`proLMH`, `callLMH`), the frame's band on the pool (`hb`). -/
theorem mainPreWHX (hp : L.prog = helloCells)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandOnP L R (-80) 8) (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {rS : Range} {ms : Spike.Lib.MemSide isa} {J : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (h : XProW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc
        R F ms (L.lab "scc_rt_main") 64 8 ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J ∧
      BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
        (mN0 L.lab R J) mB0) :
    XProW (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc
        R F ms (L.lab "scc_rt_main") 64 8 ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J ∧
      BlkW (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
        (mN0 L.lab R J) mB0 :=
  ⟨Spike.Lib.X64.Flow.XProW.imp h.1 (proLMH hp hlab hsite hsep ha hW hb hR (by omega) (by omega) htp hun)
      fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.BlkW.imp h.2 (callLMH hp hlab hsite hsep ha hW hb hR hRlo hhi)
      fun _ _ h1 h2 => h2 h1⟩

end Spike.Lib.X64.HelloPh.MainPreX

/-- info: 'Spike.Lib.X64.HelloPh.MainPreX.main_labsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainPreX.main_labsH

/-- info: 'Spike.Lib.X64.HelloPh.MainPreX.proLMH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainPreX.proLMH

/-- info: 'Spike.Lib.X64.HelloPh.MainPreX.callLMH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainPreX.callLMH

/-- info: 'Spike.Lib.X64.HelloPh.MainPreX.mainPreWHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainPreX.mainPreWHX
