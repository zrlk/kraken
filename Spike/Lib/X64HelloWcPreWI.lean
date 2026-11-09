/-
**hello.w's `wc_main` obligations before `.x24` inside `SFactsSt2` at `ownGH`** (x86-64; the twin of
`Spike/Lib/A64HelloWcPreWI.lean`, at `helloCells` the twin of x86-64 wake's `X64WakeWcPreWI`): the `SFactsSt2`
component of the pre-spawn chain's `W` for `WcPreWH`'s prologue (frame 128, five argument spills) and entry
block, `WcSp0WH`, and `WcResWH`'s call block. Each is an instance of `blkW_wcGH` or `nodeW_wcGH`
(`Spike/Lib/X64HelloWcPreW.lean`). The checks are decided by the kernel against helloCells' labels, with no
absolute address in this file.

- `proW_wcGH`: the prologue (`XProW`), the thread pointer fixed (`htp`), its limit word mapped and unmapped
  (`hmr`, `hun`). The limit's load is wake's `WcW.nodeW_fsld_pre`.
- `eW_wcGH`: the entry block.
- `BoxOkH`, `bAddr_boxH`, `slot_boxH`, `sp0bW_wcGH`, `sp0stW_wcGH`, `wcSp0W_wcGH`: `.x22`'s block and the box
  store (`movq %rax, (%rcx)` at `.x22 + 15`, the cell at slot `-56`).
- `resBlW_wcGH`: the reserve's call block.

## Differences from the AArch64 version

- There is no fence before the reserve's call (scc's `# fence st` emits no code under TSO, `X64HelloWcSp0`),
  so AArch64's `fenceW_wcGH` has no twin here.
- The prologue is x86-64's five-node `XProW` (AArch64's four-node `ProW`), its limit load a `%fs` load before
  the take (wake's `nodeW_fsld_pre`; AArch64's `nodeW_ldr_pre`); offsets are bytes (`freeAtH l os`,
  `freeBlkH`); there is no `hal`; the bounds are x86-64's frame (`R.lo ≤ -136`, `-304` at the entry block's
  call, `8 ≤ R.hi` past the return address).
- `ne_clonePc_of_freeNH` (and `clonePcH`, `clone_inCvH`) are `X64HelloWcClonePc`'s, as in x86-64 wake
  (`X64WakeWcClonePc`): they read the clone's pc, which this file's blocks do not need.
-/
import Spike.Lib.X64HelloWcPreW
import Spike.Lib.X64WakeWcPreWI

namespace Spike.Lib.X64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (blockAtB codeT_eq label_labelGapB)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl CFacts SFacts K0)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At arun fsDir bAddr mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Flow (XProW xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok xHead_run xLea_run xCmp_run
  xFr_run xS1 xS2 hdRegs prologueIn ofNat_add' ofNat_zero')
open Spike.Lib.X64.Flow.WakeWc (AGB)
open Spike.Lib.X64.Flow.HelloWc
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr exec_movfs_load_agrees exec_store_agrees)
open Spike.Lib.X64.HelloPh
open Spike.Lib.X64.WakePh.WcW (c0N_cfacts NodeW.ofAll nodeW_fsld_pre)

/-- The kernel's check of a `freeAtH` of helloCells. -/
macro "wcfreeH_dec" : tactic => `(tactic| (unfold freeAtH freeNH inCvH cvH; rw [← codeT_eq]; decide +kernel))

/-- The kernel's check of a `freeBlkH` of helloCells. -/
macro "wcfreeBH_dec" : tactic =>
  `(tactic| (unfold freeBlkH freeAtH freeNH inCvH cvH; rw [← codeT_eq]; decide +kernel))

/-! ## The box store's cell -/

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}

/-- **A box cell's facts**: mapped for writing in the loaded kernel state, unmapped in private memory under `F`,
and off the owned words `ownH L a`. -/
def BoxOkH (Λ : Scc.Sem.Layout) (L : RuntimeLayout) (a : BitVec 64) (F : MachineData → Prop) (A : BitVec 64) :
    Prop :=
  Scc.Sem.Kernel.mapped (K0 Λ) true ⟨A, 8⟩ = true ∧ (∀ m, F m → Mem.loadInt m.dmem A 8 = none) ∧
    ∀ j w, (⟨A, 8⟩, w) ∉ ownH L a j

/-- The box store's address `(%rcx)` is the cell at slot `-56`. -/
theorem bAddr_boxH {ms : Spike.Lib.MemSide isa} {lab : Label → Int64} {R : Spike.Lib.Region}
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {σ : Spike.Lib.X64.AS} {c : Spike.Lib.Ctl} (h : (sNH ms lab R J0 .st).J σ c) :
    bAddr σ.regs .rcx 0 = σ.slot (-56) := by
  obtain ⟨_, _, -, -, -, hx, -⟩ := h
  rw [← hx]
  simp [bAddr, Reg64s.get64]

/-- The box store's cell from its node's facts. -/
theorem slot_boxH {ms : Spike.Lib.MemSide isa} {lab : Label → Int64} {R : Spike.Lib.Region}
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {σ : Spike.Lib.X64.AS} {c : Spike.Lib.Ctl} (h : (sNH ms lab R J0 .st).J σ c) :
    ∃ (q : AGB ms lab) (o : Nat), (∃ σ, J0 σ q.1.c0) ∧ ms.lo o ∧ o + ms.units 1 q.1.τ ≤ ms.cells ∧
      σ.slot (-56) = BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) := by
  obtain ⟨q, o, ⟨σe, hJe, -⟩, -, -, -, hsl, hle, hlo'⟩ := h
  exact ⟨q, o.toNat, ⟨σe, hJe⟩, hlo', hle, BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, ← hsl, Nat.mod_eq_of_lt (BitVec.isLt _)])⟩

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`wc_main`'s entry block inside `SFactsSt2` at `ownGH`.** -/
theorem eW_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wNH L.lab R J0 J1 .e) wcEH :=
  blkW_wcGH hp hlo hΛ hlab a hsite (l := ".Lwc_main.entry") (k := 0)
    (by have := hello_wcEInH; simp only [wcEInH, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) wcEH_ok hR hRlo hhi (by decide) (by decide) (by wcfreeBH_dec)
    (fun σ c _ => by
      show freeNH (arun L.lab wcEH ⟨_, oWRH, σ⟩).pc.toBitVec.toNat = true
      rw [wcEH_run]
      exact freeAt_labH hlab (by wcfreeH_dec))

/-- **`.x22`'s block inside `SFactsSt2` at `ownGH`.** -/
theorem sp0bW_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (sNH ms L.lab R J0 .b) wcS0H :=
  blkW_wcGH hp hlo hΛ hlab a hsite (l := ".Lwc_main.x0") (k := 0)
    (by have := hello_wcS0InH; simp only [wcS0InH, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) wcS0H_ok hR hRlo hhi (by decide) (by decide) (by wcfreeBH_dec)
    (fun σ c _ => by
      show freeNH (arun L.lab wcS0H ⟨_, oWRH, σ⟩).pc.toBitVec.toNat = true
      rw [wcS0H_run]
      exact freeAt_pcH hlab (l := ".Lwc_main.x0") (os := [15]) (by wcfreeH_dec) (List.mem_singleton.mpr rfl))

/-- **The reserve's call block inside `SFactsSt2` at `ownGH`.** -/
theorem resBlW_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (rNH ms L.lab R J0 Q .bl) resBH :=
  blkW_wcGH hp hlo hΛ hlab a hsite (l := ".Lwc_main.x0") (k := 18)
    (by have := hello_wcResInH; simp only [wcResInH, Bool.and_eq_true] at this; exact this.1)
    rfl resBH_ok hR hRlo hhi (by decide) (by decide) (by wcfreeBH_dec)
    (fun σ c _ => by
      show freeNH (arun L.lab resBH ⟨_, ⟨-128, [(.rbp, 0)]⟩, σ⟩).pc.toBitVec.toNat = true
      rw [resBH_run]
      exact freeAt_labH hlab (by wcfreeH_dec))

/-- **The box store inside `SFactsSt2` at `ownGH`**: every cell the allocator may return, for a `q` whose `c0`
some `J0` state carries, has `BoxOkH` (`hbox`). -/
theorem sp0stW_wcGH (a : BitVec 64) {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ))) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (sNH ms L.lab R J0 .st) := by
  have hin := hello_wcS0InH
  simp only [wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨-, h3⟩ := hin
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hb : blockAtB L.prog ".Lwc_main.x0" 15 [(Spike.Lib.X64.stDir .rcx 0 .rax, 3)] = true := by
    rw [hp]; exact h3
  have hf := Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
    (wcW_factH hΛ (f := .step ".Lwc_main.x0" 15 3) (by decide))
  have hfr : freeAtH ".Lwc_main.x0" [15, 15 + 3] = true := by wcfreeH_dec
  have f0 := freeAt_pcH hlab hfr (o := 15) (by simp)
  have f3 := freeAt_pcH hlab hfr (o := 15 + 3) (by simp)
  rw [ofNat_add'] at f3
  refine NodeW.ofAll (fun σ => σ.slot (-56)) fun A => ?_
  by_cases hA : BoxOkH Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    obtain ⟨q, o, hj, hlo', hle, e⟩ := slot_boxH hJ
    exact absurd (e ▸ hbox q o hj hlo' hle) hA
  obtain ⟨hmw, hun, hno⟩ := hA
  refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
    (Spike.Lib.X64.Rt.nodeW_st_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) (ownOf := ownH L a)
      (fun _ => rfl) hb rfl rfl c0N_cfacts hf.1 (fun _ _ h => h) hf.2 ?_ hmw hun hno) f0 f3 ?_
  · rintro σ c ⟨-, c', hJ, rfl⟩
    exact bAddr_boxH hJ
  · rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, hJ, hsA⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb rfl h1 h2 h4'
    have ha' : eaddr s 3 (mB .rcx 0) = A :=
      (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs, ← hsA]; exact bAddr_boxH hJ)
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_store_agrees hc ha' (hun _ hF) (agrees_of_decls h3' _ _),
      fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl

/-- **`wc_main`'s prologue inside `SFactsSt2` at `ownGH`**: the thread pointer `tp` at every entry state
(`htp`), its limit word mapped for reading (`hmr`) and unmapped in private memory under `F` (`hun`). -/
theorem proW_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms (L.lab "wc_main") 128 8 ".Lwc_main.stk" 5 9 3 6 7
      [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)] J0 := by
  have h := hello_wcPro
  simp only [hWcPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have esc : L.lab ".Lwc_main.chk" = L.lab "wc_main" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "wc_main" + 1 + 3 = L.lab ".Lwc_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 = L.lab ".Lwc_main.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e23 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6 =
      L.lab ".Lwc_main.chk" + Int64.ofNat 23 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hfr : freeAtH ".Lwc_main.chk" [0, 5, 5 + 9, 23, 50] = true := by wcfreeH_dec
  have f0 := freeAt_pcH hlab hfr (o := 0) (by simp)
  have f5 := freeAt_pcH hlab hfr (o := 5) (by simp)
  have f14 := freeAt_pcH hlab hfr (o := 5 + 9) (by simp)
  have f23 := freeAt_pcH hlab hfr (o := 23) (by simp)
  have f50 := freeAt_pcH hlab hfr (o := 50) (by simp)
  rw [ofNat_zero'] at f0
  have hxs : (xS2 128 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_wcGH hp hlo hΛ hlab a hsite (l := "wc_main") (k := 0) bHd (ofNat_zero' _)
      (xHead_ok (lo := -136) (hi := 0) (by decide) (Int.le_refl _)) hR hRlo hhi (by decide) xHead_noRet
      (by wcfreeBH_dec) (fun σ c _ => by
        show freeNH (arun L.lab xHead ⟨L.lab "wc_main", ⟨0, []⟩, σ⟩).pc.toBitVec.toNat = true
        rw [xHead_run]
        show freeNH (L.lab "wc_main" + 1 + 3).toBitVec.toNat = true
        rw [h4]; exact f0)
  · exact blkW_wcGH hp hlo hΛ hlab a hsite (l := ".Lwc_main.chk") (k := 0) bLea
      (by show _ = L.lab "wc_main" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -136) (hi := 0) _ _) hR hRlo hhi (by decide) (xLea_noRet _ _) (by wcfreeBH_dec)
      (fun σ c _ => by
        show freeNH (arun L.lab (xLea 128 5) ⟨L.lab "wc_main" + 1 + 3, Spike.Lib.X64.Flow.oH, σ⟩).pc.toBitVec.toNat
          = true
        rw [xLea_run (Z := 128) _ _ _ (by decide)]
        show freeNH (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat = true
        rw [h4]; exact f5)
  · have hf := Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
      (wcW_factH hΛ (f := .step ".Lwc_main.chk" 5 9) (by decide))
    have hbL : blockAtB L.prog ".Lwc_main.chk" 5 [(fsDir .r11 8, 9)] = true := by rw [hp]; exact bLd
    refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
      (nodeW_fsld_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) hbL rfl
        (by show L.lab "wc_main" + 1 + 3 + _ = _; rw [h4]) c0N_cfacts hf.1 (fun _ _ h => h) hf.2 ?_ hmr hun)
      (by show freeNH (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat = true; rw [h4]; exact f5)
      (by show freeNH (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat = true
          rw [e14]; exact f14) ?_
    · rintro σ c ⟨-, c', σ0, hJ0, rfl⟩
      rw [congrFun hxs σ0, htp _ _ hJ0]; rfl
    · rintro s c ⟨h1, h2, h3', h4', σ2, hA, hF, σ0, hJ0, rfl⟩
      have hc := Spike.Lib.X64.Rt.cellOf hI hbL rfl h1 h2
        (by rw [h4']; show L.lab "wc_main" + 1 + 3 + _ = _; rw [h4])
      have ha' : fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp := by
        rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 128 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
          rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
        simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
      refine ⟨_, _, hc, fun w w' h => (by cases h),
        exec_movfs_load_agrees hc ha' (hun _ hF) (agrees_of_decls h3' _ _), fun s' hu => ?_⟩
      simp only [TreeLeaf] at hu
      obtain ⟨_, rfl⟩ := hu; rfl
  · exact blkW_wcGH hp hlo hΛ hlab a hsite (l := ".Lwc_main.chk") (k := 14) bCmp
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -136) (hi := 0) _ _ _ _) hR hRlo hhi (by decide) (xCmp_noRet _ _ _) (by wcfreeBH_dec)
      (fun σ c _ => by
        show freeNH (arun L.lab (xCmp ".Lwc_main.stk" 3 6)
          ⟨L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9, Spike.Lib.X64.Flow.oL 128, σ⟩).pc.toBitVec.toNat
          = true
        rw [(xCmp_run _ _ _ _ _ _ _).1]
        split
        · rw [e23]; exact f23
        · exact freeAt_labH hlab (by wcfreeH_dec))
  · exact blkW_wcGH hp hlo hΛ hlab a hsite (l := ".Lwc_main.chk") (k := 23) bFr
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _ + _ + _; rw [e23])
      (xFr_ok (lo := -136) (hi := 0) _ _ _ (by decide)) hR hRlo hhi (by decide) (xFr_noRet _ _ _)
      (by wcfreeBH_dec) (fun σ c _ => by
        show freeNH (arun L.lab (xFr 128 7 [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4),
            (.r8, -40, 4)])
          ⟨L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6,
            Spike.Lib.X64.Flow.oL 128, σ⟩).pc.toBitVec.toNat = true
        rw [(xFr_run _ _ _ _ _ _).1, e23, ← ofNat_add', ← ofNat_add']
        exact f50)

/-- **`WcSp0WH` at `SFactsSt2`/`ownGH`**: `.x22`'s block and the box store. -/
theorem wcSp0W_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ))) :
    WcSp0WH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 :=
  ⟨sp0bW_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi, sp0stW_wcGH hp hlo hΛ hlab hsite a hbox⟩

end Inst

end Spike.Lib.X64.HelloPh.WcW

/-- info: 'Spike.Lib.X64.HelloPh.WcW.eW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.eW_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.sp0bW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.sp0bW_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.resBlW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.resBlW_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.sp0stW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.sp0stW_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.proW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.proW_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.wcSp0W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.wcSp0W_wcGH
