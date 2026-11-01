/-
**hello.w's `wc_main` obligations before `.sp4` inside `SFactsSt2` at
`ownGH`** (AArch64): the twin of
`Spike/Lib/A64WakeWcPreWI.lean` at helloProg. It is the `SFactsSt2` component
of the pre-spawn chain's `W` for `WcPreWH`'s prologue (frame 144, five
argument spills) and entry block, `WcSp0WH`, and `WcResWH`'s fence and call
block. Each is an instance of `blkW_wcGH` or `nodeW_wcGH`
(`Spike/Lib/A64HelloWcPreW.lean`). The checks are decided by the kernel
against helloProg's labels, with no absolute address in this file.

- `proW_wcGH`: the prologue (`ProW`), the thread pointer fixed (`htp`), its
  limit word mapped and unmapped (`hmr`, `hun`).
- `eW_wcGH`: the entry block.
- `BoxOkH`, `sp0bW_wcGH`, `sp0stW_wcGH`, `wcSp0W_wcGH`: `.sp0`'s block and
  the box store (`[sp, #40]`).
- `fenceW_wcGH`, `resBlW_wcGH`: the fence and the reserve's call block.
- `ne_clonePc_of_freeNH`: a free pc is not the clone's (`clonePcH`, `.sp6`
  plus 25 instructions).
-/
import Spike.Lib.A64HelloWcPreW
import Spike.Lib.A64HelloWcInv
import Spike.Lib.A64WakeWcPreWI

namespace Spike.Lib.A64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk blockAt pcAt)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl CFacts SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ofNat4_zero ofNat4_succ)
open Spike.Lib.A64.Flow.WakeWc (AGB pubF pubF_eq boxSt_eq)
open Spike.Lib.A64.Flow.HelloWc
open Kraken.Promising.Lower.A64 (CellAt after)
open Spike.Lib.A64.HelloPh
open Spike.Lib.A64.WakePh.WcW (nodeW_dmb_pre c0N c0N_cfacts NodeW.ofAll)

/-- The kernel's check of a `freeAtH`. -/
macro "free_decH" : tactic => `(tactic| (unfold freeAtH freeNH inCvH cvH; rw [← codeT_eq]; decide +kernel))

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}

/-- **A free pc `4 k` past a label**, from `freeAtH l k 1`. -/
theorem freeKH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {l : Label} {k : Nat}
    (h : freeAtH l k 1 = true) : freeNH (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true :=
  freeAt_pc0H hlab h

/-- **A one-instruction block's cell** at a state of `L`'s executable at its pc. -/
theorem cell1H (hp : L.prog = SccCode.helloProg) {l : Label} {k : Nat} {d : Directive}
    (hb : blockAt SccCode.helloProg l k [d] = true)
    {s : State} (h1 : s.exe = L.exe) (h2 : s.endPc = L.endPc) (hpc : s.st.2 = L.lab l + Int64.ofNat (4 * k)) :
    CellAt s d 4 :=
  (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) rfl s h1 h2).cell (j := 0) rfl rfl rfl
    (by rw [hpc, ofNat4_zero])

/-- **A box cell's facts**: mapped for writing in the loaded kernel state,
unmapped in private memory under `F`, and off the owned words `ownH L a`. -/
def BoxOkH (Λ : Scc.Sem.Layout) (L : RuntimeLayout) (a : BitVec 64) (F : MachineData → Prop) (A : BitVec 64) : Prop :=
  Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨A, 8⟩ = true ∧ (∀ m, F m → Mem.loadInt m.dmem A 8 = none) ∧
    ∀ j w, (⟨A, 8⟩, w) ∉ ownH L a j

/-- The box store's address is the cell at `[sp, #8]`. -/
theorem rAddr_boxH {ms : Spike.Lib.MemSide isaLSE2} {lab : Label → Int64}
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {σ : Spike.Lib.A64.Flow.AS} {c : Spike.Lib.Ctl} (h : (sNH ms lab J0 .st).J σ c) :
    Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 = σ.slot (-104) := by
  obtain ⟨_, _, -, -, -, hx, -⟩ := h
  simp [Spike.Lib.A64.Flow.rAddr, Reg64s.getXReg, hx]

/-- The box store's cell from its node's facts. -/
theorem slot_boxH {ms : Spike.Lib.MemSide isaLSE2} {lab : Label → Int64}
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {σ : Spike.Lib.A64.Flow.AS} {c : Spike.Lib.Ctl} (h : (sNH ms lab J0 .st).J σ c) :
    ∃ (q : AGB ms lab) (o : Nat), (∃ σ, J0 σ q.1.c0) ∧ ms.lo o ∧ o + ms.units 1 q.1.τ ≤ ms.cells ∧
      σ.slot (-104) = BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) := by
  obtain ⟨q, o, ⟨σe, hJe, -⟩, -, -, -, hsl, hle, hlo'⟩ := h
  exact ⟨q, o.toNat, ⟨σe, hJe⟩, hlo', hle, BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, ← hsl, Nat.mod_eq_of_lt (BitVec.isLt _)])⟩

/-! ## Off the clone -/

/-- The clone's pc in `[.sp4, .stack_grow)`, below `2 ^ 64`. -/
theorem clone_inCvH :
    ((codeOf lo SccCode.helloProg ".L22_wc_main.sp6").isSome && decide (cvH ".L22_wc_main.sp6" + 100 < 2 ^ 64) &&
    inCvH ".L22_wc_main.sp4" ".L22_wc_main.stack_grow" (cvH ".L22_wc_main.sp6" + 100)) = true := by
  unfold inCvH cvH; rw [← codeT_eq]; decide +kernel

/-- **A free pc is not the clone's** (`ownGH`'s `[.sp4, .stack_grow)` range
contains it): with `freeAt_pc`, every pc of this file's blocks is off `clonePc`. -/
theorem ne_clonePc_of_freeNH {L : RuntimeLayout}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {x : Nat} (h : freeNH x = true) :
    x ≠ Spike.Lib.HelloPreA.clonePcH L := by
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, hin⟩ := hc
  have e : Spike.Lib.HelloPreA.clonePcH L = cvH ".L22_wc_main.sp6" + 100 := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    have ey : cvH ".L22_wc_main.sp6" = y := by simp [cvH, hy]
    rw [ey] at hb ⊢
    show (L.lab (".L22_wc_main" ++ ".sp6") + Int64.ofNat (4 * 25)).toBitVec.toNat = y + 100
    rw [show (".L22_wc_main" ++ ".sp6" : String) = ".L22_wc_main.sp6" from rfl, hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 100).toNat = y + 100
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [e]; intro hx
  unfold freeNH at h
  rw [hx, hin] at h
  simp only [Bool.not_true, Bool.false_and, Bool.and_false] at h
  cases h

section Inst

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`wc_main`'s entry block inside `SFactsSt2` at `ownGH`.** -/
theorem eW_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wNH L.lab J0 J1 .e) wcEH :=
  blkW_wcGH hp hlo hΛ hlab a hsite (l := ".L22_wc_main.0_entry") (k := 0)
    (by have := hello_wcEInH; simp only [wcEInH, Bool.and_eq_true] at this; exact this.1)
    (Int64.add_zero _) wcEH_ok hR hal hRlo hhi (by decide) (by decide) (by free_decH)
    (fun σ c _ => by
      show freeNH (Spike.Lib.A64.Flow.arun L.lab wcEH ⟨_, ⟨-144, []⟩, σ⟩).pc.toBitVec.toNat = true
      rw [wcEH_run]
      exact freeAt_labH hlab (by free_decH))

/-- **`.sp0`'s block inside `SFactsSt2` at `ownGH`.** -/
theorem sp0bW_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (sNH ms L.lab J0 .b) wcS0H :=
  blkW_wcGH hp hlo hΛ hlab a hsite (l := ".L22_wc_main.sp0") (k := 0)
    (by have := hello_wcS0InH; simp only [wcS0InH, Bool.and_eq_true] at this; exact this.1)
    (Int64.add_zero _) wcS0H_ok hR hal hRlo hhi (by decide) (by decide) (by free_decH)
    (fun σ c _ => by
      show freeNH (Spike.Lib.A64.Flow.arun L.lab wcS0H ⟨_, ⟨-144, []⟩, σ⟩).pc.toBitVec.toNat = true
      rw [wcS0H_run]
      have := freeKH hlab (l := ".L22_wc_main.sp0") (k := 3) (by free_decH)
      rwa [Spike.Lib.A64.Rt.MainU.pc3] at this)

/-- **The fence past the box store inside `SFactsSt2` at `ownGH`.** -/
theorem fenceW_wcGH (a : BitVec 64) {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (rNH ms L.lab J0 S Q .f) := by
  have hin := hello_wcResInH
  simp only [wcResInH, Bool.and_eq_true] at hin
  obtain ⟨⟨h4, -⟩, -⟩ := hin
  rw [pubF_eq] at h4
  have hf := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab (wcW_factH hΛ (f := .step ".L22_wc_main.sp0" 4) (by decide))
  refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
    (nodeW_dmb_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
    (lbl := fun _ => none) (by rw [hp]; exact h4) rfl rfl c0N_cfacts hf.1 (fun _ _ h => h) hf.2)
    (freeKH hlab (by free_decH)) ?_ ?_
  · have := freeKH hlab (l := ".L22_wc_main.sp0") (k := 5) (by free_decH)
    rwa [ofNat4_succ] at this
  · rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := cell1H hp h4 h1 h2 h4'
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_dmb hc, fun s' hu => ?_⟩
    · cases h
    · obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **The reserve's call block inside `SFactsSt2` at `ownGH`.** -/
theorem resBlW_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (rNH ms L.lab J0 S Q .bl) resBH :=
  blkW_wcGH hp hlo hΛ hlab a hsite (l := ".L22_wc_main.sp0") (k := 5)
    (by have := hello_wcResInH; simp only [wcResInH, Bool.and_eq_true] at this; exact this.1.2)
    rfl resBH_ok hR hal hRlo hhi (by decide) (by decide) (by free_decH)
    (fun σ c _ => by
      show freeNH (Spike.Lib.A64.Flow.arun L.lab resBH ⟨_, ⟨-144, []⟩, σ⟩).pc.toBitVec.toNat = true
      rw [resBH_run]
      exact freeAt_labH hlab (by free_decH))

/-- **The box store inside `SFactsSt2` at `ownGH`**: every cell the
allocator may return, for a `q` whose `c0` some `J0` state carries, has
`BoxOkH` (`hbox`). -/
theorem sp0stW_wcGH (a : BitVec 64) {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ))) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (sNH ms L.lab J0 .st) := by
  have hin := hello_wcS0InH
  simp only [wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨-, h3⟩ := hin
  rw [boxSt_eq] at h3
  have hf := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab (wcW_factH hΛ (f := .step ".L22_wc_main.sp0" 3) (by decide))
  refine NodeW.ofAll (fun σ => σ.slot (-104)) fun A => ?_
  by_cases hA : BoxOkH Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    obtain ⟨q, o, hj, hlo', hle, e⟩ := slot_boxH hJ
    exact absurd (e ▸ hbox q o hj hlo' hle) hA
  obtain ⟨hmw, hun, hno⟩ := hA
  refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
    (Spike.Lib.A64.Rt.nodeW_st_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
      (lbl := fun _ => none) (ownOf := ownH L a) (fun _ => rfl) (by rw [hp]; exact h3) rfl rfl c0N_cfacts hf.1
      (fun _ _ h => h) hf.2 ?_ hmw hun hno) (freeKH hlab (by free_decH)) ?_ ?_
  · rintro σ c ⟨-, c', hJ, rfl⟩
    exact rAddr_boxH hJ
  · have := freeKH hlab (l := ".L22_wc_main.sp0") (k := 4) (by free_decH)
    rwa [ofNat4_succ] at this
  · rintro s c ⟨h1, h2, h3', h4', σ, hAb, hF, hJ, hsA⟩
    have hc := cell1H hp h3 h1 h2 h4'
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 0 = A := by rw [hAb.regs, rAddr_boxH hJ, hsA]
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_str hc ha' (hun _ hF), fun s' hu => ?_⟩
    · cases h
    · rw [h3', EvTree.access_empty] at hu
      obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **`wc_main`'s prologue inside `SFactsSt2` at `ownGH`**: the thread
pointer `tp` at every entry state (`htp`), its limit word mapped for
reading (`hmr`) and unmapped in private memory under `F` (`hun`). -/
theorem proW_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none) :
    Spike.Lib.A64.Flow.ProW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms (L.lab "wc_main") 144 8 ".L22_wc_main.stack_grow"
      [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)] J0 := by
  have h := Spike.Lib.A64.Flow.HelloWc.hello_wcPro
  simp only [Spike.Lib.A64.Flow.HelloWc.hWcPro, Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".L22_wc_main.stack_check" = L.lab "wc_main" + Int64.ofNat (4 * 0) :=
    Scc.Cert.Rt.A64.label_labelGap L.lays (by rw [hp]; exact hgap)
  rw [ofNat4_zero] at esc
  have f2 := freeKH hlab (l := ".L22_wc_main.stack_check") (k := 2) (by free_decH)
  have f3 := freeKH hlab (l := ".L22_wc_main.stack_check") (k := 3) (by free_decH)
  have f5 := freeKH hlab (l := ".L22_wc_main.stack_check") (k := 5) (by free_decH)
  have f14 := freeKH hlab (l := ".L22_wc_main.stack_check") (k := 14) (by free_decH)
  rw [Spike.Lib.A64.Rt.MainU.pc2, esc] at f2
  rw [Spike.Lib.A64.Rt.MainU.pc3, esc] at f3
  rw [Spike.Lib.A64.Rt.MainU.pc5, esc] at f5
  rw [esc, show ∀ x : Int64, x + Int64.ofNat (4 * 14) = x + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + Int64.ofNat (4 * 5)
    from fun x => by simp only [Int64.add_assoc]; rfl] at f14
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact blkW_wcGH hp hlo hΛ hlab a hsite (l := ".L22_wc_main.stack_check") (k := 0) bHd
      (by rw [ofNat4_zero, esc]) (Spike.Lib.A64.Flow.chkHead_ok (-144) 0 144) hR hal hRlo hhi (by decide)
      (Spike.Lib.A64.Rt.MainU.chkHead_noRet 144) (by free_decH) (fun σ c _ => by
        show freeNH (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.chkHead 144) ⟨_, ⟨0, []⟩, σ⟩).pc.toBitVec.toNat
          = true
        rw [Spike.Lib.A64.Flow.chkHead_run]; exact f2)
  · have hf := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab
      (wcW_factH hΛ (f := .step ".L22_wc_main.stack_check" 2) (by decide))
    refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
      (Spike.Lib.A64.Rt.nodeW_ldr_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
        (lbl := fun _ => none) (by rw [hp]; exact bLd) rfl
        (by show L.lab "wc_main" + 4 + 4 = _; rw [Spike.Lib.A64.Rt.MainU.pc2, esc]) c0N_cfacts hf.1
        (fun _ _ h => h) hf.2 ?_ hmr hun) f2 f3 ?_
    · rintro σ c ⟨-, c', σ0, hJ0, rfl⟩
      rw [Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp _ _ hJ0)
    · rintro s c ⟨h1, h2, h3', h4', σ1, hAb, hF, σ0, hJ0, he⟩
      have hc := cell1H hp bLd h1 h2
        (by rw [h4']; show L.lab "wc_main" + 4 + 4 = _; rw [Spike.Lib.A64.Rt.MainU.pc2, esc])
      have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 8 = Spike.Lib.A64.Flow.Ret0.limA tp := by
        rw [hAb.regs, he, Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp _ _ hJ0)
      refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_ldr hc ha' (hun _ hF), fun s' hu => ?_⟩
      · cases h
      · rw [h3', EvTree.access_empty] at hu
        obtain ⟨_, hu⟩ := hu
        simp only [TreeLeaf] at hu
        subst hu; rfl
  · exact blkW_wcGH hp hlo hΛ hlab a hsite (l := ".L22_wc_main.stack_check") (k := 3) bBr
      (by rw [Spike.Lib.A64.Rt.MainU.pc3, esc]; rfl) (Spike.Lib.A64.Flow.chkBr_ok (-144) 0 144 _) hR hal hRlo hhi
      (by decide) (Spike.Lib.A64.Rt.MainU.chkBr_noRet _) (by free_decH) (fun σ c _ => by
        show freeNH (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.chkBr ".L22_wc_main.stack_grow")
          ⟨L.lab "wc_main" + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 144, σ⟩).pc.toBitVec.toNat = true
        rw [(Spike.Lib.A64.Flow.chkBr_run _ _ _ _ _).1]
        split
        · exact f5
        · exact freeAt_labH hlab (by free_decH))
  · exact blkW_wcGH hp hlo hΛ hlab a hsite (l := ".L22_wc_main.stack_check") (k := 5) bFr
      (by rw [Spike.Lib.A64.Rt.MainU.pc5, esc]; rfl)
      (Spike.Lib.A64.Flow.frameSet_ok (lo := -144) (hi := 0) (by decide) (by decide) (by decide) (Int.le_refl _)
        (by decide)) hR hal hRlo hhi (by decide)
      (by simp [Spike.Lib.A64Consumer.noRetBlk, Spike.Lib.A64.Flow.frameSet, Spike.Lib.A64.Flow.frSetup,
        Spike.Lib.A64.Flow.spStr, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly]) (by free_decH)
      (fun σ c _ => by
        show freeNH (Spike.Lib.A64.Flow.arun L.lab
          (Spike.Lib.A64.Flow.frameSet 144 [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)])
          ⟨L.lab "wc_main" + 4 + 4 + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 144, σ⟩).pc.toBitVec.toNat = true
        rw [Spike.Lib.A64.Flow.frameSet_run _ _ _ (by decide)]
        exact f14)

/-- **`WcSp0W` at `SFactsSt2`/`ownGH`**: `.sp0`'s block and the box store. -/
theorem wcSp0W_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ))) :
    WcSp0WH (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 :=
  ⟨sp0bW_wcGH hp hlo hΛ hlab hsite a hR hal hRlo hhi, sp0stW_wcGH hp hlo hΛ hlab hsite a hbox⟩

end Inst

/-- info: 'Spike.Lib.A64.HelloPh.WcW.eW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.eW_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.fenceW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.fenceW_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.resBlW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.resBlW_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.proW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.proW_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.wcSp0W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.wcSp0W_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.ne_clonePc_of_freeNH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.ne_clonePc_of_freeNH

end Spike.Lib.A64.HelloPh.WcW
