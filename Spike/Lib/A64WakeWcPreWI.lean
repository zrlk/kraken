/-
**`wc_main`'s obligations before `.sp4` inside `SFactsSt2` at `ownG`**
(AArch64): the `SFactsSt2` component of the pre-spawn chain's `W`
for `WcPreW`'s prologue and entry block, `WcSp0W` and `WcResW`'s fence and
call block. Each is an instance of `blkW_wcG` or `nodeW_wcG`. The checks
(the code, the phase facts, the free pcs) are decided by the kernel against
the certificate's labels, with no absolute address in this file.

- `proW_wcG`: the prologue (`ProW`). The limit's load needs the thread
  pointer fixed (`htp`) and its limit word mapped and unmapped (`hmr`,
  `hun`).
- `eW_wcG`: the entry block.
- `BoxOk`, `sp0W_wcG`: `.sp0`'s block and the box store. Every cell the
  allocator may return must be mapped for writing, unmapped in private
  memory and off the owned words (`hbox`).
- `fenceW_wcG`, `resBlW_wcG`: the fence and the reserve's call block.
- `wcSp0W_wcG`: `WcSp0W` from its two parts.
- `ne_clonePc_of_freeN`: a free pc is not the clone's.
-/
import Spike.Lib.A64WakeWcPreWN
import Spike.Lib.A64WakeWcInv

namespace Spike.Lib.A64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk blockAt pcAt)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl CFacts SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ofNat4_zero ofNat4_succ)
open Spike.Lib.A64.Flow.WakeWc
open Kraken.Promising.Lower.A64 (CellAt after)

/-- The kernel's check of a `freeAt`. -/
macro "free_dec" : tactic => `(tactic| (unfold freeAt freeN inCv cv; rw [← codeT_eq]; decide +kernel))

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}

/-- **A free pc `4 k` past a label**, from `freeAt l k 1`. -/
theorem freeK (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {l : Label} {k : Nat}
    (h : freeAt l k 1 = true) : freeN (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true :=
  freeAt_pc0 hlab h

/-- **A one-instruction block's cell** at a state of `L`'s executable at its pc. -/
theorem cell1 (hp : L.prog = wakeProg) {l : Label} {k : Nat} {d : Directive} (hb : blockAt wakeProg l k [d] = true)
    {s : State} (h1 : s.exe = L.exe) (h2 : s.endPc = L.endPc) (hpc : s.st.2 = L.lab l + Int64.ofNat (4 * k)) :
    CellAt s d 4 :=
  (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) rfl s h1 h2).cell (j := 0) rfl rfl rfl
    (by rw [hpc, ofNat4_zero])

/-- **A box cell's facts**: mapped for writing in the loaded kernel state,
unmapped in private memory under `F`, and off the owned words `ownW L a`. -/
def BoxOk (Λ : Scc.Sem.Layout) (L : RuntimeLayout) (a : BitVec 64) (F : MachineData → Prop) (A : BitVec 64) : Prop :=
  Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨A, 8⟩ = true ∧ (∀ m, F m → Mem.loadInt m.dmem A 8 = none) ∧
    ∀ j w, (⟨A, 8⟩, w) ∉ ownW L a j

/-- The box store's address is the cell at `[sp, #8]`. -/
theorem rAddr_box {ms : Spike.Lib.MemSide isaLSE2} {lab : Label → Int64}
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {σ : Spike.Lib.A64.Flow.AS} {c : Spike.Lib.Ctl} (h : (sN ms lab J0 .st).J σ c) :
    Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 = σ.slot (-72) := by
  obtain ⟨_, _, -, -, -, hx, -⟩ := h
  simp [Spike.Lib.A64.Flow.rAddr, Reg64s.getXReg, hx]

/-- The box store's cell from its node's facts. -/
theorem slot_box {ms : Spike.Lib.MemSide isaLSE2} {lab : Label → Int64}
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {σ : Spike.Lib.A64.Flow.AS} {c : Spike.Lib.Ctl} (h : (sN ms lab J0 .st).J σ c) :
    ∃ (q : AGB ms lab) (o : Nat), (∃ σ, J0 σ q.1.c0) ∧ ms.lo o ∧ o + ms.units 1 q.1.τ ≤ ms.cells ∧
      σ.slot (-72) = BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) := by
  obtain ⟨q, o, ⟨σe, hJe, -⟩, -, -, -, hsl, hle, hlo'⟩ := h
  exact ⟨q, o.toNat, ⟨σe, hJe⟩, hlo', hle, BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, ← hsl, Nat.mod_eq_of_lt (BitVec.isLt _)])⟩

/-! ## Off the clone -/

/-- The clone's pc in `[.sp4, .stack_grow)`, below `2 ^ 64`. -/
theorem clone_inCv :
    ((codeOf lo wakeProg ".L21_wc_main.sp6").isSome && decide (cv ".L21_wc_main.sp6" + 52 < 2 ^ 64) &&
    inCv ".L21_wc_main.sp4" ".L21_wc_main.stack_grow" (cv ".L21_wc_main.sp6" + 52)) = true := by
  unfold inCv cv; rw [← codeT_eq]; decide +kernel

/-- **A free pc is not the clone's** (`ownG`'s `[.sp4, .stack_grow)` range
contains it): with `freeAt_pc`, every pc of this file's blocks is off `clonePc`. -/
theorem ne_clonePc_of_freeN {L : RuntimeLayout}
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {x : Nat} (h : freeN x = true) :
    x ≠ clonePc L := by
  have hc := clone_inCv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, hin⟩ := hc
  have e : clonePc L = cv ".L21_wc_main.sp6" + 52 := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    have ey : cv ".L21_wc_main.sp6" = y := by simp [cv, hy]
    rw [ey] at hb ⊢
    show (L.lab (".L21_wc_main" ++ ".sp6") + Int64.ofNat (4 * 13)).toBitVec.toNat = y + 52
    rw [show (".L21_wc_main" ++ ".sp6" : String) = ".L21_wc_main.sp6" from rfl, hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 52).toNat = y + 52
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [e]; intro hx
  unfold freeN at h
  rw [hx, hin] at h
  simp only [Bool.not_true, Bool.false_and, Bool.and_false] at h
  cases h

section Inst

variable (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`wc_main`'s entry block inside `SFactsSt2` at `ownG`.** -/
theorem eW_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi)
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wN L.lab J0 .e) wcE :=
  blkW_wcG hp hlo hΛ hlab a hsite (l := ".L21_wc_main.0_entry") (k := 0)
    (by have := wake_wcEIn; simp only [wcEIn, Bool.and_eq_true] at this; exact this.1)
    (Int64.add_zero _) wcE_ok hR hal hRlo hhi (by decide) (by decide) (by free_dec)
    (fun σ c _ => by
      show freeN (Spike.Lib.A64.Flow.arun L.lab wcE ⟨_, ⟨-80, []⟩, σ⟩).pc.toBitVec.toNat = true
      rw [wcE_run]
      exact freeAt_lab hlab (by free_dec))

/-- **`.sp0`'s block inside `SFactsSt2` at `ownG`.** -/
theorem sp0bW_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (sN ms L.lab J0 .b) wcS0 :=
  blkW_wcG hp hlo hΛ hlab a hsite (l := ".L21_wc_main.sp0") (k := 0)
    (by have := wake_wcS0In; simp only [wcS0In, Bool.and_eq_true] at this; exact this.1)
    (Int64.add_zero _) wcS0_ok hR hal hRlo hhi (by decide) (by decide) (by free_dec)
    (fun σ c _ => by
      show freeN (Spike.Lib.A64.Flow.arun L.lab wcS0 ⟨_, ⟨-80, []⟩, σ⟩).pc.toBitVec.toNat = true
      rw [wcS0_run]
      have := freeK hlab (l := ".L21_wc_main.sp0") (k := 3) (by free_dec)
      rwa [Spike.Lib.A64.Rt.MainU.pc3] at this)

/-- **The fence past the box store inside `SFactsSt2` at `ownG`.** -/
theorem fenceW_wcG (a : BitVec 64) {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (rNQ ms L.lab J0 S Q .f) := by
  have hin := wake_wcResIn
  simp only [wcResIn, Bool.and_eq_true] at hin
  obtain ⟨⟨h4, -⟩, -⟩ := hin
  rw [pubF_eq] at h4
  have hf := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab (wcW_fact hΛ (f := .step ".L21_wc_main.sp0" 4) (by decide))
  refine nodeW_wcG (TkW := fun _ => False) (rS := rS) hlab hsite
    (nodeW_dmb_pre (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
    (lbl := fun _ => none) (by rw [hp]; exact h4) rfl rfl c0N_cfacts hf.1 (fun _ _ h => h) hf.2)
    (freeK hlab (by free_dec)) ?_ ?_
  · have := freeK hlab (l := ".L21_wc_main.sp0") (k := 5) (by free_dec)
    rwa [ofNat4_succ] at this
  · rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := cell1 hp h4 h1 h2 h4'
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_dmb hc, fun s' hu => ?_⟩
    · cases h
    · obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **The reserve's call block inside `SFactsSt2` at `ownG`.** -/
theorem resBlW_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    {S : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (rN ms L.lab J0 S .bl) resB :=
  blkW_wcG hp hlo hΛ hlab a hsite (l := ".L21_wc_main.sp0") (k := 5)
    (by have := wake_wcResIn; simp only [wcResIn, Bool.and_eq_true] at this; exact this.1.2)
    rfl resB_ok hR hal hRlo hhi (by decide) (by decide) (by free_dec)
    (fun σ c _ => by
      show freeN (Spike.Lib.A64.Flow.arun L.lab resB ⟨_, ⟨-80, []⟩, σ⟩).pc.toBitVec.toNat = true
      rw [resB_run]
      exact freeAt_lab hlab (by free_dec))

/-- **The box store inside `SFactsSt2` at `ownG`**: every cell the
allocator may return, for a `q` whose `c0` some `J0` state carries, has
`BoxOk` (`hbox`). -/
theorem sp0stW_wcG (a : BitVec 64) {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOk Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ))) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (sN ms L.lab J0 .st) := by
  have hin := wake_wcS0In
  simp only [wcS0In, Bool.and_eq_true] at hin
  obtain ⟨-, h3⟩ := hin
  rw [boxSt_eq] at h3
  have hf := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab (wcW_fact hΛ (f := .step ".L21_wc_main.sp0" 3) (by decide))
  refine NodeW.ofAll (fun σ => σ.slot (-72)) fun A => ?_
  by_cases hA : BoxOk Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    obtain ⟨q, o, hj, hlo', hle, e⟩ := slot_box hJ
    exact absurd (e ▸ hbox q o hj hlo' hle) hA
  obtain ⟨hmw, hun, hno⟩ := hA
  refine nodeW_wcG (TkW := fun _ => False) (rS := rS) hlab hsite
    (Spike.Lib.A64.Rt.nodeW_st_pre (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
      (lbl := fun _ => none) (ownOf := ownW L a) (fun _ => rfl) (by rw [hp]; exact h3) rfl rfl c0N_cfacts hf.1
      (fun _ _ h => h) hf.2 ?_ hmw hun hno) (freeK hlab (by free_dec)) ?_ ?_
  · rintro σ c ⟨-, c', hJ, rfl⟩
    exact rAddr_box hJ
  · have := freeK hlab (l := ".L21_wc_main.sp0") (k := 4) (by free_dec)
    rwa [ofNat4_succ] at this
  · rintro s c ⟨h1, h2, h3', h4', σ, hAb, hF, hJ, hsA⟩
    have hc := cell1 hp h3 h1 h2 h4'
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 0 = A := by rw [hAb.regs, rAddr_box hJ, hsA]
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_str hc ha' (hun _ hF), fun s' hu => ?_⟩
    · cases h
    · rw [h3', EvTree.access_empty] at hu
      obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **`wc_main`'s prologue inside `SFactsSt2` at `ownG`**: the thread
pointer `tp` at every entry state (`htp`), its limit word mapped for
reading (`hmr`) and unmapped in private memory under `F` (`hun`). -/
theorem proW_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none) :
    Spike.Lib.A64.Flow.ProW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms (L.lab "wc_main") 80 8 ".L21_wc_main.stack_grow"
      [(.X0, 0)] J0 := by
  have h := wake_wcPro
  simp only [wcPro, Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".L21_wc_main.stack_check" = L.lab "wc_main" + Int64.ofNat (4 * 0) :=
    Scc.Cert.Rt.A64.label_labelGap L.lays (by rw [hp]; exact hgap)
  rw [ofNat4_zero] at esc
  have f2 := freeK hlab (l := ".L21_wc_main.stack_check") (k := 2) (by free_dec)
  have f3 := freeK hlab (l := ".L21_wc_main.stack_check") (k := 3) (by free_dec)
  have f5 := freeK hlab (l := ".L21_wc_main.stack_check") (k := 5) (by free_dec)
  have f10 := freeK hlab (l := ".L21_wc_main.stack_check") (k := 10) (by free_dec)
  rw [Spike.Lib.A64.Rt.MainU.pc2, esc] at f2
  rw [Spike.Lib.A64.Rt.MainU.pc3, esc] at f3
  rw [Spike.Lib.A64.Rt.MainU.pc5, esc] at f5
  rw [esc, show ∀ x : Int64, x + Int64.ofNat (4 * 10) = x + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + Int64.ofNat (4 * 1)
    from fun x => by simp only [Int64.add_assoc]; rfl] at f10
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact blkW_wcG hp hlo hΛ hlab a hsite (l := ".L21_wc_main.stack_check") (k := 0) bHd
      (by rw [ofNat4_zero, esc]) (Spike.Lib.A64.Flow.chkHead_ok (-80) 0 80) hR hal hRlo hhi (by decide)
      (Spike.Lib.A64.Rt.MainU.chkHead_noRet 80) (by free_dec) (fun σ c _ => by
        show freeN (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.chkHead 80) ⟨_, ⟨0, []⟩, σ⟩).pc.toBitVec.toNat
          = true
        rw [Spike.Lib.A64.Flow.chkHead_run]; exact f2)
  · have hf := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab
      (wcW_fact hΛ (f := .step ".L21_wc_main.stack_check" 2) (by decide))
    refine nodeW_wcG (TkW := fun _ => False) (rS := rS) hlab hsite
      (Spike.Lib.A64.Rt.nodeW_ldr_pre (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
        (lbl := fun _ => none) (by rw [hp]; exact bLd) rfl
        (by show L.lab "wc_main" + 4 + 4 = _; rw [Spike.Lib.A64.Rt.MainU.pc2, esc]) c0N_cfacts hf.1
        (fun _ _ h => h) hf.2 ?_ hmr hun) f2 f3 ?_
    · rintro σ c ⟨-, c', σ0, hJ0, rfl⟩
      rw [Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp _ _ hJ0)
    · rintro s c ⟨h1, h2, h3', h4', σ1, hAb, hF, σ0, hJ0, he⟩
      have hc := cell1 hp bLd h1 h2
        (by rw [h4']; show L.lab "wc_main" + 4 + 4 = _; rw [Spike.Lib.A64.Rt.MainU.pc2, esc])
      have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 8 = Spike.Lib.A64.Flow.Ret0.limA tp := by
        rw [hAb.regs, he, Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp _ _ hJ0)
      refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_ldr hc ha' (hun _ hF), fun s' hu => ?_⟩
      · cases h
      · rw [h3', EvTree.access_empty] at hu
        obtain ⟨_, hu⟩ := hu
        simp only [TreeLeaf] at hu
        subst hu; rfl
  · exact blkW_wcG hp hlo hΛ hlab a hsite (l := ".L21_wc_main.stack_check") (k := 3) bBr
      (by rw [Spike.Lib.A64.Rt.MainU.pc3, esc]; rfl) (Spike.Lib.A64.Flow.chkBr_ok (-80) 0 80 _) hR hal hRlo hhi
      (by decide) (Spike.Lib.A64.Rt.MainU.chkBr_noRet _) (by free_dec) (fun σ c _ => by
        show freeN (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.chkBr ".L21_wc_main.stack_grow")
          ⟨L.lab "wc_main" + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 80, σ⟩).pc.toBitVec.toNat = true
        rw [(Spike.Lib.A64.Flow.chkBr_run _ _ _ _ _).1]
        split
        · exact f5
        · exact freeAt_lab hlab (by free_dec))
  · exact blkW_wcG hp hlo hΛ hlab a hsite (l := ".L21_wc_main.stack_check") (k := 5) bFr
      (by rw [Spike.Lib.A64.Rt.MainU.pc5, esc]; rfl)
      (Spike.Lib.A64.Flow.frameSet_ok (lo := -80) (hi := 0) (by decide) (by decide) (by decide) (Int.le_refl _)
        (by decide)) hR hal hRlo hhi (by decide)
      (by simp [Spike.Lib.A64Consumer.noRetBlk, Spike.Lib.A64.Flow.frameSet, Spike.Lib.A64.Flow.frSetup,
        Spike.Lib.A64.Flow.spStr, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly]) (by free_dec)
      (fun σ c _ => by
        show freeN (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.frameSet 80 [(.X0, 0)])
          ⟨L.lab "wc_main" + 4 + 4 + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 80, σ⟩).pc.toBitVec.toNat = true
        rw [Spike.Lib.A64.Flow.frameSet_run _ _ _ (by decide)]
        exact f10)

/-- **`WcSp0W` at `SFactsSt2`/`ownG`**: `.sp0`'s block and the box store. -/
theorem wcSp0W_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOk Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ))) :
    WcSp0W (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 :=
  ⟨sp0bW_wcG hp hlo hΛ hlab hsite a hR hal hRlo hhi, sp0stW_wcG hp hlo hΛ hlab hsite a hbox⟩

end Inst

/-- info: 'Spike.Lib.A64.WakePh.WcW.eW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.eW_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcW.sp0bW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.sp0bW_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcW.fenceW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.fenceW_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcW.resBlW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.resBlW_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcW.sp0stW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.sp0stW_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcW.proW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.proW_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcW.wcSp0W_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.wcSp0W_wcG

end Spike.Lib.A64.WakePh.WcW

/-- info: 'Spike.Lib.A64.WakePh.WcW.ne_clonePc_of_freeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.ne_clonePc_of_freeN
