/-
**`wc_main`'s obligations before `.x20` inside `SFactsSt2` at `ownG`**
(x86-64; twin of `Spike/Lib/A64WakeWcPreWI.lean`): the `SFactsSt2`
component of the pre-spawn chain's `W` for `WcPreW`'s prologue and entry
block, `WcSp0W` and `WcResW`'s call block. Each is an instance of
`blkW_wcG` or `nodeW_wcG`. The checks (the code, the phase facts, the free
pcs) are decided by the kernel against the certificate's labels, with no
absolute address in this file.

- `nodeW_fsld_pre`: a node at a thread-pointer load `movq %fs:k, %d` before
  the take inside `SFacts`, for any cells.
- `proW_wcG`: the prologue (`XProW`). The limit's load needs the thread
  pointer fixed (`htp`) and its limit word mapped and unmapped (`hmr`,
  `hun`).
- `eW_wcG`: the entry block.
- `BoxOk`, `bAddr_box`, `slot_box`, `sp0bW_wcG`, `sp0stW_wcG`: `.x18`'s
  block and the box store. Every cell the allocator may return must be
  mapped for writing, unmapped in private memory and off the owned words
  (`hbox`).
- `resBlW_wcG`: the reserve's call block.
- `wcSp0W_wcG`: `WcSp0W` from its two parts.

**Where this differs from AArch64**: there is no fence before the reserve's
call (scc's `# fence st` emits no code under TSO, `X64WakeWcRes`), so A64's
`fenceW_wcG` has no twin here (wc_main's one `mfence`, at `.Lwc_main.x21`,
is `WcSp4W`'s, by `nodeW_mfence_pre`); the prologue is x86-64's five-node
`XProW` (A64's four-node `ProW`), its limit load a `%fs` load before the
take (`nodeW_fsld_pre`, this file's: `Rt/X64RtW` has only the after-switch
`nodeW_fsld_postO`; A64's `nodeW_ldr_pre`); offsets are bytes (`freeAt l
os`, `freeBlk`); the box store is one `movq %rax, (%rcx)` at `.x18 + 15`,
its address `bAddr σ.regs .rcx 0` the cell at slot `-24` (A64's `str` at
`[x10]`, slot `-72`); `ne_clonePc_of_freeN` is already
`X64WakeWcClonePc`'s; there is no `hal`; the bounds are x86-64's frame
(`R.lo ≤ -72`, `-240` at the entry block's call, `8 ≤ R.hi` past the
return address).
-/
import Spike.Lib.X64WakeWcPreWN

namespace Spike.Lib.X64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (blockAtB codeT_eq label_labelGapB)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl CFacts SFacts K0)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At arun fsDir bAddr mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok
  xHead_run xLea_run xCmp_run xFr_run xS1 xS2 hdRegs prologueIn ofNat_add' ofNat_zero')
open Spike.Lib.X64.Flow.WakeWc
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr exec_movfs_load_agrees exec_store_agrees)

/-- The kernel's check of a `freeAt` of wakeCells. -/
macro "wcfree_dec" : tactic => `(tactic| (unfold freeAt freeN inCv cv; rw [← codeT_eq]; decide +kernel))

/-- The kernel's check of a `freeBlk` of wakeCells. -/
macro "wcfreeB_dec" : tactic =>
  `(tactic| (unfold freeBlk freeAt freeN inCv cv; rw [← codeT_eq]; decide +kernel))

/-! ## A thread-pointer load inside `SFacts` -/

section Fs

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Spike.Lib.X64Consumer.Own}
  {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout}
  {rS : Range} {lbl : Lbl} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A node at a thread-pointer load `movq %fs:k, %d`** of a mapped word
`a` (`hmr`) unmapped in private memory under the frame condition (`hun`),
before the take, its next pc in its phase. -/
theorem nodeW_fsld_pre {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {d : Reg64}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAtB cells l off [(fsDir d k, z)] = true) (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → σ.regs.fsBase.toBitVec + k.toBitVec = a)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨a, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  Spike.Lib.X64.Rt.nodeW_pre hI hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
    have ha' : fsAddr s z { base := none, idx := none, disp := .int64 k } = a := by
      rw [← ha σ c hJ]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    have hex := exec_movfs_load_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := Spike.Lib.X64Consumer.load_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain)
      (s := s) (z := z) (m := fun v => { s.st.1 with regs := s.st.1.regs.set (.low d .W64) (v.setWidth 64) })
      hmr (fun _ => (Spike.Lib.X64.Rt.next_same hI hpc hph _).2)
      (fun _ => (Spike.Lib.X64.Rt.next_same hI hpc hph _).1)
    exact Spike.Lib.X64Consumer.sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown' htk hO

end Fs

/-! ## The box store's cell -/

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}

/-- **A box cell's facts**: mapped for writing in the loaded kernel state,
unmapped in private memory under `F`, and off the owned words `ownW L a`. -/
def BoxOk (Λ : Scc.Sem.Layout) (L : RuntimeLayout) (a : BitVec 64) (F : MachineData → Prop) (A : BitVec 64) : Prop :=
  Scc.Sem.Kernel.mapped (K0 Λ) true ⟨A, 8⟩ = true ∧ (∀ m, F m → Mem.loadInt m.dmem A 8 = none) ∧
    ∀ j w, (⟨A, 8⟩, w) ∉ ownW L a j

/-- The box store's address `(%rcx)` is the cell at slot `-24`. -/
theorem bAddr_box {ms : Spike.Lib.MemSide isa} {lab : Label → Int64} {R : Spike.Lib.Region}
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {σ : Spike.Lib.X64.AS} {c : Spike.Lib.Ctl} (h : (sN ms lab R J0 .st).J σ c) :
    bAddr σ.regs .rcx 0 = σ.slot (-24) := by
  obtain ⟨_, _, -, -, -, hx, -⟩ := h
  rw [← hx]
  simp [bAddr, Reg64s.get64]

/-- The box store's cell from its node's facts. -/
theorem slot_box {ms : Spike.Lib.MemSide isa} {lab : Label → Int64} {R : Spike.Lib.Region}
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {σ : Spike.Lib.X64.AS} {c : Spike.Lib.Ctl} (h : (sN ms lab R J0 .st).J σ c) :
    ∃ (q : AGB ms lab) (o : Nat), (∃ σ, J0 σ q.1.c0) ∧ ms.lo o ∧ o + ms.units 1 q.1.τ ≤ ms.cells ∧
      σ.slot (-24) = BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) := by
  obtain ⟨q, o, ⟨σe, hJe, -⟩, -, -, -, hsl, hle, hlo'⟩ := h
  exact ⟨q, o.toNat, ⟨σe, hJe⟩, hlo', hle, BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, ← hsl, Nat.mod_eq_of_lt (BitVec.isLt _)])⟩

section Inst

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`wc_main`'s entry block inside `SFactsSt2` at `ownG`.** -/
theorem eW_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi)
    {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wN L.lab R J0 .e) wcE :=
  blkW_wcG hp hlo hΛ hlab a hsite (l := ".Lwc_main.entry") (k := 0)
    (by have := wake_wcEIn; simp only [wcEIn, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) wcE_ok hR hRlo hhi (by decide) (by decide) (by wcfreeB_dec)
    (fun σ c _ => by
      show freeN (arun L.lab wcE ⟨_, oWR, σ⟩).pc.toBitVec.toNat = true
      rw [wcE_run]
      exact freeAt_lab hlab (by wcfree_dec))

/-- **`.x18`'s block inside `SFactsSt2` at `ownG`.** -/
theorem sp0bW_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (sN ms L.lab R J0 .b) wcS0 :=
  blkW_wcG hp hlo hΛ hlab a hsite (l := ".Lwc_main.x18") (k := 0)
    (by have := wake_wcS0In; simp only [wcS0In, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) wcS0_ok hR hRlo hhi (by decide) (by decide) (by wcfreeB_dec)
    (fun σ c _ => by
      show freeN (arun L.lab wcS0 ⟨_, oWR, σ⟩).pc.toBitVec.toNat = true
      rw [wcS0_run]
      exact freeAt_pc hlab (l := ".Lwc_main.x18") (os := [15]) (by wcfree_dec) (List.mem_singleton.mpr rfl))

/-- **The reserve's call block inside `SFactsSt2` at `ownG`.** -/
theorem resBlW_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (rN ms L.lab R J0 Q .bl) resB :=
  blkW_wcG hp hlo hΛ hlab a hsite (l := ".Lwc_main.x18") (k := 18)
    (by have := wake_wcResIn; simp only [wcResIn, Bool.and_eq_true] at this; exact this.1)
    rfl resB_ok hR hRlo hhi (by decide) (by decide) (by wcfreeB_dec)
    (fun σ c _ => by
      show freeN (arun L.lab resB ⟨_, ⟨-64, [(.rbp, 0)]⟩, σ⟩).pc.toBitVec.toNat = true
      rw [resB_run]
      exact freeAt_lab hlab (by wcfree_dec))

/-- **The box store inside `SFactsSt2` at `ownG`**: every cell the
allocator may return, for a `q` whose `c0` some `J0` state carries, has
`BoxOk` (`hbox`). -/
theorem sp0stW_wcG (a : BitVec 64) {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOk Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ))) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (sN ms L.lab R J0 .st) := by
  have hin := wake_wcS0In
  simp only [wcS0In, Bool.and_eq_true] at hin
  obtain ⟨-, h3⟩ := hin
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hb : blockAtB L.prog ".Lwc_main.x18" 15 [(Spike.Lib.X64.stDir .rcx 0 .rax, 3)] = true := by
    rw [hp]; exact h3
  have hf := Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
    (wcW_fact hΛ (f := .step ".Lwc_main.x18" 15 3) (by decide))
  have hfr : freeAt ".Lwc_main.x18" [15, 15 + 3] = true := by wcfree_dec
  have f0 := freeAt_pc hlab hfr (o := 15) (by simp)
  have f3 := freeAt_pc hlab hfr (o := 15 + 3) (by simp)
  rw [ofNat_add'] at f3
  refine NodeW.ofAll (fun σ => σ.slot (-24)) fun A => ?_
  by_cases hA : BoxOk Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    obtain ⟨q, o, hj, hlo', hle, e⟩ := slot_box hJ
    exact absurd (e ▸ hbox q o hj hlo' hle) hA
  obtain ⟨hmw, hun, hno⟩ := hA
  refine nodeW_wcG (TkW := fun _ => False) (rS := rS) hlab hsite
    (Spike.Lib.X64.Rt.nodeW_st_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) (ownOf := ownW L a)
      (fun _ => rfl) hb rfl rfl c0N_cfacts hf.1 (fun _ _ h => h) hf.2 ?_ hmw hun hno) f0 f3 ?_
  · rintro σ c ⟨-, c', hJ, rfl⟩
    exact bAddr_box hJ
  · rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, hJ, hsA⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb rfl h1 h2 h4'
    have ha' : eaddr s 3 (mB .rcx 0) = A :=
      (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs, ← hsA]; exact bAddr_box hJ)
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_store_agrees hc ha' (hun _ hF) (agrees_of_decls h3' _ _),
      fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl

/-- **`wc_main`'s prologue inside `SFactsSt2` at `ownG`**: the thread
pointer `tp` at every entry state (`htp`), its limit word mapped for
reading (`hmr`) and unmapped in private memory under `F` (`hun`). -/
theorem proW_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms (L.lab "wc_main") 64 8 ".Lwc_main.stk" 5 9 3 6 4 [(.rdi, -8, 4)] J0 := by
  have h := wake_wcPro
  simp only [wcPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have esc : L.lab ".Lwc_main.chk" = L.lab "wc_main" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "wc_main" + 1 + 3 = L.lab ".Lwc_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 = L.lab ".Lwc_main.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e23 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6 =
      L.lab ".Lwc_main.chk" + Int64.ofNat 23 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hfr : freeAt ".Lwc_main.chk" [0, 5, 5 + 9, 23, 31] = true := by wcfree_dec
  have f0 := freeAt_pc hlab hfr (o := 0) (by simp)
  have f5 := freeAt_pc hlab hfr (o := 5) (by simp)
  have f14 := freeAt_pc hlab hfr (o := 5 + 9) (by simp)
  have f23 := freeAt_pc hlab hfr (o := 23) (by simp)
  have f31 := freeAt_pc hlab hfr (o := 31) (by simp)
  rw [ofNat_zero'] at f0
  have hxs : (xS2 64 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_wcG hp hlo hΛ hlab a hsite (l := "wc_main") (k := 0) bHd (ofNat_zero' _)
      (xHead_ok (lo := -72) (hi := 0) (by decide) (Int.le_refl _)) hR hRlo hhi (by decide) xHead_noRet
      (by wcfreeB_dec) (fun σ c _ => by
        show freeN (arun L.lab xHead ⟨L.lab "wc_main", ⟨0, []⟩, σ⟩).pc.toBitVec.toNat = true
        rw [xHead_run]
        show freeN (L.lab "wc_main" + 1 + 3).toBitVec.toNat = true
        rw [h4]; exact f0)
  · exact blkW_wcG hp hlo hΛ hlab a hsite (l := ".Lwc_main.chk") (k := 0) bLea
      (by show _ = L.lab "wc_main" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -72) (hi := 0) _ _) hR hRlo hhi (by decide) (xLea_noRet _ _) (by wcfreeB_dec)
      (fun σ c _ => by
        show freeN (arun L.lab (xLea 64 5) ⟨L.lab "wc_main" + 1 + 3, Spike.Lib.X64.Flow.oH, σ⟩).pc.toBitVec.toNat
          = true
        rw [xLea_run (Z := 64) _ _ _ (by decide)]
        show freeN (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat = true
        rw [h4]; exact f5)
  · have hf := Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
      (wcW_fact hΛ (f := .step ".Lwc_main.chk" 5 9) (by decide))
    have hbL : blockAtB L.prog ".Lwc_main.chk" 5 [(fsDir .r11 8, 9)] = true := by rw [hp]; exact bLd
    refine nodeW_wcG (TkW := fun _ => False) (rS := rS) hlab hsite
      (nodeW_fsld_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) hbL rfl
        (by show L.lab "wc_main" + 1 + 3 + _ = _; rw [h4]) c0N_cfacts hf.1 (fun _ _ h => h) hf.2 ?_ hmr hun)
      (by show freeN (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat = true; rw [h4]; exact f5)
      (by show freeN (L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat = true
          rw [e14]; exact f14) ?_
    · rintro σ c ⟨-, c', σ0, hJ0, rfl⟩
      rw [congrFun hxs σ0, htp _ _ hJ0]; rfl
    · rintro s c ⟨h1, h2, h3', h4', σ2, hA, hF, σ0, hJ0, rfl⟩
      have hc := Spike.Lib.X64.Rt.cellOf hI hbL rfl h1 h2
        (by rw [h4']; show L.lab "wc_main" + 1 + 3 + _ = _; rw [h4])
      have ha' : fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp := by
        rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 64 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
          rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
        simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
      refine ⟨_, _, hc, fun w w' h => (by cases h),
        exec_movfs_load_agrees hc ha' (hun _ hF) (agrees_of_decls h3' _ _), fun s' hu => ?_⟩
      simp only [TreeLeaf] at hu
      obtain ⟨_, rfl⟩ := hu; rfl
  · exact blkW_wcG hp hlo hΛ hlab a hsite (l := ".Lwc_main.chk") (k := 14) bCmp
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -72) (hi := 0) _ _ _ _) hR hRlo hhi (by decide) (xCmp_noRet _ _ _) (by wcfreeB_dec)
      (fun σ c _ => by
        show freeN (arun L.lab (xCmp ".Lwc_main.stk" 3 6)
          ⟨L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9, Spike.Lib.X64.Flow.oL 64, σ⟩).pc.toBitVec.toNat
          = true
        rw [(xCmp_run _ _ _ _ _ _ _).1]
        split
        · rw [e23]; exact f23
        · exact freeAt_lab hlab (by wcfree_dec))
  · exact blkW_wcG hp hlo hΛ hlab a hsite (l := ".Lwc_main.chk") (k := 23) bFr
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _ + _ + _; rw [e23])
      (xFr_ok (lo := -72) (hi := 0) _ _ _ (by decide)) hR hRlo hhi (by decide) (xFr_noRet _ _ _)
      (by wcfreeB_dec) (fun σ c _ => by
        show freeN (arun L.lab (xFr 64 4 [(.rdi, -8, 4)])
          ⟨L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6,
            Spike.Lib.X64.Flow.oL 64, σ⟩).pc.toBitVec.toNat = true
        rw [(xFr_run _ _ _ _ _ _).1, e23, ← ofNat_add', ← ofNat_add']
        exact f31)

/-- **`WcSp0W` at `SFactsSt2`/`ownG`**: `.x18`'s block and the box store. -/
theorem wcSp0W_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOk Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ))) :
    WcSp0W (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 :=
  ⟨sp0bW_wcG hp hlo hΛ hlab hsite a hR hRlo hhi, sp0stW_wcG hp hlo hΛ hlab hsite a hbox⟩

end Inst

end Spike.Lib.X64.WakePh.WcW

/-- info: 'Spike.Lib.X64.WakePh.WcW.nodeW_fsld_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.nodeW_fsld_pre

/-- info: 'Spike.Lib.X64.WakePh.WcW.eW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.eW_wcG

/-- info: 'Spike.Lib.X64.WakePh.WcW.sp0bW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.sp0bW_wcG

/-- info: 'Spike.Lib.X64.WakePh.WcW.resBlW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.resBlW_wcG

/-- info: 'Spike.Lib.X64.WakePh.WcW.sp0stW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.sp0stW_wcG

/-- info: 'Spike.Lib.X64.WakePh.WcW.proW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.proW_wcG

/-- info: 'Spike.Lib.X64.WakePh.WcW.wcSp0W_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.wcSp0W_wcG
