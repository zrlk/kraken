/-
**wake.w's `wc_main` up to the allocator's return** (AArch64, the
pre-spawn consumer), inside `W`, in any valid layout of
`wakeProg` (`Spike/Lib/A64WakeCode.lean`), from checks decided once on the
program (`decide +kernel`). The wake twin of `hello1_rodata_pre_segW`
(`Spike/Lib/A64Hello1Rodata.lean`).

- `wake_alloc`: the allocator's code in `wakeProg` (`allocIn`);
- `wcPro`, `wake_wcPro`: `wc_main`'s stack-checked prologue (frame 80, the
  limit at `[tpidr_el0, #8]`, `x0`, main's `ThreadId`, at the frame's base);
- `wcE`, `wcEIn`, `wake_wcEIn`: `.0_entry` (the allocation's arguments, the
  call), `.sp0` right after it;
- `wcJ`, `wN`, `wX`, `wAR`, `WcCtx`, `WcPreW`: `wc_main`'s frame record and
  saved `ThreadId`, its nodes and exits up to the allocator's return, the
  allocator's region and call context, `wc_main`'s states inside `W`;
- `AGB`, `seg_allocB_ofW`: the allocator's ghost at a box allocation and
  its segment from the code's checks (`Alloc.seg_allocBW_at`);
- `wake_wc_pre_segW`: the segment from `wc_main`'s entry to the allocator's
  return at `.sp0` or its heap abort. The source is at a box allocation of
  one object of two units with header `256` (`hq`: wake.w's
  `let o = new z`, `Call.OKB`); the allocator's return keeps the hold, the
  source's `new` being the box's store at `.sp0` (`Out.newStore`).
-/
import Spike.Lib.A64WakeMain
import Spike.Lib.A64Hello1Rodata
import Spike.Lib.A64AllocBox

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.A64.Flow.Hello1 (AG)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

theorem wake_alloc : allocIn SccCode.wakeProg = true := by decide +kernel

/-- `wc_main`'s prologue: frame 80, `x0` (main's `ThreadId`) at 0. -/
abbrev wcPro : Bool := prologueIn SccCode.wakeProg "wc_main" ".L21_wc_main.stack_check" ".L21_wc_main.0_entry"
  80 8 ".L21_wc_main.stack_grow" [(.X0, 0)]

theorem wake_wcPro : wcPro = true := by decide +kernel

/-- `wc_main`'s `.0_entry` block: the allocation's arguments, the call. -/
def wcE : List Directive := parseAArch64("movz x0, #256
movz x1, #1
movz x2, #2
bl scc_rt_alloc")

block_spec wcE (-240) 0 (⟨-80, []⟩ : SO) wcE

/-- **`wc_main`'s entry block in `prog`**, `.sp0` right after the call. -/
def wcEIn (prog : List Directive) : Bool :=
  blockAt prog ".L21_wc_main.0_entry" 0 wcE && labelGap prog ".L21_wc_main.0_entry" ".L21_wc_main.sp0" 4

theorem wake_wcEIn : wcEIn SccCode.wakeProg = true := by decide +kernel

/-! ## The allocator at a box allocation -/

/-- The allocator's ghost at a box allocation: a call with its premises. -/
abbrev AGB (ms : MemSide isaLSE2) (lab : Label → Int64) : Type := {q : Call // q.OKB ms lab}

section AllocB

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {q : Call}

/-- **`scc_rt_alloc` at a box allocation is one segment inside `W`** in any
valid layout `exe` of a program `prog` with `allocIn prog = true`:
`Alloc.seg_allocBW_at` with its code from the checks (`seg_alloc_ofW`'s
box twin). -/
theorem seg_allocB_ofW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OKB ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hW : AllocW ms q W K exe endPc R F) :
    SegW W K p lbl ms (At exe endPc R F (Alloc.N (_root_.Executable.labels exe).label ms q .e))
      (fun s c => ∃ x, At exe endPc R F (Alloc.EB (_root_.Executable.labels exe).label ms q x) s c) := by
  have hcode := Spike.Lib.A64.Flow.alloc_code (ms := ms) (q := q) hp hend hprog
  simp only [allocIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap⟩ := hprog
  exact Alloc.seg_allocBW_at hF hR hal hlo hhi hq hcode
    (by rw [label_labelGap hp hgap]; simp only [Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
    hmem hW .e

end AllocB

/-! ## Nodes -/

/-- **`wc_main`'s frame** as some entry state of `J0` left it: the record
and the saved `x0` (main's `ThreadId`). -/
def wcJ (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J0 σe c ∧ σ.slot (-16) = σe.regs.X29.toBitVec ∧ σ.slot (-8) = σe.regs.X30.toBitVec ∧
    σ.slot (-80) = σe.regs.X0.toBitVec

/-- `wc_main`'s nodes up to the call. -/
inductive WN where
  | e | call

/-- `wc_main`'s exits up to the allocator's return. -/
inductive WX where
  | sp0 | abort

section Wc

variable (ms : MemSide isaLSE2) (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat)
  (J0 : AS → Ctl → Prop)

/-- **The nodes**: `.0_entry` and the allocator's entry with its arguments. -/
def wN : WN → ND
  | .e => ⟨lab ".L21_wc_main.0_entry", ⟨-80, []⟩, wcJ J0⟩
  | .call => ⟨lab "scc_rt_alloc", ⟨-80, []⟩, fun σ c => wcJ J0 σ c ∧ σ.regs.X0.toBitVec = 256#64 ∧
      σ.regs.X1.toBitVec = 1#64 ∧ σ.regs.X2.toBitVec = 2#64 ∧
      σ.regs.X30.toBitVec = (lab ".L21_wc_main.sp0").toBitVec⟩

/-- **The exits**: the allocator's return at `.sp0` (its return's facts,
the frame kept), and its heap abort (`x30` past `.4_full`'s `bl scc_rt_abort`). -/
def wX : WX → ND
  | .sp0 => ⟨lab ".L21_wc_main.sp0", ⟨-80, []⟩, fun σ c => ∃ q : AGB ms lab, wcJ J0 σ q.1.c0 ∧
      (Alloc.EB lab ms q.1 .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-240, []⟩, fun σ c => σ.regs.X0 = 2 ∧
      σ.regs.X30.toBitVec = (lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec ∧ ∃ q : AGB ms lab, Jfull ms q.1 c ∧
      ∃ σe, J0 σe q.1.c0⟩

end Wc

/-- The allocator's region at the call. -/
abbrev wAR (R : Region) : Region := R.callee (-80) (-160) 0

/-- **The allocator's call context in `wc_main`'s region `R`** at the
memory `m` (`Hello1.RdCtx` at frame 80). -/
def WcCtx (ms : MemSide isaLSE2) (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (q : Call)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-80, []⟩ mC σC ∧ (wN lab Jc .call).J σC c ∧ (Alloc.N lab ms q .e).J (enter (-80) σC) c ∧
    CKept R (-80) (-160) 0 mC m

/-- **`wc_main`'s states up to the allocator's return inside `W`**, none
moved by `K`: its prologue's, the entry block's, and the allocator's in its
region (`Hello1.RdPreW` at frame 80). -/
structure WcPreW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J0 Jc : AS → Ctl → Prop) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 80 8
    ".L21_wc_main.stack_grow" [(.X0, 0)] J0
  e : BlkW W K exe endPc R F (wN (_root_.Executable.labels exe).label J0 .e) wcE
  alloc : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label →
    q.ra = ((_root_.Executable.labels exe).label ".L21_wc_main.sp0").toBitVec →
    AllocW ms q W K exe endPc (wAR R)
      (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms (_root_.Executable.labels exe).label R Jc q m)

/-- `wc_main` up to the allocator's return is inside the trivial
predicate, with no outside moves. -/
theorem WcPreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J0 Jc : AS → Ctl → Prop} :
    WcPreW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 Jc :=
  ⟨ProW.triv, BlkW.triv, fun q _ _ => Alloc.AllocW.triv ms q⟩

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` up to the allocator's return is one segment inside `W`**
in any valid layout of `wakeProg`: from its entry (invariant `J0`, `sp` at
the region's base, the limit word's facts for its frame of 80, `hlim`) to
the allocator's return at `.sp0` or its heap abort. The source at the entry
is at a box allocation the allocator's premises hold for (`Call.OKB`:
wake.w's `let o = new z`, after `let z = zero int`), with header `256`, one
object of two units (`hq`); the counter and the headers it may store are
unmapped in private memory under `F` (`hmem`). The allocator's return keeps
the hold recording the counter's old value (`Alloc.EB`): the source's
`new` (`TermRun.alloc`) is taken at `.sp0`'s `str x9, [x10]`, the box's
store (`Out.newStore`, `Alloc.newStore_ndW`). Its states lie in `W`, none
moved by `K` (`hW`). -/
theorem wake_wc_pre_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop} (hW : WcPreW W K exe endPc R F ms J0 J0)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec))
    (hq : ∀ σ c, J0 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (wX ms (_root_.Executable.labels exe).label J0 y) s c) := by
  have hin := wake_wcEIn
  simp only [wcEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  have e4 := label_labelGap hp hgap
  let lab := (_root_.Executable.labels exe).label
  have e4' : lab ".L21_wc_main.sp0" = lab ".L21_wc_main.0_entry" + Int64.ofNat (4 * 4) := e4
  refine SegW.seq (prologue_seg_ofW hp hend wake_wcPro (nb := wN lab J0 .e) (by decide) (by decide) hF hR hal
    (by show R.lo ≤ -80; omega) hhi (by simp [Spike.Lib.offOk]) rfl
    (by show SO.le ⟨-80, []⟩ (oFr 80) = true; decide) hW.pro ?_)
    (fn_segW (N := wN lab J0) (E := wX ms lab J0) (fun i => ?_) WN.e)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Ret0.setXReg_TPIDR]
  cases i
  case e =>
    refine seg_ndW (by simp [wcE]) wcE_ok hF hR hal hlo hhi (code_of hp hend h0 (ofNat4_zero _)) hW.e
      fun σ c hJ => ⟨c, .refl c, .inl ⟨WN.call, ?_, ?_, ?_⟩⟩
    · simp only [wN]; rw [wcE_run]
    · simp only [wN]; rw [wcE_run]; rfl
    · simp only [wN] at hJ ⊢
      rw [wcE_run]
      refine ⟨?_, rfl, rfl, rfl, ?_⟩
      · obtain ⟨σe, hJe, h16, h8, h80⟩ := hJ
        exact ⟨σe, hJe, h16, h8, h80⟩
      · rw [e4']
        show BitVec.ofInt 64 _ = _
        rw [Ret0.ofInt_bmod]
        simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
        rfl
  case call =>
    refine call_nd_FWK (KC := False) (lo' := -160) (hi' := 0) (M := fun _ => True)
      (Ne := fun g : AGB ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AGB ms lab => Alloc.EB lab ms g.1)
      hR hal hF (by show R.lo ≤ -80 + -160; omega) (by decide) (by show (-80 : Int) < R.hi; omega) (by decide)
      (by show (-80 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, -, h30⟩, ⟨-, -, h30', -⟩⟩ := hg
        have hra : g.1.ra = (lab ".L21_wc_main.sp0").toBitVec := by
          rw [← h30']; exact h30
        exact (seg_allocB_ofW hp hend wake_alloc hF' hR' hal' hlo' hhi' g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (allocW_mono (hW.alloc g.1 g.2 hra) fun m h =>
            ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨σe, hJe, -, -, -⟩, h0, h1, h2, -⟩
      obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
      exact ⟨⟨{ q with x29 := σC.regs.X29.toBitVec, ra := σC.regs.X30.toBitVec },
        ⟨{ hok.toS with }, hok.newOk, hok.term, hok.ev, hok.one⟩⟩, rfl,
        hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
    · rintro g y σC c σx c' σR ⟨⟨σe, hJe, h16, h8, h80⟩, -, -, -, h30⟩ ⟨hc, -, h30', -⟩ hx hreg - hsl
      cases y
      · refine .inr ⟨WX.sp0, ?_, rfl, g, ⟨σe, hc ▸ hJe, ?_, ?_, ?_⟩, ?_⟩
        · show lab ".L21_wc_main.sp0" = Int64.ofBitVec g.1.ra
          rw [← h30']
          show _ = Int64.ofBitVec σC.regs.X30.toBitVec
          rw [h30, int64_ofBitVec_toBitVec]
        · rw [hsl (-16) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), h16]
        · rw [hsl (-8) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), h8]
        · rw [hsl (-80) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), h80]
        · simp only [Alloc.EB] at hx ⊢
          rw [hreg]; exact hx
      · obtain ⟨h2, h30x, hfull⟩ := hx
        refine .inr ⟨WX.abort, rfl, rfl, ?_, ?_, g, hfull, σe, hc ▸ hJe⟩
        · show σR.regs.X0 = 2
          rw [hreg]; exact h2
        · show σR.regs.X30.toBitVec = _
          rw [hreg]; exact h30x

end WcFn

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_alloc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_pre_segW
