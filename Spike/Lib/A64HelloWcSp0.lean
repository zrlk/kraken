/-
**`hello.w`'s `wc_main` from the box's allocator's return to `.sp3`** (AArch64), inside `W`, in any
valid layout of `helloProg`, from checks decided once on the program (`decide +kernel`). It is the twin of
`Spike/Lib/A64WakeWcSp0.lean` and `Spike/Lib/A64WakeWcRes.lean` at hello's `wc_main` (frame 144, the cell at
`[sp, #40]`):

    .L22_wc_main.sp0:                   -- x0 = the box's cell (Alloc.EB)
      str x0, [sp, #40]; movz x9, #0; ldr x10, [sp, #40]        (wcS0H)
      str x9, [x10]                     -- row: the box's store (Out.newStore)
      dmb ishst                         -- row: the source's `publish o` (FenceRun.pub)
      bl scc_rt_thread_reserve          -- (resBH), x30 = .sp3
    .L22_wc_main.sp3:                   -- x0 = n + 1 = 1

There are two segments, as in wake. The first ends at the box's store: for every fresh label `l` the pair lands at
`bXH l A`, which one `ms.xa` continues in (`hxa`, the instance's choice). The second starts from that landing: at
the fence the source publishes the box and runs locally to its spawn-ready control (`hfr`:
`HelloMainPreSrc.src_spawnH`), and the reserve runs at the counter's old value `0`.

- `wcS0H`, `wcS0InH`, `hello_wcS0InH`, `resBH`, `wcResInH`, `hello_wcResInH`, `hello_reserveIn`: the blocks, rows and
  checks.
- `sNH`, `bXH`, `WcSp0WH`, `hello_wc_sp0_segW`: `.sp0` to the box's store's landing.
- `wFrH`, `rNH`, `rXH`, `rNeH`, `rARH`, `ResCtxH`, `WcResWH`, `hello_wc_res_segW`: the landing to `.sp3`.
-/
import Spike.Lib.A64HelloWcPre

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.Flow.WakeWc (AGB WN WX SN RsN BoxW boxSt boxSt_eq pubF pubF_eq reserveW_mono)
open Spike.Lib.A64.Rt.Reserve (ResG RN rvN rvX ResOkA ReserveW reserve_segWA)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

/-! ## The blocks, the rows and the checks -/

/-- `.sp0`'s block: the cell to `[sp, #40]`, the box's word `0`, the cell back. -/
def wcS0H : List Directive := parseAArch64("str x0, [sp, #40]
movz x9, #0
ldr x10, [sp, #40]")

block_spec wcS0H (-144) 0 (⟨-144, []⟩ : SO) wcS0H

/-- **`.sp0`'s block and the box's store in `prog`**: the block at `0`, the store at `3`. -/
def wcS0InH (prog : List Directive) : Bool :=
  blockAt prog ".L22_wc_main.sp0" 0 wcS0H && blockAt prog ".L22_wc_main.sp0" 3 boxSt

theorem hello_wcS0InH : wcS0InH SccCode.helloProg = true := by decide +kernel

/-- The reserve's call. -/
def resBH : List Directive := parseAArch64("bl scc_rt_thread_reserve")

block_spec resBH (-144) 0 (⟨-144, []⟩ : SO) resBH

/-- **The fence and the call in `prog`**: at `.sp0`'s `4` and `5`, `.sp3` right after. -/
def wcResInH (prog : List Directive) : Bool :=
  blockAt prog ".L22_wc_main.sp0" 4 pubF && blockAt prog ".L22_wc_main.sp0" 5 resBH &&
    labelGap prog ".L22_wc_main.sp0" ".L22_wc_main.sp3" 6

theorem hello_wcResInH : wcResInH SccCode.helloProg = true := by decide +kernel

theorem hello_reserveIn : Flow.Reserve.reserveIn SccCode.helloProg = true := by decide +kernel

/-! ## `.sp0` to the box's store -/

section Sp0

variable (ms : MemSide isaLSE2) (lab : Label → Int64) (J1 : AS → Ctl → Prop)

/-- **The nodes**: `.sp0` (the allocator's return, `wXH .sp0`) and the box's store (`x9` the word `0`, `x10` and
`[sp, #40]` the cell, the hold kept). -/
def sNH : SN → ND
  | .b => wXH ms lab J1 .sp0
  | .st => ⟨lab ".L22_wc_main.sp0" + Int64.ofNat (4 * 3), ⟨-144, []⟩, fun σ c => ∃ q : AGB ms lab,
      ∃ o : BitVec 64, wcJH J1 σ q.1.c0 ∧ c = holdCtr ms q.1.c0 o ∧ σ.regs.X9.toBitVec = 0#64 ∧
      σ.regs.X10.toBitVec = σ.slot (-104) ∧ (σ.slot (-104)).toNat = ms.heap + 16 * o.toNat + ms.off 1 q.1.τ ∧
      o.toNat + ms.units 1 q.1.τ ≤ ms.cells ∧ ms.lo o.toNat⟩

/-- **The landing past the box's store** for the fresh label `l` at the cell `A`: the source past its `new` (`x`
bound to `l`'s owned pointer, no hold), the cell at `[sp, #40]`, the frame kept; the cell the allocator's. -/
def bXH (l : WeakMem.AllocLabel) (A : Nat) : ND :=
  ⟨lab ".L22_wc_main.sp0" + Int64.ofNat (4 * 4), ⟨-144, []⟩, fun σ c => ∃ q : AGB ms lab,
    wcJH J1 σ q.1.c0 ∧ (σ.slot (-104)).toNat = A ∧
    c = ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ ∧
    ∃ o : Nat, A = ms.heap + 16 * o + ms.off 1 q.1.τ ∧ o + ms.units 1 q.1.τ ≤ ms.cells⟩

end Sp0

/-- **`.sp0`'s states inside `W`**, none moved by `K`: the block's and the store's. -/
structure WcSp0WH (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J1 : AS → Ctl → Prop) : Prop where
  b : BlkW W K exe endPc R F (sNH ms (_root_.Executable.labels exe).label J1 .b) wcS0H
  st : NodeW W K exe endPc R F (sNH ms (_root_.Executable.labels exe).label J1 .st)

/-- `.sp0` is inside the trivial predicate, with no outside moves. -/
theorem WcSp0WH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop} :
    WcSp0WH (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J1 :=
  ⟨BlkW.triv, fun _ _ _ => ⟨trivial, fun _ h => h⟩⟩

section Sp0Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` at `.sp0` is one segment inside `W`** in any valid layout of `helloProg`: from the allocator's
return at a box allocation (`wXH .sp0`) to the box's store, where the source takes its `new` and every fresh
label's landing `bXH l A` is one `ms.xa` continues in (`hxa`); the segment has no other exit (`Q` any).
- The value boxed is one word represented by `0` (`hbox`).
- Every cell the allocator may return is mapped for writing and unmapped in private memory under `F` (`hcell`).
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_wc_sp0_segW {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {J1 : AS → Ctl → Prop} (hW : WcSp0WH W K exe endPc R F ms J1)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) →
      ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c →
      ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc R F (wXH ms (_root_.Executable.labels exe).label J1 .sp0)) Q := by
  have hin := hello_wcS0InH
  simp only [wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  refine (fn_segW (N := sNH ms lab J1) (E := fun x : Empty => x.elim) (fun i => ?_) SN.b).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case b =>
    refine seg_ndW (by simp [wcS0H]) wcS0H_ok hF hR hal hlo hhi (code_of hp hend h0 (ofNat4_zero _)) hW.b
      fun σ c hJ => ⟨c, .refl c, .inl ⟨SN.st, ?_, ?_, ?_⟩⟩
    · simp only [sNH, wXH]; rw [wcS0H_run]
      rw [show Int64.ofNat (4 * 3) = 4 + 4 + 4 from rfl]; simp only [Int64.add_assoc]
    · simp only [sNH, wXH]; rw [wcS0H_run]; rfl
    · simp only [sNH, wXH] at hJ ⊢
      rw [wcS0H_run]
      obtain ⟨q, ⟨σe, hJe, h16, h8, h0', h1', h2', h3', h4'⟩, o, hc, hx0, hle, hlo', -, -⟩ := hJ
      have h1 := q.2.one
      rw [h1] at hx0 hle
      refine ⟨q, o, ⟨σe, hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hc, rfl, ?_, ?_, hle, hlo'⟩
      · simp [Spike.Lib.upd, h16]
      · simp [Spike.Lib.upd, h8]
      · simp [Spike.Lib.upd, h0']
      · simp [Spike.Lib.upd, h1']
      · simp [Spike.Lib.upd, h2']
      · simp [Spike.Lib.upd, h3']
      · simp [Spike.Lib.upd, h4']
      · simp [Spike.Lib.upd]
      · simpa [Spike.Lib.upd] using hx0
  case st =>
    refine Alloc.newStore_ndW (t := .X9) (b := .X10) (i := 0) (bXH ms lab J1)
      (code_of hp hend (boxSt_eq ▸ h3) rfl) hxa hW.st fun m σ c hA hD hJ => ?_
    obtain ⟨q, o, hwc, rfl, h9, h10, hA104, hle, hlo'⟩ := hJ
    have hj : ∃ σ, J1 σ q.1.c0 := let ⟨σe, hJe, _⟩ := hwc; ⟨σe, hJe⟩
    obtain ⟨w, hws, hacc, hrep⟩ := hbox q hj
    have ha : rAddr σ.regs .X10 0 = σ.slot (-104) := by
      rw [Ret0.rAddr_x10 h10]; simp
    have ha' : rAddr σ.regs .X10 0 = BitVec.ofNat 64 (ms.heap + 16 * o.toNat + ms.off 1 q.1.τ) := by
      rw [ha, ← hA104, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    obtain ⟨hmp, hun⟩ := hcell q hj o.toNat hlo' hle
    refine ⟨q.2.newOk, ha' ▸ hmp, ha' ▸ hun m hD, q.1.x, q.1.a, q.1.τ, q.1.e, w, TermRun.cst (.num o.toNat),
      o.toNat, q.2.term, hws ▸ q.2.ev, hacc, ?_, rfl, rfl, by rw [ha, hA104], hle, fun l _ => ⟨?_, rfl, q, hwc,
      by rw [ha], rfl, o.toNat, by rw [ha, hA104], hle⟩⟩
    · rw [Ret0.getRegOrZr_x9, h9]; exact hrep
    · show lab ".L22_wc_main.sp0" + Int64.ofNat (4 * 4) = lab ".L22_wc_main.sp0" + Int64.ofNat (4 * 3) + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl

end Sp0Seg

/-! ## The box's store's landing to `.sp3` -/

section Res

variable (ms : MemSide isaLSE2) (lab : Label → Int64) (J1 : AS → Ctl → Prop)

/-- **`wc_main`'s frame past the box's store**: some allocator's ghost whose caller's frame it is (`wcJH`), the cell
`A` at `[sp, #40]`. -/
def wFrH (A : Nat) (σ : AS) : Prop := ∃ q : AGB ms lab, wcJH J1 σ q.1.c0 ∧ (σ.slot (-104)).toNat = A

variable (S Q : WeakMem.AllocLabel → Nat → Ctl → Prop)

/-- **The nodes**: the fence (some fresh label's landing past the box's store, the source at `Q l A`), the call
block (the source at `S l A`), the reserve's entry (`x30 = .sp3`). -/
def rNH : RsN → ND
  | .f => ⟨lab ".L22_wc_main.sp0" + Int64.ofNat (4 * 4), ⟨-144, []⟩, fun σ c => ∃ l A,
      (bXH ms lab J1 l A).J σ c ∧ Q l A c⟩
  | .bl => ⟨lab ".L22_wc_main.sp0" + Int64.ofNat (4 * 5), ⟨-144, []⟩, fun σ c => ∃ l A, S l A c ∧
      wFrH ms lab J1 A σ⟩
  | .call => ⟨lab "scc_rt_thread_reserve", ⟨-144, []⟩, fun σ c => (∃ l A, S l A c ∧ wFrH ms lab J1 A σ) ∧
      σ.regs.X30.toBitVec = (lab ".L22_wc_main.sp3").toBitVec⟩

/-- **The exit at `.sp3`**: the reserve's result `1` in `x0`, the source at `S l A`, the frame kept. -/
def rXH : Unit → ND
  | () => ⟨lab ".L22_wc_main.sp3", ⟨-144, []⟩, fun σ c => ∃ l A, S l A c ∧ wFrH ms lab J1 A σ ∧
      σ.regs.X0.toBitVec = 1#64⟩

end Res

/-- The reserve's entry for the frame ghosts `g.1` and the control `g.2`, at the counter's old value `0`. -/
def rNeH (lab : Label → Int64) (g : Flow.Reserve.G × Ctl) : ND := rvN lab ⟨g.1, 0#64, g.2⟩ .e

/-- The reserve's region at the call (its frame of 48). -/
abbrev rARH (R : Region) : Region := R.callee (-144) (-48) 0

/-- **The reserve's call context in `wc_main`'s region `R`** at the memory `m`, for the ghosts `g`. -/
def ResCtxH (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (g : Flow.Reserve.G × Ctl)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-144, []⟩ mC σC ∧ Jc σC c ∧ (rNeH lab g).J (enter (-144) σC) c ∧ CKept R (-144) (-48) 0 mC m

/-- **`wc_main`'s states from the fence to `.sp3` inside `W`**, none moved by `K`: the fence's, the call block's,
and the reserve's in its region (at the counter's old value `0`, returning to `.sp3`). -/
structure WcResWH (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J1 : AS → Ctl → Prop)
    (S Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  f : NodeW W K exe endPc R F (rNH ms (_root_.Executable.labels exe).label J1 S Q .f)
  bl : BlkW W K exe endPc R F (rNH ms (_root_.Executable.labels exe).label J1 S Q .bl) resBH
  res : ∀ g : Flow.Reserve.G × Ctl, g.1.ra = ((_root_.Executable.labels exe).label ".L22_wc_main.sp3").toBitVec →
    ∀ i, ReserveW W K exe endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH (_root_.Executable.labels exe).label R
        (rNH ms (_root_.Executable.labels exe).label J1 S Q .call).J g m) ⟨g.1, 0#64, g.2⟩ i

/-- From the fence to `.sp3` inside the trivial predicate, with no outside moves. -/
theorem WcResWH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcResWH (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J1 S Q := by
  refine ⟨fun _ _ _ => ⟨trivial, fun _ h => h⟩, BlkW.triv, fun _ _ i => ?_⟩
  cases i <;> dsimp only [ReserveW] <;> first | exact BlkW.triv | exact fun _ _ _ => ⟨trivial, fun _ h => h⟩

section ResSeg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from the box's store to `.sp3` is one segment inside `W`** in any valid layout of `helloProg`: from
the landing past the box's store (`bXH l A`, some fresh label `l`, the source at `Q l A`) to `.sp3` (`rXH`).
- At the fence the source publishes the box and runs locally to `S l A` (`hfr`, from any source at `Q l A`).
- The reserve runs at the counter's old value `0` (`hres`), returning `1`, the source unchanged.
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_wc_res_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hW : WcResWH W K exe endPc R F ms J1 S Q)
    (hfr : ∀ (q : AGB ms (_root_.Executable.labels exe).label) (l : WeakMem.AllocLabel) (A : Nat),
      Q l A ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ →
      ∃ c', FenceRun p ms.pub .st
        ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ c' ∧ S l A c')
    (hres : ∀ g : Flow.Reserve.G × Ctl, ResOkA ms F exe endPc (rARH R) F ⟨g.1, 0#64, g.2⟩) :
    SegW W K p lbl ms
      (fun s c => ∃ l A, At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c ∧ Q l A c)
      (fun s c => ∃ x, At exe endPc R F (rXH ms (_root_.Executable.labels exe).label J1 S x) s c) := by
  have hin := hello_wcResInH
  simp only [wcResInH, Bool.and_eq_true] at hin
  obtain ⟨⟨h4, h5⟩, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e3 : lab ".L22_wc_main.sp3" = lab ".L22_wc_main.sp0" + Int64.ofNat (4 * 6) := label_labelGap hp hgap
  refine (fn_segW (N := rNH ms lab J1 S Q) (E := rXH ms lab J1 S) (fun i => ?_) RsN.f).mono_pre ?_
  rotate_left
  · rintro s c ⟨l, A, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hQ⟩
    exact ⟨he, hn, hdc, hpc, σ, hA, hD, l, A, hJ, hQ⟩
  cases i
  case f =>
    refine dmb_ndW (code_of hp hend (pubF_eq ▸ h4) rfl) hW.f fun σ c hJ => ?_
    obtain ⟨l, A, ⟨q, hwc, h104, rfl, -⟩, hQ⟩ := hJ
    obtain ⟨c', hr, hS⟩ := hfr q l A hQ
    refine ⟨c', hr, .inl ⟨RsN.bl, ?_, rfl, l, A, hS, q, hwc, h104⟩⟩
    show lab ".L22_wc_main.sp0" + Int64.ofNat (4 * 5) = lab ".L22_wc_main.sp0" + Int64.ofNat (4 * 4) + Int64.ofNat 4
    rw [Int64.add_assoc]; rfl
  case bl =>
    refine seg_ndW (by simp [resBH]) resBH_ok hF hR hal (by show R.lo ≤ -144; omega) hhi
      (code_of hp hend h5 rfl) hW.bl fun σ c hJ => ⟨c, .refl c, .inl ⟨RsN.call, ?_, ?_, ?_⟩⟩
    · simp only [rNH]; rw [resBH_run]
    · simp only [rNH]; rw [resBH_run]; rfl
    · simp only [rNH] at hJ ⊢
      rw [resBH_run]
      refine ⟨hJ, ?_⟩
      rw [e3]
      show BitVec.ofInt 64 _ = _
      rw [Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
      rfl
  case call =>
    refine call_nd_FWK (KC := False) (lo' := -48) (hi' := 0) (M := fun _ => True)
      (Ne := rNeH lab) (Ex := fun g : Flow.Reserve.G × Ctl => rvX ⟨g.1, 0#64, g.2⟩)
      hR hal hF (by show R.lo ≤ -144 + -48; omega) (by decide) (by show (-144 : Int) < R.hi; omega) (by decide)
      (by show (-144 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h30⟩, ⟨-, -, -, h30'⟩⟩ := hg
        have hra : g.1.ra = (lab ".L22_wc_main.sp3").toBitVec := by
          rw [← h30']; exact h30
        exact (reserve_segWA hp hend hello_reserveIn hF' hR' hal' hlo' hhi' hFF ⟨g.1, 0#64, g.2⟩
          (by show (0#64 : BitVec 64).toNat + 1 ≤ 1023; decide) ((hres g).mono hFF)
          fun i => reserveW_mono (hW.res g hra i) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨-, -⟩
      exact ⟨(⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, c), rfl, rfl, rfl, rfl, rfl⟩
    · rintro g ⟨⟩ σC c σx c' σR ⟨⟨l, A, hS, q, ⟨σe, hJe, h16, h8, h0', h1', h2', h3', h4'⟩, h104⟩, h30⟩
        ⟨hc, -, -, h30'⟩ ⟨hc', hpost⟩ hreg - hsl
      have hkeep : ∀ k : Int, -144 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rNH]; omega)
      refine .inr ⟨(), ?_, rfl, l, A, hc' ▸ hc ▸ hS, ⟨q, ⟨σe, hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · show lab ".L22_wc_main.sp3" = Int64.ofBitVec g.1.ra
        rw [← h30']
        show _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
      · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
      · rw [hkeep (-144) (by omega) (by omega) (by omega), h0']
      · rw [hkeep (-136) (by omega) (by omega) (by omega), h1']
      · rw [hkeep (-128) (by omega) (by omega) (by omega), h2']
      · rw [hkeep (-120) (by omega) (by omega) (by omega), h3']
      · rw [hkeep (-112) (by omega) (by omega) (by omega), h4']
      · rw [hkeep (-104) (by omega) (by omega) (by omega), h104]
      · rw [hreg, Rt.Reserve.post_x0 hpost]; rfl

end ResSeg

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wcS0InH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wcS0InH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wcResInH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wcResInH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_reserveIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_reserveIn

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_sp0_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_sp0_segW

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_res_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_res_segW
