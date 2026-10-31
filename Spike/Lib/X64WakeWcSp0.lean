/-
**wake.w's `wc_main` at `.x18`: the box's store** (x86-64; twin of
`Spike/Lib/A64WakeWcSp0.lean`), inside `W`, in any valid layout of
`wakeCells` (`Spike/Lib/X64WakeCode.lean`), from checks decided once on the
cells (`decide +kernel`):

    .Lwc_main.x18:                      -- %rax = the box's cell (Alloc.EB)
      movq %rax, -16(%rbp); movq -16(%rbp), %rcx; movq $0, %rax  (wcS0)
      movq %rax, (%rcx)                 -- row: the box's store (Out.newStore)
      # fence st: no code under TSO
      call scc_rt_thread_reserve        -- `.x18 + 18`, the next segment's

The allocator's return at a box allocation keeps the source at wake.w's
`let o = new z` with the hold recording the counter's old value
(`Alloc.EB`, `wake_wc_pre_segW`'s exit `wX .x18`); the box's store is where
the source takes its `new` (`Alloc.newStore_ndW`). The segment ends there:
for every fresh label `l` the pair lands at `bX l A` (`o` bound to `l`'s
owned pointer, the cell `A` at `-16(%rbp)`), which one `ms.xa` continues in
(`hxa`, the instance's choice).

**The region's re-basing.** Up to the store the nodes are on `wc_main`'s
region `R` as handed over at the call (based at the return address's cell,
`X64WakeWcPre`: offsets `oWR = ⟨-72, [(.rbp, -8)]⟩`, the cell at slot
`-24`). The landing `bX` is stated on `R.fp (-8)`, the frame based at the
saved `%rbp`, at `WcClone.oW = ⟨-64, [(.rbp, 0)]⟩` (the cell at `-16`, the
saved `%rdi` at `-8`, the caller's `%rbp` and return address at `0` and
`8`), the region and offsets every later `wc_main` piece is stated on. The
store's landing `bXR` on `R` is carried there by `At.rebase`
(`X64AtRebase`, `bXR_rebase`): this is the only re-basing.

- `wcS0`, `boxSt`, `wcS0In`, `wake_wcS0In`: the block and the row at
  `.x18`;
- `sN`: the nodes (`.x18`, the store); `wcJF`: `wcJ`'s frame facts on
  `R.fp (-8)`; `bXR`, `bX`: the landing past the store on `R` and on
  `R.fp (-8)`; `bXR_rebase`: from one to the other;
- `BoxW`: the source's box facts at the allocator's ghost (one word, its
  representation `0`);
- `WcSp0W`: the nodes' states inside `W`;
- `wake_wc_sp0_segW`: the segment from `wX .x18` to the landing.
-/
import Spike.Lib.X64WakeWcPre
import Spike.Lib.X64AtRebase

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Alloc (Call)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field)

set_option linter.unusedSimpArgs false

/-! ## The block and the row -/

/-- `.x18`'s block: the cell to `-16(%rbp)`, the cell back, the box's word
`0`. -/
def wcS0 : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rcx
movq $0, %rax")).zip [4, 4, 7]

block_spec wcS0 (-72) 8 oWR wcS0

/-- The box's store (a row). -/
def boxSt : List (Directive × Nat) := [(stDir .rcx 0 .rax, 3)]

/-- **`.x18`'s block and row in `cells`**: the block at `0`, the store at
`15`. -/
def wcS0In (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.x18" 0 wcS0 && blockAtB cells ".Lwc_main.x18" 15 boxSt

theorem wake_wcS0In : wcS0In SccCode.wakeCells = true := by decide +kernel

/-! ## Nodes -/

/-- `.x18`'s nodes. -/
inductive SN where
  | b | st

/-- **`wcJ`'s frame facts on `R.fp (-8)`**: the return address at `8`, the
caller's `%rbp` at `0`, the saved `%rdi` at `-8`. -/
def wcJF (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J0 σe c ∧ σ.slot 8 = σe.slot 0 ∧ σ.slot 0 = σe.regs.rbp.toBitVec ∧
    σ.slot (-8) = σe.regs.rdi.toBitVec

section Sp0

variable (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J0 : AS → Ctl → Prop)

/-- **The nodes**: `.x18` (the allocator's return, `wX .x18`, with `%rbp`'s
offset) and the box's store (`%rax` the word `0`, `%rcx` and slot `-24`
the cell, the hold kept). -/
def sN : SN → ND
  | .b => ⟨lab ".Lwc_main.x18", oWR, (wX ms lab R J0 .x18).J⟩
  | .st => ⟨lab ".Lwc_main.x18" + Int64.ofNat 15, oWR, fun σ c => ∃ q : AGB ms lab, ∃ o : BitVec 64,
      wcJ J0 σ q.1.c0 ∧ c = holdCtr ms q.1.c0 o ∧ σ.regs.rax.toBitVec = 0#64 ∧
      σ.regs.rcx.toBitVec = σ.slot (-24) ∧ (σ.slot (-24)).toNat = ms.heap + 16 * o.toNat + ms.off 1 q.1.τ ∧
      o.toNat + ms.units 1 q.1.τ ≤ ms.cells ∧ ms.lo o.toNat⟩

end Sp0

section Land

variable (ms : MemSide isa) (lab : Label → Int64) (J0 : AS → Ctl → Prop)

/-- **The landing past the box's store on `R`** for the fresh label `l`
at the cell `A`, at `oWR` (the cell at slot `-24`). -/
def bXR (l : WeakMem.AllocLabel) (A : Nat) : ND :=
  ⟨lab ".Lwc_main.x18" + Int64.ofNat 18, oWR, fun σ c => ∃ q : AGB ms lab,
    wcJ J0 σ q.1.c0 ∧ (σ.slot (-24)).toNat = A ∧
    c = ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ ∧
    ∃ o : Nat, A = ms.heap + 16 * o + ms.off 1 q.1.τ ∧ o + ms.units 1 q.1.τ ≤ ms.cells⟩

/-- **The landing past the box's store** on `R.fp (-8)` (the frame based
at the saved `%rbp`, `WcClone.oW`) for the fresh label `l` at the cell
`A`: the source past its `new` (`o` bound to `l`'s owned pointer, no hold),
the cell at `-16`, the frame kept (`wcJF`); the cell the allocator's,
`ms.heap + 16·o + ms.off 1 τ` for a counter value `o` within the cells. -/
def bX (l : WeakMem.AllocLabel) (A : Nat) : ND :=
  ⟨lab ".Lwc_main.x18" + Int64.ofNat 18, ⟨-64, [(.rbp, 0)]⟩, fun σ c => ∃ q : AGB ms lab,
    wcJF J0 σ q.1.c0 ∧ (σ.slot (-16)).toNat = A ∧
    c = ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ ∧
    ∃ o : Nat, A = ms.heap + 16 * o + ms.off 1 q.1.τ ∧ o + ms.units 1 q.1.τ ≤ ms.cells⟩

end Land

/-- **The landing re-based**: a pair at `bXR l A` on `R` is at `bX l A` on
`R.fp (-8)` (`At.rebase` at `d = -8`). -/
theorem bXR_rebase {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {lab : Label → Int64} {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl} (h : At exe endPc R F (bXR ms lab J0 l A) s c) :
    At exe endPc (R.fp (-8)) F (bX ms lab J0 l A) s c :=
  At.rebase (d := -8) (n := bXR ms lab J0 l A) (n' := bX ms lab J0 l A) (by decide) rfl
    so_rebase_wcMain
    (fun σ c ⟨q, ⟨σe, hJe, h0, h8, h16⟩, hA, hc, ho⟩ =>
      ⟨q, ⟨σe, hJe, by simpa [enter] using h0, by simpa [enter] using h8, by simpa [enter] using h16⟩,
        by simpa [enter] using hA, hc, ho⟩) h

/-- **The source's box facts** at the allocator's ghost `q`: the value
`new` boxes is one word `w` of a one-word type, represented by `0` (wake.w's
`let z = zero[Int]`). -/
def BoxW (lbl : WeakMem.AllocLabel → Option Nat) (q : Call) : Prop :=
  ∃ w : TermRun.Word, q.ws = [w] ∧ TermRun.accs q.τ = some [.one] ∧ Scc.Sem.ValRep lbl w.val 0

/-- **`.x18`'s states inside `W`**, none moved by `K`: the block's and the
store's. -/
structure WcSp0W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J0 : AS → Ctl → Prop) : Prop where
  b : BlkW W K exe endPc R F (sN ms (_root_.Executable.labels exe).label R J0 .b) wcS0
  st : NodeW W K exe endPc R F (sN ms (_root_.Executable.labels exe).label R J0 .st)

/-- `.x18` is inside the trivial predicate, with no outside moves. -/
theorem WcSp0W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J0 : AS → Ctl → Prop} :
    WcSp0W (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 :=
  ⟨BlkW.triv, NodeW.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` at `.x18` is one segment inside `W`** in any valid layout
of `wakeCells`: from the allocator's return at a box allocation (`wX .x18`)
to the box's store, where the source takes its `new` and every fresh
label's landing `bX l A` on `R.fp (-8)` is one `ms.xa` continues in
(`hxa`); the segment has no other exit (`Q` any). The value boxed is one
word represented by `0` (`hbox`); every cell the allocator may return is
mapped for writing and unmapped in private memory under `F` (`hcell`). Its
states lie in `W`, none moved by `K` (`hW`). -/
theorem wake_wc_sp0_segW {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {J0 : AS → Ctl → Prop} (hW : WcSp0W W K exe endPc R F ms J0)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J0 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J0 σ q.1.c0) →
      ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none →
      At exe endPc (R.fp (-8)) F (bX ms (_root_.Executable.labels exe).label J0 l A) s c → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc R F (wX ms (_root_.Executable.labels exe).label R J0 .x18)) Q := by
  have hin := wake_wcS0In
  simp only [wcS0In, Bool.and_eq_true] at hin
  obtain ⟨h0, h15⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  refine ((fn_segW (N := sN ms lab R J0) (E := fun x : Empty => x.elim) (fun i => ?_) SN.b).mono_post
    fun _ _ ⟨x, _⟩ => x.elim).mono_pre
    fun _ _ h => Hello1.At.rbp_addr (J := (wX ms lab R J0 .x18).J) h fun _ _ ⟨_, _, hb, _⟩ => hb
  cases i
  case b =>
    refine seg_ndW (by simp [wcS0]) wcS0_ok hF hR hlo hhi (code_field hp hend h0 (ofNat_zero' _)) hW.b
      fun σ c hJ => ⟨c, .refl c, .inl ⟨SN.st, ?_, ?_, ?_⟩⟩
    · simp only [sN]; rw [wcS0_run]; rfl
    · simp only [sN]; rw [wcS0_run]; rfl
    · simp only [sN, wX] at hJ ⊢
      rw [wcS0_run]
      obtain ⟨q, ⟨σe, hJe, h0', h8, h16⟩, -, o, hc, hx0, hle, hlo', -⟩ := hJ
      have h1 := q.2.one
      rw [h1] at hx0 hle
      refine ⟨q, o, ⟨σe, hJe, ?_, ?_, ?_⟩, hc, ?_, ?_, ?_, hle, hlo'⟩
      · simp [Spike.Lib.upd, h0']
      · simp [Spike.Lib.upd, h8]
      · simp [Spike.Lib.upd, h16]
      · simp [Reg64s.set64]
      · simp [Spike.Lib.upd, Reg64s.set64, Reg64s.get64]
      · simpa [Spike.Lib.upd, Reg64s.get64] using hx0
  case st =>
    refine Alloc.newStore_ndW (b := .rcx) (r := .rax) (k := 0) (z := 3)
      (fun l A => bXR ms lab J0 l A) (code_field hp hend h15 rfl)
      (fun l A s c hl h => hxa l A s c hl (bXR_rebase h)) hW.st fun m σ c hA hD hJ => ?_
    obtain ⟨q, o, hwc, rfl, h0, hcx, hA24, hle, hlo'⟩ := hJ
    have hj : ∃ σ, J0 σ q.1.c0 := let ⟨σe, hJe, _⟩ := hwc; ⟨σe, hJe⟩
    obtain ⟨w, hws, hacc, hrep⟩ := hbox q hj
    have ha : bAddr σ.regs .rcx 0 = σ.slot (-24) := by
      rw [← hcx]; simp [bAddr, Reg64s.get64]
    have ha' : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 (ms.heap + 16 * o.toNat + ms.off 1 q.1.τ) := by
      rw [ha, ← hA24, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    obtain ⟨hmp, hun⟩ := hcell q hj o.toNat hlo' hle
    refine ⟨q.2.newOk, ha' ▸ hmp, ha' ▸ hun m hD, q.1.x, q.1.a, q.1.τ, q.1.e, w, TermRun.cst (.num o.toNat),
      o.toNat, q.2.term, hws ▸ q.2.ev, hacc, ?_, rfl, rfl, by rw [ha, hA24], hle, fun l _ => ⟨?_, rfl, q, hwc,
      by rw [ha], rfl, o.toNat, by rw [ha, hA24], hle⟩⟩
    · have : (σ.regs.get64 .rax).toNat = 0 := by simp [Reg64s.get64, h0]
      rw [this]; exact hrep
    · show lab ".Lwc_main.x18" + Int64.ofNat 18 = lab ".Lwc_main.x18" + Int64.ofNat 15 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl

end Seg

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wcS0In' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wcS0In

/-- info: 'Spike.Lib.X64.Flow.WakeWc.bXR_rebase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.bXR_rebase

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_sp0_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_sp0_segW
